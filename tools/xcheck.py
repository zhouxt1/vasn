#!/usr/bin/env python3
"""Check vasnc's codec for a schema against pycrate and asn1c.

    tools/xcheck.py SCHEMA.asn1 [-n N] [--seed S] [--types A,B] [--vectors FILE]
                    [--containing octets|decode] [--aper]

Builds three decoders for SCHEMA: ours (vasnc and its `--driver`, compiled
with Verus, --no-verify: the per-type verification is a separate run), asn1c's
converter-example (tools/get-asn1c.sh), and pycrate's generated module. Then:

* random values: N per type from our generator (`driver gen`), encoded by our
  encoder. pycrate and asn1c must each decode the bytes to the same value as
  ours (compared as JER, X.697) and re-encode them to the same bytes.
* vectors (--vectors): encodings written by hand from X.691, one per line,

      accept TYPE HEX JER     every decoder gives this value, and ours re-encodes to HEX
      reject TYPE HEX         every decoder rejects it
      deviates-encode TOOL TYPE   TOOL decodes TYPE as X.691 does but encodes it
                              otherwise: its re-encodings are not compared
      deviates TOOL TYPE      TOOL is known to deviate from X.691 on TYPE: the
                              random-value checks leave TOOL out for TYPE

  X.691 is the judge. A line where pycrate or asn1c disagree with X.691 is
  marked in the file, `accept! ...` / `reject! ...` with a comment, and a
  disagreement there is reported but not counted as ours.

`--aper` checks ALIGNED PER instead of UNALIGNED: vasnc's `--aper`, asn1c's
`-iaper`/`-oaper`, pycrate's `from_aper`/`to_aper`.

`--containing` is passed to vasnc. `OCTET STRING (CONTAINING T)` is octets
to asn1c and a T to pycrate, so a schema that has one is checked against
asn1c alone under `octets` (the default) and against pycrate alone under
`decode`.

Exit status is 1 if any check of ours failed.
"""
import argparse
import collections
import contextlib
import glob
import importlib.util
import io
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
VERUS = os.environ.get("VERUS") or shutil.which("verus") or str(ROOT / "tools/verus-x86-linux/verus")
VASNC = ROOT / "target/release/vasnc"
VASN = ROOT / "target/verus"          # vasn built by Verus, as crate-dir Makefiles do
ASN1C = ROOT / "tools/asn1c/bin/asn1c"
# rasn-compiler 0.16.0 (bench/decode/build.sh installs it), and the rasn it
# generates bindings for
RASNC = ROOT / "bench/decode/rasn/tool/bin/rasn_compiler_cli"
RASN_VERSION = "=0.28.14"
# one target directory for every schema's rasn driver: rasn builds once
RASN_TARGET = ROOT / "target/xcheck/rasn-target"
# a REAL's exact decimal can run to thousands of digits (2^32767 has 9865)
sys.set_int_max_str_digits(0)
sys.path[:0] = glob.glob("/usr/local/lib/python3*/dist-packages/pycrate-*.egg")


# "uper" or "aper", from --aper: which PER variant every tool is asked for
VARIANT = "uper"

# a wide ENUMERATED or CHOICE compiles to a deep if/else chain, which
# overflows rustc's default stack (as vasnc's generated Makefiles note)
os.environ.setdefault("RUST_MIN_STACK", "2000000000")


def sh(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        sys.exit(f"{' '.join(map(str, cmd))} failed:\n{r.stdout}{r.stderr}")
    return r.stdout


# ------------------------------------------------------------------ builds

def src_dir(crate):
    """vasn's sources are here; vbits' and vsimd's are wherever cargo put
    verified_binary_formats (tools/dep-src.sh)."""
    if crate == "vasn":
        return ROOT / "vasn" / "src"
    return pathlib.Path(sh([ROOT / "tools" / "dep-src.sh", crate]).strip())


def build_tools():
    """vasnc with cargo, and vbits, vsimd and vasn with Verus: the generated
    module imports their .vir, which only Verus writes. vasn is rebuilt
    whenever vbits or vsimd is, since an rlib built against another build of
    either is refused."""
    sh(["cargo", "build", "--release", "-q", "-p", "vasnc"], cwd=ROOT)
    VASN.mkdir(parents=True, exist_ok=True)
    rebuilt = False
    for crate, deps in (("vbits", []), ("vsimd", []), ("vasn", ["vbits", "vsimd"])):
        rlib = VASN / f"lib{crate}.rlib"
        src = src_dir(crate)
        srcs = list(src.rglob("*.rs"))
        if rebuilt or not rlib.exists() or any(f.stat().st_mtime > rlib.stat().st_mtime for f in srcs):
            imports = [a for d in deps for a in
                       ("--import", f"{d}={VASN}/{d}.vir", "--extern", f"{d}={VASN}/lib{d}.rlib")]
            silent = ["--triggers-mode", "silent"] if crate == "vsimd" else []
            sh([VERUS, "--crate-type=lib", "--crate-name", crate, "--compile", "-C", "opt-level=3",
                *silent, *imports, "--export", VASN / f"{crate}.vir", src / "lib.rs", "-o", rlib])
            rebuilt = True


def vasn_args():
    """What a crate built on vasn passes Verus. vbits is imported too, since
    vasn's specs unfold to it, and -L lets rustc find its rlib behind vasn's."""
    return ["-L", VASN, "--import", f"vbits={VASN}/vbits.vir", "--import", f"vsimd={VASN}/vsimd.vir",
            "--import", f"vasn={VASN}/vasn.vir", "--extern", f"vasn={VASN}/libvasn.rlib"]


def build_ours(schema, d, containing):
    rs, drv = d / "m.rs", d / "driver.rs"
    aper = ["--aper"] if VARIANT == "aper" else []
    out = subprocess.run([VASNC, schema, rs, "--driver", drv, "--containing", containing, *aper],
                         capture_output=True, text=True)
    skipped = [l.strip() for l in out.stderr.splitlines() if l.strip().startswith("skipped")]
    if out.returncode != 0:
        sys.exit(out.stderr)
    sh([VERUS, "--compile", "-C", "opt-level=1", "--no-verify", *vasn_args(),
        drv, "-o", d / "driver"])
    return d / "driver", skipped


def build_asn1c(schema, d):
    a = d / "asn1c"
    shutil.rmtree(a, ignore_errors=True)
    a.mkdir()
    other = "-no-gen-UPER" if VARIANT == "aper" else "-no-gen-APER"
    # XCHECK_ASN1C_FLAGS: more of asn1c's options (-findirect-choice, as the
    # RAN stacks build their protocols with)
    extra = os.environ.get("XCHECK_ASN1C_FLAGS", "").split()
    sh([ASN1C, "-pdu=all", "-fcompound-names", *extra, "-no-gen-BER", "-no-gen-XER", "-no-gen-OER",
        other, schema], cwd=a)
    # XCHECK_ASN1C_RANGE8=1: asn1c's ALIGNED decoder with its known 8-bit
    # INTEGER bug fixed (it aligns before a range of 129 to 255 values, which
    # X.691 11.5.7.1 does not; tests/ioc/range8.asn1), so that what that bug
    # hides shows
    if VARIANT == "aper" and os.environ.get("XCHECK_ASN1C_RANGE8"):
        f = a / "INTEGER_aper.c"
        src = f.read_text()
        old = "} else if (ct->range_bits == 8) {\n                    if (aper_get_align(pd) < 0)"
        if src.count(old) != 1:
            sys.exit("XCHECK_ASN1C_RANGE8: asn1c's INTEGER_aper.c is not the one the fix is for")
        f.write_text(src.replace(old, "} else if (ct->range_bits == 8) {\n                    "
                                 "if (ct->upper_bound - ct->lower_bound == 255 && aper_get_align(pd) < 0)"))
    sh(["make", "-s", "-f", "converter-example.mk", f"-j{os.cpu_count()}"], cwd=a)
    return a / "converter-example"


RASN_MAIN = r"""// Generated by tools/xcheck.py: rasn's PER codec for every type of one
// schema, by ASN.1 name.
//   driver dec TYPE < hex-lines   per line: `ok REENC JER`, or `err WHY`
#[allow(warnings, clippy::all)]
mod m;
use std::io::BufRead;

fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }

fn run<T: rasn::Decode + rasn::Encode>() {
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let line = line.trim();
        if line.is_empty() { continue; }
        let b: Option<Vec<u8>> = (0..line.len()).step_by(2)
            .map(|i| line.get(i..i + 2).and_then(|x| u8::from_str_radix(x, 16).ok())).collect();
        let Some(b) = b else { println!("err not hex"); continue };
        match rasn::PERV::decode::<T>(&b) {
            Ok(v) => {
                let e = rasn::PERV::encode(&v).map(|e| hex(&e)).unwrap_or_else(|_| "-".into());
                match rasn::jer::encode(&v) {
                    Ok(j) => println!("ok {e} {}", j.replace('\n', " ")),
                    Err(err) => println!("err JER: {}", err.to_string().replace('\n', " ")),
                }
            }
            Err(err) => println!("err {}", err.to_string().replace('\n', " ")),
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match (args.get(1).map(String::as_str), args.get(2).map(String::as_str)) {
        (Some("types"), _) => { for t in [TYPES] { println!("{t}"); } }
ARMS        _ => { eprintln!("usage: driver types | dec TYPE"); std::process::exit(2); }
    }
}
"""


def build_rasn(schema, d, asn_types):
    """rasn-compiler's bindings for the schema, and a driver over them. A type
    is looked up by its ASN.1 name less its hyphens, which is how
    rasn-compiler names one; a type it does not have is left out."""
    r = d / "rasn"
    shutil.rmtree(r / "src", ignore_errors=True)
    (r / "src").mkdir(parents=True)
    out = subprocess.run([RASNC, "-m", schema, "-o", r / "src/m.rs"], capture_output=True, text=True)
    code = (r / "src/m.rs").read_text() if (r / "src/m.rs").exists() else ""
    if not code.strip():
        raise SystemExit((out.stderr or out.stdout or "rasn-compiler wrote nothing").strip()[-300:])
    # rasn-compiler makes a REAL an f64 and still derives Eq and Hash on what
    # holds one, which f64 has neither of; nothing here needs them unless a
    # SET OF does
    if "f64" in code and "SetOf" not in code:
        code = code.replace(" , Eq , Hash)", ")")
        (r / "src/m.rs").write_text(code)
    # the generated items, per module
    names = {}
    for mod, body in re.findall(r"pub mod (\w+) \{(.*?)(?=pub mod \w+ \{|\Z)", code, re.S):
        for n in re.findall(r"pub (?:struct|enum|type) (\w+)", body):
            names.setdefault(n, mod)
    have = {}
    for t in asn_types:
        rn = t.replace("-", "")
        rn = rn[0].upper() + rn[1:]
        if rn in names:
            have[t] = f"m::{names[rn]}::{rn}"
    arms = "".join(f'        (Some("dec"), Some({json.dumps(t)})) => run::<{p}>(),\n' for t, p in have.items())
    (r / "src/main.rs").write_text(RASN_MAIN.replace("PERV", VARIANT).replace("[TYPES]", "[" + ", ".join(json.dumps(t) for t in have) + "]")
                                   .replace("ARMS", arms))
    (r / "Cargo.toml").write_text(f"""[package]
name = "rasn_driver"
version = "0.1.0"
edition = "2021"

[dependencies]
rasn = "{RASN_VERSION}"

[[bin]]
name = "driver"
path = "src/main.rs"

[workspace]
""")
    RASN_TARGET.mkdir(parents=True, exist_ok=True)
    b = subprocess.run(["cargo", "build", "--release", "--offline", "-q", "--target-dir", RASN_TARGET],
                       cwd=r, capture_output=True, text=True)
    if b.returncode != 0:
        errs = [l for l in b.stderr.splitlines() if l.startswith("error")]
        raise SystemExit(f"rasn-compiler's bindings do not compile: {(errs or [b.stderr.strip()[-200:]])[0][:200]}")
    exe = r / "driver"
    shutil.copy(RASN_TARGET / "release/driver", exe)
    return exe


def build_pycrate(schema, d):
    from pycrate_asn1c.asnproc import compile_text, generate_modules, PycrateGenerator
    from pycrate_asn1c import asnobj
    out = d / "pyc.py"
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        asnobj.GLOBAL.clear()
        compile_text(pathlib.Path(schema).read_text())
        generate_modules(PycrateGenerator, str(out))
    spec = importlib.util.spec_from_file_location("pyc", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ------------------------------------------------------------------ decoders

class Ours:
    def __init__(self, exe):
        self.exe = exe

    def types(self):
        return sh([self.exe, "types"]).split()

    def gen(self, ty, n, seed):
        rows = []
        for line in sh([self.exe, "gen", ty, str(n), str(seed)]).splitlines():
            if line.startswith("err"):
                # the driver's writer was too small for the value
                print(f"note {ty}: a random value our encoder ran out of buffer for")
                continue
            hx, bits, j = line.split(" ", 2)
            rows.append((hx, int(bits), json.loads(j)))
        return rows

    def dec(self, ty, hexes):
        """per hex: (value, flag, reencoding) or None"""
        out = sh([self.exe, "dec", ty], input="\n".join(hexes) + "\n")
        res = []
        for line in out.splitlines():
            if line.startswith("err"):
                res.append(("reject", line[4:]))
            else:
                _, flag, _bits, re, j = line.split(" ", 4)
                res.append(("accept", json.loads(j), flag, re))
        return res


class Pycrate:
    # pycrate checks the constraints it knows on decoding, always
    def __init__(self, mod, module_names):
        self.ms = [getattr(mod, n.replace("-", "_")) for n in module_names]

    def type(self, ty):
        """the type, from whichever module defines it"""
        for m in self.ms:
            t = getattr(m, ty.replace("-", "_"), None)
            if t is not None:
                return t
        return None

    def knows(self, ty):
        return self.type(ty) is not None

    def dec(self, ty, hx, check=False):
        t = self.type(ty)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                if VARIANT == "aper":
                    t.from_aper(bytes.fromhex(hx))
                    return ("accept", json.loads(t.to_jer()), t.to_aper().hex())
                t.from_uper(bytes.fromhex(hx))
                return ("accept", json.loads(t.to_jer()), t.to_uper().hex())
        except Exception as e:  # pycrate raises on any decoding error
            return ("reject", f"{type(e).__name__}: {str(e)[:120]}")


def splice_groups(j):
    """asn1c prints an extension addition group as an object of its own,
    `"ext1": {..}`; X.697 27.2.1 makes a group's components components of the
    enclosing SEQUENCE. `extN` is not an identifier in these schemas, so an
    object member of that name is one of asn1c's groups."""
    if isinstance(j, dict):
        out = {}
        for k, v in j.items():
            v = splice_groups(v)
            if k.startswith("ext") and k[3:].isdigit() and isinstance(v, dict):
                out.update(v)
            else:
                out[k] = v
        return out
    if isinstance(j, list):
        return [splice_groups(x) for x in j]
    return j


class Rasn:
    def __init__(self, exe):
        self.exe = exe
        self.have = set(sh([exe, "types"]).split())

    def knows(self, ty):
        return ty in self.have

    def dec(self, ty, hx, check=False):
        r = subprocess.run([self.exe, "dec", ty], input=hx + "\n", capture_output=True, text=True)
        # a panic (rasn's `todo!()`s) prints to stderr and nothing to stdout
        why = " ".join(l for l in r.stderr.splitlines() if l and not l.startswith("note:"))
        line = (r.stdout.strip().splitlines() or ["err " + (why[-160:] or "no output")])[0]
        if line.startswith("err"):
            return ("reject", line[4:][:160])
        _, re_, j = line.split(" ", 2)
        try:
            return ("accept", json.loads(j), re_)
        except json.JSONDecodeError as e:
            return ("reject", f"JER not JSON: {e}")


class Asn1c:
    def __init__(self, exe):
        self.exe = exe
        self.pdus = set(subprocess.run([exe, "-p", "list"], capture_output=True, text=True).stdout.split())
        # asn1c's converter drops a codec that some type of the module lacks:
        # it has no APER for SET (`SET_decode_aper` is null), and then refuses
        # -iaper for the whole module
        probe = subprocess.run([exe, f"-i{VARIANT}", "/dev/null"], capture_output=True, text=True)
        if "improper format selector" in probe.stderr:
            raise SystemExit(f"its converter has no {VARIANT.upper()} for this module (asn1c implements none for SET)")

    def pdu(self, ty):
        """the name the converter knows the type by: as written, or (older
        asn1c) with `_` for `-`"""
        return ty if ty in self.pdus else ty.replace("-", "_")

    def knows(self, ty):
        return self.pdu(ty) in self.pdus

    def dec(self, ty, hx, check=False):
        """`check`: asn1c's -c, every constraint, PER-visible or not. Vectors
        use it; random values do not, since they come from the effective
        (PER-visible) constraint, which may allow values the type does not
        (X.691 10.3.10: SIZE (1..4 | 8) is encoded as SIZE (1..8))."""
        v = VARIANT
        with tempfile.NamedTemporaryFile(suffix="." + v) as f:
            f.write(bytes.fromhex(hx))
            f.flush()
            pdu = self.pdu(ty)
            j = subprocess.run([self.exe, "-p", pdu, "-1"] + (["-c"] if check else []) + [f"-i{v}", "-ojer", f.name],
                               capture_output=True, text=True, errors="replace")
            if j.returncode != 0 and "Cannot convert" in j.stderr and ("<absent>" in j.stderr or "<unknown>" in j.stderr):
                # it decoded the value, but an open type whose id no object
                # of its set has (a newer peer's IE) comes out <absent>, and
                # its JER printer refuses a value with one
                return ("absent", "asn1c: an IE of an id it does not know is decoded <absent>, and not printed")
            if j.returncode != 0 or not j.stdout.strip():
                return ("reject", (j.stderr.strip().splitlines() or ["?"])[-1][:160])
            u = subprocess.run([self.exe, "-p", pdu, "-1", f"-i{v}", f"-o{v}", f.name], capture_output=True)
            try:
                # asn1c's JER writes control characters in a string unescaped,
                # which JSON forbids: read them anyway
                # and an OBJECT IDENTIFIER or RELATIVE-OID as `{ 1.2.840 }`, which
                # is not JSON either; X.697 29, 30 make it the string "1.2.840"
                txt = re.sub(r"\{ ([0-9]+(?:\.[0-9]+)*) \}", r'"\1"', j.stdout)
                return ("accept", json.loads(txt, strict=False), u.stdout.hex())
            except json.JSONDecodeError as e:
                return ("reject", f"JER not JSON: {e}")


HEX = set("0123456789abcdefABCDEF")


def jer_eq(a, b):
    """Equal JER values. X.697 24-25 allows hex digits in either case, so two
    strings of hex digits equal but for case are equal. (A character string
    that differs only in case would also change the re-encoded bytes, which
    are compared exactly, so this cannot hide one.)"""
    if isinstance(a, dict) and isinstance(b, dict):
        # a decoded CONTAINING: X.697 25.4's {"containing": v}, which pycrate
        # prints as {"TypeName": v} (tests/x691/README.md)
        if len(a) == 1 and len(b) == 1 and "containing" in (a.keys() | b.keys()):
            return jer_eq(next(iter(a.values())), next(iter(b.values())))
        return a.keys() == b.keys() and all(jer_eq(a[k], b[k]) for k in a)
    # a BIT STRING under an extensible size constraint: X.697's variable form
    # {"value", "length"} against pycrate's fixed form, the hex alone, of the
    # same bits (its length a whole number of hex digits)
    for x, y in ((a, b), (b, a)):
        if isinstance(x, dict) and x.keys() == {"value", "length"} and isinstance(y, str) \
                and isinstance(x["value"], str) and 4 * len(y) - 7 <= x["length"] <= 4 * len(y):
            # (pycrate's fixed form loses a length that is not a whole number
            # of octets, tests/x691/README.md; the bits are the same)
            return x["value"].upper() == y.upper()
    if isinstance(a, list) and isinstance(b, list):
        return len(a) == len(b) and all(jer_eq(x, y) for x, y in zip(a, b))
    if isinstance(a, str) and isinstance(b, str) and a != b:
        return (a.upper() == b.upper() and set(a) <= HEX and set(b) <= HEX) or octet_chars(a, b) or octet_chars(b, a)
    # X.697 23.4's base-10 object, against a printer that writes every REAL
    # as a number: the same number (whether the base survived is the
    # re-encoding's business)
    # (pycrate writes the base-10 value as a string, "9.6000000000000002e-02",
    # where the other side has a number)
    def b10(v):
        if isinstance(v, str):
            try:
                return float(v)
            except ValueError:
                return v
        return v
    if isinstance(a, dict) and list(a) == ["base10Value"] and not isinstance(b, dict):
        return jer_eq(b10(a["base10Value"]), b)
    if isinstance(b, dict) and list(b) == ["base10Value"] and not isinstance(a, dict):
        return jer_eq(a, b10(b["base10Value"]))
    num = (int, float)
    if isinstance(a, num) and isinstance(b, num) and not isinstance(a, bool) and not isinstance(b, bool) \
            and (isinstance(a, float) or isinstance(b, float)):
        # a REAL: one printer writes 1, another 1.0 (X.697 23.3: "a JSON
        # number denoting the value", in any form)
        return float(a) == float(b)
    return a == b and type(a) is type(b)


OID = re.compile(r"[0-9]+(\.[0-9]+)*")


def wide_arc(j):
    """Whether a value holds an OBJECT IDENTIFIER or RELATIVE-OID with an arc
    over 2^32 - 1 (a dotted string of numbers, X.697 29, 30)."""
    if isinstance(j, dict):
        return any(wide_arc(v) for v in j.values())
    if isinstance(j, list):
        return any(wide_arc(v) for v in j)
    return isinstance(j, str) and OID.fullmatch(j) is not None and \
        any(int(a) > 2**32 - 1 for a in j.split("."))


def octet_chars(s, h):
    """asn1c prints a string that is not known-multiplier (GeneralString and
    the like, X.691 30.6) as the hex of its octets, where X.697 38 prints the
    characters. The octets are what the encoding carries, so the two are
    the same value when the hex is `s`'s octets, one character each. (The
    re-encodings are compared exactly as well.)"""
    if len(h) != 2 * len(s) or not set(h) <= HEX or any(ord(c) > 255 for c in s):
        return False
    return bytes.fromhex(h) == s.encode("latin-1")


class Defaults:
    """X.697 lets a JER encoder print a component whose value is its DEFAULT
    or omit it; the three printers choose differently. So before comparing,
    members equal to their DEFAULT are removed from both sides, walking the
    value with pycrate's compiled type, which knows every component's
    default. Without pycrate (a schema it cannot compile) nothing is removed."""

    def __init__(self, pyc=None):
        self.m = pyc
        self.cache = {}

    def default_jer(self, c):
        k = id(c)
        if k not in self.cache:
            with contextlib.redirect_stdout(io.StringIO()):
                c.set_val(c._def)
                self.cache[k] = json.loads(c.to_jer())
        return self.cache[k]

    def strip(self, j, t):
        if t is None:
            return splice_groups(j)
        ty = getattr(t, "TYPE", None)
        cont = getattr(t, "_cont", None)
        inner = getattr(t, "_const_cont", None)
        if ty == "OCTET STRING" and inner is not None and isinstance(j, dict) and len(j) == 1:
            # pycrate prints a contained value as `{"T": value}`; X.697 25.4,
            # and ours, as `{"containing": value}`
            (k, v), = j.items()
            return {"containing": self.strip(v, inner)}
        if ty in ("SEQUENCE", "SET") and isinstance(j, dict) and cont is not None:
            # asn1c's `"extN": {..}` group objects (see splice_groups), told
            # apart from a component really called extN by the schema
            flat = {}
            for k, v in j.items():
                if k not in cont and k.startswith("ext") and k[3:].isdigit() and isinstance(v, dict):
                    flat.update(v)
                else:
                    flat[k] = v
            out = {}
            for k, v in flat.items():
                c = cont[k] if k in cont else None
                if c is not None and getattr(c, "_def", None) is not None and jer_eq(v, self.default_jer(c)):
                    continue
                out[k] = self.strip(v, c)
            return out
        if ty == "CHOICE" and isinstance(j, dict) and len(j) == 1 and cont is not None:
            (k, v), = j.items()
            return {k: self.strip(v, cont[k] if k in cont else None)}
        if ty in ("SEQUENCE OF", "SET OF") and isinstance(j, list):
            return [self.strip(x, cont) for x in j]
        return j

    def same(self, ty, a, b):
        t = self.m.type(ty) if self.m is not None else None
        return jer_eq(self.strip(a, t), self.strip(b, t))


DEFAULTS = Defaults()


def pad(hx):
    """X.691 11.1.3: the outermost value is a whole number of octets, at least one"""
    return hx if hx else "00"


# ------------------------------------------------------------------ checks

def deviations(path):
    out = set()
    if path:
        for line in pathlib.Path(path).read_text().splitlines():
            w = line.split("#", 1)[0].split()
            if len(w) == 3 and w[0] in ("deviates", "deviates-encode"):
                out.add((w[1], w[2]) if w[0] == "deviates" else ("encode", w[1], w[2]))
    return out


def check_random(ours, others, types, n, seed, report, deviates=frozenset()):
    for ty in types:
        if not all(dec.knows(ty) for _, dec in others):
            # an instance of a parameterised type, named by us: it is checked
            # inside the types that use it
            continue
        rows = ours.gen(ty, n, seed)
        for hx, bits, val in rows:
            for name, dec in others:
                if (name, ty) in deviates:
                    report.known()
                    continue
                r = dec.dec(ty, pad(hx))
                if r[0] == "absent":
                    report.known()
                    continue
                if name == "pycrate" and len(pad(hx)) >= 2 * 16384 and not (
                        r[0] == "accept" and DEFAULTS.same(ty, r[1], val) and r[2] == pad(hx)):
                    # pycrate misreads a container after an open type of 16K
                    # octets or more (tests/ioc/bigie.vec)
                    report.known()
                    continue
                if r[0] == "reject" and ("out of constraint" in r[1] or "out of size constraint" in r[1]
                                         or "constraint check failed" in r[1]):
                    # our generator draws from the effective, PER-visible
                    # constraint: `(0..7 | 9)` is encoded as 0..9 and it may
                    # draw 8, which is not a value of the type. The encoding
                    # is still X.691's; pycrate checks the full constraint.
                    report.outside()
                elif name in ("asn1c", "rasn") and wide_arc(val) and (r[0] == "reject" or not DEFAULTS.same(ty, r[1], val)):
                    # both hold an OBJECT IDENTIFIER's arcs in 32 bits: asn1c
                    # (asn_oid_arc_t) cannot convert a wider one, rasn keeps
                    # its low 32 bits
                    report.known()
                elif r[0] == "reject":
                    report.fail(ty, hx, f"{name} rejects our encoding: {r[1]}", val)
                elif not DEFAULTS.same(ty, r[1], val):
                    report.fail(ty, hx, f"{name} decodes a different value", val, r[1])
                elif r[2] != pad(hx) and ("encode", name, ty) in deviates:
                    report.known()
                elif r[2] != pad(hx):
                    report.fail(ty, hx, f"{name} re-encodes to {r[2]}", val)
                else:
                    report.ok()
        report.progress(ty, len(rows))


def check_corpus(spec, ours, others, report):
    """Captured messages, one per file (`DIR:TYPE`): ours must decode each
    to what every reference decodes it to, and re-encode it to the same
    octets when it decoded it as this version (`SameVer`). A message ours
    rejects and a reference accepts is a failure until triaged; one a
    reference rejects and ours accepts is reported as the reference's."""
    d, ty = spec.rsplit(":", 1)
    files = sorted(p for p in pathlib.Path(d).iterdir() if p.is_file())
    hexes = [f.read_bytes().hex() for f in files]
    res = []
    for i in range(0, len(hexes), 500):
        res.extend(ours.dec(ty, hexes[i:i + 500]))
    tally = collections.Counter()
    for f, hx, r in zip(files, hexes, res):
        theirs = {name: dec.dec(ty, hx) for name, dec in others if dec.knows(ty)}
        if r[0] == "reject":
            acc = [n for n, t in theirs.items() if t[0] in ("accept", "absent")]
            if acc and r[1].startswith("padding:"):
                # not a complete encoding (X.691 11.1.3, 11.1.4): a padding
                # bit not zero, or octets after the value's. Ours rejects
                # it, by decision; the references are lenient
                report.known()
                tally["ours rejects for padding or trailing octets, a reference accepts"] += 1
            elif acc:
                report.fail(ty, hx, f"{f.name}: ours rejects ({r[1]}), {', '.join(acc)} accept")
                tally["ours rejects, a reference accepts"] += 1
            else:
                report.ok()
                tally["all reject"] += 1
            continue
        _, val, flag, re_ = r
        if flag == "SameVer" and re_ != hx:
            report.fail(ty, hx, f"{f.name}: ours re-encodes it to {re_[:64]}")
            tally["ours re-encodes differently"] += 1
            continue
        good = True
        for name, t in theirs.items():
            if t[0] == "absent":
                tally[f"{name}: an IE it does not know, <absent>"] += 1
                continue
            if t[0] == "reject":
                report.fail(ty, hx, f"{f.name}: {name} rejects it: {t[1]}", counts=False)
                tally[f"{name} rejects"] += 1
            elif not DEFAULTS.same(ty, t[1], val):
                report.fail(ty, hx, f"{f.name}: {name} decodes a different value", val, t[1])
                tally[f"{name} decodes differently"] += 1
                good = False
        if good:
            report.ok()
            tally["all agree" if flag == "SameVer" else "all agree, DiffVer"] += 1
    print(f"     {spec}: {len(files)} messages: " + ", ".join(f"{n} {k}" for k, n in sorted(tally.items())))


def check_vectors(path, ours, others, types, report):
    for lineno, line in enumerate(pathlib.Path(path).read_text().splitlines(), 1):
        line = line.split(" #", 1)[0].strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("deviates"):
            continue
        kind, ty, hx, *rest = line.split(" ", 3)
        if ty not in types:
            report.fail(ty, hx, f"{path}:{lineno}: no such type")
            continue
        known_bad = kind.endswith("!")   # the reference implementations are known to deviate here
        kind = kind.rstrip("!")
        want = json.loads(rest[0]) if kind == "accept" else None
        res = {"ours": ours.dec(ty, [hx])[0]}
        for name, dec in others:
            if dec.knows(ty):
                res[name] = dec.dec(ty, hx, check=True)
        for name, r in res.items():
            good = (r[0] == kind) and (kind == "reject" or DEFAULTS.same(ty, r[1], want))
            if name == "ours" and kind == "accept" and good:
                good = r[3] == hx and r[2] == "SameVer"
            where = f"{path}:{lineno}"
            if good:
                report.ok()
            elif name == "ours" or not known_bad:
                msg = r[1] if r[0] == "reject" else json.dumps(r[1])
                report.fail(ty, hx, f"{where}: {name} {r[0]}s, X.691 says {kind}: {msg[:200]}",
                            want, counts=(name == "ours"))
            else:
                report.known()


class Report:
    def __init__(self):
        self.oks = self.fails = self.theirs = self.known_n = self.outside_n = 0

    def ok(self):
        self.oks += 1

    def known(self):
        self.known_n += 1

    def outside(self):
        self.outside_n += 1

    def fail(self, ty, hx, why, want=None, got=None, counts=True):
        if counts:
            self.fails += 1
        else:
            self.theirs += 1
        if os.environ.get("XCHECK_DUMP"):
            # every failure whole, for triage: TYPE<TAB>WHY<TAB>HEX
            with open(os.environ["XCHECK_DUMP"], "a") as f:
                f.write(f"{ty}\t{why.splitlines()[0] if why else ''}\t{hx}\n")
        print(f"{'FAIL' if counts else 'ref '} {ty} {hx[:64]}{'...' if len(hx) > 64 else ''}: {why}")
        if want is not None:
            print(f"       expected {json.dumps(want)[:300]}")
        if got is not None:
            print(f"       got      {json.dumps(got)[:300]}")

    def progress(self, ty, n):
        print(f"     {ty}: {n} values")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("schema")
    ap.add_argument("-n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--types")
    ap.add_argument("--vectors")
    ap.add_argument("--dir", help="build directory (default target/xcheck/<schema>)")
    ap.add_argument("--verify", action="store_true", help="also verify the generated module with Verus")
    ap.add_argument("--containing", choices=("octets", "decode"), default="octets")
    ap.add_argument("--aper", action="store_true", help="ALIGNED PER instead of UNALIGNED")
    ap.add_argument("--no-rasn", action="store_true", help="leave rasn out")
    ap.add_argument("--keep-refs", action="store_true",
                    help="keep every reference despite CONTAINING (its fields then differ, to be triaged)")
    ap.add_argument("--driver", help="a prebuilt driver (a crate-dir build's), instead of building one")
    ap.add_argument("--corpus", action="append", default=[],
                    help="DIR:TYPE, captured messages of TYPE, one per file")
    a = ap.parse_args()
    global VARIANT
    VARIANT = "aper" if a.aper else "uper"
    schema = pathlib.Path(a.schema).resolve()
    d = pathlib.Path(a.dir or ROOT / "target/xcheck" / (schema.stem + ("-aper" if a.aper else ""))).resolve()
    d.mkdir(parents=True, exist_ok=True)
    if a.driver:
        exe, skipped = pathlib.Path(a.driver).resolve(), []
    else:
        build_tools()
        exe, skipped = build_ours(schema, d, a.containing)
    for s in skipped:
        print(f"note {s}")
    if a.verify:
        r = subprocess.run([VERUS, "--crate-type=lib", "--crate-name", "xcheck", *vasn_args(), d / "m.rs"],
                           capture_output=True, text=True)
        res = [l for l in (r.stdout + r.stderr).splitlines() if "verification results" in l]
        print(f"verus {res[-1].split('::')[-1].strip() if res else 'failed'}")
        if r.returncode != 0:
            print(r.stdout + r.stderr)
            sys.exit(1)
    ours = Ours(exe)
    # every module: the word before DEFINITIONS, and an OID in braces between
    text = "\n".join(l.split("--")[0] for l in schema.read_text().splitlines())
    module_names = re.findall(r"([A-Za-z][\w-]*)\s*(?:\{[^}]*\}\s*)?DEFINITIONS", text)
    # each reference parses only part of X.680; one that cannot compile the
    # schema is left out, and says why
    others = []
    refs = [("pycrate", lambda: Pycrate(build_pycrate(schema, d), module_names)),
            ("asn1c", lambda: Asn1c(build_asn1c(schema, d))),
            ("rasn", lambda: Rasn(build_rasn(schema, d, ours.types())))]
    if a.no_rasn:
        refs = [r for r in refs if r[0] != "rasn"]
    if "CONTAINING" in text and not a.keep_refs:
        # pycrate decodes a CONTAINING, asn1c and rasn keep its octets
        drop = {"pycrate"} if a.containing == "octets" else {"asn1c", "rasn"}
        print(f"note CONTAINING is {'octets' if a.containing == 'octets' else 'decoded'} (--containing "
              f"{a.containing}): {', '.join(sorted(drop))} left out")
        refs = [r for r in refs if r[0] not in drop]
    for name, make in refs:
        try:
            others.append((name, make()))
        except (Exception, SystemExit) as e:
            why = str(e).strip().splitlines()
            print(f"note {name} cannot compile {schema.name}, left out: {why[-1][:160] if why else '?'}")
    if not others:
        print("note no reference implementation compiles this schema: vectors are checked against ours alone")
    for name, dec in others:
        if name == "pycrate":
            DEFAULTS.m = dec
    types = ours.types()
    report = Report()
    if a.vectors:
        check_vectors(a.vectors, ours, others, types, report)
    for c in a.corpus:
        check_corpus(c, ours, others, report)
    if a.n > 0:
        check_random(ours, others, a.types.split(",") if a.types else types, a.n, a.seed, report,
                     deviations(a.vectors))
    print(f"{report.oks} checks passed, {report.fails} failed"
          + (f", {report.theirs} reference-implementation deviations from X.691" if report.theirs else "")
          + (f", {report.known_n} known reference deviations" if report.known_n else "")
          + (f", {report.outside_n} random values outside the full (non-PER-visible) constraint" if report.outside_n else ""))
    sys.exit(1 if report.fails else 0)


if __name__ == "__main__":
    main()
