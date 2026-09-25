#!/usr/bin/env python3
"""Check vuperc's codec for a schema against pycrate and asn1c.

    tools/xcheck.py SCHEMA.asn1 [-n N] [--seed S] [--types A,B] [--vectors FILE]
                    [--containing octets|decode]

Builds three decoders for SCHEMA: ours (vuperc and its `--driver`, compiled
with Verus, --no-verify: the per-type verification is a separate run), asn1c's
converter-example (tools/get-asn1c.sh), and pycrate's generated module. Then:

* random values: N per type from our generator (`driver gen`), encoded by our
  encoder. pycrate and asn1c must each decode the bytes to the same value as
  ours (compared as JER, X.697) and re-encode them to the same bytes.
* vectors (--vectors): encodings written by hand from X.691, one per line,

      accept TYPE HEX JER     every decoder gives this value, and ours re-encodes to HEX
      reject TYPE HEX         every decoder rejects it
      deviates TOOL TYPE      TOOL is known to deviate from X.691 on TYPE: the
                              random-value checks leave TOOL out for TYPE

  X.691 is the judge. A line where pycrate or asn1c disagree with X.691 is
  marked in the file, `accept! ...` / `reject! ...` with a comment, and a
  disagreement there is reported but not counted as ours.

`--containing` is passed to vuperc. `OCTET STRING (CONTAINING T)` is octets
to asn1c and a T to pycrate, so a schema that has one is checked against
asn1c alone under `octets` (the default) and against pycrate alone under
`decode`.

Exit status is 1 if any check of ours failed.
"""
import argparse
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
VUPERC = ROOT / "target/release/vuperc"
VUPERX = ROOT / "target/verus"          # vuperx built by Verus, as crate-dir Makefiles do
ASN1C = ROOT / "tools/asn1c/bin/asn1c"
sys.path[:0] = glob.glob("/usr/local/lib/python3*/dist-packages/pycrate-*.egg")


# a wide ENUMERATED or CHOICE compiles to a deep if/else chain, which
# overflows rustc's default stack (as vuperc's generated Makefiles note)
os.environ.setdefault("RUST_MIN_STACK", "2000000000")


def sh(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        sys.exit(f"{' '.join(map(str, cmd))} failed:\n{r.stdout}{r.stderr}")
    return r.stdout


# ------------------------------------------------------------------ builds

def build_tools():
    """vuperc with cargo, and vuperx with Verus: the generated module imports
    vuperx's .vir, which only Verus writes."""
    sh(["cargo", "build", "--release", "-q", "-p", "vuperc"], cwd=ROOT)
    rlib = VUPERX / "libvuperx.rlib"
    srcs = list((ROOT / "vuperx/src").glob("*.rs"))
    if not rlib.exists() or any(f.stat().st_mtime > rlib.stat().st_mtime for f in srcs):
        VUPERX.mkdir(parents=True, exist_ok=True)
        sh([VERUS, "--crate-type=lib", "--crate-name", "vuperx", "--compile", "-C", "opt-level=3",
            "--export", VUPERX / "vuperx.vir", ROOT / "vuperx/src/lib.rs", "-o", rlib])


def vuperx_args():
    return ["--import", f"vuperx={VUPERX}/vuperx.vir", "--extern", f"vuperx={VUPERX}/libvuperx.rlib"]


def build_ours(schema, d, containing):
    rs, drv = d / "m.rs", d / "driver.rs"
    out = subprocess.run([VUPERC, schema, rs, "--driver", drv, "--containing", containing],
                         capture_output=True, text=True)
    skipped = [l.strip() for l in out.stderr.splitlines() if l.strip().startswith("skipped")]
    if out.returncode != 0:
        sys.exit(out.stderr)
    sh([VERUS, "--compile", "-C", "opt-level=1", "--no-verify", *vuperx_args(),
        drv, "-o", d / "driver"])
    return d / "driver", skipped


def build_asn1c(schema, d):
    a = d / "asn1c"
    shutil.rmtree(a, ignore_errors=True)
    a.mkdir()
    sh([ASN1C, "-pdu=all", "-fcompound-names", "-no-gen-BER", "-no-gen-XER", "-no-gen-OER",
        "-no-gen-APER", schema], cwd=a)
    sh(["make", "-s", "-f", "converter-example.mk", f"-j{os.cpu_count()}"], cwd=a)
    return a / "converter-example"


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


class Asn1c:
    def __init__(self, exe):
        self.exe = exe
        self.pdus = set(subprocess.run([exe, "-p", "list"], capture_output=True, text=True).stdout.split())

    def knows(self, ty):
        return ty.replace("-", "_") in self.pdus

    def dec(self, ty, hx, check=False):
        """`check`: asn1c's -c, every constraint, PER-visible or not. Vectors
        use it; random values do not, since they come from the effective
        (PER-visible) constraint, which may allow values the type does not
        (X.691 10.3.10: SIZE (1..4 | 8) is encoded as SIZE (1..8))."""
        with tempfile.NamedTemporaryFile(suffix=".uper") as f:
            f.write(bytes.fromhex(hx))
            f.flush()
            pdu = ty.replace("-", "_")
            j = subprocess.run([self.exe, "-p", pdu, "-1"] + (["-c"] if check else []) + ["-iuper", "-ojer", f.name],
                               capture_output=True, text=True, errors="replace")
            if j.returncode != 0 or not j.stdout.strip():
                return ("reject", (j.stderr.strip().splitlines() or ["?"])[-1][:160])
            u = subprocess.run([self.exe, "-p", pdu, "-1", "-iuper", "-ouper", f.name], capture_output=True)
            try:
                return ("accept", json.loads(j.stdout), u.stdout.hex())
            except json.JSONDecodeError as e:
                return ("reject", f"JER not JSON: {e}")


HEX = set("0123456789abcdefABCDEF")


def jer_eq(a, b):
    """Equal JER values. X.697 24-25 allows hex digits in either case, so two
    strings of hex digits equal but for case are equal. (A character string
    that differs only in case would also change the re-encoded bytes, which
    are compared exactly, so this cannot hide one.)"""
    if isinstance(a, dict) and isinstance(b, dict):
        return a.keys() == b.keys() and all(jer_eq(a[k], b[k]) for k in a)
    if isinstance(a, list) and isinstance(b, list):
        return len(a) == len(b) and all(jer_eq(x, y) for x, y in zip(a, b))
    if isinstance(a, str) and isinstance(b, str) and a != b:
        return a.upper() == b.upper() and set(a) <= HEX and set(b) <= HEX
    return a == b and type(a) is type(b)


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
            if len(w) == 3 and w[0] == "deviates":
                out.add((w[1], w[2]))
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
                if r[0] == "reject" and ("out of constraint" in r[1] or "out of size constraint" in r[1]
                                         or "constraint check failed" in r[1]):
                    # our generator draws from the effective, PER-visible
                    # constraint: `(0..7 | 9)` is encoded as 0..9 and it may
                    # draw 8, which is not a value of the type. The encoding
                    # is still X.691's; pycrate checks the full constraint.
                    report.outside()
                elif r[0] == "reject":
                    report.fail(ty, hx, f"{name} rejects our encoding: {r[1]}", val)
                elif not DEFAULTS.same(ty, r[1], val):
                    report.fail(ty, hx, f"{name} decodes a different value", val, r[1])
                elif r[2] != pad(hx):
                    report.fail(ty, hx, f"{name} re-encodes to {r[2]}", val)
                else:
                    report.ok()
        report.progress(ty, len(rows))


def check_vectors(path, ours, others, types, report):
    for lineno, line in enumerate(pathlib.Path(path).read_text().splitlines(), 1):
        line = line.split(" #", 1)[0].strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("deviates "):
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
    a = ap.parse_args()
    schema = pathlib.Path(a.schema).resolve()
    d = pathlib.Path(a.dir or ROOT / "target/xcheck" / schema.stem).resolve()
    d.mkdir(parents=True, exist_ok=True)
    build_tools()
    exe, skipped = build_ours(schema, d, a.containing)
    for s in skipped:
        print(f"note {s}")
    if a.verify:
        r = subprocess.run([VERUS, "--crate-type=lib", "--crate-name", "xcheck", *vuperx_args(), d / "m.rs"],
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
            ("asn1c", lambda: Asn1c(build_asn1c(schema, d)))]
    if "CONTAINING" in text:
        drop = "pycrate" if a.containing == "octets" else "asn1c"
        print(f"note CONTAINING is {'octets' if drop == 'pycrate' else 'decoded'} (--containing "
              f"{a.containing}), as {'pycrate' if drop == 'asn1c' else 'asn1c'} does: {drop} left out")
        refs = [r for r in refs if r[0] != drop]
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
