#!/usr/bin/env python3
"""pycrate's UPER encodings of the values examples/src/bin/frag.rs encodes, in
the same format (`name bits hex`), so the two can be diffed:

    python3 tools/frag_pycrate.py > a.txt
    cargo run -q --release -p vuper-examples --bin frag -- --cases > b.txt
    diff a.txt b.txt

The values are defined here and in frag.rs by the same rules (see CASES).
"""
import glob
import pathlib
import sys

sys.path[:0] = glob.glob("/usr/local/lib/python3*/dist-packages/pycrate-*.egg")
import contextlib  # noqa: E402
import importlib.util  # noqa: E402
import io  # noqa: E402
import tempfile  # noqa: E402

from pycrate_asn1c.asnproc import compile_text, generate_modules, PycrateGenerator  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
# pycrate compiles the module to Python source, which is then imported
OUT = pathlib.Path(tempfile.mkdtemp()) / "frag_py.py"
with contextlib.redirect_stdout(io.StringIO()):
    compile_text((ROOT / "examples/asn1/frag.asn1").read_text())
    generate_modules(PycrateGenerator, str(OUT))
spec = importlib.util.spec_from_file_location("frag_py", OUT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
M = mod.FRAG_Definitions


def bits(n, k=0):
    """n bits, bit i = ((i * 7 + k) % 5 == 0): the pattern frag_main.rs uses"""
    return [((i * 7 + k) % 5 == 0) for i in range(n)]


def as_bitstring(bs):
    v = 0
    for b in bs:
        v = (v << 1) | int(b)
    return (v, len(bs))


def octets(n):
    return bytes((i * 31 + 7) % 256 for i in range(n))


CASES = []
for n in (1, 127, 128, 16383, 16384, 16385, 32768, 49152, 65535, 65536):
    CASES.append((f"BigBits/{n}", "BigBits", as_bitstring(bits(n))))
CASES.append(("FixedBig/65536", "FixedBig", as_bitstring(bits(65536, 3))))
for n in (0, 1, 16384, 65536, 81921, 100000):
    CASES.append((f"BigOctets/{n}", "BigOctets", octets(n)))
for n in (1, 16384, 20000, 65536):
    CASES.append((f"BigList/{n}", "BigList", [i % 8 for i in range(n)]))
for n in (3, 16385):
    CASES.append((f"NibbleList/{n}", "NibbleList", [as_bitstring(bits(4, i)) for i in range(n)]))
for n in (2, 16384):
    CASES.append((f"ExtList/{n}", "ExtList",
                  [{"a": i % 2 == 0, **({"b": i % 3 == 0} if i % 4 == 0 else {})} for i in range(n)]))

for name, ty, val in CASES:
    t = getattr(M, ty.replace("-", "_"))
    t.set_val(val)
    print(name, t.to_uper().hex())
