#!/bin/sh
# The source directory of a dependency of vasn (vbits, vsimd), as cargo
# resolved it: they come from verified_binary_formats, and the builds that
# run Verus directly (tools/xcheck.py, vasnc --crate-dir's Makefile) compile
# them from their sources.
#   tools/dep-src.sh vbits
cd "$(dirname "$0")/.." && cargo metadata --format-version 1 --locked |
  python3 -c 'import json, os, sys
m = json.load(sys.stdin)
print(next(os.path.dirname(p["manifest_path"]) + "/src" for p in m["packages"] if p["name"] == sys.argv[1]))' "$1"
