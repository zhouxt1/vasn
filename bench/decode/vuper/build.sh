#!/usr/bin/env bash
# Build vbench: VUPER's extracted NR decoder with a timing loop, from the
# checkout ../build.sh fetches into ../VUPER. Needs the OCaml 4.14
# switch with yojson, ppx_import, base and mtime, and an unlimited stack.
#
#   build.sh       vbench, DL-DCCH-MessageType, from ../VUPER/diff_test/fuzz/ocaml_test
#   build.sh ul    vbench_ul, UL-DCCH-MessageType, from .../ocaml_test_ul_srs
#
# VUPER ships no extraction of the other five channel messages.
set -euo pipefail
cd "$(dirname "$0")"
SWITCH=${OPAM_SWITCH:-4.14.0}
VUPER=$(cd ../VUPER && pwd)
case ${1:-dl} in
    dl) SRC=$VUPER/diff_test/fuzz/ocaml_test; OUT=vbench; FMT=dL_DCCH ;;
    ul) SRC=$VUPER/diff_test/fuzz/ocaml_test_ul_srs; OUT=vbench_ul; FMT=uL_DCCH ;;
    *) echo "usage: build.sh [dl|ul]" >&2; exit 2 ;;
esac
rm -rf _build/src && mkdir -p _build/src/vbench
cp -r "$SRC"/dune-project "$SRC"/src "$SRC"/jer_deriver _build/src/
sed "s/dL_DCCH_MessageType__Format/${FMT}_MessageType__Format/" vbench.ml > _build/src/vbench/vbench.ml
cp dune.in _build/src/vbench/dune
ulimit -s unlimited
eval "$(opam env --switch="$SWITCH" --set-switch)"
( cd _build/src && dune build vbench/vbench.exe )
install -m 0755 _build/src/_build/default/vbench/vbench.exe "$OUT"
echo "built $(pwd)/$OUT"
