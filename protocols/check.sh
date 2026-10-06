#!/usr/bin/env bash
# Ours against asn1c and pycrate (tools/xcheck.py), on N random values of the
# protocol's types (default 300 each) and on its captured messages
# (corpus/PROTO.tar.gz, if there is one). Needs build.sh PROTO first.
#   check.sh PROTO [N] [xcheck options...]
# XCHECK_ASN1C_RANGE8=1 builds asn1c with its 8-bit INTEGER misalignment fixed
# (tests/ioc/range8.vec), so that what that bug hides shows; XCHECK_DUMP=FILE
# writes every failure whole.
set -uo pipefail
. "$(dirname "$0")/lib.sh"
p=$1; N=${2:-300}; shift; [ $# -gt 0 ] && shift
need_asn "$p"
drv=$WORK/driver/$p/target/release/driver
[ -x "$drv" ] || { echo "no driver: run protocols/build.sh $p first" >&2; exit 2; }
corp=()
if [ -f "$P/corpus/$p.tar.gz" ]; then
    mkdir -p "$WORK/corpus"; tar xzf "$P/corpus/$p.tar.gz" -C "$WORK/corpus"
    while read -r name ty use _; do
        case $use in *check*) corp+=(--corpus "$WORK/corpus/$name:$ty") ;; esac
    done < <(grep "^$p/" "$P/corpus/index.txt")
fi
XCHECK_ASN1C_FLAGS="${XCHECK_ASN1C_FLAGS:-$(asn1c_flags "$p")}" \
    "$ROOT/tools/xcheck.py" "$WORK/asn/$p.asn1" --aper -n "$N" --types "$(types "$p")" --no-rasn \
    --driver "$drv" --dir "$WORK/xcheck/$p" "${corp[@]}" "$@"
