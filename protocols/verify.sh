#!/usr/bin/env bash
# Every crate of a protocol verified with Verus, from a fresh crate directory
# (work/verify/PROTO). Its Makefile re-verifies only what changed on a rerun.
#   verify.sh PROTO...     JOBS=N to set make's -j (default: the cores)
set -uo pipefail
. "$(dirname "$0")/lib.sh"
[ -x "$VASNC" ] || (cd "$ROOT" && cargo build --release -q -p vasnc)
for p in "$@"; do
    need_asn "$p"
    d=$WORK/verify/$p
    rm -rf "$d"; mkdir -p "$WORK/verify"
    "$VASNC" "$WORK/asn/$p"/*.asn --aper --crate-dir "$d" 2>&1 | tail -1
    s=$(date +%s)
    make -C "$d" -k -j"${JOBS:-$(nproc)}" ROOT="$ROOT" VASN_DIR="$WORK/vasn-verify" > "$d.log" 2>&1
    rc=$?
    echo "$p: make $rc; $(grep -c '^error' "$d.log") errors; $(ls "$d"/*.vir 2>/dev/null | wc -l) of $(ls "$d"/*.rs | wc -l) crates verified; $(( ($(date +%s) - s) / 60 )) min ($d.log)"
    grep '^error' -A3 "$d.log" | grep -- '-->' | head -10
done
