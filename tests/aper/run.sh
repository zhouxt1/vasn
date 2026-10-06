#!/usr/bin/env bash
# Every schema checked in the ALIGNED variant: tests/aper's own modules with
# their hand-derived vectors, the X.691 test modules, and the examples, each
# with N random values (default 40) through ours, pycrate and asn1c, and the
# generated module verified with Verus. Exits 1 if any check of ours fails.
#
#   tests/aper/run.sh [N]
set -uo pipefail
cd "$(dirname "$0")/../.."
N=${1:-40}
fail=0
run() {
    local label=$1 asn=$2; shift 2
    out=$(tools/xcheck.py "$asn" --aper "$@" -n "$N" --verify --dir "target/xcheck/aper-$label" 2>&1)
    rc=$?
    printf '%-20s %s | %s\n' "$label" "$(grep '^verus ' <<<"$out" | tail -1)" "$(tail -n 1 <<<"$out")"
    if [ $rc -ne 0 ]; then fail=1; grep -E '^FAIL' <<<"$out" | head -5; fi
}
for asn in tests/aper/*.asn1; do
    # a module marked `run.sh: noverify` is checked but not verified
    if grep -q "run.sh: noverify" "$asn"; then
        t=$(basename "$asn" .asn1)
        out=$(tools/xcheck.py "$asn" --aper --vectors "tests/aper/$t.vec" -n "$N" --dir "target/xcheck/aper-$t" 2>&1); rc=$?
        printf '%-20s %s | %s\n' "$t" "not verified" "$(tail -n 1 <<<"$out")"
        [ $rc -ne 0 ] && { fail=1; grep -E '^FAIL' <<<"$out" | head -5; }
        continue
    fi
    t=$(basename "$asn" .asn1)
    run "$t" "$asn" --vectors "tests/aper/$t.vec"
done
for asn in tests/x691/*.asn1; do
    t=$(basename "$asn" .asn1)
    flags=()
    [ "$t" = containing ] && flags=(--containing decode)
    # the X.691 modules' vector files are UPER encodings; their deviations
    # (the reference implementations' own quirks) carry over
    dev=target/xcheck/aper-x691-$t.deviations
    mkdir -p target/xcheck
    grep -h '^deviates' tests/x691/"$t".vec tests/x691/"$t".*.vec > "$dev" 2>/dev/null
    # and what is the ALIGNED variant's own: tests/aper/x691-T.vec
    [ -f "tests/aper/x691-$t.vec" ] && cat "tests/aper/x691-$t.vec" >> "$dev"
    run "x691-$t" "$asn" "${flags[@]}" --vectors "$dev"
done
for asn in examples/asn1/*.asn1; do
    t=$(basename "$asn" .asn1)
    vec=tests/aper/$t.vec
    if [ -f "$vec" ]; then run "ex-$t" "$asn" --vectors "$vec"; else run "ex-$t" "$asn"; fi
done
exit $fail
