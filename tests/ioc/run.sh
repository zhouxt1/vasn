#!/usr/bin/env bash
# Information object classes (X.681, X.682, X.683): the 3GPP protocols'
# pattern cut down (ies.asn1), and the reference implementations' deviations
# found on the real protocols, each with its vectors, in ALIGNED (the 3GPP
# protocols' variant), N random values (default 40), verified; ies.asn1 in
# UNALIGNED too. Exits 1 if any check of ours fails.
#
#   tests/ioc/run.sh [N]
set -uo pipefail
cd "$(dirname "$0")/../.."
N=${1:-40}
fail=0
run() {
    local label=$1; shift
    out=$(tools/xcheck.py "$@" -n "$N" --verify --dir "target/xcheck/ioc-$label" 2>&1)
    rc=$?
    printf '%-20s %s | %s\n' "$label" "$(grep '^verus ' <<<"$out" | tail -1)" "$(tail -n 1 <<<"$out")"
    if [ $rc -ne 0 ]; then fail=1; grep -E '^FAIL' <<<"$out" | head -5; fi
}
for asn in tests/ioc/*.asn1; do
    t=$(basename "$asn" .asn1)
    v=(); [ -f "tests/ioc/$t.vec" ] && v=(--vectors "tests/ioc/$t.vec")
    run "$t" "$asn" --aper "${v[@]}"
done
run ies-uper tests/ioc/ies.asn1
exit $fail
