#!/usr/bin/env bash
# INTEGER (0..18446744073709551615), the 3GPP protocols' usage counters, in
# both variants: N random values (default 40), verified. Exits 1 if any check
# of ours fails.
#
#   tests/wide/run.sh [N]
set -uo pipefail
cd "$(dirname "$0")/../.."
N=${1:-40}
fail=0
for variant in "" --aper; do
    label=u64${variant:+-aper}
    out=$(tools/xcheck.py tests/wide/u64.asn1 $variant --vectors tests/wide/u64.vec -n "$N" --verify --dir "target/xcheck/$label" 2>&1)
    rc=$?
    printf '%-20s %s | %s\n' "$label" "$(grep '^verus ' <<<"$out" | tail -1)" "$(tail -n 1 <<<"$out")"
    if [ $rc -ne 0 ]; then fail=1; grep -E '^FAIL' <<<"$out" | head -5; fi
done
exit $fail
