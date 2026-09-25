#!/usr/bin/env bash
# Every X.691 test module here: its hand-derived vectors and N random values
# (default 40) through ours, pycrate and asn1c, and the generated module
# verified with Verus. Exits 1 if any check of ours fails.
#
# A module may have several vector files, `T.vec` and `T.<variant>.vec`, one
# run each; a `# xcheck: FLAGS` line in one passes FLAGS to tools/xcheck.py
# (e.g. `--containing decode`).
#
#   tests/x691/run.sh [N]
set -uo pipefail
cd "$(dirname "$0")/../.."
N=${1:-40}
fail=0
for asn in tests/x691/*.asn1; do
    t=$(basename "$asn" .asn1)
    vecs=$(ls tests/x691/"$t".vec tests/x691/"$t".*.vec 2>/dev/null)
    for vec in ${vecs:-none}; do
        args=()
        label=$t
        if [ "$vec" != none ]; then
            args=(--vectors "$vec")
            read -ra flags <<<"$(sed -n 's/^# xcheck: *//p' "$vec" | head -1)"
            args+=("${flags[@]}")
            label=$(basename "$vec" .vec)
        fi
        out=$(tools/xcheck.py "$asn" "${args[@]}" -n "$N" --verify --dir "target/xcheck/$label" 2>&1)
        rc=$?
        printf '%-20s %s | %s\n' "$label" "$(grep '^verus ' <<<"$out" | tail -1)" "$(tail -n 1 <<<"$out")"
        if [ $rc -ne 0 ]; then
            fail=1
            grep -E '^FAIL' <<<"$out" | head -5
        fi
    done
done
exit $fail
