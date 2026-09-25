#!/usr/bin/env bash
# The timed corpus for one channel: the messages of corpus/shield/TYPE that
# ours, asn1c and rasn all decode, hard-linked into corpus/shield/TYPE-common.
# Speed is comparable only on what every decoder accepts; the rejects are
# listed in TYPE-common.rejects, one `DECODER FILE` a line.
#
#   common.sh TYPE      e.g. DL-DCCH-Message
set -euo pipefail
cd "$(dirname "$0")"
TYPE=$1
IN=corpus/shield/$TYPE
OUT=corpus/shield/${TYPE%-Message}-common
{
    ours/target/release/bench_ours why "$IN" "$TYPE" | sed 's|^.*/\([^/:]*\): .*|ours \1|'
    asn1c/obj/bench_asn1c "$IN" 0 "$TYPE" | awk '{print "asn1c", $1}'
    rasn/target/release/bench_rasn fails "$IN" "$TYPE" | awk '$2 == "decode:" {print "rasn", $1}'
} | sort -k2 > "$OUT.rejects"
rm -rf "$OUT" && mkdir -p "$OUT"
ls "$IN" | sort | comm -23 - <(awk '{print $2}' "$OUT.rejects" | sort -u) |
    while read -r f; do ln "$IN/$f" "$OUT/$f"; done
echo "$TYPE: $(ls "$OUT" | wc -l) of $(ls "$IN" | wc -l) in $OUT;" \
     "rejected by ours $(grep -c '^ours ' "$OUT.rejects" || true)," \
     "asn1c $(grep -c '^asn1c ' "$OUT.rejects" || true), rasn $(grep -c '^rasn ' "$OUT.rejects" || true)"
