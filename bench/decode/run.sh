#!/usr/bin/env bash
# Time the four decoders on one corpus, each pinned to the same core:
#
#   run.sh [DIR] [CORE] [TYPE]    default corpus/shield/DL-DCCH-common, core 4, DL-DCCH-Message
#
# TYPE is any of the seven channel messages. VUPER is timed on DL-DCCH and
# UL-DCCH only, the two it ships an extraction of.
#
# Each harness loads every message first, then times whole rounds of
# decode-and-free (asn1c), decode-and-drop (ours, rasn) or decode (VUPER,
# whose GC frees), and prints the fastest and the median round.
set -euo pipefail
cd "$(dirname "$0")"
DIR=${1:-corpus/shield/DL-DCCH-common}
CORE=${2:-4}
TYPE=${3:-DL-DCCH-Message}
T="taskset -c $CORE"
$T ours/target/release/bench_ours bench "$DIR" 20 "$TYPE"
$T asn1c/obj/bench_asn1c "$DIR" 20 "$TYPE"
$T rasn/target/release/bench_rasn bench "$DIR" 20 "$TYPE"
case $TYPE in
    DL-DCCH-Message) $T vuper/vbench "$DIR" 5 ;;
    UL-DCCH-Message) $T vuper/vbench_ul "$DIR" 5 ;;
esac
