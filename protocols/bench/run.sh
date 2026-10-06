#!/usr/bin/env bash
# Ours against asn1c, decoding and encoding the captured messages whole
# (corpus/index.txt's bench sets), on one core: ours at opt-level 3 (OPT=3
# build.sh, which this runs), asn1c's C from the same schema at -O2 and -O3,
# both with their asn1c options (lib.sh). Per message, the minimum over the
# rounds (and the median).
#   bench/run.sh [PROTO...]    (default: those with a bench set)
#   CORE=N to pin to another core than 4; ROUNDS=N (default 20)
set -uo pipefail
. "$(dirname "$0")/../lib.sh"
CORE=${CORE:-4}; ROUNDS=${ROUNDS:-20}
ASN1C=$ROOT/tools/asn1c/bin/asn1c
[ -x "$ASN1C" ] || { echo "no asn1c: run tools/get-asn1c.sh" >&2; exit 2; }
want=${*:-ngap f1ap e1ap s1ap e2ap kpm rc}
for p in $want; do
    need_asn "$p"
    [ -x "$WORK/driver-o3/$p/target/release/driver" ] || OPT=3 "$P/build.sh" "$p" >/dev/null
    [ -f "$P/corpus/$p.tar.gz" ] && { mkdir -p "$WORK/corpus"; tar xzf "$P/corpus/$p.tar.gz" -C "$WORK/corpus"; }
    read -r set ty _ < <(grep "^$p/" "$P/corpus/index.txt" | awk '$3 ~ /bench/')
    dir=$WORK/corpus/$set
    src=$WORK/bench/asn1c-src/$p
    if [ ! -f "$src/Makefile.am.libasncodec" ]; then
        rm -rf "$src"; mkdir -p "$src"
        (cd "$src" && "$ASN1C" -pdu=all -fcompound-names $(asn1c_flags "$p") -no-gen-BER -no-gen-XER \
            -no-gen-OER -no-gen-UPER "$WORK/asn/$p.asn1" > asn1c.log 2>&1) || { echo "$p: asn1c fails ($src/asn1c.log)"; }
    fi
    echo "== $p: $set, $(ls "$dir" | wc -l) messages"
    taskset -c "$CORE" "$WORK/driver-o3/$p/target/release/driver" bench "$dir" "$ROUNDS"
    for o in O2 O3; do
        b=$WORK/bench/obj-$p-$o/bench_asn1c
        [ -x "$b" ] || make -s -C "$P/bench" -j"$(nproc)" SRC="$src" PDU="$ty" OPT=-$o O="$WORK/bench/obj-$p-$o" >/dev/null 2>&1
        [ -x "$b" ] && { echo -n "$o "; taskset -c "$CORE" "$b" "$dir" "$ROUNDS"; } || echo "$o asn1c: its C does not compile"
    done
    taskset -c "$CORE" "$WORK/driver-o3/$p/target/release/driver" encode "$dir" "$ROUNDS"
    for o in O2 O3; do
        b=$WORK/bench/obj-$p-$o/bench_asn1c
        [ -x "$b" ] && { echo -n "$o "; taskset -c "$CORE" "$b" "$dir" "-$ROUNDS"; }
    done
done
