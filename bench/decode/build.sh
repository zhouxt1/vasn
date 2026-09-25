#!/usr/bin/env bash
# Build the four decoders that run.sh times, all from nr-rrc-17.3.0.asn1, for
# each of the seven channel messages in CHANNELS:
#
#   ours   vuperc's crates, one per ASN.1 type, opt-level 3, into nr/
#   asn1c  the C that VUPER's harness ships, gcc -O2, into asn1c/obj/
#   rasn   rasn-compiler 0.16.0's bindings, patched to compile (rasn/patch.py)
#   vuper  VUPER's extracted OCaml, as VUPER builds it: DL-DCCH and UL-DCCH only
#
# The schema, asn1c's C and VUPER's OCaml are VUPER's, fetched at the commit
# these results were measured with into VUPER/. Needs `verus` on PATH (the
# nr/ crates link against Verus's vstd), gcc, and for vuper the OCaml 4.14
# switch that vuper/build.sh names. SKIP="vuper" leaves a decoder out.
set -euo pipefail
cd "$(dirname "$0")"
ROOT=$(cd ../.. && pwd)
VUPER_COMMIT=1543c5ab2d19ae803c43436dc17bd82ba2e2e484
JOBS=${JOBS:-$(nproc)}
SKIP=${SKIP:-}
CHANNELS="DL_DCCH_Message UL_DCCH_Message PCCH_Message BCCH_BCH_Message
          BCCH_DL_SCH_Message UL_CCCH_Message DL_CCCH_Message"

if [ ! -d VUPER ]; then
    echo "== fetching VUPER at ${VUPER_COMMIT:0:7} =="
    git init -q VUPER
    git -C VUPER fetch -q --depth 1 https://github.com/SyNSec-den/VUPER.git "$VUPER_COMMIT"
    git -C VUPER -c advice.detachedHead=false checkout -q FETCH_HEAD
fi
NR=$PWD/VUPER/diff_test/ASN_Coding/asnfuzzgen/ASN1/nr-rrc-17.3.0.asn1

echo "== ours =="
cargo build --release -q -p vuperc --manifest-path "$ROOT/Cargo.toml"
"$ROOT/target/release/vuperc" "$NR" --crate-dir nr.new >/dev/null
mkdir -p nr
for f in nr.new/*; do
    b=$(basename "$f")
    cmp -s "$f" "nr/$b" || cp "$f" "nr/$b"
done
rm -rf nr.new
# --no-verify: `make -C nr` without VFLAGS verifies these same sources
make -C nr -k -j"$JOBS" $(printf '%s.vir ' $CHANNELS) ROOT="$ROOT" \
     VFLAGS="--crate-type=lib --compile -C opt-level=3 -L . --no-verify" >/dev/null
( cd ours && cargo build --release -q )

echo "== asn1c =="
make -C asn1c -s -j"$JOBS"

echo "== rasn =="
[ -x rasn/tool/bin/rasn_compiler_cli ] ||
    cargo install -q rasn-compiler --version 0.16.0 --features cli --root rasn/tool
rasn/tool/bin/rasn_compiler_cli -m "$NR" -o rasn/src/nr_rasn.rs
rustfmt --edition 2021 rasn/src/nr_rasn.rs
python3 rasn/patch.py rasn/src/nr_rasn.rs >/dev/null
( cd rasn && cargo build --release -q )

case " $SKIP " in
    *" vuper "*) ;;
    *) echo "== vuper =="; vuper/build.sh dl; vuper/build.sh ul ;;
esac
