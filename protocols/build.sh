#!/usr/bin/env bash
# A protocol's codecs, compiled without verification, and its driver
# (driver/): for check.sh, bench/ and your own use.
#   build.sh PROTO...           work/crates/PROTO, work/driver/PROTO/target/release/driver
#   OPT=3 build.sh PROTO...     the same at opt-level 3, in work/crates-o3, work/driver-o3
# vasnc's crate-dir build is one crate per ASN.1 type; only the driver's types
# and what they use are built.
set -uo pipefail
. "$(dirname "$0")/lib.sh"
OPT=${OPT:-1}
sfx=$([ "$OPT" = 1 ] || echo "-o$OPT")
cgu=$([ "$OPT" = 1 ] && echo 16 || echo 1)   # timed builds: one codegen unit
[ -x "$VASNC" ] || (cd "$ROOT" && cargo build --release -q -p vasnc)
for p in "$@"; do
    need_asn "$p"
    T=$(types "$p") || exit 2
    d=$WORK/crates$sfx/$p
    [ -d "$d" ] || "$VASNC" "$WORK/asn/$p"/*.asn --aper --crate-dir "$d" 2>&1 | tail -1
    s=$(date +%s)
    # vasn as these crates are compiled against, apart from target/verus,
    # which tools/xcheck.py and verify.sh build too
    V=$WORK/vasn-build$sfx
    make -C "$d" -k -j"${JOBS:-$(nproc)}" $(echo "$T" | tr - _ | tr , '\n' | sed 's/$/.vir/') ROOT="$ROOT" VASN_DIR="$V" \
        VFLAGS="--crate-type=lib --compile -C opt-level=$OPT -L . -L $V --no-verify" > "$d.log" 2>&1
    rc=$?
    echo "$p: make $rc in $(( $(date +%s) - s ))s ($d.log)"
    [ $rc = 0 ] || continue
    dd=$WORK/driver$sfx/$p
    mkdir -p "$dd"; cp "$P/driver"/{Cargo.toml,build.rs,rust-toolchain.toml,mkmain.py} "$dd"/
    ( cd "$dd" && python3 mkmain.py "$T" && CRATES=$d VASN=$V \
        CARGO_PROFILE_RELEASE_OPT_LEVEL=$OPT CARGO_PROFILE_RELEASE_CODEGEN_UNITS=$cgu cargo build --release -q 2>&1 | grep -E '^error' | head -3 )
    ls "$dd/target/release/driver"
done
