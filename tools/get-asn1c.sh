#!/usr/bin/env bash
# Build asn1c from git source into tools/asn1c/: the mouse07410 fork, which
# VUPER's pre-generated NR C came from (its `-gen-UPER -no-gen-BER` flags are
# that fork's), pinned to one commit. A reference encoder for X.691 cases that
# NR and ITS do not have, next to pycrate.
#
#   tools/get-asn1c.sh    then  tools/asn1c/bin/asn1c, skeletons in tools/asn1c/share
set -euo pipefail
COMMIT=844f9caa33f53d887a58f7696cca17e9657bf984   # vlm_master, v1.5.1-44, 2026-07-24
cd "$(dirname "$0")"
[ -x asn1c/bin/asn1c ] && { echo "already present"; exit 0; }
[ -d asn1c-src ] || git clone -q https://github.com/mouse07410/asn1c.git asn1c-src
cd asn1c-src
git checkout -q "$COMMIT"
autoreconf -iv >/dev/null 2>&1
./configure -q --prefix="$(cd .. && pwd)/asn1c" >/dev/null
make -s -j"$(nproc)" >/dev/null
make -s install >/dev/null
echo "asn1c $(git rev-parse --short HEAD) ready: tools/asn1c/bin/asn1c"
