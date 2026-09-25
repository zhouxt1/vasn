#!/usr/bin/env bash
# Fetch the pinned Verus release into tools/verus-x86-linux/.
set -euo pipefail
VERSION="0.2026.09.20.aef82ed"
cd "$(dirname "$0")"
[ -d verus-x86-linux ] && { echo "already present"; exit 0; }
curl -sSL -o verus.zip \
  "https://github.com/verus-lang/verus/releases/download/release/${VERSION}/verus-${VERSION}-x86-linux.zip"
unzip -q verus.zip && rm verus.zip
echo "verus ${VERSION} ready: tools/verus-x86-linux/verus"
