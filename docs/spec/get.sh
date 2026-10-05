#!/usr/bin/env bash
# Fetch the standards the codec is written against. ITU-T Recommendations are
# free to download but not ours to redistribute, so they are not committed.
set -euo pipefail
cd "$(dirname "$0")"
for rec in X.680 X.690 X.691 X.697; do
    curl -sfL -o "T-REC-$rec-202102.pdf" \
      "https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-$rec-202102-I%21%21PDF-E&type=items"
done
echo "X.680 (02/2021), ASN.1 notation: $(pwd)/T-REC-X.680-202102.pdf"
echo "X.690 (02/2021), BER/CER/DER: $(pwd)/T-REC-X.690-202102.pdf"
echo "X.691 (02/2021), PER: $(pwd)/T-REC-X.691-202102.pdf"
echo "X.697 (02/2021), JER: $(pwd)/T-REC-X.697-202102.pdf"
