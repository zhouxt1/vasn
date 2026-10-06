#!/usr/bin/env bash
# The protocols' ASN.1, into work/asn/PROTO/ (one file per module), and for
# each the whole schema as one file for the reference implementations,
# work/asn/PROTO.asn1:
#   3GPP: from the specifications in the 3GPP archive (extract_asn1.py);
#   O-RAN: E2AP V03.01, E2SM-KPM V03.00 and E2SM-RC V1.03 as FlexRIC ships
#   them (O-RAN's own files are behind a licence form), and FlexRIC's E42AP.
#   get-asn1.sh [PROTO...]     (default: all)
set -euo pipefail
. "$(dirname "$0")/lib.sh"
# the 3GPP specifications, their versions: V19.4.0 (j40), V19.2.0 (j20) ...
spec() {
    case $1 in
    ngap) echo 38_series/38.413/38413-j40 ;; f1ap) echo 38_series/38.473/38473-j40 ;;
    e1ap) echo 37_series/37.483/37483-j40 ;; xnap) echo 38_series/38.423/38423-j40 ;;
    s1ap) echo 36_series/36.413/36413-j20 ;; x2ap) echo 36_series/36.423/36423-j10 ;;
    nrppa) echo 38_series/38.455/38455-j30 ;; lppa) echo 36_series/36.455/36455-j00 ;;
    esac
}
FLEXRIC=https://gitlab.eurecom.fr/mosaic5g/flexric.git
FLEXRIC_REV=20eab78d7d1da7322a4fec6ec157e8418c5a1cf7     # 2 October 2026
# the 3GPP archive refuses a client that does not look like a browser
UA="Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/120 Safari/537.36"
mkdir -p "$WORK/spec" "$WORK/asn"
want=${*:-$PROTOS}
for p in $want; do
    s=$(spec "$p")
    case $p in
    e2ap | e42ap | kpm | rc)
        [ -d "$WORK/flexric" ] || { git clone -q "$FLEXRIC" "$WORK/flexric"; git -C "$WORK/flexric" checkout -q "$FLEXRIC_REV"; }
        F=$WORK/flexric/src
        case $p in
        e2ap) f=$F/lib/e2ap/v3_01/ie/e2ap_v3_01.asn ;;
        e42ap) f=$F/lib/e2ap/v3_01/ie/e42ap_v3_01.asn ;;
        kpm) f=$F/sm/kpm_sm/kpm_sm_v03.00/ie/e2sm_kpm_v03.00_standard.asn1 ;;
        rc) f=$F/sm/rc_sm/ie/e2sm_rc_v1_03_standard.asn ;;
        esac
        rm -rf "$WORK/asn/$p"; mkdir -p "$WORK/asn/$p"; cp "$f" "$WORK/asn/$p/$p.asn" ;;
    *)
        z=$(basename "$s")
        [ -f "$WORK/spec/$z.zip" ] || curl -sfA "$UA" -o "$WORK/spec/$z.zip" "https://www.3gpp.org/ftp/Specs/archive/$s.zip"
        rm -rf "$WORK/spec/$z" "$WORK/asn/$p"; unzip -q -o "$WORK/spec/$z.zip" -d "$WORK/spec/$z"
        python3 "$P/extract_asn1.py" "$WORK/spec/$z"/*.docx "$WORK/asn/$p" ;;
    esac
    cat "$WORK/asn/$p"/*.asn > "$WORK/asn/$p.asn1"
    case $p in
    e2ap | e42ap)
        # E2AP V03.01 uses four names it does not import (X.680 13.16; vasnc
        # warns): pycrate refuses the schema. The references' copy imports them.
        python3 - "$WORK/asn/$p.asn1" <<'PY'
import re, sys
p = sys.argv[1]; s = open(p).read()
def add(module, src, after, names):
    global s
    i = re.search(r'(?m)^%s \{' % module, s).start()
    j = s.index('\t%s,\n' % after, i)
    assert j < s.index('FROM %s' % src, i)
    s = s[:j] + ''.join('\t%s,\n' % n for n in names) + s[j:]
add('E2AP-PDU-Descriptions', 'E2AP-PDU-Contents', 'RICsubscriptionDeleteRequired', ['RICQueryRequest', 'RICQueryResponse', 'RICQueryFailure'])
add('E2AP-PDU-Contents', 'E2AP-IEs', 'TNLinformation', ['RICtimeToWait'])
open(p, 'w').write(s)
PY
        ;;
    esac
    echo "$p: $(ls "$WORK/asn/$p" | wc -l) modules"
done
