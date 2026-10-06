# Sourced by the scripts here: where things are, and what each protocol is.
P=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)    # protocols/
ROOT=$(cd "$P/.." && pwd)                            # the vasn checkout
WORK=${VASN_WORK:-$P/work}                           # downloads, builds, captures
VASNC=$ROOT/target/release/vasnc
[ -x "$ROOT/tools/verus-x86-linux/verus" ] && PATH=$ROOT/tools/verus-x86-linux:$PATH
export PATH
PROTOS="ngap f1ap e1ap xnap s1ap x2ap nrppa lppa e2ap e42ap kpm rc"

# The types a protocol's driver has (comma-separated; `bench` times the first)
types() {
    case $1 in
    ngap) echo NGAP-PDU ;; f1ap) echo F1AP-PDU ;; e1ap) echo E1AP-PDU ;;
    xnap) echo XnAP-PDU ;; s1ap) echo S1AP-PDU ;; x2ap) echo X2AP-PDU ;;
    nrppa) echo NRPPA-PDU ;; lppa) echo LPPA-PDU ;; e2ap | e42ap) echo E2AP-PDU ;;
    kpm) echo E2SM-KPM-IndicationMessage,E2SM-KPM-IndicationHeader,E2SM-KPM-ActionDefinition,E2SM-KPM-EventTriggerDefinition,E2SM-KPM-RANfunction-Description ;;
    rc) echo E2SM-RC-IndicationMessage,E2SM-RC-IndicationHeader,E2SM-RC-ActionDefinition,E2SM-RC-EventTrigger,E2SM-RC-ControlHeader,E2SM-RC-ControlMessage,E2SM-RC-ControlOutcome,E2SM-RC-CallProcessID,E2SM-RC-RANFunctionDefinition ;;
    *) echo "unknown protocol $1" >&2; return 1 ;;
    esac
}

# asn1c's options for a protocol, as the stacks that use it build it: without
# them asn1c's C for XnAP and NRPPa does not compile
asn1c_flags() {
    case $1 in xnap | nrppa | e2ap | e42ap | kpm | rc) echo "-findirect-choice -fno-include-deps" ;; esac
}

need_asn() {
    [ -d "$WORK/asn/$1" ] || { echo "no $WORK/asn/$1: run protocols/get-asn1.sh first" >&2; exit 2; }
}
