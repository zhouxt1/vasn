#!/usr/bin/env bash
# Xn Setup among three OAI gNBs (OAI's xn-simulator configurations, made by
# fetch.sh); XnAP (and NGAP) captured in gNB 0's namespace
#   run-xn.sh SECONDS OUT.pcap
set -uo pipefail
[ $# -ge 2 ] && set -- "$1" "$(realpath -m "$2")"
SECS=${1:-30}; OUT=$2
. "$(dirname "$0")/../../lib.sh"
D=$WORK/oai
[ -d "$D/ci-scripts" ] || { echo "run capture/oai/fetch.sh first" >&2; exit 2; }
CN="docker compose -f $D/doc/tutorial_resources/oai-cn5g/docker-compose.yaml"
cd $D/xn
T=$(date +%s)
$CN up -d mysql oai-nrf oai-udr oai-udm oai-ausf oai-amf oai-smf oai-upf oai-ext-dn >/dev/null 2>&1
sleep 30
docker compose up -d gnb0 >/dev/null 2>&1; sleep 2
docker run -d --rm --name oai-cap-$T --user 0 --cap-add NET_RAW --cap-add NET_ADMIN --network container:xn-gnb0 \
    -v $D:/out --entrypoint tcpdump gradiant/open5gs:2.7.2 -Z root -i any -s 0 -w /out/cap-$T.pcap sctp >/dev/null
sleep 8
docker compose up -d gnb1 >/dev/null 2>&1; sleep 8
docker compose up -d gnb2 >/dev/null 2>&1
sleep $SECS
docker compose stop gnb2 >/dev/null 2>&1; sleep 5
docker compose stop gnb1 >/dev/null 2>&1; sleep 5
docker stop oai-cap-$T >/dev/null
docker compose logs 2>/dev/null | grep -i "xn" | tail -12
docker compose down >/dev/null 2>&1
$CN down >/dev/null 2>&1
mv $D/cap-$T.pcap "$OUT"; ls -la "$OUT"
