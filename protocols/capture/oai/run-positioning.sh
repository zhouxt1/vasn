#!/usr/bin/env bash
# NRPPa: the LMF asked for a UE's location N times; NGAP (with NRPPa in its
# NRPPa transport messages) captured in the gNB's network namespace.
#   run-positioning.sh N OUT.pcap
set -uo pipefail
# OUT relative to where this was run from, not to the compose directory
[ $# -ge 2 ] && set -- "$1" "$(realpath -m "$2")"
N=${1:-5}; OUT=$2
. "$(dirname "$0")/../../lib.sh"
D=$WORK/oai
[ -d "$D/ci-scripts" ] || { echo "run capture/oai/fetch.sh first" >&2; exit 2; }
CN="docker compose -f $D/doc/tutorial_resources/oai-cn5g/docker-compose-positioning.yaml"
cd $D/positioning
T=$(date +%s)
$CN up -d mysql oai-nrf oai-udr oai-udm oai-ausf oai-amf oai-lmf oai-smf oai-upf oai-ext-dn >/dev/null 2>&1
sleep 30
docker compose up -d oai-gnb >/dev/null 2>&1; sleep 2
docker run -d --rm --name oai-cap-$T --user 0 --cap-add NET_RAW --cap-add NET_ADMIN --network container:rfsim5g-oai-gnb \
    -v $D:/out --entrypoint tcpdump gradiant/open5gs:2.7.2 -Z root -i any -s 0 -w /out/cap-$T.pcap sctp >/dev/null
sleep 10
docker compose up -d oai-nr-ue >/dev/null 2>&1; sleep 30
for i in $(seq 1 $N); do
  curl -s -m 20 --http2-prior-knowledge -H "Content-Type: application/json" \
      -d "$(cat InputData.json)" -X POST http://192.168.70.141:8080/nlmf-loc/v1/determine-location | head -c 300; echo
  sleep 5
done
docker compose stop oai-nr-ue >/dev/null 2>&1; sleep 5
docker compose stop oai-gnb >/dev/null 2>&1; sleep 3
docker stop oai-cap-$T >/dev/null
$CN logs oai-lmf 2>/dev/null | grep -iE "error|nrppa|trp" | tail -8
docker compose down >/dev/null 2>&1
$CN down >/dev/null 2>&1
mv $D/cap-$T.pcap "$OUT"; ls -la "$OUT"
