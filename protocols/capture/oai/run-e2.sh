#!/usr/bin/env bash
# OAI's CI FlexRIC test with rfsim: the OAI 5GC (its tutorial deployment), a
# monolithic gNB with its E2 agent, two UEs, FlexRIC's nearRT-RIC and its
# xApps (RC monitoring, KPM monitoring, KPM with RC control, FlexRIC's own
# MAC/RLC/PDCP/GTP SMs). E2AP (gNB-RIC) and E42AP (xApp-RIC) captured in the
# RIC's network namespace.   run-e2.sh SECONDS OUT.pcap
set -uo pipefail
# OUT relative to where this was run from, not to the compose directory
[ $# -ge 2 ] && set -- "$1" "$(realpath -m "$2")"
SECS=${1:-60}; OUT=$2
. "$(dirname "$0")/../../lib.sh"
D=$WORK/oai
[ -d "$D/ci-scripts" ] || { echo "run capture/oai/fetch.sh first" >&2; exit 2; }
CN="docker compose -f $D/doc/tutorial_resources/oai-cn5g/docker-compose.yaml"
cd $D/ci-scripts/yaml_files/5g_rfsimulator_flexric
T=$(date +%s)
$CN up -d mysql oai-nrf oai-udr oai-udm oai-ausf oai-amf oai-smf oai-upf oai-ext-dn >/dev/null 2>&1
sleep 30
docker compose up -d nearRT-RIC >/dev/null 2>&1; sleep 3
docker run -d --rm --name oai-cap-$T --user 0 --cap-add NET_RAW --cap-add NET_ADMIN --network container:nearRT-RIC \
    -v $D:/out --entrypoint tcpdump gradiant/open5gs:2.7.2 -Z root -i any -s 0 -w /out/cap-$T.pcap sctp >/dev/null
sleep 2
docker compose up -d oai-gnb >/dev/null 2>&1; sleep 10
docker compose up -d xapp-rc-moni >/dev/null 2>&1; sleep 5
docker compose up -d oai-nr-ue oai-nr-ue2 >/dev/null 2>&1; sleep 30
docker compose up -d xapp-kpm-moni >/dev/null 2>&1; sleep 10
docker compose up -d xapp-kpm-rc >/dev/null 2>&1; sleep 10
docker compose up -d xapp-gtp-mac-rlc-pdcp-moni >/dev/null 2>&1
docker exec rfsim5g-oai-nr-ue ping -c 5 -I oaitun_ue1 192.168.70.135 2>&1 | tail -1
sleep $SECS
docker compose ps -a --format '{{.Name}} {{.Status}}' 2>/dev/null
for s in xapp-rc-moni xapp-kpm-moni xapp-kpm-rc xapp-gtp-mac-rlc-pdcp-moni; do docker compose stop $s >/dev/null 2>&1; done
sleep 3
docker compose stop oai-nr-ue oai-nr-ue2 >/dev/null 2>&1; sleep 5
docker compose stop oai-gnb >/dev/null 2>&1; sleep 3
docker stop oai-cap-$T >/dev/null
docker compose logs xapp-kpm-moni 2>/dev/null | tail -5
docker compose down >/dev/null 2>&1
$CN down >/dev/null 2>&1
mv $D/cap-$T.pcap "$OUT"; ls -la "$OUT"
