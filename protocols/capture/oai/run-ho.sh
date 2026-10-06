#!/usr/bin/env bash
# OAI's CI N2 handover with rfsim: two gNBs, each a CU-CP, CU-UP and DU, one
# UE handed over between them over NG (and its F1 and E1 contexts with it).
# NGAP, F1AP and E1AP captured in each CU-CP's network namespace.
#   run-ho.sh NHO OUTDIR      (NHO handovers, alternating)
set -uo pipefail
# OUT relative to where this was run from, not to the compose directory
[ $# -ge 2 ] && set -- "$1" "$(realpath -m "$2")"
NHO=${1:-6}; OUT=$2
. "$(dirname "$0")/../../lib.sh"
D=$WORK/oai
[ -d "$D/ci-scripts" ] || { echo "run capture/oai/fetch.sh first" >&2; exit 2; }
C=$D/ci-scripts/yaml_files/5g_rfsimulator_n2_ho
cd $C
T=$(date +%s); mkdir -p "$OUT"
cap() { docker run -d --rm --name oai-cap-$1-$T --user 0 --cap-add NET_RAW --cap-add NET_ADMIN --network container:$1 \
          -v $D:/out --entrypoint tcpdump gradiant/open5gs:2.7.2 -Z root -i any -s 0 -w /out/cap-$1-$T.pcap sctp >/dev/null; }
docker compose up -d mysql oai-amf oai-smf oai-upf oai-ext-dn >/dev/null 2>&1
sleep 25
docker compose up -d oai-cucp-0 >/dev/null 2>&1; sleep 3; cap rfsim5g-oai-cucp-0; sleep 2
docker compose up -d oai-cuup-0 oai-du-0 >/dev/null 2>&1; sleep 10
docker compose up -d oai-nr-ue >/dev/null 2>&1; sleep 30
docker compose up -d oai-cucp-1 >/dev/null 2>&1; sleep 3; cap rfsim5g-oai-cucp-1; sleep 2
docker compose up -d oai-cuup-1 oai-du-1 >/dev/null 2>&1; sleep 20
docker exec rfsim5g-oai-nr-ue ping -c 3 -I oaitun_ue1 192.168.72.135 2>&1 | tail -1
for i in $(seq 1 $NHO); do
  if [ $((i % 2)) = 1 ]; then echo ci trigger_n2_ho 1,1 | nc -q 2 192.168.71.150 9090; else echo ci trigger_n2_ho 0,1 | nc -q 2 192.168.71.180 9090; fi
  sleep 12
  docker exec rfsim5g-oai-nr-ue ping -c 3 -I oaitun_ue1 192.168.72.135 2>&1 | tail -1
done
# then the CU-CP serving the UE releases its PDU session
if [ $((NHO % 2)) = 0 ]; then cu=192.168.71.150; else cu=192.168.71.180; fi
echo ci pdu_session_release | nc -q 2 $cu 9090; sleep 8
docker compose ps --format '{{.Name}} {{.Status}}' 2>/dev/null
docker compose logs oai-amf > "$OUT/amf.log" 2>&1; docker compose logs oai-smf > "$OUT/smf.log" 2>&1
docker compose stop oai-nr-ue >/dev/null 2>&1; sleep 10
docker compose stop oai-du-0 oai-du-1 >/dev/null 2>&1; sleep 5
docker compose stop oai-cuup-0 oai-cuup-1 >/dev/null 2>&1; sleep 5
docker stop oai-cap-rfsim5g-oai-cucp-0-$T oai-cap-rfsim5g-oai-cucp-1-$T >/dev/null
docker compose logs oai-cucp-0 oai-cucp-1 2>/dev/null | grep -iE "handover" | tail -12
docker compose down >/dev/null 2>&1
mv $D/cap-rfsim5g-oai-cucp-0-$T.pcap "$OUT/cucp0.pcap"; mv $D/cap-rfsim5g-oai-cucp-1-$T.pcap "$OUT/cucp1.pcap"; ls -la "$OUT"
