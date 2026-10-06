#!/usr/bin/env bash
# OAI's CI E1/F1 split with rfsim (3 DU, 3 CU-UP, 3 UE, OAI 5GC), F1AP, E1AP
# and NGAP captured in the CU-CP's network namespace.  run-split.sh SECONDS OUT.pcap
set -uo pipefail
[ $# -ge 2 ] && set -- "$1" "$(realpath -m "$2")"
SECS=${1:-180}; OUT=$2
. "$(dirname "$0")/../../lib.sh"
D=$WORK/oai
[ -d "$D/ci-scripts" ] || { echo "run capture/oai/fetch.sh first" >&2; exit 2; }
C=$D/ci-scripts/yaml_files/5g_rfsimulator_e1
cd $C
T=$(date +%s)
docker compose up -d mysql oai-amf oai-smf oai-upf >/dev/null 2>&1
sleep 25
docker compose up -d oai-cucp >/dev/null 2>&1
sleep 3
docker run -d --rm --name oai-cap-$T --user 0 --cap-add NET_RAW --cap-add NET_ADMIN --network container:rfsim5g-oai-cucp \
    -v $D:/out --entrypoint tcpdump gradiant/open5gs:2.7.2 -Z root -i any -s 0 -w /out/cap-$T.pcap sctp >/dev/null
sleep 2
docker compose up -d oai-cuup oai-cuup2 oai-cuup3 >/dev/null 2>&1
sleep 5
docker compose up -d oai-du oai-du2 oai-du3 >/dev/null 2>&1
sleep 15
docker compose up -d oai-nr-ue oai-nr-ue2 oai-nr-ue3 >/dev/null 2>&1
sleep $SECS
docker compose ps --format '{{.Name}} {{.Status}}' 2>/dev/null
for u in oai-nr-ue oai-nr-ue2 oai-nr-ue3; do docker compose stop $u >/dev/null 2>&1; done
sleep 10
for u in oai-du oai-du2 oai-du3; do docker compose stop $u >/dev/null 2>&1; done
sleep 8
docker stop oai-cap-$T >/dev/null
docker compose logs oai-nr-ue 2>/dev/null | grep -iE "PDU session|registration|REGISTRATION" | tail -3
docker compose down >/dev/null 2>&1
mv $D/cap-$T.pcap "$OUT"; ls -la "$OUT"
