#!/usr/bin/env bash
# OAI's CI 4G rfsim (FDD 5 MHz): Cassandra, OAI's HSS and SPGW, Magma's MME,
# OAI's eNB and LTE UE. S1AP captured in the MME's network namespace. The UE
# attaches, pings, is stopped and started again CYCLES times.
#   run-4g.sh CYCLES OUT.pcap
set -uo pipefail
[ $# -ge 2 ] && set -- "$1" "$(realpath -m "$2")"
CYC=${1:-2}; OUT=$2
. "$(dirname "$0")/../../lib.sh"
D=$WORK/oai
[ -d "$D/ci-scripts" ] || { echo "run capture/oai/fetch.sh first" >&2; exit 2; }
cd $D/ci-scripts/yaml_files/4g_rfsimulator_fdd_05MHz
T=$(date +%s)
docker compose up -d cassandra db_init >/dev/null 2>&1; sleep 40
docker compose up -d oai_hss redis magma_mme oai_spgwc oai_spgwu trf_gen >/dev/null 2>&1; sleep 30
# in the MME's namespace, up before the eNB: its S1 Setup too
docker run -d --rm --name oai-cap-$T --user 0 --cap-add NET_RAW --cap-add NET_ADMIN --network container:rfsim4g-magma-mme \
    -v $D:/out --entrypoint tcpdump gradiant/open5gs:2.7.2 -Z root -i any -s 0 -w /out/cap-$T.pcap sctp >/dev/null
sleep 2
docker compose up -d oai_enb0 >/dev/null 2>&1; sleep 15
for i in $(seq 1 $CYC); do
  docker compose up -d oai_ue0 >/dev/null 2>&1; sleep 40
  docker exec rfsim4g-oai-lte-ue0 ping -c 3 -I oaitun_ue1 192.168.61.11 2>&1 | tail -1
  docker compose stop oai_ue0 >/dev/null 2>&1; sleep 15
done
docker compose ps -a --format '{{.Name}} {{.Status}}' 2>/dev/null
docker compose stop oai_enb0 >/dev/null 2>&1; sleep 3
docker stop oai-cap-$T >/dev/null
docker compose logs magma_mme 2>/dev/null | grep -iE "s1ap|attach" | tail -5
docker compose down >/dev/null 2>&1
mv $D/cap-$T.pcap "$OUT"; ls -la "$OUT"
