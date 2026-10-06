#!/usr/bin/env bash
# Real NGAP: Open5GS 2.7.2 and UERANSIM 3.2.6 in one network namespace,
# on loopback; NGAP captured on lo. Containers are --rm and stopped at the end.
#   run.sh NUE CYCLES OUT.pcap
set -uo pipefail
[ $# -ge 3 ] && set -- "$1" "$2" "$(realpath -m "$3")"
NUE=${1:-20}; CYCLES=${2:-3}; OUT=$3
. "$(dirname "$0")/../../lib.sh"
# the containers mount this directory and write to it: a copy in work/
D=$WORK/open5gs; mkdir -p "$D"; cp -r "$(dirname "$0")"/{conf,ran,core.sh,subs.js} "$D"/
T=$(date +%s)
: > $D/ran/ue.log; : > $D/ran/gnb.log
docker run -d --rm --name o5gs-net-$T mongo:6.0 >/dev/null
sleep 5
docker exec -i o5gs-net-$T mongosh --quiet open5gs --eval "var NUE=$NUE" --file /dev/stdin < $D/subs.js 2>/dev/null | tail -1
docker run -d --rm --name o5gs-cap-$T --user 0 --cap-add NET_RAW --cap-add NET_ADMIN --network container:o5gs-net-$T \
    -v $D:/out --entrypoint tcpdump gradiant/open5gs:2.7.2 -Z root -i lo -s 0 -w /out/cap-$T.pcap sctp >/dev/null
docker run -d --rm --name o5gs-$T --privileged --user 0 -e DB_URI=mongodb://localhost/open5gs --network container:o5gs-net-$T \
    -v $D/conf:/conf -v $D/core.sh:/core.sh --entrypoint sh gradiant/open5gs:2.7.2 /core.sh >/dev/null
sleep 12
docker run --rm --name o5gs-ran-$T --privileged --network container:o5gs-net-$T -v $D/ran:/ran \
    --entrypoint sh gradiant/ueransim:3.2.6 /ran/scenario.sh $NUE $CYCLES
docker stop o5gs-cap-$T >/dev/null
docker stop o5gs-$T o5gs-net-$T >/dev/null
mv $D/cap-$T.pcap "$OUT"
ls -la "$OUT"
