# in the UERANSIM container: NUE UEs, CYCLES rounds of procedures
NUE=$1; CYCLES=$2
imsi() { echo imsi-99970$(printf %010d $1); }
nr-gnb -c /ran/gnb.yaml > /ran/gnb.log 2>&1 &
sleep 3
for c in $(seq $CYCLES); do
  nr-ue -c /ran/ue.yaml -n $NUE >> /ran/ue.log 2>&1 &
  sleep 25
  for i in $(seq 1 $NUE); do nr-cli $(imsi $i) -e 'ps-establish IPv4 --sst 1 --dnn internet' >/dev/null 2>&1; done
  sleep 6
  for i in $(seq 1 $NUE); do nr-cli $(imsi $i) -e 'ps-release 2' >/dev/null 2>&1; done
  sleep 4
  for i in $(seq 1 $((NUE / 2))); do nr-cli $(imsi $i) -e 'ps-release 1' >/dev/null 2>&1; done
  sleep 4
  for i in $(seq 1 $((NUE / 2))); do nr-cli $(imsi $i) -e 'ps-establish IPv4 --sst 1 --dnn internet' >/dev/null 2>&1; done
  sleep 6
  # the gNB releases half the UEs' contexts; traffic brings them back (Service Request)
  for id in $(nr-cli UERANSIM-gnb-999-70-1 -e ue-list | awk '/ue-id/ {print $3}' | head -$((NUE / 2))); do
    nr-cli UERANSIM-gnb-999-70-1 -e "ue-release $id" >/dev/null 2>&1
  done
  sleep 6
  for i in $(seq 1 $NUE); do ping -c 1 -W 2 -I uesimtun$((i - 1)) 10.45.0.1 >/dev/null 2>&1 & done
  sleep 8
  for i in $(seq 1 $NUE); do
    if [ $((i % 2)) = 0 ]; then d='deregister normal'; else d='deregister switch-off'; fi
    nr-cli $(imsi $i) -e "$d" >/dev/null 2>&1
  done
  sleep 8
  pkill nr-ue; sleep 3
done
pkill nr-gnb; sleep 2
grep -c 'Initial Registration is successful' /ran/ue.log
grep -c 'PDU Session establishment is successful' /ran/ue.log
grep -c 'Service Request' /ran/ue.log
