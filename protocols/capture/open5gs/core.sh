B=/opt/open5gs/bin; C=/conf
ip tuntap add name ogstun mode tun; ip addr add 10.45.0.1/16 dev ogstun; ip link set ogstun up
$B/open5gs-nrfd -c $C/nrf.yaml & sleep 1
$B/open5gs-scpd -c $C/scp.yaml & sleep 1
for n in ausf udm udr pcf nssf bsf; do $B/open5gs-${n}d -c $C/$n.yaml & done
sleep 1; $B/open5gs-upfd -c $C/upf.yaml & sleep 1; $B/open5gs-smfd -c $C/smf.yaml & sleep 1
$B/open5gs-amfd -c $C/amf.yaml & wait
