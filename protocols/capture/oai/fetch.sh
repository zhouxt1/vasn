#!/usr/bin/env bash
# OpenAirInterface's CI set-ups the run-*.sh here start, into work/oai: the
# files they use, from OAI at the commit they were captured with, and the
# positioning and Xn configurations made from OAI's own.
#   capture/oai/fetch.sh
# The images: oaisoftwarealliance/oai-{gnb,nr-cuup,nr-ue,enb,lte-ue,flexric,lmf}
# :develop and oai-{amf,smf,upf,...}:v2.2.1, magma-mme:latest; the captures
# in corpus/ used the digests in capture/README.md.
set -euo pipefail
. "$(dirname "$0")/../../lib.sh"
OAI=f8f769592a7030be88ede4bb5ca66fa1ca6a80e0      # develop, 4 October 2026
URL=https://raw.githubusercontent.com/OPENAIRINTERFACE/openairinterface5g/$OAI
D=$WORK/oai; mkdir -p "$D"
FILES="
ci-scripts/conf_files/enb.band7.25prb.rfsim.conf
ci-scripts/conf_files/gnb-cucp.sa.e1-ho-n2.conf
ci-scripts/conf_files/gnb-cucp.sa.f1.conf
ci-scripts/conf_files/gnb-cuup.sa.f1.conf
ci-scripts/conf_files/gnb-du.sa.band78.106prb.rfsim.conf
ci-scripts/conf_files/gnb.sa.band78.106prb.rfsim.flexric.conf
ci-scripts/conf_files/lteue.rfsim.conf
ci-scripts/conf_files/lteue.usim-ci.conf
ci-scripts/conf_files/neighbour-config.conf
ci-scripts/conf_files/nrue.uicc.conf
ci-scripts/yaml_files/4g_rfsimulator_fdd_05MHz/docker-compose.yml
ci-scripts/yaml_files/4g_rfsimulator_fdd_05MHz/entrypoint.sh
ci-scripts/yaml_files/4g_rfsimulator_fdd_05MHz/mme.conf
ci-scripts/yaml_files/4g_rfsimulator_fdd_05MHz/mme_fd.sprint.conf
ci-scripts/yaml_files/4g_rfsimulator_fdd_05MHz/oai_db.cql
ci-scripts/yaml_files/4g_rfsimulator_fdd_05MHz/redis_extern.conf
ci-scripts/yaml_files/5g_rfsimulator_e1/docker-compose.yaml
ci-scripts/yaml_files/5g_rfsimulator_e1/mini_nonrf_config_3slices.yaml
ci-scripts/yaml_files/5g_rfsimulator_flexric/conf/flexric.conf
ci-scripts/yaml_files/5g_rfsimulator_flexric/docker-compose.yml
ci-scripts/yaml_files/5g_rfsimulator/mini_nonrf_config.yaml
ci-scripts/yaml_files/5g_rfsimulator/mysql-healthcheck.sh
ci-scripts/yaml_files/5g_rfsimulator/oai_db.sql
ci-scripts/yaml_files/5g_rfsimulator_n2_ho/docker-compose.yaml
doc/tutorial_resources/oai-cn5g/conf/config.yaml
doc/tutorial_resources/oai-cn5g/conf/sip.conf
doc/tutorial_resources/oai-cn5g/conf/users.conf
doc/tutorial_resources/oai-cn5g/database/oai_db.sql
doc/tutorial_resources/oai-cn5g/docker-compose-positioning.yaml
doc/tutorial_resources/oai-cn5g/docker-compose.yaml
doc/tutorial_resources/oai-cn5g/healthscripts/mysql-healthcheck.sh
doc/tutorial_resources/positioning/InputData.json
openair2/XNAP/tests/xn-simulator/gnb.sa.band78.fr1.106PRB.pci0.xn.rfsim.conf
openair2/XNAP/tests/xn-simulator/gnb.sa.band78.fr1.106PRB.pci1.xn.rfsim.conf
openair2/XNAP/tests/xn-simulator/gnb.sa.band78.fr1.106PRB.pci2.xn.rfsim.conf
"
for f in $FILES; do
    [ -f "$D/$f" ] && continue
    mkdir -p "$D/$(dirname "$f")"; curl -sf "$URL/$f" -o "$D/$f" || { echo "cannot fetch $f" >&2; exit 1; }
done
chmod +x "$D"/ci-scripts/yaml_files/4g_rfsimulator_fdd_05MHz/entrypoint.sh "$D"/ci-scripts/yaml_files/5g_rfsimulator/mysql-healthcheck.sh \
         "$D"/doc/tutorial_resources/oai-cn5g/healthscripts/mysql-healthcheck.sh
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$D/positioning" "$D/xn"
cp "$here/positioning/compose.yaml" "$D/positioning/"; cp "$here/xn/compose.yaml" "$D/xn/"
python3 - "$D" <<'PY'
import re, sys
D = sys.argv[1]
# positioning: the FlexRIC CI's gNB without its E2 agent, with the TRPs of
# OAI's own NRPPa test (tests/nr-cu-nrppa); the LMF asks for UE 3 in that cell
s = open(D + '/ci-scripts/conf_files/gnb.sa.band78.106prb.rfsim.flexric.conf').read()
s = re.sub(r'\ne2_agent = \{.*?\};\n', '\n', s, flags=re.S)
s += '''
positioning_config = (
    {
        NumTRPs  = 4; # number of TRPs
        TRPIDs   = [1,2,3,4]; # userdefined distinct IDs
        TRPxAxis = [71,21,10,45]; # X-axis value of each TRP
        TRPyAxis = [11,22,62,14]; # Y-axis value of each TRP
        TRPzAxis = [41,22,33,42]; # Z-axis value of each TRP
        Units    = [0, 0, 0, 0]; # 0 = mm, 1 = cm, 2 = dm
    }
);
'''
open(D + '/positioning/gnb.pos.conf', 'w').write(s)
j = open(D + '/doc/tutorial_resources/positioning/InputData.json').read()
j = j.replace('imsi-001010000000001', 'imsi-001010000000003').replace('"nrCellId": "917505"', '"nrCellId": "12345678"')
open(D + '/positioning/InputData.json', 'w').write(j)
# Xn: OAI's xn-simulator gNBs on the 5GC's network, each the others' neighbour
ips = {0: '192.168.70.161', 1: '192.168.70.162', 2: '192.168.70.163'}
for i in (0, 1, 2):
    s = open(D + '/openair2/XNAP/tests/xn-simulator/gnb.sa.band78.fr1.106PRB.pci%d.xn.rfsim.conf' % i).read()
    old = '127.0.0.%d' % ((i + 1) * 10)
    others = [ips[k] for k in (0, 1, 2) if k != i]
    s = s.replace('gnb_ipv4_address_for_xnc             = "%s"' % old, 'gnb_ipv4_address_for_xnc             = "%s"' % ips[i])
    s = re.sub(r'candidate_gnb_ipv4_address_for_xnc   = \(.*?\);', 'candidate_gnb_ipv4_address_for_xnc   = ({ ip = "%s";}, { ip = "%s";});' % tuple(others), s)
    s = s.replace('GNB_IPV4_ADDRESS_FOR_NG_AMF              = "192.168.70.129/24"', 'GNB_IPV4_ADDRESS_FOR_NG_AMF              = "%s"' % ips[i])
    s = s.replace('GNB_IPV4_ADDRESS_FOR_NGU                 = "%s"' % old, 'GNB_IPV4_ADDRESS_FOR_NGU                 = "%s"' % ips[i])
    assert ips[i] in s and old not in s
    open(D + '/xn/gnb%d.conf' % i, 'w').write(s)
PY
echo "OAI's set-ups in $D"
