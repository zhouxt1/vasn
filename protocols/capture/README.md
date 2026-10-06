# Capturing the traffic in corpus/

Real messages between open-source 5G stacks, all in Docker on one machine,
the RAN over OpenAirInterface's RF simulator or UERANSIM. Each script starts
a set-up, runs a scenario, captures SCTP with tcpdump in one container's
network namespace (containers run as root, `--rm`, and are stopped at the
end) and writes a pcap; `sctp_pdus.py` then writes each message of a protocol
to a file.

| | the set-up | corpus/ |
| --- | --- | --- |
| `open5gs/run.sh NUE CYCLES OUT.pcap` | Open5GS 2.7.2 (every network function) and UERANSIM 3.2.6, in one network namespace on loopback; NUE UEs register, set up and release PDU sessions, have their contexts released by the gNB and come back with a Service Request, and deregister, CYCLES times | ngap/bench (3944) |
| `oai/run-split.sh SECONDS OUT.pcap` | OAI's CI `5g_rfsimulator_e1`: a CU-CP, three CU-UPs, three DUs, three UEs and OAI's 5G core; captured in the CU-CP | ngap/bench (48), f1ap/oai-split, e1ap/oai-split |
| `oai/run-ho.sh NHO OUTDIR` | OAI's CI `5g_rfsimulator_n2_ho`: two split gNBs, one UE handed over between them NHO times by telnet; captured in each CU-CP | ngap/oai-handover, f1ap/oai-handover, e1ap/oai-handover |
| `oai/run-e2.sh SECONDS OUT.pcap` | OAI's CI `5g_rfsimulator_flexric`: a gNB with its E2 agent, two UEs, FlexRIC's nearRT-RIC and four xApps (RC and KPM monitoring, KPM with RC control, FlexRIC's own SMs); captured in the RIC | e2ap, e42ap (FlexRIC sends PPID 0: `sctp_pdus.py ... port:36421`, `port:36422`), and kpm and rc (`embedded.py ... e2sm 2=kpm 3=rc`) |
| `oai/run-positioning.sh N OUT.pcap` | a gNB with the TRP positions of OAI's own NRPPa test, a UE, and the OAI 5G core with its LMF, asked N times where the UE is; captured in the gNB | ngap/oai-positioning |
| `oai/run-xn.sh SECONDS OUT.pcap` | three gNBs with OAI's xn-simulator configurations, on the 5G core's network; captured in gNB 0 | xnap/oai-xn-setup |
| `oai/run-4g.sh CYCLES OUT.pcap` | OAI's CI `4g_rfsimulator_fdd_05MHz`: OAI's eNB and LTE UE, Magma's MME, OAI's HSS and SPGW; captured in the MME | s1ap/oai-magma |

`oai/fetch.sh` first: it fetches the CI files these use from OAI at the
commit they were captured with (f8f7695, 4 October 2026), and makes the
positioning and Xn configurations from OAI's own.

| | |
| --- | --- |
| `sctp_pdus.py PCAP OUTDIR PPID` | each SCTP DATA user message of one payload protocol (60 NGAP, 62 F1AP, 64 E1AP, 61 XnAP, 18 S1AP), reassembled, to a file; `port:N` instead of a PPID selects by port |
| `embedded.py DRIVER TYPE INDIR OUTDIR nrppa\|e2sm FUNC=NAME...` | the PDUs carried as octets in others, from our decoder's JER: NRPPa in NGAP, and the E2SM octets in E2AP by RAN function |
| `mutate.py IN OUT K [SEED]` | K mutants of each message: a truncation, a bit flipped, an octet changed or inserted, a tail appended |

The corpora were captured on 5 and 6 October 2026 with these images:

| image | digest |
| --- | --- |
| `oaisoftwarealliance/oai-gnb:develop` | `sha256:afb4d40130632502c74e166e52663c49a3ac183b3983f1132a97d49bbdf7281e` |
| `oaisoftwarealliance/oai-nr-cuup:develop` | `sha256:c6a1e3b59942de12d363f96d460e477ae2eed93f143e951ec81bdcb639cbdc4c` |
| `oaisoftwarealliance/oai-nr-ue:develop` | `sha256:54368b56e1a506d9be91a72c1d9330247d49358e16b154df2481ec192e4cc1ec` |
| `oaisoftwarealliance/oai-flexric:develop` | `sha256:46133687d05b22b12bf3dfc0c9cf293cae561849a43daff64772a02305b06032` |
| `oaisoftwarealliance/oai-lmf:develop` | `sha256:1b785386a5d034480f4ca8b8f0be0e0cdfeb401dc36995132a878dc5a7a59cca` |
| `oaisoftwarealliance/oai-enb:develop` | `sha256:1d10c901126e5046bfafd9049e635d87705dd73a1b5d1672cfe180872f05df2e` |
| `oaisoftwarealliance/oai-lte-ue:develop` | `sha256:1609f378dbf0f0216ec1c51785834492700ed901502f8a72380055e801c0ddab` |
| `oaisoftwarealliance/oai-amf:v2.2.1` | `sha256:c6dee19b65b2bf29b73e6647f98e0381d96a2eb4c6f9a68f5c3bc70534afa14c` |
| `oaisoftwarealliance/oai-smf:v2.2.1` | `sha256:c1f1452edfc835c36aa96a2efca337da0149212a6561bbb5f9b1994356beee24` |
| `oaisoftwarealliance/oai-upf:v2.2.1` | `sha256:03985036c2477a75755ded9b7fe9508b62f49e4ce9e9f059bbb68af63932e7f7` |
| `oaisoftwarealliance/magma-mme:latest` | `sha256:2585b66e3e2a254e17181030b0e9b2cf1df664e6fc1a07c4527f6994adc7c2a4` |
| `gradiant/open5gs:2.7.2` | `sha256:f8a3aa0115c5cf97a7a757e35a7ee78f5f8dae0d842e0f09c14d4d7597ad6ff3` |
| `gradiant/ueransim:3.2.6` | `sha256:015b30d5fa0f9fa847cfa254ba48a336195c2a77a25122cea71114d8b09265ab` |

E2AP's RIC Indications are sampled: `e2ap/flexric-sample` has every message
but the Indications and every 80th Indication, `e2ap/flexric-bench` every
13th message of the 266,031.
