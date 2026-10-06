# The 3GPP and O-RAN protocols, in aligned PER

The application protocols of the RAN and of O-RAN's E2, compiled by
`vasnc --aper` from the ASN.1 of their specifications, verified, checked
against asn1c and pycrate, and timed against asn1c:

| | specification | types | crates verified |
| --- | --- | --- | --- |
| `ngap` | NGAP, TS 38.413 V19.4.0 | 4514 | 4362 |
| `f1ap` | F1AP, TS 38.473 V19.4.0 | 6867 | 6488 |
| `e1ap` | E1AP, TS 37.483 V19.4.0 | 2211 | 2123 |
| `xnap` | XnAP, TS 38.423 V19.4.0 | 5229 | 5020 |
| `s1ap` | S1AP, TS 36.413 V19.2.0 | 2361 | 2247 |
| `x2ap` | X2AP, TS 36.423 V19.1.0 | 3193 | 3071 |
| `nrppa` | NRPPa, TS 38.455 V19.3.0 | 1795 | 1671 |
| `lppa` | LPPa, TS 36.455 V19.0.0 | 409 | 374 |
| `e2ap` | O-RAN E2AP V03.01 | 599 | 556 |
| `e42ap` | FlexRIC's E42AP (E2AP between an xApp and the RIC) | 632 | 588 |
| `kpm` | O-RAN E2SM-KPM V03.00 | 205 | 181 |
| `rc` | O-RAN E2SM-RC V1.03 (recursive, unrolled 8 levels deep) | 520 | 489 |

Every type compiles, none is skipped, and every crate verifies. OVERVIEW.md §3
has the results.

## Running it

Needs `verus` on `PATH` (`tools/get-verus.sh`), and for `check.sh` pycrate
0.7.11 (`pip install pycrate`) and asn1c (`tools/get-asn1c.sh`). Everything
goes into `protocols/work/` (`VASN_WORK=DIR` for another place). `build.sh`
and `verify.sh` keep their own builds of vasn there, and can run at the same
time; two runs of the same one should not.

```bash
protocols/get-asn1.sh              # the ASN.1 of all twelve (or: get-asn1.sh ngap e1ap)
protocols/verify.sh ngap           # every crate of NGAP verified: 21 min on 20 cores
protocols/build.sh ngap            # compiled without verification, and its driver
protocols/check.sh ngap            # ours against asn1c and pycrate: 300 random values, and the traffic
protocols/bench/run.sh ngap        # ours against asn1c, decoding and encoding the traffic
```

| | |
| --- | --- |
| `get-asn1.sh [PROTO...]` | The 3GPP specifications from the 3GPP archive, their ASN.1 extracted (`extract_asn1.py`: the text between `-- ASN1START` and `-- ASN1STOP`, each module cut at its `END`) into `work/asn/PROTO/`. O-RAN's from FlexRIC at a pinned commit, as O-RAN's own files are behind a licence form. `work/asn/PROTO.asn1` is the whole schema for the reference implementations; for E2AP it adds the four names E2AP-PDU-Descriptions and E2AP-PDU-Contents use without importing them (X.680 13.16), which pycrate otherwise refuses |
| `verify.sh PROTO...` | `vasnc --aper --crate-dir` and `make`: one crate per type, verified in parallel (`JOBS=N`). The Makefile re-verifies only what changed |
| `build.sh PROTO...` | The same crates compiled without verification, only those of the protocol's PDU types, and a driver (`driver/`, `mkmain.py` writes it) that decodes, encodes, prints JER, draws random values and times. `OPT=3` builds the timed ones |
| `check.sh PROTO [N]` | `tools/xcheck.py` with the driver: N random values of each PDU type, and each captured message of the protocol in `corpus/`, through ours, asn1c and pycrate. `XCHECK_ASN1C_RANGE8=1` builds asn1c with its 8-bit INTEGER misalignment fixed (`tests/ioc/range8.vec`), so that what that bug hides shows; `XCHECK_DUMP=FILE` writes every failure whole |
| `bench/run.sh [PROTO...]` | Ours (opt-level 3) and asn1c (-O2 and -O3, the C its compiler makes from the same schema, with the options the stacks build it with) decoding and encoding the captured messages whole, on one core |
| `corpus/` | The captured messages, by protocol (`index.txt` says what each set is, and which `check.sh` and `bench/run.sh` use) |
| `capture/` | The scripts that captured them, from Open5GS with UERANSIM and from OpenAirInterface's CI set-ups, with FlexRIC; see its README |

`check.sh` passes asn1c the options the stacks that use a protocol build it
with (`lib.sh`): `-findirect-choice -fno-include-deps` for XnAP, NRPPa and
O-RAN's, without which asn1c's C for XnAP and NRPPa does not compile.
pycrate 0.7.11 cannot compile F1AP V19.4.0 or NRPPa V19.3.0, and asn1c's C
for S1AP V19.2.0 does not compile: those are checked against the other.

What `check.sh` reports as failures on random values are the references'
deviations from X.691 in OVERVIEW.md §3 (asn1c's 8-bit INTEGERs, its 64-bit
counters, its reading of UTF8String's SIZE and of unknown IEs; the REAL and
zero-length padding deviations of all; pycrate's 16K open types and
recursion), and on captured messages there are none.
