# Decoding speed on 5G Shield's captures

These scripts reproduce OVERVIEW.md §3: our NR RRC decoders against asn1c,
rasn and VUPER, on every distinct message of the 5G Shield dataset's
over-the-air captures, for the seven channel messages.

| | |
| --- | --- |
| `build.sh` | Builds the four decoders from `nr-rrc-17.3.0.asn1`. It first fetches VUPER at the commit these results were measured with into `VUPER/`: the schema, the asn1c-generated C and VUPER's OCaml all come from there, and VUPER carries no license, so none of it is copied into this repository |
| `shield.py RAW_DATA_DIR` | Sorts the dataset's `raw_data/` logs by channel, keeping each distinct message once, into `corpus/shield/<TYPE>/` |
| `common.sh TYPE` | The timed set for one channel: the messages ours, asn1c and rasn all decode, in `corpus/shield/<TYPE>-common/`, with the rejects listed next to it |
| `run.sh DIR CORE TYPE` | Times each decoder on one directory, pinned to one core |
| `ours/`, `asn1c/`, `rasn/`, `vuper/` | One timing harness per decoder. Each loads every message first, then times whole rounds of decode-and-free |
| `results_shield.txt` | The recorded run behind the table in OVERVIEW.md |

## Requirements

* `verus` on `PATH` (`tools/get-verus.sh`). The NR crates link against its
  `vstd`, and `ours/` must build with its Rust toolchain (1.98.1, pinned in
  `ours/rust-toolchain.toml`).
* gcc, for asn1c.
* For VUPER: opam with an OCaml 4.14.0 switch that has dune, yojson,
  ppx_import, base and mtime (`vuper/build.sh`). `SKIP=vuper ./build.sh`
  leaves it out.
* The [5G Shield dataset](https://pennstateoffice365-my.sharepoint.com/:f:/g/personal/tvw5452_psu_edu/IgA-17pGa6QkRrVIFx_lzIedAQ-vOQTiSQM09dyPCZ-4TTY?e=sNfXkj) (a OneDrive folder; download it as a zip),
  unpacked, for its `dataset/raw_data/`.

## Steps

```bash
cd bench/decode
./build.sh                               # about 10 min on 16 cores
./shield.py /path/to/dataset/raw_data    # writes corpus/shield/ and its summary.txt
for t in DL-DCCH-Message UL-DCCH-Message PCCH-Message BCCH-BCH-Message \
         BCCH-DL-SCH-Message UL-CCCH-Message DL-CCCH-Message; do
    ./common.sh $t
    ./run.sh corpus/shield/${t%-Message}-common 4 $t
done
```

`bench_ours why DIR TYPE` names, for each message ours rejects, the
component and bit where decoding stopped. That is how the rejections in
OVERVIEW.md §3 were classified.

`build.sh` compiles the NR crates with `--no-verify`. To verify all 6726 of
them (about 20 min at `-j28`), generate a separate copy, since the unverified
build's `.vir` files would otherwise count as done:

```bash
../../target/release/vuperc VUPER/diff_test/ASN_Coding/asnfuzzgen/ASN1/nr-rrc-17.3.0.asn1 --crate-dir nr-verify
make -C nr-verify -j$(nproc) ROOT=$(cd ../.. && pwd)
```

## Citation

The 5G Shield dataset is from:

Wu, Ishtiaq, Yang, Dong, Tu, Song, Tanvir, Toufikuzzaman, Mehnaz and
Hussain, *Guardians of the Air: In-Device Detection of 5G Control-Plane
Threats*, IEEE S&P 2026, pp. 2759–2778.

```bibtex
@inproceedings{5gshield,
  title={Guardians of the Air: In-Device Detection of 5G Control-Plane Threats},
  author={Wu, Tianwei and Ishtiaq, Abdullah Al and Yang, Tianchang and Dong, Yilu and Tu, kai and Song, Zeyu and Tanvir, Ridwanul Hasan and Toufikuzzaman, Md and Mehnaz, Shagufta and Hussain, Syed Rafiul},
  booktitle={2026 IEEE Symposium on Security and Privacy (SP)},
  pages={2759--2778},
  year={2026},
  organization={IEEE}
}
```
