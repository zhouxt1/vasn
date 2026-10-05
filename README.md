# vasn: verified ASN.1 codecs in Rust

## What it is

vasn (verified ASN.1) generates ASN.1 codecs whose correctness is proved in
[Verus](https://github.com/verus-lang/verus), for unaligned PER (ITU-T
X.691), the encoding 5G and LTE RRC and ETSI ITS use. `vasnc` compiles an
ASN.1 schema into Rust encoders and decoders, each generated type with its
proof. `vasn` is the verified runtime the generated code builds on, over
`vbits`, a verified bit layer.

**Faster than the open-source alternatives, and proved correct.** On real 5G
traffic (every channel message of
[5G Shield](bench/decode/README.md#citation)'s over-the-air NR RRC
captures), vasn decodes 1.7 to 3.7 times faster than asn1c and 4.7 to 6.8
times faster than rasn, and encodes 2.6 to 9.6 times faster than asn1c and
31 to 206 times faster than rasn, on every channel (OVERVIEW.md §3). And it
is verified:

* **Correct by proof.** Each decoder accepts exactly the encodings X.691
  allows, and returns the value they encode; each encoder writes exactly
  that encoding. Verus checks the proof for every generated type, all 6,919
  of NR RRC Rel-17 included.
* **Free of memory bugs.** The codecs and their runtime are safe Rust, with
  no `unsafe`, and are proved never to panic (no out-of-bounds index, no
  arithmetic overflow) and always to terminate. A decoder is proved so on
  any input at all, malformed and hostile messages included. The only
  trusted code underneath is a few SSE2 intrinsics, each checked against
  the CPU (OVERVIEW.md §1).

It is a rewrite of [VUPER](https://github.com/SyNSec-den/VUPER) (CCS '26),
whose verified codec is written in Rocq and extracted to OCaml. Here the
proofs are about the Rust that ships.

**More verified formats are coming.** vasn is the ASN.1 member of a family
of verified binary-format codecs built on the same bit layer; the others
will be published in
[verified_binary_formats](https://github.com/zhouxt1/verified_binary_formats).

**[OVERVIEW.md](OVERVIEW.md)** lists what is proved and what is trusted, the
ASN.1 features that are supported, and the compatibility and speed results.

## Build and run

Stable Rust (1.94 or later) is all you need to build, test and run the code:

```bash
cargo build --release
cargo test --release
cargo run --release -p vasn-examples --bin its     # encode, decode, round-trip ETSI ITS messages
```

The examples are `demo`, `optional`, `lists`, `frag`, `choice`, `enum_ext`,
`ext` and `its`, one for each schema in `examples/asn1/`.

## Verify the proofs

Checking the proofs needs Verus. `tools/get-verus.sh` fetches the pinned
release (about 1.6 GB unpacked), which includes `cargo verus`:

```bash
tools/get-verus.sh
export PATH=$PWD/tools/verus-x86-linux:$PATH
cargo verus verify --workspace --release
```

This verifies `vbits` (145 obligations), `vsimd` (171), `vasn` (345) and every
example codec, ETSI ITS included (2410), with 0 errors, in a few minutes.
Plain `cargo build` compiles the same code with the proofs erased.

## Use it on your own schema

```bash
cargo install --path vasnc       # or: cargo run --release -p vasnc -- ...
vasnc my-schema.asn1 src/my_schema.rs
```

The generated module depends on `vasn` and Verus's `vstd`. The versions
must match the Verus release the proofs were checked with, as pinned in this
repository's `Cargo.toml`:

```toml
[dependencies]
vasn = { git = "https://github.com/zhouxt1/vasn" }
vstd = "=0.0.0-2026-09-20-0158"
verus_builtin = "=0.0.0-2026-09-16-0054"
verus_builtin_macros = "=0.0.0-2026-09-20-0158"

[package.metadata.verus]
verify = true
```

```rust
mod my_schema;
use my_schema::*;
use vasn::uper::cursor::{BitReader, BitWriter};

let mut r = BitReader::new(&bytes);
match MyMessage_decode(&mut r) {
    Some((msg, _flag)) => { /* msg: MyMessage */ }
    None => eprintln!("rejected: {}", r.error()),  // e.g. "message.c1.rrcReconfiguration.measConfig: SIZE (1..64) length at bit 211"
}

let mut w = BitWriter::with_capacity(1024);
assert!(MyMessage_encode(&mut w, &msg));
let out = &w.buf[..(w.pos + 7) / 8];
```

Every type also gets `T_jer`, which prints the value as JER (X.697), and
`T_arb`, which generates a random valid value. `cargo verus verify` in your
crate re-checks the proofs for your schema.

`vasnc` options:

| | |
| --- | --- |
| `vasnc a.asn1 b.asn1 ... out.rs` | every module of every input, in one namespace, with IMPORTS checked |
| `--containing decode` | decode `OCTET STRING (CONTAINING T)` as the `T`. The default, `octets`, keeps the octets, as asn1c does |
| `--crate-dir DIR` | one crate per type, plus a Makefile that verifies them in parallel and incrementally (`make -j$(nproc)`). This is how all of NR RRC (6919 types) is verified. Set `ROOT=` to a checkout of this repository so the Makefile can build `vasn` |
| `--output-dir DIR` | one module per type, in one crate |
| `--stats` | what the schema uses, and what would be skipped |

A construct `vasnc` does not support is reported by name, with the reason,
and the type is skipped rather than approximated.

## Repository layout

| | |
| --- | --- |
| `vbits/` | The verified bit layer every codec shares: the bit views of byte buffers and the primitive bit reads and writes, with no encoding rules. `vasn` re-exports it as `vasn::bits` |
| `vasn/` | The verified runtime, built on `vbits`. `src/uper/` holds unaligned PER: the bit reader and writer (`cursor.rs`), the format definition and its combinators (`format.rs`), and one proved format for each X.691 building block: integers (`intx.rs`), length determinants (`lendet.rs`), fragmentation (`frag.rs`, `fraglist.rs`), open types and the extensible SEQUENCE (`seqext.rs`). `src/utf8.rs`, `time.rs`, `oid.rs` and `real.rs` are the proved checks of UTF-8, of the time types' DER forms, of OBJECT IDENTIFIER contents and of REAL's CER/DER form; `jer.rs` and `arb.rs` are the unverified JER printer and value generator |
| `vasnc/` | The compiler: lexer, parser, constraint resolution (`constraints.rs`), normalization, and the code and proof generator (`emit.rs`). Not itself verified: see OVERVIEW.md |
| `examples/` | `asn1/` holds seven small schemas, one per feature, and ETSI ITS (CAM, DENM and ITS-Container). `src/` holds the codecs `vasnc` generates from them, which are checked in, and `src/bin/` holds a driver for each that checks encodings by hand against X.691. `cargo test` fails if a checked-in codec is out of date |
| `tests/x691/` | 17 test modules with encodings derived by hand from X.691, and 6 more checked with random values (OBJECT IDENTIFIER, REAL, the strings beyond ISO 646, the time types), run through ours, pycrate, asn1c and rasn. Each deviation from X.691 found in them is recorded in its README. `tests/protocols/its.vec` holds the same check for ETSI ITS, and `tests/examples/` the references' deviations on two of the examples |
| `tools/` | `get-verus.sh` and `get-asn1c.sh` fetch the pinned Verus release and build asn1c. `xcheck.py` cross-checks one schema against pycrate, asn1c and rasn. `frag_pycrate.py` compares the fragmentation example with pycrate |
| `vsimd/` | 128-bit SIMD for Verus: SSE2 intrinsics with lane-level contracts, each checked against the CPU through a proved model. `vasn` copies octets that are not on an octet boundary with it. See its README |
| `bench/decode/` | Decoding and encoding speed on 5G Shield's over-the-air NR RRC captures, against asn1c, rasn and VUPER. See its README |
| `docs/spec/` | `get.sh` downloads ITU-T X.680, X.690, X.691 and X.697 (02/2021): the editions every clause number in the code refers to |

## Cross-checking against pycrate, asn1c and rasn

This needs `verus` on `PATH`, pycrate 0.7.11 (`pip install pycrate`), asn1c
(`tools/get-asn1c.sh`) and rasn-compiler 0.16.0 (`bench/decode/build.sh`
installs it; rasn 0.28.14 itself comes from cargo). `--no-rasn` leaves rasn out:

```bash
tests/x691/run.sh                    # all 23 modules: vectors, 40 random values each, verified
tools/xcheck.py examples/asn1/its.asn1 --vectors tests/protocols/its.vec -n 50
tools/xcheck.py examples/asn1/frag.asn1 --vectors tests/examples/frag.vec -n 40   # likewise ext
```

## License

MIT, see [LICENSE](LICENSE). `examples/asn1/its.asn1` is ETSI's ITS ASN.1
(TS 102 894-2, EN 302 637-2 and EN 302 637-3).
