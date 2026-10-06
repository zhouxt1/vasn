# vasn: what is proved, what is supported, how it performs

1. [What is proved, and what is trusted](#1-what-is-proved-and-what-is-trusted)
2. [ASN.1 features supported](#2-asn1-features-supported)
3. [Compatibility and performance](#3-compatibility-and-performance)

Clause numbers refer to ITU-T X.691 (02/2021), PER, unless marked X.680 (the
notation), X.681 to X.683 (information objects, constraints, parameterization),
X.690 (BER) or X.697 (JER). `docs/spec/get.sh` downloads them.

## How it works

```
schema.asn1 ──vasnc──▶ schema.rs ──Verus──▶ checked: code matches spec, spec is a format
                          │
                          ├─ Rust types, one per ASN.1 type
                          ├─ spec functions: wf, enc, dec (the format)
                          ├─ proofs that the format is correct
                          └─ exec decode/encode, proved against the spec
                                  │
                                  └─ built on vasn: runtime + combinators, proved once
```

`vasnc` generates specialized code for every ASN.1 type. No format is
interpreted at run time, and there are no closures, trait objects or indirect
calls. The format of a type is a composition of `vasn`'s proved
combinators (`pair`, `dep`, `map`, `restrict`, `opt`, `list`, the extensible
SEQUENCE) over its proved terminal formats (integers, lengths, strings, open
types, fragmentation). Each generated proof is a chain of those lemmas, one
function per nesting level, so verification cost grows linearly with the
schema.

`vasnc --aper` writes the ALIGNED variant against `vasn::aper`, whose
formats are UPER's indexed by the absolute bit position they start at, since
an aligned field is preceded by zero bits to the next octet (11.1.4). The
combinators pass the position on, so their proofs keep UPER's shape; only
`align` looks at `pos % 8`. Fields that X.691 encodes the same way in both
variants are UPER's formats, lifted with their proofs (`aper::format::lift`).

The 3GPP and O-RAN application protocols are written with information object
classes (X.681 to X.683): a class of IEs, object sets naming each IE's id,
criticality and type, and containers whose `value` is the type the `id`
selects (a table and component relation constraint). `vasnc` reads the
classes, objects and object sets and turns each container field into a
*keyed* SEQUENCE: its format is a dependent pair, the key's format followed
by the format of the type the key selects, proved once in `vasn` and
instantiated per container. An id that no object has, from a newer peer, is
kept as `Unknown(id, octets)` when the set is extensible, as an unknown CHOICE
alternative is. A recursive type (O-RAN's E2SM-RC holds RAN parameters that
are structures and lists of RAN parameters) is unrolled 8 levels deep, since
vasnc builds no recursive format: its format is the recursive type's
restricted to values nested at most 8 deep.

---

## 1. What is proved, and what is trusted

### Proved, for every type `T` that vasnc compiles

**The format.** `T_wf` (the value satisfies its constraints), `T_enc` (value
to bits) and `T_dec` (bits to value, bits consumed and a version flag) are
Verus spec functions, and `T_is_format` proves three properties:

| property | statement | meaning |
| --- | --- | --- |
| round trip | `wf(a) ⟹ dec(enc(a) ++ rest) = (a, len(enc(a)), SameVer)` | every valid value decodes back to itself, whatever follows it |
| non-malleability | `dec(b) = (a, k, SameVer) ⟹ b[..k] = enc(a)` | a decoder accepts only the one canonical encoding of each value: no overlong lengths, no explicitly encoded DEFAULTs, no all-zero extension bitmaps, no nonzero padding |
| well-formed output | `dec(b) = (a, k, _) ⟹ wf(a) ∧ k ≤ len(b)` | anything decoded, even from a newer peer, satisfies its constraints, and was read from bits actually there |

The flag is `DiffVer` when an extensible SEQUENCE came from a different
version of the schema: a newer sender's unknown additions were stepped over,
or an older sender's missing ones were filled in as absent. It is `SameVer`
otherwise. Non-malleability can only hold for `SameVer`, because the
skipped additions are not in the value, so re-encoding cannot reproduce
them. An unknown CHOICE alternative is different: it is kept in the value as
`Unknown(index, octets)`, re-encodes identically and is `SameVer`. An
unknown ENUMERATED extension value is rejected.

**The code.** The Rust that runs is proved against those spec functions:

* `T_decode(r)` returns `Some((v, f))` exactly when `T_dec` accepts the
  remaining bits as `v` with flag `f`, and has then advanced `r` by exactly
  the bits consumed. It returns `None` exactly when `T_dec` rejects them.
* `T_encode(w, v)` requires `wf(v)`. When it returns `true`, it has appended
  exactly `T_enc(v)` to what was written, and left the earlier bits
  unchanged. The writer's buffer does not grow, and `false` means it ran
  out. The proof makes no claim about that case beyond leaving the buffer's
  length unchanged.

**In APER** all of the above holds at every starting position. Each type
also gets `T_decode_complete` and `T_encode_complete`, proved against the
complete encoding of an outermost value (11.1.4, 11.1.5, `vasn/src/aper/complete.rs`):
the value's bits from bit 0, then zero bits to the octet, and an empty
encoding as one zero octet. A message with a non-zero padding bit, or one
octet more, is rejected. X.691 says the sender "shall" pad with zeros and
says nothing of a receiver given other bits; rejecting them is our choice,
since accepting them would give one value several encodings.

**Implicit in every Verus-checked function:** no panics (every index is in
bounds and no arithmetic overflows), termination (every loop carries a
checked `decreases`), and no `unsafe` code.

The standard's own worked examples of fragmentation, 144K + 1 units (11.9.3.8.1
NOTE 2) and an exact multiple of 16K (11.9.3.8.3 NOTE), are proved against the
definition in `vasn/src/uper/frag.rs`.

### Trusted: what the proofs do not cover

| | |
| --- | --- |
| **The spec follows X.691** | `vasn`'s formats are written by hand from X.691. That they match the standard is tested, not proved: by hand-derived vectors, and against pycrate, asn1c and VUPER (§3) |
| **`vasnc` is not verified** | The compiler chooses which format each ASN.1 type gets, and which type each IE id selects. Verus proves the generated code correct for the format it was given. If vasnc chose the wrong format, the result would be a verified codec for the wrong format. This happened once during development, when an ENUMERATED with `...` and no extension values was compiled as non-extensible. Differential testing found it, and it is the reason for the cross-checks in §3 |
| **Verus, Z3, rustc** | the verifier, its SMT solver and its standard library `vstd`, and the Rust compiler |
| **SSE2 intrinsics, on x86-64** | the reader's `read_octets` and the writer's `write_slice` copy octets that are not on an octet boundary sixteen at a time (`vasn/src/uper/simd.rs`), with `vsimd::x86`'s `loadu`, `set1_epi16`, `unpacklo_epi8`, `unpackhi_epi8`, `srl_epi16`, `and_si128`, `packus_epi16` and `to_bytes`. Each is `external_body`, trusted to compute its lane-level spec; `vsimd/tests/validate.rs` (in [verified_binary_formats](https://github.com/zhouxt1/verified_binary_formats)) checks each against the CPU through a proved model of the same spec. Everything built on them is proved. Off x86-64 none is used |
| **Four diagnostic functions** | `BitReader::fail`, `step` and `adopt` in `vasn/src/uper/err.rs`, and `note_bad_padding` in `vasn/src/aper/cursor.rs`, are `external_body`. They record why a decode failed, for `r.error()`, and are trusted to leave the buffer and position alone, as their contracts state |
| **Unverified by design** | the JER printers (`T_jer`, `vasn/src/jer.rs`), the random value generators (`T_arb`, `vasn/src/arb.rs`), the example drivers and the benchmarks |
| **The encoder's precondition** | `T_encode` requires a well-formed value, for example an INTEGER within its range. Verified callers must prove that. A plain Rust caller is trusted to meet it, since it is not checked at run time. Decoders have no such precondition and are safe on any input |

### What this closes relative to VUPER

VUPER assumes four things that are proved or removed here:

1. **In-place mutation.** VUPER models its buffer as persistent, but the
   extracted OCaml overwrites it. Here the buffer is a `&mut Vec<u8>`, and the
   borrow checker enforces linear use.
2. **Machine arithmetic.** VUPER caps bit fields at 48 bits by convention, so
   OCaml's 63-bit `int` cannot overflow. Here every operation is on `u64`,
   every bound is a proof obligation, and fields go up to 56 bits.
3. **Extraction.** VUPER trusts Rocq's extractor and the OCaml runtime.
   Verus checks the Rust that rustc compiles.
4. **Fragmentation.** VUPER stops at lengths of 16K and exempts larger ones
   from its injectivity theorem. Here lengths fragment (11.9.3.8), and the
   open-type theorem has no size condition.

---

## 2. ASN.1 features supported

Both variants, UNALIGNED and ALIGNED (`--aper`), except where marked. Each
row is built and verified, and checked against pycrate, asn1c and rasn
wherever they can parse the construct, with hand-derived X.691 vectors except
where marked (`tests/x691/`, `tests/aper/`, `tests/ioc/`, §3).

| construct | supported | X.691 |
| --- | --- | --- |
| BOOLEAN, NULL | yes | 12, 18 |
| INTEGER, constrained | ranges up to 56 bits, including `INTEGER (lb..ub, ...)`, and `INTEGER (0..18446744073709551615)` (the 3GPP usage counters) as a `u64`. In APER, a range of 256 in one aligned octet, up to 64K in two, and over 64K with its octet count first (the indefinite-length case) | 13, 11.5 |
| INTEGER, semi-constrained and unconstrained | up to `i64`, in the minimal number of octets (longer ones are rejected) | 13, 11.7, 11.8, 11.3.6, 11.4.6 |
| ENUMERATED | root, extensible, numbered items in value order, extension values. Extension indexes of 64 and more use the long form. In APER, up to 64K root values (an index of 256 or more is octet-aligned) | 14, 11.6, 11.5.7 |
| BIT STRING | fixed, constrained, extensible and unbounded SIZE, named bits in their shortest form | 16 |
| OCTET STRING | fixed, constrained, extensible and unbounded SIZE | 17 |
| `OCTET STRING (CONTAINING T)` | kept as octets (default), or decoded as `T` with `--containing decode`, which rejects octets that are not exactly one `T` | 11.1, X.682 11.3 |
| SEQUENCE | OPTIONAL and DEFAULT components, extension marker, extension additions, `[[ ]]` groups, root components after a second marker. A newer peer's unknown additions are skipped, with the flag `DiffVer` | 19 |
| SET | in canonical tag order. UPER only: asn1c has no APER for SET to check against | 21 |
| SEQUENCE OF, SET OF | any SIZE, including extensible and `ub` of 64K or more | 20, 22 |
| CHOICE | root and extension alternatives, canonical tag order. An unknown alternative from a newer peer is kept as `Unknown(index, octets)`. In APER, up to 64K root alternatives | 23 |
| character strings | IA5String, NumericString, PrintableString and VisibleString, with SIZE and permitted alphabets (FROM). UTF8String, checked as UTF-8 | 30.5, 30.6 |
| more character strings (UPER: random values only) | BMPString and UniversalString, with permitted alphabets as code-point ranges. GeneralString, GraphicString, TeletexString, VideotexString and ObjectDescriptor as their octets | 30.5, 30.6 |
| GeneralizedTime, UTCTime (UPER: random values only) | the VisibleString they are, restricted to DER's forms (`vasn/src/time.rs`, a proved check) | 10.6.5, X.690 11.7, 11.8 |
| OBJECT IDENTIFIER, RELATIVE-OID (UPER: random values only) | the BER contents octets, restricted to the canonical ones (`vasn/src/oid.rs`), so that octets and arcs are a bijection | 24, 25, X.690 8.19 |
| REAL (UPER: random values only) | the CER/DER contents octets, restricted to the one form (`vasn/src/real.rs`) | 15, X.690 8.5, 11.3 |
| open types | padded to octets, with an empty encoding written as one octet | 11.2, 11.1.3.1 |
| length determinants | every form: constrained, normally small, general, and fragmented at 16K octets, bits or components, with the canonical fragment count enforced | 11.9 |
| constraints | unions, intersections, EXCEPT, open range ends, contained subtypes, serial application, constraints on type references, all resolved to the effective PER-visible constraint | 10.3, X.680 |
| tagging | IMPLICIT, EXPLICIT and AUTOMATIC tags, EXTENSIBILITY IMPLIED | X.680 |
| modules | several modules and files in one namespace. IMPORTS are checked against what the modules define, and a name a module uses without defining or importing it is reported | X.680 13 |
| information object classes | CLASS with WITH SYNTAX, objects and object sets (extensible, unions), `CLASS.&field` with a table or component relation constraint (`({Set}{@id})`), parameterized types with object-set and value parameters: the 3GPP protocols' containers, as keyed SEQUENCEs (see How it works) | X.681, X.682, X.683 |
| recursive types | unrolled 8 levels deep: a value nested deeper is not decoded, a limit of ours as a buffer's size is, not X.691's | |

Every type also gets a JER printer (X.697), a random-value generator, and
decode diagnostics that name the failing component path and bit position.

### Not supported

`vasnc` reports each of these by name and skips the type:

| | |
| --- | --- |
| BER, DER, OER | PER only |
| INTEGER beyond `i64`, or a constrained range wider than 56 bits, but `(0..18446744073709551615)` | rejected |
| a recursive `CONTAINING` | kept as octets under `--containing decode`: the three in NR |
| an ENUMERATED or CHOICE of more than 64K root values, in APER | not built |
| `CONTAINING` with ENCODED BY, a SIZE, or on a BIT STRING | kept as octets, or rejected under `--containing decode` |

One known deviation from X.691: a mandatory extension addition that is absent
decodes with the flag `SameVer`. It should be `DiffVer`, since only an older
sender omits it. The message is still accepted, correctly. `vasnc --stats`
lists the affected components: one in NR (`RLF-TimersAndConstants`'
`[[ t311 ]]`), none in ETSI ITS.

---

## 3. Compatibility and performance

### Real schemas, compiled and verified

| schema | compiled | verified |
| --- | --- | --- |
| 3GPP NR RRC Rel-17 (`nr-rrc-17.3.0.asn1`, all six modules) | 6919 types, 0 skipped | 6726 crates, 96,330 obligations, 0 errors, 42 min at `make -j20` |
| ETSI ITS (ITS-Container, CAM, DENM) and the seven feature examples (`examples/`) | 0 skipped | 2410 obligations, 0 errors |
| `vasn` runtime, with `vbits` and `vsimd` (from verified_binary_formats) | | 907 obligations, 0 errors |
| NGAP (TS 38.413 V19.4.0), ALIGNED | 4514 types, 0 skipped | 4362 crates, 0 errors, 21 min at `make -j20` |
| F1AP (TS 38.473 V19.4.0) | 6867 types, 0 skipped | 6488 crates, 0 errors, 15 min |
| E1AP (TS 37.483 V19.4.0) | 2211 types, 0 skipped | 2123 crates, 0 errors, 10 min |
| XnAP (TS 38.423 V19.4.0) | 5229 types, 0 skipped | 5020 crates, 0 errors, 18 min |
| S1AP (TS 36.413 V19.2.0) | 2361 types, 0 skipped | 2247 crates, 0 errors, 10 min |
| X2AP (TS 36.423 V19.1.0) | 3193 types, 0 skipped | 3071 crates, 0 errors, 19 min |
| NRPPa (TS 38.455 V19.3.0) | 1795 types, 0 skipped | 1671 crates, 0 errors, 5 min |
| LPPa (TS 36.455 V19.0.0) | 409 types, 0 skipped | 374 crates, 0 errors, 2 min |
| O-RAN E2AP V03.01, and FlexRIC's E42AP | 599 and 632 types, 0 skipped | 556 and 588 crates, 0 errors, 2 min each |
| O-RAN E2SM-KPM V03.00 | 205 types, 0 skipped | 181 crates, 0 errors, 1 min |
| O-RAN E2SM-RC V1.03 (recursive, unrolled 8 deep) | 520 types, 0 skipped | 489 crates, 0 errors, 6 min |

`bench/decode/README.md` shows how to fetch the NR schema and verify it,
and `protocols/README.md` the twelve APER protocols.

### Against X.691, pycrate, asn1c and rasn

`tests/x691/` has 23 modules covering §2's features: 17 with encodings
derived by hand from X.691 and the clause they follow, and 6 checked with
random values only (marked in §2). `tests/x691/run.sh`
checks each vector against our decoder, pycrate 0.7.11, asn1c and rasn
0.28.14, checks that ours re-encodes it to the same bytes, and then draws
random values. Our encoder writes each one, and the references must decode
it to the same value (compared as JER) and re-encode it to the same bytes. ETSI ITS gets the
same random-value check (`tests/protocols/its.vec`). Every check of ours
passes.

The references deviate from X.691 in places, and each deviation is
recorded in `tests/x691/README.md`. Among them: asn1c swaps its canonical
CHOICE order maps, decodes the extension of `INTEGER (0..MAX, ...)` as
unsigned, and treats UTF8String's SIZE as PER-visible. pycrate uses textual
CHOICE order under any tagging, and misnumbers an unnumbered enumeration
addition. Both accept non-canonical encodings that ours rejects: an
all-absent group, a DEFAULT sent at its default, an overlong integer. rasn
drops contained subtypes, applies UTF8String's SIZE, and corrupts a
fragmented character string when it encodes one; asn1c encodes the time
types with 8 bits a character instead of VisibleString's 7.

The fragmentation example (`examples/asn1/frag.asn1`, 25 encodings from 1
bit to 800,032 bits) is byte-identical to pycrate's (`tools/frag_pycrate.py`).

### ALIGNED PER, against X.691, pycrate, asn1c and rasn

`tests/aper/run.sh` runs `tests/aper/`'s own modules (alignment, integers,
wide indexes, the strings beyond ISO 646, OBJECT IDENTIFIER, REAL, a recursive
type, each with hand-derived vectors), the X.691 modules and the examples in
APER, verified, and `tests/ioc/run.sh` and `tests/wide/run.sh` the 3GPP
protocols' information object classes and 64-bit counters,
against pycrate's `to_aper`, asn1c's `-oaper` and rasn 0.28's `rasn::aper`.
Every check of ours passes. The random values include the boundaries where
an ALIGNED encoding changes form (a whole number's 255, 256 and 64K, a
length's 127/128, 16K, 32K, 48K and 64K). Where a reference departs from
X.691 it is recorded in the `.vec` files of `tests/aper/`, `tests/ioc/` and
`tests/wide/`, and X.691 is followed:

| | pycrate | asn1c | rasn |
| --- | --- | --- | --- |
| padding after a zero length of a BIT, OCTET or character string (11.9.3.3 NOTE 2 says none) | pads | pads | pads |
| a character string under 16 bits (`NumericString (SIZE (0..3))`, 30.5.6, 30.5.7 align only from 16) | aligns | aligns | aligns |
| an extension addition's open type | writes an extra `00` first, and cannot read its own output | | |
| a semi-constrained INTEGER's octets (11.7.4: the fewest, non-negative) | | 2's complement, a leading `00` | |
| an alphabet of 2 characters (30.5.2: 1 bit) | | 2 bits | |
| a constrained INTEGER of 129 to 255 values (11.5.7.1: an 8-bit field, not aligned; `tests/ioc/range8.vec`) | | aligns it when it reads it: writes it right, reads its own bytes wrong. In F1AP, XnAP, NRPPa and LPPa (positioning, IAB), and `n6Jitter` in NGAP, E1AP, XnAP and F1AP | |
| `INTEGER (0..18446744073709551615)` (`tests/wide/u64.vec`) | | UPER: stops on an assertion; APER: rejects every value | its JER stops at 2^63 - 1 |
| an extension value of `INTEGER (1..4294967295, ...)` (13.1, 11.8: 2's complement) | | reads it as unsigned | |
| a UTF8String's SIZE (not PER-visible, 10.3.7, 30.6; `tests/ioc/utf8.vec`): NGAP's node and AMF names | | applies it: misreads a peer that follows X.691 | applies it |
| an open type of 16K octets or more followed by another IE (`tests/ioc/bigie.vec`) | cannot read it back, even its own | | |
| a recursive type (`tests/aper/recursive.vec`) | fails on a node whose first child has a child | | misreads a child |
| an IE whose id the set has no object for (a newer peer's) | | decodes it as `<absent>` and drops it | |
| an ENUMERATED of 256 or more root values (11.5.7.3: two octets, aligned) | | aligns, then reads 9 bits | 9 bits, not aligned |
| a CHOICE of 256 or more | | as for ENUMERATED | an `INTEGER (0..256)` alternative after the index it encodes wrongly |
| octet alignment of fixed strings over 16 bits, a length of range 257 to 64K, a SEQUENCE OF's elements (16.10, 17.7, 11.5.7.3, 20.6) | | | wrong in both directions: `SIZE (1..65535)` containers written unaligned (`alignment.vec`) |
| a mandatory extension addition absent (an older sender, 19.7) | | | rejects the message |
| BMPString, TeletexString, UniversalString, the time types | cannot print the strings that are not known-multiplier; fragments BMP in octets, not characters | a permitted alphabet on BMP or Universal mapped wrongly | `todo!()`, BER, misread |
| a fragmented character string (16K or more, not a multiple) | | | its encoder repeats the first fragment |
| OBJECT IDENTIFIER | accepts `80` leading a subidentifier | arcs of 32 bits: rejects wider | arcs of 32 bits: *truncates* wider; RELATIVE-OID as OID; an element OID unaligned |
| REAL | decodes a binary value to twice it | a C double: base 10 lost (15.1), N not minimal | no REAL in PER |
| time types in other than DER's form | accepts, rewrites | accepts | |
| a fragmented SEQUENCE OF or SET OF | its APER encoder crashes (`encode_pas`) | | |
| a fragmented BIT STRING (`tests/aper/frag.vec`) | reads 65535 bits as 32766 | | |
| JER of a list element whose components are all absent | | its printer stops ("Cannot convert") | |
| SET | | no APER at all (`SET_decode_aper` is null); left out | |

`widechoice.asn1` (a CHOICE of 256 and more alternatives) is checked but not
verified: its proofs exceed the solver.

### The 3GPP and O-RAN protocols, against asn1c and pycrate

`protocols/` builds, verifies and checks the twelve protocols of the table
above from their specifications (`protocols/get-asn1.sh` extracts the 3GPP
ASN.1 from the specification documents; O-RAN's comes from FlexRIC, as O-RAN's
own files are behind a licence form). Each schema compiles whole and
verifies, every crate. Ours is checked against asn1c and pycrate
(`protocols/check.sh`) on random values of every PDU type, on traffic
captured from open-source stacks and on mutants of that traffic:

| traffic (`protocols/corpus/`) | messages |
| --- | --- |
| NGAP, Open5GS 2.7.2 with UERANSIM 3.2.6: registration, PDU sessions, UE context release, service request, deregistration | 3944 |
| NGAP, F1AP, E1AP from OpenAirInterface's split gNB (CU-CP, CU-UPs, DUs) and 5G core, over rfsim, and N2 handovers between two such gNBs | 6360 |
| NGAP with NRPPa, OAI's gNB and its 5G core's LMF; XnAP, Xn Setup among three OAI gNBs | 21 |
| S1AP, OAI's eNB and LTE UE with Magma's MME | 33 |
| E2AP and E42AP from FlexRIC's nearRT-RIC and four xApps over OAI's E2 agent (266,031 and 266,037 messages; samples), and the E2SM-KPM and E2SM-RC messages they carry | 9314 checked |

On every captured message ours and the references agree, each where it
compiles the schema (pycrate cannot compile F1AP V19.4.0 or NRPPa V19.3.0,
nor asn1c's C for S1AP V19.2.0 compile): the same value, and ours re-encodes
it to the same octets. Every disagreement on random values, and on mutants of
the traffic (`protocols/capture/mutate.py`, 27,851 of them), is one of the
references' deviations above, or ours
rejecting what X.691 does not make an encoding (a non-zero padding bit,
octets after a complete encoding, an open type's content that is not exactly
one encoding of its type, a length or integer not in its fewest octets, a
character outside a PER-visible alphabet).

### Against VUPER, on 5G Shield's over-the-air captures

The [5G Shield dataset](https://pennstateoffice365-my.sharepoint.com/:f:/g/personal/tvw5452_psu_edu/IgA-17pGa6QkRrVIFx_lzIedAQ-vOQTiSQM09dyPCZ-4TTY?e=sNfXkj)'s
`raw_data/` holds QXDM logs of commercial and testbed 5G traffic, each RRC
message with its UPER bytes. The dataset is from
Wu, Ishtiaq, Yang, Dong, Tu, Song, Tanvir, Toufikuzzaman, Mehnaz and
Hussain, *Guardians of the Air: In-Device Detection of 5G Control-Plane
Threats*, IEEE S&P 2026, pp. 2759–2778. `bench/decode/shield.py` sorts them by channel
and keeps each distinct message once:

| channel | messages | distinct |
| --- | --- | --- |
| PCCH | 580,828 | 355,025 |
| UL-DCCH | 488,028 | 156,284 |
| DL-DCCH | 406,315 | 131,090 |
| BCCH-BCH | 155,062 | 9,897 |
| BCCH-DL-SCH | 69,203 | 5,273 |
| UL-CCCH | 64,774 | 9,496 |
| DL-CCCH | 59,237 | 53,722 |

VUPER ships decoders for DL-DCCH and UL-DCCH. On all 287,374 distinct
messages of those two, the two decoders accept and reject exactly the same
messages, and every message both accept decodes to the same value.

Ours rejects some messages that asn1c and rasn accept. Each rejection is a
non-canonical encoding, named by `bench_ours why`:

* **DL-DCCH, 3,509 (VUPER rejects them too):** a DEFAULT value encoded
  explicitly, which 19.5 does not allow. This is
  `measObjectNR.offsetMO.rsrpOffsetSSB` in 3,464 messages and
  `quantityConfigEUTRA.filterCoefficientRSRP` in 45.
* **BCCH-DL-SCH, 355:** 325 explicit DEFAULTs, 29 SIB1s with the extension
  bit set and an all-zero bitmap (19.8), and one unreadable unknown
  addition. asn1c rejects 364 of the same channel, rasn 1.

Accepting any of them would give one value two encodings.

### Speed, UNALIGNED: NR RRC

Speed, in ns per message, on the messages every decoder compared accepts
(`bench/decode/common.sh`). Each harness loads every message first, then
times whole rounds, 20 after a warm-up: decode-and-free, or encoding the
values the messages decode to. The tables give the fastest round, on one
core pinned with `taskset`, on an AMD Ryzen 9 9950X3D with the `performance`
governor. `bench/decode/results_shield.txt` is the run behind them, and
`bench/decode/README.md` shows how to reproduce it.

**Decoding, UNALIGNED.**

| channel | messages | **ours** | asn1c | rasn | VUPER | asn1c ÷ ours | rasn ÷ ours |
| --- | --- | --- | --- | --- | --- | --- | --- |
| DL-DCCH | 127,581 | **689** | 2,578 | 4,196 | 32,951 | 3.7 | 6.1 |
| UL-DCCH | 156,284 | **220** | 663 | 1,040 | 3,680 | 3.0 | 4.7 |
| PCCH | 355,025 | **77.2** | 163 | 520 | — | 2.1 | 6.7 |
| BCCH-BCH | 9,897 | **51.3** | 159 | 258 | — | 3.1 | 5.0 |
| BCCH-DL-SCH | 4,871 | **1,491** | 5,585 | 7,151 | — | 3.7 | 4.8 |
| UL-CCCH | 9,496 | **64.0** | 108 | 390 | — | 1.7 | 6.1 |
| DL-CCCH | 53,722 | **167** | 537 | 1,129 | — | 3.2 | 6.8 |

**Encoding**, the same messages: ours into one 4096-byte writer
reused for every message, asn1c into one 4096-byte buffer
(`uper_encode_to_buffer`), rasn into the `Vec` its `encode` returns, an
allocation the other two do not make.

| channel | messages | **ours** | asn1c | rasn | asn1c ÷ ours | rasn ÷ ours |
| --- | --- | --- | --- | --- | --- | --- |
| DL-DCCH | 127,581 | **458** | 1,704 | 27,751 | 3.7 | 61 |
| UL-DCCH | 156,284 | **134** | 354 | 4,108 | 2.6 | 31 |
| PCCH | 355,025 | **28.2** | 82.1 | 1,636 | 2.9 | 58 |
| BCCH-BCH | 9,897 | **13.3** | 127 | 659 | 9.6 | 50 |
| BCCH-DL-SCH | 4,871 | **574** | 3,408 | 24,204 | 5.9 | 42 |
| UL-CCCH | 9,496 | **15.4** | 71.6 | 964 | 4.6 | 63 |
| DL-CCCH | 53,722 | **62.7** | 445 | 12,938 | 7.1 | 206 |

The decoders and encoders compared, all built from the same
`nr-rrc-17.3.0.asn1`:

| | built as |
| --- | --- |
| ours | `vasnc --crate-dir`, one crate per type, `opt-level=3`, every exec function `#[inline]` |
| asn1c | the C that VUPER's harness ships, gcc `-O2` |
| rasn | rasn 0.28.14, with bindings from rasn-compiler 0.16.0, patched to compile (`bench/decode/rasn/patch.py`) |
| VUPER | its extracted OCaml, unchanged, built as VUPER builds its timing test (OCaml 4.14.0). It ships decoders for DL-DCCH and UL-DCCH only |

**Noise.** Rounds and repeat runs agree within 2%, but code layout alone
moves a channel by up to 6%: removing an unused function from the harness
once took DL-DCCH from 1,280 to 1,362 ns, with the decoder crates
unchanged.

**Where the time goes.** asn1c interprets per-type tables through a
function pointer per member, and allocates every OPTIONAL member,
constructed value and list element. Ours is a straight-line decoder and
encoder per type that keeps SEQUENCEs, CHOICEs and `Option`s by value and
allocates only for lists and strings, each `Vec` sized from its decoded
count. Beyond that, what made ours faster, all proved:

* a field read is one unaligned 64-bit load, a shift and a mask (`movbe`,
  `shrx`, `bzhi`), the same code as a hand-written unverified reader, and
  the slow path near the buffer's end is out of line;
* a SEQUENCE's preamble (extension bit and presence bitmap) is read and
  written as one word;
* an OCTET STRING off an octet boundary is copied seven octets per 64-bit
  read, or sixteen at a time in SSE2, and BIT STRINGs and OCTET STRINGs are
  read and written in bulk rather than an element at a time;
* a field write is one byte load and one 8-byte store; open types' scratch
  buffers are reused, and an aligned octet run is one `copy_from_slice`.

### Speed, ALIGNED: the 3GPP and O-RAN protocols

The captured messages of `protocols/corpus/` (index.txt's bench sets),
decoded whole and encoded whole (the complete encoding, 11.1.4), ns per
message unless marked, the fastest of 20 rounds after a warm-up, on one core
(`protocols/bench/run.sh`), on the same machine. Ours is built at opt-level 3; asn1c is the C its
compiler (mouse07410, `tools/get-asn1c.sh`) makes from the same schema, with
the options the stacks build it with, at gcc -O2 and -O3.

| | messages | decode: **ours** | asn1c -O2 | asn1c -O3 | asn1c -O3 ÷ ours | encode: **ours** | asn1c -O2 | asn1c -O3 | asn1c -O3 ÷ ours |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| NGAP | 3992 (Open5GS, OAI) | **282** | 928 | 846 | 3.0 | **193** | 660 | 598 | 3.1 |
| F1AP | 3112 (OAI) | **156** | 713 | 654 | 4.2 | **173** | 534 | 488 | 2.8 |
| E1AP | 24 (OAI) | **380** | 1,089 | 1,018 | 2.7 | **246** | 741 | 698 | 2.8 |
| E2AP | 20000 (FlexRIC with OAI) | **215** | 1,377 | 1,111 | 5.2 | **252** | 1,201 | 997 | 4.0 |
| E2SM-KPM indication messages | 318, up to 25 KB | **107 µs** | 279 µs | 292 µs | 2.7 | **53 µs** | 154 µs | 157 µs | 3.0 |
| E2SM-RC indication messages | 1119 | **89.1** | 183 | 182 | 2.0 | **50.7** | 118 | 111 | 2.2 |

asn1c's C for S1AP V19.2.0 does not compile; ours decodes OAI's S1AP in
274 ns and encodes it in 243 ns.

**Not measured:** speed on malformed input.
