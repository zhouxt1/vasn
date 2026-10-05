# vsimd: 128-bit SIMD for Verus

`vsimd` lets Verus-verified code use SSE2 intrinsics, with proofs about
what each lane holds. `vasn` uses it to copy octets that are not on an
octet boundary, sixteen at a time; it was built for a verified WebP
decoder's loop filter, inverse DCT and intra prediction, which are not part
of this repository.

## How it is built

| module | what it is | trusted? |
|---|---|---|
| `spec.rs` | what each intrinsic computes, as a function of the vector's 16 bytes (`Seq<u8>`), built from a function of one lane | the definition |
| `model.rs` | each intrinsic implemented on `[u8; 16]`, proved to compute its spec function | no |
| `x86.rs` | the SSE2 intrinsics, each `external_body` with the contract `v8(r) == spec::f(v8(a), v8(b))` | **yes: the trusted base** |
| `mem.rs` | scalar accesses without bounds checks (`get`, `get_ref`, `aget`, `aset`, `vset`, `copy_within`), each `external_body`, in bounds by its precondition | **yes** |
| `idiom.rs` | sequences of intrinsics with a lane-level theorem: absolute difference, a threshold mask, halving bytes by a 16-bit shift, a signed byte shift by unpack/shift/pack, 8 x 8 and 16 x 8 byte transposes | no |

A vector is Rust's `__m128i`, an opaque type to Verus. Its view is
`v8(v)`, 16 bytes read by the uninterpreted `byte(v, k)`, byte 0 lowest
(first in memory). A contract states the result's bytes, as the spec
function's, and `lemma_byte` connects `byte(v, k)` to `v8(v)[k]` so that
lane facts flow through chains of operations. Loads and stores are
unchecked pointer accesses: they are in bounds by their preconditions
(`i + 16 <= s.len()` and the like), which Verus checks at every verified
call site, so their memory safety is part of what the proofs give; a caller
that is not verified must meet them itself. (Bounds-checked slices cost
about 6% of the WebP decoder's time.)

`spec.rs` also has lemmas for reasoning in 16- and 32-bit lanes
(`w16`/`sw16`, `w32`/`sw32`: a lane's value unsigned and signed): what one
lane of an add, subtract, high multiply, shift, pack or unpack holds, mod
2^16 or 2^32.

## Why the trusted base can be trusted

Every contract in `x86.rs` is checked against the CPU, through the proved
model of the same contract (`tests/validate.rs`), so what is tested is
exactly what the proofs assume:

* two-operand byte operations: every pair of byte values, in every lane;
* one-operand 16-bit operations (shifts, packs): every 16-bit value in
  every lane;
* two-operand 16-bit operations (`add_epi16`, `mulhi_epi16`): every pair
  of 16-bit values (`--ignored`, 30 s);
* 32-bit shifts: every 32-bit value (`--ignored`, about 2 min);
* everything: random vectors, which also covers moving bytes across lanes,
  and values near every power of two for the 32-bit operations;
* the byte order against `_mm_set_epi8`, which names lanes independently
  of this crate.

The harness catches a wrong contract: bound to `_mm_mulhi_epi16(a, a)` in
place of `(a, b)` (the kind of wrong multiplication axiom found in libcrux,
Kobeissi, ePrint 2026/192) or to `_mm_subs_epi8` in place of
`_mm_subs_epu8`, the tests fail.

```
tools/simd/vv                                   # verify
cargo test --release -p vsimd                   # validate (1 s)
cargo test --release -p vsimd -- --ignored      # exhaustive 16- and 32-bit (2 min)
```

## What is not covered

Only SSE2 (x86-64's baseline); the models in `model.rs` are a portable
fallback but nothing selects them yet. The trusted base is tested, not
proved: linking it to a formal ISA semantics (Intel's pseudocode, or Arm's
ASL for a NEON backend) would be the next step.
