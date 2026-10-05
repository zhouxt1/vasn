//! What each operation computes, on the 16 bytes of a vector (byte 0 is the
//! lowest, the first in memory). One spec function per intrinsic, over
//! `Seq<u8>`, built from a function of one lane.
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------ byte values

/// A byte read as a signed 8-bit value.
pub open spec fn sb(b: u8) -> int { if b < 128 { b as int } else { b as int - 256 } }

/// The byte holding `x`, for -128 <= x <= 255 (two's complement below 0).
pub open spec fn ub(x: int) -> u8 { (if x < 0 { x + 256 } else { x }) as u8 }

pub open spec fn clamp(x: int, lo: int, hi: int) -> int { if x < lo { lo } else if x > hi { hi } else { x } }

// ------------------------------------------------------- one 8-bit lane

pub open spec fn subs_u8(a: u8, b: u8) -> u8 { if a >= b { (a - b) as u8 } else { 0 } }
pub open spec fn adds_u8(a: u8, b: u8) -> u8 { if a as int + b as int > 255 { 255 } else { (a + b) as u8 } }
pub open spec fn max_u8(a: u8, b: u8) -> u8 { if a >= b { a } else { b } }
pub open spec fn eq_u8(a: u8, b: u8) -> u8 { if a == b { 255 } else { 0 } }
pub open spec fn and_u8(a: u8, b: u8) -> u8 { a & b }
pub open spec fn or_u8(a: u8, b: u8) -> u8 { a | b }
pub open spec fn xor_u8(a: u8, b: u8) -> u8 { a ^ b }
/// `!a & b`, as `_mm_andnot_si128` (the first operand is inverted).
pub open spec fn andnot_u8(a: u8, b: u8) -> u8 { !a & b }
pub open spec fn adds_i8(a: u8, b: u8) -> u8 { ub(clamp(sb(a) + sb(b), -128, 127)) }
pub open spec fn subs_i8(a: u8, b: u8) -> u8 { ub(clamp(sb(a) - sb(b), -128, 127)) }
pub open spec fn add_u8(a: u8, b: u8) -> u8 { ((a as int + b as int) % 256) as u8 }
pub open spec fn sub_u8(a: u8, b: u8) -> u8 { ((a as int - b as int + 256) % 256) as u8 }
pub open spec fn avg_u8(a: u8, b: u8) -> u8 { ((a as int + b as int + 1) / 2) as u8 }

// ------------------------------------------------- whole vectors, bytewise

pub open spec fn subs_epu8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| subs_u8(a[k], b[k])) }
pub open spec fn adds_epu8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| adds_u8(a[k], b[k])) }
pub open spec fn max_epu8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| max_u8(a[k], b[k])) }
pub open spec fn cmpeq_epi8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| eq_u8(a[k], b[k])) }
pub open spec fn and_si128(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| and_u8(a[k], b[k])) }
pub open spec fn or_si128(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| or_u8(a[k], b[k])) }
pub open spec fn xor_si128(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| xor_u8(a[k], b[k])) }
pub open spec fn andnot_si128(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| andnot_u8(a[k], b[k])) }
pub open spec fn adds_epi8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| adds_i8(a[k], b[k])) }
pub open spec fn subs_epi8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| subs_i8(a[k], b[k])) }
pub open spec fn add_epi8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| add_u8(a[k], b[k])) }
pub open spec fn sub_epi8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| sub_u8(a[k], b[k])) }
pub open spec fn avg_epu8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| avg_u8(a[k], b[k])) }

pub open spec fn set1_epi8(x: u8) -> Seq<u8> { Seq::new(16, |k: int| x) }

// ----------------------------------------------------------- 16-bit lanes

/// 16-bit lane `j` (bytes 2j and 2j + 1, little-endian), unsigned.
pub open spec fn w16(a: Seq<u8>, j: int) -> int { a[2 * j] as int + 256 * a[2 * j + 1] as int }

/// 16-bit lane `j`, signed.
pub open spec fn sw16(a: Seq<u8>, j: int) -> int { if w16(a, j) < 32768 { w16(a, j) } else { w16(a, j) - 65536 } }

/// Byte `k` of a vector whose 16-bit lane `k / 2` holds `x` (mod 2^16).
pub open spec fn put16(x: int, k: int) -> u8 {
    let u = x % 65536;
    if k % 2 == 0 { (u % 256) as u8 } else { (u / 256) as u8 }
}

/// Arithmetic shift right of each signed 16-bit lane, by `n` (0 <= n < 16).
pub open spec fn srai_epi16(a: Seq<u8>, n: nat) -> Seq<u8> { Seq::new(16, |k: int| put16(sw16(a, k / 2) / vstd::arithmetic::power2::pow2(n) as int, k)) }

/// Logical shift right of each unsigned 16-bit lane, by `n` (0 <= n < 16).
pub open spec fn srli_epi16(a: Seq<u8>, n: nat) -> Seq<u8> { Seq::new(16, |k: int| put16(w16(a, k / 2) / vstd::arithmetic::power2::pow2(n) as int, k)) }

/// Shift left of each 16-bit lane, by `n` (0 <= n < 16), mod 2^16.
pub open spec fn slli_epi16(a: Seq<u8>, n: nat) -> Seq<u8> { Seq::new(16, |k: int| put16(w16(a, k / 2) * vstd::arithmetic::power2::pow2(n) as int, k)) }

pub open spec fn add_epi16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| put16(w16(a, k / 2) + w16(b, k / 2), k)) }

/// The high 16 bits of each signed 32-bit product.
pub open spec fn mulhi_epi16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| put16(sw16(a, k / 2) * sw16(b, k / 2) / 65536, k)) }

/// The high 16 bits of each unsigned 32-bit product.
pub open spec fn mulhi_epu16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| put16(w16(a, k / 2) * w16(b, k / 2) / 65536, k)) }

/// Unsigned 16-bit sums and differences, saturated to 0..65535.
pub open spec fn adds_epu16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| put16(clamp(w16(a, k / 2) + w16(b, k / 2), 0, 65535), k)) }
pub open spec fn subs_epu16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| put16(clamp(w16(a, k / 2) - w16(b, k / 2), 0, 65535), k)) }

pub open spec fn set1_epi16(x: u16) -> Seq<u8> { Seq::new(16, |k: int| put16(x as int, k)) }

// ------------------------------------------------------- across lanes

/// Interleave the low halves: a0 b0 a1 b1 ... a7 b7.
pub open spec fn unpacklo_epi8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| if k % 2 == 0 { a[k / 2] } else { b[k / 2] }) }

/// Interleave the high halves: a8 b8 a9 b9 ... a15 b15.
pub open spec fn unpackhi_epi8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| if k % 2 == 0 { a[8 + k / 2] } else { b[8 + k / 2] }) }

/// The signed 16-bit lanes of a, then of b, saturated to signed bytes.
pub open spec fn packs_epi16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |k: int| if k < 8 { ub(clamp(sw16(a, k), -128, 127)) } else { ub(clamp(sw16(b, k - 8), -128, 127)) })
}

/// Interleave the low halves in elements of `s` bytes (1, 2, 4 or 8):
/// element e of the result is element e / 2 of a (e even) or of b (e odd).
pub open spec fn unpacklo(a: Seq<u8>, b: Seq<u8>, s: int) -> Seq<u8> {
    Seq::new(16, |k: int| if (k / s) % 2 == 0 { a[(k / s / 2) * s + k % s] } else { b[(k / s / 2) * s + k % s] })
}

/// The same with the high halves.
pub open spec fn unpackhi(a: Seq<u8>, b: Seq<u8>, s: int) -> Seq<u8> {
    Seq::new(16, |k: int| if (k / s) % 2 == 0 { a[8 + (k / s / 2) * s + k % s] } else { b[8 + (k / s / 2) * s + k % s] })
}

pub open spec fn unpacklo_epi16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { unpacklo(a, b, 2) }
pub open spec fn unpackhi_epi16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { unpackhi(a, b, 2) }
pub open spec fn unpacklo_epi32(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { unpacklo(a, b, 4) }
pub open spec fn unpackhi_epi32(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { unpackhi(a, b, 4) }
pub open spec fn unpacklo_epi64(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { unpacklo(a, b, 8) }
pub open spec fn unpackhi_epi64(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { unpackhi(a, b, 8) }

/// Eight bytes, then eight zeros (`_mm_loadl_epi64`).
pub open spec fn lo8(a: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| if k < 8 { a[k] } else { 0u8 }) }

pub open spec fn sub_epi16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| put16(w16(a, k / 2) - w16(b, k / 2), k)) }

/// Each signed 16-bit lane saturated to an unsigned byte: a's 8, then b's.
pub open spec fn packus_epi16(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |k: int| if k < 8 { clamp(sw16(a, k), 0, 255) as u8 } else { clamp(sw16(b, k - 8), 0, 255) as u8 })
}

// ----------------------------------------------------------- 32-bit lanes

/// 32-bit lane `j` (bytes 4j .. 4j + 4, little-endian), unsigned.
pub open spec fn w32(a: Seq<u8>, j: int) -> int {
    a[4 * j] as int + 256 * a[4 * j + 1] as int + 65536 * a[4 * j + 2] as int + 16777216 * a[4 * j + 3] as int
}

/// 32-bit lane `j`, signed.
pub open spec fn sw32(a: Seq<u8>, j: int) -> int { if w32(a, j) < 2147483648 { w32(a, j) } else { w32(a, j) - 4294967296 } }

/// Byte `k` of a vector whose 32-bit lane `k / 4` holds `x` (mod 2^32).
pub open spec fn put32(x: int, k: int) -> u8 {
    let u = x % 4294967296;
    let q = if k % 4 == 0 { u } else if k % 4 == 1 { u / 256 } else if k % 4 == 2 { u / 65536 } else { u / 16777216 };
    (q % 256) as u8
}

pub open spec fn add_epi32(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| put32(w32(a, k / 4) + w32(b, k / 4), k)) }
pub open spec fn sub_epi32(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| put32(w32(a, k / 4) - w32(b, k / 4), k)) }

/// Arithmetic shift right of each signed 32-bit lane, by `n` (0 <= n < 32).
pub open spec fn srai_epi32(a: Seq<u8>, n: nat) -> Seq<u8> { Seq::new(16, |k: int| put32(sw32(a, k / 4) / vstd::arithmetic::power2::pow2(n) as int, k)) }

/// The signed 32-bit lanes of a, then of b, saturated to 16 bits.
pub open spec fn packs_epi32(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |k: int| if k < 8 { put16(clamp(sw32(a, k / 2), -32768, 32767), k) } else { put16(clamp(sw32(b, k / 2 - 4), -32768, 32767), k) })
}

/// Logical shift right of each unsigned 32-bit lane, by `n` (0 <= n < 32).
pub open spec fn srli_epi32(a: Seq<u8>, n: nat) -> Seq<u8> { Seq::new(16, |k: int| put32(w32(a, k / 4) / vstd::arithmetic::power2::pow2(n) as int, k)) }

/// Shift left of each 32-bit lane, by `n` (0 <= n < 32), mod 2^32.
pub open spec fn slli_epi32(a: Seq<u8>, n: nat) -> Seq<u8> { Seq::new(16, |k: int| put32(w32(a, k / 4) * vstd::arithmetic::power2::pow2(n) as int, k)) }

/// Every 32-bit lane `x`.
pub open spec fn set1_epi32(x: u32) -> Seq<u8> { Seq::new(16, |k: int| put32(x as int, k)) }

/// The bytes of four u32s from `s[i]` on, little-endian (a 16-byte load of u32s).
pub open spec fn u32s(s: Seq<u32>, i: int) -> Seq<u8> { Seq::new(16, |k: int| put32(s[i + k / 4] as int, k)) }

/// Four bytes, then twelve zeros (`_mm_cvtsi32_si128`).
pub open spec fn lo4(a: Seq<u8>) -> Seq<u8> { Seq::new(16, |k: int| if k < 4 { a[k] } else { 0u8 }) }

// ------------------------------------------------------ 16-bit lemmas

/// `put16` sees its value only mod 2^16.
pub proof fn lemma_put16_mod(x: int, y: int, k: int)
    requires x % 65536 == y % 65536,
    ensures put16(x, k) == put16(y, k),
{}

/// A 16-bit lane written with `put16(x)` reads back as x.
pub proof fn lemma_rt16(a: Seq<u8>, j: int, x: int)
    requires 0 <= j, 2 * j + 1 < a.len(), a[2 * j] == put16(x, 2 * j), a[2 * j + 1] == put16(x, 2 * j + 1),
    ensures w16(a, j) == x % 65536, -32768 <= x < 32768 ==> sw16(a, j) == x,
{
    assert((2 * j) % 2 == 0 && (2 * j + 1) % 2 == 1);
    let u = x % 65536;
    assert(u % 256 + 256 * (u / 256) == u);
}

/// A 32-bit lane written with `put32(x)` reads back as x.
pub proof fn lemma_rt32(a: Seq<u8>, j: int, x: int)
    requires 0 <= j, 4 * j + 3 < a.len(),
        a[4 * j] == put32(x, 4 * j), a[4 * j + 1] == put32(x, 4 * j + 1), a[4 * j + 2] == put32(x, 4 * j + 2), a[4 * j + 3] == put32(x, 4 * j + 3),
    ensures w32(a, j) == x % 4294967296, -2147483648 <= x < 2147483648 ==> sw32(a, j) == x,
{
    use vstd::arithmetic::div_mod::*;
    assert((4 * j) % 4 == 0 && (4 * j + 1) % 4 == 1 && (4 * j + 2) % 4 == 2 && (4 * j + 3) % 4 == 3);
    let u = x % 4294967296;
    let (q1, q2, q3) = (u / 256, u / 256 / 256, u / 256 / 256 / 256);
    lemma_div_denominator(u, 256, 256);
    lemma_div_denominator(u / 256, 256, 256);
    lemma_div_denominator(u, 256, 65536);
    assert(q2 == u / 65536 && q3 == u / 16777216);
    lemma_fundamental_div_mod(u, 256);
    lemma_fundamental_div_mod(q1, 256);
    lemma_fundamental_div_mod(q2, 256);
    assert(q3 < 256);
    assert(q3 % 256 == q3);
    assert(u == u % 256 + 256 * (q1 % 256) + 65536 * (q2 % 256) + 16777216 * q3) by (nonlinear_arith)
        requires u == 256 * q1 + u % 256, q1 == 256 * q2 + q1 % 256, q2 == 256 * q3 + q2 % 256;
    assert(w32(a, j) == u % 256 + 256 * (q1 % 256) + 65536 * (q2 % 256) + 16777216 * (q3 % 256));
}

/// `put32` sees its value only mod 2^32.
pub proof fn lemma_put32_mod(x: int, y: int, k: int)
    requires x % 4294967296 == y % 4294967296,
    ensures put32(x, k) == put32(y, k),
{}

// ------------------------------------------------------ lane lemmas
//
// What one 16- or 32-bit lane of an operation's result holds, as its
// unsigned value mod 2^16 or 2^32 (`w16`, `w32`), from its operands' lanes.

pub proof fn lemma_w16_bounds(a: Seq<u8>, j: int)
    requires 0 <= j, 2 * j + 1 < a.len(),
    ensures 0 <= w16(a, j) < 65536, -32768 <= sw16(a, j) < 32768, w16(a, j) == sw16(a, j) % 65536,
{}

pub proof fn lemma_w32_bounds(a: Seq<u8>, j: int)
    requires 0 <= j, 4 * j + 3 < a.len(),
    ensures 0 <= w32(a, j) < 4294967296, -2147483648 <= sw32(a, j) < 2147483648, w32(a, j) == sw32(a, j) % 4294967296,
{}

pub proof fn lemma_add16_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16, b.len() == 16,
    ensures w16(add_epi16(a, b), j) == (w16(a, j) + w16(b, j)) % 65536,
{
    let r = add_epi16(a, b);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    lemma_rt16(r, j, w16(a, j) + w16(b, j));
}

pub proof fn lemma_sub16_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16, b.len() == 16,
    ensures w16(sub_epi16(a, b), j) == (w16(a, j) - w16(b, j)) % 65536,
{
    let r = sub_epi16(a, b);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    lemma_rt16(r, j, w16(a, j) - w16(b, j));
}

pub proof fn lemma_mulhi_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16, b.len() == 16,
    ensures w16(mulhi_epi16(a, b), j) == (sw16(a, j) * sw16(b, j) / 65536) % 65536,
        sw16(mulhi_epi16(a, b), j) == sw16(a, j) * sw16(b, j) / 65536,
{
    let r = mulhi_epi16(a, b);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    let (x, y) = (sw16(a, j), sw16(b, j));
    lemma_w16_bounds(a, j);
    lemma_w16_bounds(b, j);
    assert(-32768 <= x * y / 65536 < 32768) by (nonlinear_arith) requires -32768 <= x < 32768, -32768 <= y < 32768;
    lemma_rt16(r, j, x * y / 65536);
}

/// A 16-bit lane holding x mod 2^16, for a signed 16-bit x, is x signed.
pub proof fn lemma_sw16_of(a: Seq<u8>, j: int, x: int)
    requires 0 <= j, 2 * j + 1 < a.len(), w16(a, j) == x % 65536, -32768 <= x < 32768,
    ensures sw16(a, j) == x,
{}

pub proof fn lemma_mulhiu_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16, b.len() == 16,
    ensures w16(mulhi_epu16(a, b), j) == w16(a, j) * w16(b, j) / 65536,
{
    let r = mulhi_epu16(a, b);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    let (x, y) = (w16(a, j), w16(b, j));
    lemma_w16_bounds(a, j);
    lemma_w16_bounds(b, j);
    assert(0 <= x * y / 65536 < 65536) by (nonlinear_arith) requires 0 <= x < 65536, 0 <= y < 65536;
    lemma_rt16(r, j, x * y / 65536);
}

pub proof fn lemma_addsu_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16, b.len() == 16,
    ensures w16(adds_epu16(a, b), j) == clamp(w16(a, j) + w16(b, j), 0, 65535),
{
    let r = adds_epu16(a, b);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    lemma_rt16(r, j, clamp(w16(a, j) + w16(b, j), 0, 65535));
}

pub proof fn lemma_subsu_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16, b.len() == 16,
    ensures w16(subs_epu16(a, b), j) == clamp(w16(a, j) - w16(b, j), 0, 65535),
{
    let r = subs_epu16(a, b);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    lemma_rt16(r, j, clamp(w16(a, j) - w16(b, j), 0, 65535));
}

pub proof fn lemma_srai16_lane(a: Seq<u8>, n: nat, j: int)
    requires 0 <= j < 8, a.len() == 16, n < 16,
    ensures sw16(srai_epi16(a, n), j) == sw16(a, j) / vstd::arithmetic::power2::pow2(n) as int,
{
    let r = srai_epi16(a, n);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    lemma_w16_bounds(a, j);
    let p = vstd::arithmetic::power2::pow2(n) as int;
    vstd::arithmetic::power2::lemma_pow2_pos(n);
    let x = sw16(a, j);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, p);
    let (q, m) = (x / p, x % p);
    assert(-32768 <= q < 32768) by (nonlinear_arith)
        requires x == p * q + m, 0 <= m < p, p >= 1, -32768 <= x < 32768;
    lemma_rt16(r, j, x / p);
}

pub proof fn lemma_srli16_lane(a: Seq<u8>, n: nat, j: int)
    requires 0 <= j < 8, a.len() == 16, n < 16,
    ensures w16(srli_epi16(a, n), j) == w16(a, j) / vstd::arithmetic::power2::pow2(n) as int,
{
    let r = srli_epi16(a, n);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    lemma_w16_bounds(a, j);
    let p = vstd::arithmetic::power2::pow2(n) as int;
    vstd::arithmetic::power2::lemma_pow2_pos(n);
    let x = w16(a, j);
    assert(0 <= x / p < 65536) by (nonlinear_arith) requires 0 <= x < 65536, p >= 1;
    lemma_rt16(r, j, x / p);
}

/// A byte moved to the high half of a 16-bit lane (zeros below).
pub proof fn lemma_hi8_lane(z: Seq<u8>, a: Seq<u8>, l: int)
    requires 0 <= l < 8, a.len() == 16, z.len() == 16, forall|k: int| 0 <= k < 16 ==> #[trigger] z[k] == 0,
    ensures w16(unpacklo_epi8(z, a), l) == 256 * a[l] as int,
{
    assert((2 * l) / 2 == l && (2 * l + 1) / 2 == l && (2 * l) % 2 == 0 && (2 * l + 1) % 2 == 1);
}

pub proof fn lemma_set1_16_lane(x: u16, j: int)
    requires 0 <= j < 8,
    ensures w16(set1_epi16(x), j) == x as int,
{
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    lemma_rt16(set1_epi16(x), j, x as int);
}

pub proof fn lemma_add32_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 4, a.len() == 16, b.len() == 16,
    ensures w32(add_epi32(a, b), j) == (w32(a, j) + w32(b, j)) % 4294967296,
{
    let r = add_epi32(a, b);
    assert((4 * j) / 4 == j && (4 * j + 1) / 4 == j && (4 * j + 2) / 4 == j && (4 * j + 3) / 4 == j);
    lemma_rt32(r, j, w32(a, j) + w32(b, j));
}

pub proof fn lemma_sub32_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 4, a.len() == 16, b.len() == 16,
    ensures w32(sub_epi32(a, b), j) == (w32(a, j) - w32(b, j)) % 4294967296,
{
    let r = sub_epi32(a, b);
    assert((4 * j) / 4 == j && (4 * j + 1) / 4 == j && (4 * j + 2) / 4 == j && (4 * j + 3) / 4 == j);
    lemma_rt32(r, j, w32(a, j) - w32(b, j));
}

pub proof fn lemma_srai32_lane(a: Seq<u8>, n: nat, j: int)
    requires 0 <= j < 4, a.len() == 16, n < 32,
    ensures sw32(srai_epi32(a, n), j) == sw32(a, j) / vstd::arithmetic::power2::pow2(n) as int,
{
    let r = srai_epi32(a, n);
    assert((4 * j) / 4 == j && (4 * j + 1) / 4 == j && (4 * j + 2) / 4 == j && (4 * j + 3) / 4 == j);
    lemma_w32_bounds(a, j);
    let p = vstd::arithmetic::power2::pow2(n) as int;
    vstd::arithmetic::power2::lemma_pow2_pos(n);
    let x = sw32(a, j);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, p);
    let (q, m) = (x / p, x % p);
    assert(-2147483648 <= q < 2147483648) by (nonlinear_arith)
        requires x == p * q + m, 0 <= m < p, p >= 1, -2147483648 <= x < 2147483648;
    lemma_rt32(r, j, sw32(a, j) / p);
}

pub proof fn lemma_packs32_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16, b.len() == 16,
    ensures sw16(packs_epi32(a, b), j) == if j < 4 { clamp(sw32(a, j), -32768, 32767) } else { clamp(sw32(b, j - 4), -32768, 32767) },
{
    let r = packs_epi32(a, b);
    assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j);
    let x = if j < 4 { clamp(sw32(a, j), -32768, 32767) } else { clamp(sw32(b, j - 4), -32768, 32767) };
    lemma_rt16(r, j, x);
}

/// 16-bit lane l of a 16-bit interleave: lane l / 2 of a (l even) or b.
pub proof fn lemma_unpack16_lane(a: Seq<u8>, b: Seq<u8>, l: int)
    requires 0 <= l < 8, a.len() == 16, b.len() == 16,
    ensures
        w16(unpacklo_epi16(a, b), l) == if l % 2 == 0 { w16(a, l / 2) } else { w16(b, l / 2) },
        w16(unpackhi_epi16(a, b), l) == if l % 2 == 0 { w16(a, 4 + l / 2) } else { w16(b, 4 + l / 2) },
{
    let (e, o) = (2 * l, 2 * l + 1);
    assert(e / 2 == l && o / 2 == l && e % 2 == 0 && o % 2 == 1);
    assert((e / 2 / 2) * 2 + e % 2 == 2 * (l / 2) && (o / 2 / 2) * 2 + o % 2 == 2 * (l / 2) + 1);
}

/// 16-bit lane l of a 32-bit interleave.
pub proof fn lemma_unpack32_lane16(a: Seq<u8>, b: Seq<u8>, l: int)
    requires 0 <= l < 8, a.len() == 16, b.len() == 16,
    ensures
        w16(unpacklo_epi32(a, b), l) == if (l / 2) % 2 == 0 { w16(a, (l / 4) * 2 + l % 2) } else { w16(b, (l / 4) * 2 + l % 2) },
        w16(unpackhi_epi32(a, b), l) == if (l / 2) % 2 == 0 { w16(a, 4 + (l / 4) * 2 + l % 2) } else { w16(b, 4 + (l / 4) * 2 + l % 2) },
{
    let (e, o) = (2 * l, 2 * l + 1);
    assert(e / 4 == l / 2 && o / 4 == l / 2);
    assert((e / 4 / 2) * 4 + e % 4 == 2 * ((l / 4) * 2 + l % 2));
    assert((o / 4 / 2) * 4 + o % 4 == 2 * ((l / 4) * 2 + l % 2) + 1);
}

/// A 16-bit lane moved to the high half of a 32-bit lane (zeros below).
pub proof fn lemma_widen_lane(z: Seq<u8>, x: Seq<u8>, r: int)
    requires 0 <= r < 4, z.len() == 16, x.len() == 16, forall|k: int| 0 <= k < 16 ==> #[trigger] z[k] == 0,
    ensures
        sw32(unpacklo_epi16(z, x), r) == 65536 * sw16(x, r),
        sw32(unpackhi_epi16(z, x), r) == 65536 * sw16(x, 4 + r),
{
    assert((4 * r) / 2 == 2 * r && (4 * r + 1) / 2 == 2 * r && (4 * r + 2) / 2 == 2 * r + 1 && (4 * r + 3) / 2 == 2 * r + 1);
    assert(((4 * r) / 2 / 2) * 2 + (4 * r) % 2 == 2 * r && ((4 * r + 2) / 2 / 2) * 2 + (4 * r + 2) % 2 == 2 * r);
    assert(((4 * r + 3) / 2 / 2) * 2 + (4 * r + 3) % 2 == 2 * r + 1);
}

/// A byte zero-extended to a 16-bit lane.
pub proof fn lemma_zext_lane(a: Seq<u8>, z: Seq<u8>, l: int)
    requires 0 <= l < 8, a.len() == 16, z.len() == 16, forall|k: int| 0 <= k < 16 ==> #[trigger] z[k] == 0,
    ensures w16(unpacklo_epi8(a, z), l) == a[l] as int, w16(unpackhi_epi8(a, z), l) == a[8 + l] as int,
{
    assert((2 * l) / 2 == l && (2 * l + 1) / 2 == l && (2 * l) % 2 == 0 && (2 * l + 1) % 2 == 1);
}

} // verus!
