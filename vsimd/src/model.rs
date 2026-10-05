//! Portable models of the intrinsics on `[u8; 16]`, proved to compute the
//! spec functions in `spec.rs`. They are the oracles the hardware is tested
//! against (`tests/validate.rs`), and a backend for targets without SSE2.
use vstd::prelude::*;
use crate::spec::*;

verus! {

// ------------------------------------------------------- one lane, exec

pub fn sb_x(b: u8) -> (r: i32) ensures r == sb(b), -128 <= r <= 127 { if b < 128 { b as i32 } else { b as i32 - 256 } }

pub fn ub_x(x: i32) -> (r: u8) requires -128 <= x <= 255, ensures r == ub(x as int) { if x < 0 { (x + 256) as u8 } else { x as u8 } }

pub fn clamp_x(x: i32, lo: i32, hi: i32) -> (r: i32) requires lo <= hi, ensures r == clamp(x as int, lo as int, hi as int), lo <= r <= hi {
    if x < lo { lo } else if x > hi { hi } else { x }
}

pub fn subs_u8_x(a: u8, b: u8) -> (r: u8) ensures r == subs_u8(a, b) { if a >= b { a - b } else { 0 } }
pub fn adds_u8_x(a: u8, b: u8) -> (r: u8) ensures r == adds_u8(a, b) { if a as u16 + b as u16 > 255 { 255 } else { a + b } }
pub fn max_u8_x(a: u8, b: u8) -> (r: u8) ensures r == max_u8(a, b) { if a >= b { a } else { b } }
pub fn eq_u8_x(a: u8, b: u8) -> (r: u8) ensures r == eq_u8(a, b) { if a == b { 255 } else { 0 } }
pub fn and_u8_x(a: u8, b: u8) -> (r: u8) ensures r == and_u8(a, b) { a & b }
pub fn or_u8_x(a: u8, b: u8) -> (r: u8) ensures r == or_u8(a, b) { a | b }
pub fn xor_u8_x(a: u8, b: u8) -> (r: u8) ensures r == xor_u8(a, b) { a ^ b }
pub fn andnot_u8_x(a: u8, b: u8) -> (r: u8) ensures r == andnot_u8(a, b) { !a & b }
pub fn adds_i8_x(a: u8, b: u8) -> (r: u8) ensures r == adds_i8(a, b) { ub_x(clamp_x(sb_x(a) + sb_x(b), -128, 127)) }
pub fn subs_i8_x(a: u8, b: u8) -> (r: u8) ensures r == subs_i8(a, b) { ub_x(clamp_x(sb_x(a) - sb_x(b), -128, 127)) }
pub fn add_u8_x(a: u8, b: u8) -> (r: u8) ensures r == add_u8(a, b) { ((a as u16 + b as u16) % 256) as u8 }
pub fn sub_u8_x(a: u8, b: u8) -> (r: u8) ensures r == sub_u8(a, b) { ((a as u16 + 256 - b as u16) % 256) as u8 }
pub fn avg_u8_x(a: u8, b: u8) -> (r: u8) ensures r == avg_u8(a, b) { ((a as u16 + b as u16 + 1) / 2) as u8 }

// ------------------------------------------------- 16-bit lanes, exec

pub fn w16_x(a: &[u8; 16], j: usize) -> (r: i32) requires j < 8, ensures r == w16(a@, j as int), 0 <= r < 65536 {
    a[2 * j] as i32 + 256 * a[2 * j + 1] as i32
}

pub fn sw16_x(a: &[u8; 16], j: usize) -> (r: i32) requires j < 8, ensures r == sw16(a@, j as int), -32768 <= r < 32768 {
    let w = w16_x(a, j);
    if w < 32768 { w } else { w - 65536 }
}

pub fn put16_x(x: i32, k: usize) -> (r: u8) requires -65536 <= x < 131072, ensures r == put16(x as int, k as int) {
    let u = if x < 0 { x + 65536 } else if x >= 65536 { x - 65536 } else { x };
    assert(u as int == (x as int) % 65536);
    if k % 2 == 0 { (u % 256) as u8 } else { (u / 256) as u8 }
}

/// floor(x / 2^n) for a signed 16-bit x, as unsigned division of x + 2^15.
pub fn sra16_x(x: i32, n: u32) -> (r: i32)
    requires -32768 <= x < 32768, n < 16,
    ensures r == x as int / vstd::arithmetic::power2::pow2(n as nat) as int, -32768 <= r < 32768,
{
    let d: i32 = 1i32 << n;
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        assert(d == vstd::arithmetic::power2::pow2(n as nat)) by {
            vstd::bits::lemma_u32_shl_is_mul(1, n);
            assert((1i32 << n) as int == (1u32 << n) as int) by (bit_vector) requires n < 16u32;
        }
    }
    let q = (x + 32768) as u32 / d as u32;
    let s = (32768u32 / d as u32) as i32;
    proof {
        use vstd::arithmetic::power2::*;
        use vstd::arithmetic::div_mod::*;
        let p = pow2(n as nat) as int;
        let m = pow2((15 - n) as nat) as int;
        lemma_pow2_adds(n as nat, (15 - n) as nat);
        lemma_pow2_pos((15 - n) as nat);
        assert(p * m == 32768);
        lemma_fundamental_div_mod(x as int, p);
        let t = x as int / p;
        let b = x as int % p;
        assert(x as int + 32768 == p * (t + m) + b) by (nonlinear_arith)
            requires x as int == p * t + b, p * m == 32768;
        lemma_div_multiples_vanish_fancy(t + m, b, p);
        lemma_div_multiples_vanish_fancy(m, 0, p);
        assert(p * m + 0 == 32768);
    }
    q as i32 - s
}

// --------------------------------------------------- whole vectors, exec

macro_rules! model {
    ($name:ident ( $($arg:ident : $ty:ty),* ) => $spec:tt ; |$k:ident| $lane:tt ; $req:tt) => {
        verus! {
        pub fn $name($($arg: $ty),*) -> (r: [u8; 16])
            requires $req,
            ensures r@ == $spec,
        {
            let mut r = [0u8; 16];
            let mut $k: usize = 0;
            while $k < 16
                invariant $k <= 16, r@.len() == 16, $req,
                    forall|j: int| 0 <= j < $k ==> r@[j] == ($spec)[j],
                decreases 16 - $k,
            {
                let x = $lane;
                r[$k] = x;
                $k += 1;
            }
            proof { assert(r@ =~= $spec); }
            r
        }
        }
    };
}

model!(subs_epu8(a: [u8; 16], b: [u8; 16]) => (crate::spec::subs_epu8(a@, b@)); |k| { subs_u8_x(a[k], b[k]) }; (true));
model!(adds_epu8(a: [u8; 16], b: [u8; 16]) => (crate::spec::adds_epu8(a@, b@)); |k| { adds_u8_x(a[k], b[k]) }; (true));
model!(max_epu8(a: [u8; 16], b: [u8; 16]) => (crate::spec::max_epu8(a@, b@)); |k| { max_u8_x(a[k], b[k]) }; (true));
model!(cmpeq_epi8(a: [u8; 16], b: [u8; 16]) => (crate::spec::cmpeq_epi8(a@, b@)); |k| { eq_u8_x(a[k], b[k]) }; (true));
model!(and_si128(a: [u8; 16], b: [u8; 16]) => (crate::spec::and_si128(a@, b@)); |k| { and_u8_x(a[k], b[k]) }; (true));
model!(or_si128(a: [u8; 16], b: [u8; 16]) => (crate::spec::or_si128(a@, b@)); |k| { or_u8_x(a[k], b[k]) }; (true));
model!(xor_si128(a: [u8; 16], b: [u8; 16]) => (crate::spec::xor_si128(a@, b@)); |k| { xor_u8_x(a[k], b[k]) }; (true));
model!(andnot_si128(a: [u8; 16], b: [u8; 16]) => (crate::spec::andnot_si128(a@, b@)); |k| { andnot_u8_x(a[k], b[k]) }; (true));
model!(adds_epi8(a: [u8; 16], b: [u8; 16]) => (crate::spec::adds_epi8(a@, b@)); |k| { adds_i8_x(a[k], b[k]) }; (true));
model!(subs_epi8(a: [u8; 16], b: [u8; 16]) => (crate::spec::subs_epi8(a@, b@)); |k| { subs_i8_x(a[k], b[k]) }; (true));
model!(add_epi8(a: [u8; 16], b: [u8; 16]) => (crate::spec::add_epi8(a@, b@)); |k| { add_u8_x(a[k], b[k]) }; (true));
model!(sub_epi8(a: [u8; 16], b: [u8; 16]) => (crate::spec::sub_epi8(a@, b@)); |k| { sub_u8_x(a[k], b[k]) }; (true));
model!(avg_epu8(a: [u8; 16], b: [u8; 16]) => (crate::spec::avg_epu8(a@, b@)); |k| { avg_u8_x(a[k], b[k]) }; (true));
model!(set1_epi8(x: u8) => (crate::spec::set1_epi8(x)); |k| { x }; (true));
model!(set1_epi16(x: u16) => (crate::spec::set1_epi16(x)); |k| { put16_x(x as i32, k) }; (true));
model!(unpacklo_epi8(a: [u8; 16], b: [u8; 16]) => (crate::spec::unpacklo_epi8(a@, b@)); |k| { if k % 2 == 0 { a[k / 2] } else { b[k / 2] } }; (true));
model!(unpackhi_epi8(a: [u8; 16], b: [u8; 16]) => (crate::spec::unpackhi_epi8(a@, b@)); |k| { if k % 2 == 0 { a[8 + k / 2] } else { b[8 + k / 2] } }; (true));
model!(packs_epi16(a: [u8; 16], b: [u8; 16]) => (crate::spec::packs_epi16(a@, b@));
    |k| { if k < 8 { ub_x(clamp_x(sw16_x(&a, k), -128, 127)) } else { ub_x(clamp_x(sw16_x(&b, k - 8), -128, 127)) } }; (true));
model!(add_epi16(a: [u8; 16], b: [u8; 16]) => (crate::spec::add_epi16(a@, b@)); |k| { put16_x(w16_x(&a, k / 2) + w16_x(&b, k / 2), k) }; (true));
model!(mulhi_epi16(a: [u8; 16], b: [u8; 16]) => (crate::spec::mulhi_epi16(a@, b@)); |k| { mulhi_lane(&a, &b, k) }; (true));
model!(mulhi_epu16(a: [u8; 16], b: [u8; 16]) => (crate::spec::mulhi_epu16(a@, b@)); |k| { mulhiu_lane(&a, &b, k) }; (true));
model!(adds_epu16(a: [u8; 16], b: [u8; 16]) => (crate::spec::adds_epu16(a@, b@)); |k| { put16_x(clamp_x(w16_x(&a, k / 2) + w16_x(&b, k / 2), 0, 65535), k) }; (true));
model!(subs_epu16(a: [u8; 16], b: [u8; 16]) => (crate::spec::subs_epu16(a@, b@)); |k| { put16_x(clamp_x(w16_x(&a, k / 2) - w16_x(&b, k / 2), 0, 65535), k) }; (true));
model!(srai_epi16(a: [u8; 16], n: u32) => (crate::spec::srai_epi16(a@, n as nat)); |k| { put16_x(sra16_x(sw16_x(&a, k / 2), n), k) }; (n < 16));
model!(slli_epi16(a: [u8; 16], n: u32) => (crate::spec::slli_epi16(a@, n as nat)); |k| { put16_x(sll16_x(w16_x(&a, k / 2), n), k) }; (n < 16));
model!(srli_epi32(a: [u8; 16], n: u32) => (crate::spec::srli_epi32(a@, n as nat)); |k| { put32_x(srl32_x(w32_x(&a, k / 4), n), k) }; (n < 32));
model!(slli_epi32(a: [u8; 16], n: u32) => (crate::spec::slli_epi32(a@, n as nat)); |k| { put32_x(sll32_x(w32_x(&a, k / 4), n), k) }; (n < 32));
model!(set1_epi32(x: u32) => (crate::spec::set1_epi32(x)); |k| { put32_x(x as i64, k) }; (true));
model!(srli_epi16(a: [u8; 16], n: u32) => (crate::spec::srli_epi16(a@, n as nat)); |k| { put16_x(srl16_x(w16_x(&a, k / 2), n), k) }; (n < 16));

model!(unpacklo_epi16(a: [u8; 16], b: [u8; 16]) => (crate::spec::unpacklo_epi16(a@, b@)); |k| { unpack_lane(&a, &b, 2, 0, k) }; (true));
model!(unpackhi_epi16(a: [u8; 16], b: [u8; 16]) => (crate::spec::unpackhi_epi16(a@, b@)); |k| { unpack_lane(&a, &b, 2, 8, k) }; (true));
model!(unpacklo_epi32(a: [u8; 16], b: [u8; 16]) => (crate::spec::unpacklo_epi32(a@, b@)); |k| { unpack_lane(&a, &b, 4, 0, k) }; (true));
model!(unpackhi_epi32(a: [u8; 16], b: [u8; 16]) => (crate::spec::unpackhi_epi32(a@, b@)); |k| { unpack_lane(&a, &b, 4, 8, k) }; (true));
model!(unpacklo_epi64(a: [u8; 16], b: [u8; 16]) => (crate::spec::unpacklo_epi64(a@, b@)); |k| { unpack_lane(&a, &b, 8, 0, k) }; (true));
model!(unpackhi_epi64(a: [u8; 16], b: [u8; 16]) => (crate::spec::unpackhi_epi64(a@, b@)); |k| { unpack_lane(&a, &b, 8, 8, k) }; (true));

/// Byte k of an unpack in elements of s bytes, from the half at `off`.
pub fn unpack_lane(a: &[u8; 16], b: &[u8; 16], s: usize, off: usize, k: usize) -> (r: u8)
    requires s == 2 || s == 4 || s == 8, off == 0 || off == 8, k < 16,
    ensures r == if (k / s) % 2 == 0 { a@[off + (k / s / 2) * s + k % s] } else { b@[off + (k / s / 2) * s + k % s] },
{
    let e = k / s;
    assert((e / 2) * s + k % s < 8) by (nonlinear_arith) requires e == k / s, k < 16, s == 2 || s == 4 || s == 8;
    let j = off + (e / 2) * s + k % s;
    if e % 2 == 0 { a[j] } else { b[j] }
}

model!(sub_epi16(a: [u8; 16], b: [u8; 16]) => (crate::spec::sub_epi16(a@, b@)); |k| { put16_x(w16_x(&a, k / 2) - w16_x(&b, k / 2), k) }; (true));
model!(packus_epi16(a: [u8; 16], b: [u8; 16]) => (crate::spec::packus_epi16(a@, b@));
    |k| { if k < 8 { clamp_x(sw16_x(&a, k), 0, 255) as u8 } else { clamp_x(sw16_x(&b, k - 8), 0, 255) as u8 } }; (true));
model!(add_epi32(a: [u8; 16], b: [u8; 16]) => (crate::spec::add_epi32(a@, b@)); |k| { put32_x(w32_x(&a, k / 4) + w32_x(&b, k / 4), k) }; (true));
model!(sub_epi32(a: [u8; 16], b: [u8; 16]) => (crate::spec::sub_epi32(a@, b@)); |k| { put32_x(w32_x(&a, k / 4) - w32_x(&b, k / 4), k) }; (true));
model!(srai_epi32(a: [u8; 16], n: u32) => (crate::spec::srai_epi32(a@, n as nat)); |k| { put32_x(sra32_x(sw32_x(&a, k / 4), n), k) }; (n < 32));
model!(packs_epi32(a: [u8; 16], b: [u8; 16]) => (crate::spec::packs_epi32(a@, b@));
    |k| { if k < 8 { put16_x(clamp32_x(sw32_x(&a, k / 2), -32768, 32767) as i32, k) } else { put16_x(clamp32_x(sw32_x(&b, k / 2 - 4), -32768, 32767) as i32, k) } }; (true));

pub fn w32_x(a: &[u8; 16], j: usize) -> (r: i64) requires j < 4, ensures r == w32(a@, j as int), 0 <= r < 4294967296 {
    a[4 * j] as i64 + 256 * a[4 * j + 1] as i64 + 65536 * a[4 * j + 2] as i64 + 16777216 * a[4 * j + 3] as i64
}

pub fn sw32_x(a: &[u8; 16], j: usize) -> (r: i64) requires j < 4, ensures r == sw32(a@, j as int), -2147483648 <= r < 2147483648 {
    let w = w32_x(a, j);
    if w < 2147483648 { w } else { w - 4294967296 }
}

pub fn clamp32_x(x: i64, lo: i64, hi: i64) -> (r: i64) requires lo <= hi, ensures r == clamp(x as int, lo as int, hi as int), lo <= r <= hi {
    if x < lo { lo } else if x > hi { hi } else { x }
}

pub fn put32_x(x: i64, k: usize) -> (r: u8) requires -4294967296 <= x < 8589934592, ensures r == put32(x as int, k as int) {
    let u = if x < 0 { x + 4294967296 } else if x >= 4294967296 { x - 4294967296 } else { x };
    assert(u as int == (x as int) % 4294967296);
    let q = if k % 4 == 0 { u } else if k % 4 == 1 { u / 256 } else if k % 4 == 2 { u / 65536 } else { u / 16777216 };
    (q % 256) as u8
}

/// floor(x / 2^n) for a signed 32-bit x.
pub fn sra32_x(x: i64, n: u32) -> (r: i64)
    requires -2147483648 <= x < 2147483648, n < 32,
    ensures r == x as int / vstd::arithmetic::power2::pow2(n as nat) as int, -2147483648 <= r < 2147483648,
{
    let d: i64 = 1i64 << n;
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        assert(d == vstd::arithmetic::power2::pow2(n as nat)) by {
            vstd::bits::lemma_u64_shl_is_mul(1, n as u64);
            assert((1i64 << n) as int == (1u64 << (n as u64)) as int) by (bit_vector) requires n < 32u32;
        }
    }
    let q = (x + 2147483648) / d;
    let s = 2147483648i64 / d;
    proof {
        use vstd::arithmetic::power2::*;
        use vstd::arithmetic::div_mod::*;
        let p = pow2(n as nat) as int;
        let m = pow2((31 - n) as nat) as int;
        lemma_pow2_adds(n as nat, (31 - n) as nat);
        lemma_pow2_pos((31 - n) as nat);
        assert(p * m == 2147483648);
        lemma_fundamental_div_mod(x as int, p);
        let t = x as int / p;
        let b = x as int % p;
        assert(x as int + 2147483648 == p * (t + m) + b) by (nonlinear_arith)
            requires x as int == p * t + b, p * m == 2147483648;
        lemma_div_multiples_vanish_fancy(t + m, b, p);
        lemma_div_multiples_vanish_fancy(m, 0, p);
        assert(p * m + 0 == 2147483648);
        lemma_div_is_ordered_by_denominator(x as int + 2147483648, 1, p);
    }
    q - s
}

/// Values 4k .. 4k + 4 of `c` as 32-bit lanes (`x86::load_i32x4`).
pub fn load_i32x4(c: &[i32; 16], k: usize) -> (r: [u8; 16])
    requires k < 4,
    ensures forall|j: int| 0 <= j < 4 ==> #[trigger] crate::spec::sw32(r@, j) == c@[4 * k + j] as int,
{
    let (x0, x1, x2, x3) = (c[4 * k] as i64, c[4 * k + 1] as i64, c[4 * k + 2] as i64, c[4 * k + 3] as i64);
    let r = [put32_x(x0, 0), put32_x(x0, 1), put32_x(x0, 2), put32_x(x0, 3), put32_x(x1, 4), put32_x(x1, 5), put32_x(x1, 6), put32_x(x1, 7),
             put32_x(x2, 8), put32_x(x2, 9), put32_x(x2, 10), put32_x(x2, 11), put32_x(x3, 12), put32_x(x3, 13), put32_x(x3, 14), put32_x(x3, 15)];
    proof {
        crate::spec::lemma_rt32(r@, 0, x0 as int);
        crate::spec::lemma_rt32(r@, 1, x1 as int);
        crate::spec::lemma_rt32(r@, 2, x2 as int);
        crate::spec::lemma_rt32(r@, 3, x3 as int);
        assert forall|j: int| 0 <= j < 4 implies #[trigger] crate::spec::sw32(r@, j) == c@[4 * k + j] as int by {
            if j == 0 {} else if j == 1 {} else if j == 2 {} else {}
        }
    }
    r
}

pub fn mulhi_lane(a: &[u8; 16], b: &[u8; 16], k: usize) -> (r: u8)
    requires k < 16,
    ensures r == put16(sw16(a@, k as int / 2) * sw16(b@, k as int / 2) / 65536, k as int),
{
    let x = sw16_x(a, k / 2) as i64;
    let y = sw16_x(b, k / 2) as i64;
    assert(-1073741824 <= x * y <= 1073741824) by (nonlinear_arith) requires -32768 <= x < 32768, -32768 <= y < 32768;
    let p = x * y;
    let q = ((p + 1073741824) as u64 / 65536) as i64 - 16384;
    put16_x(q as i32, k)
}

pub fn mulhiu_lane(a: &[u8; 16], b: &[u8; 16], k: usize) -> (r: u8)
    requires k < 16,
    ensures r == put16(w16(a@, k as int / 2) * w16(b@, k as int / 2) / 65536, k as int),
{
    let x = w16_x(a, k / 2) as u64;
    let y = w16_x(b, k / 2) as u64;
    assert(x * y < 65536 * 65536) by (nonlinear_arith) requires x < 65536, y < 65536;
    assert(x * y / 65536 < 65536) by (nonlinear_arith) requires x * y < 65536 * 65536;
    put16_x((x * y / 65536) as i32, k)
}

/// x * 2^n mod 2^16 for an unsigned 16-bit x; put16 takes the lane mod 2^16.
pub fn sll16_x(x: i32, n: u32) -> (r: i32)
    requires 0 <= x < 65536, n < 16,
    ensures r == (x as int * vstd::arithmetic::power2::pow2(n as nat) as int) % 65536, 0 <= r < 65536,
{
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(n as nat, 16);
        assert(x as int * vstd::arithmetic::power2::pow2(n as nat) as int <= 65536 * 65536) by (nonlinear_arith)
            requires 0 <= x < 65536, vstd::arithmetic::power2::pow2(n as nat) <= 65536;
        vstd::bits::lemma_u64_shl_is_mul(x as u64, n as u64);
    }
    let y: u64 = (x as u64) << (n as u64);
    let r = y & 0xffff;
    assert(r == y % 65536) by (bit_vector) requires r == y & 0xffff;
    r as i32
}

/// floor(x / 2^n) for an unsigned 32-bit x.
pub fn srl32_x(x: i64, n: u32) -> (r: i64)
    requires 0 <= x < 4294967296, n < 32,
    ensures r == x as int / vstd::arithmetic::power2::pow2(n as nat) as int, 0 <= r < 4294967296,
{
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::bits::lemma_u64_shl_is_mul(1, n as u64);
        vstd::arithmetic::power2::lemma_pow2_pos(n as nat);
        vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x as int, 1, vstd::arithmetic::power2::pow2(n as nat) as int);
    }
    (x as u64 / (1u64 << (n as u64))) as i64
}

/// x * 2^n mod 2^32 for an unsigned 32-bit x.
pub fn sll32_x(x: i64, n: u32) -> (r: i64)
    requires 0 <= x < 4294967296, n < 32,
    ensures r == (x as int * vstd::arithmetic::power2::pow2(n as nat) as int) % 4294967296, 0 <= r < 4294967296,
{
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(n as nat, 32);
        assert(x as int * vstd::arithmetic::power2::pow2(n as nat) as int <= 4294967295 * 4294967295) by (nonlinear_arith)
            requires 0 <= x <= 4294967295, vstd::arithmetic::power2::pow2(n as nat) <= 4294967295;
        vstd::bits::lemma_u64_shl_is_mul(x as u64, n as u64);
    }
    let y: u64 = (x as u64) << (n as u64);
    let r = y & 0xffff_ffff;
    assert(r == y % 4294967296) by (bit_vector) requires r == y & 0xffff_ffff;
    r as i64
}

/// floor(x / 2^n) for an unsigned 16-bit x.
pub fn srl16_x(x: i32, n: u32) -> (r: i32)
    requires 0 <= x < 65536, n < 16,
    ensures r == x as int / vstd::arithmetic::power2::pow2(n as nat) as int, 0 <= r < 65536,
{
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::bits::lemma_u32_shl_is_mul(1, n);
        vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x as int, 1, vstd::arithmetic::power2::pow2(n as nat) as int);
    }
    (x as u32 / (1u32 << n)) as i32
}

} // verus!
