//! Idioms: short sequences of intrinsics that compute something the
//! instruction set has no single instruction for, proved lane by lane.
//! Codecs use them for what crypto code rarely needs: comparisons made into
//! masks, saturating signed bytes, byte shifts done in 16-bit lanes.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::spec::{sb, ub, w16, sw16, put16};
use crate::x86::*;

verus! {

pub open spec fn absd8(a: u8, b: u8) -> int { if a >= b { a - b } else { b - a } }

proof fn lemma_or_zero(x: u8)
    ensures x | 0u8 == x, 0u8 | x == x,
{
    assert(x | 0u8 == x && 0u8 | x == x) by (bit_vector);
}

pub proof fn lemma_and_mask(x: u8)
    ensures x & 255u8 == x, x & 0u8 == 0, 255u8 & x == x, 0u8 & x == 0,
        !255u8 & x == 0, !0u8 & x == x,
{
    assert(x & 255u8 == x && x & 0u8 == 0 && 255u8 & x == x && 0u8 & x == 0 && !255u8 & x == 0 && !0u8 & x == x) by (bit_vector);
}

/// |a - b| per byte: `subs(a, b) | subs(b, a)`, one of which is 0.
#[inline(always)]
pub fn absdiff_epu8(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures forall|k: int| 0 <= k < 16 ==> #[trigger] byte(r, k) as int == absd8(byte(a, k), byte(b, k)),
{
    let x = subs_epu8(a, b);
    let y = subs_epu8(b, a);
    let r = or_si128(x, y);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] byte(r, k) as int == absd8(byte(a, k), byte(b, k)) by {
            assert(v8(r)[k] == byte(r, k) && v8(x)[k] == byte(x, k) && v8(y)[k] == byte(y, k));
            assert(v8(a)[k] == byte(a, k) && v8(b)[k] == byte(b, k));
            lemma_or_zero(byte(x, k));
            lemma_or_zero(byte(y, k));
        }
    }
    r
}

/// 255 where a <= t, else 0: `cmpeq(subs(a, t), 0)`.
#[inline(always)]
pub fn le_mask_epu8(a: __m128i, t: __m128i) -> (r: __m128i)
    ensures forall|k: int| 0 <= k < 16 ==> #[trigger] byte(r, k) == if byte(a, k) <= byte(t, k) { 255u8 } else { 0u8 },
{
    let d = subs_epu8(a, t);
    let z = setzero();
    let r = cmpeq_epi8(d, z);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] byte(r, k) == if byte(a, k) <= byte(t, k) { 255u8 } else { 0u8 } by {
            assert(v8(r)[k] == byte(r, k) && v8(d)[k] == byte(d, k) && v8(z)[k] == byte(z, k));
            assert(v8(a)[k] == byte(a, k) && v8(t)[k] == byte(t, k));
        }
    }
    r
}

/// Each byte halved, rounding down: a 16-bit shift of the bytes with their
/// low bits cleared, so no bit crosses into the byte below.
#[inline(always)]
pub fn half_epu8(a: __m128i) -> (r: __m128i)
    ensures forall|k: int| 0 <= k < 16 ==> #[trigger] byte(r, k) == byte(a, k) / 2,
{
    let fe = set1_epi8(0xfe);
    let c = and_si128(a, fe);
    let r = srli_epi16_1(c);
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        assert forall|k: int| 0 <= k < 16 implies #[trigger] byte(r, k) == byte(a, k) / 2 by {
            let j = k / 2;
            assert(v8(r)[k] == byte(r, k));
            assert(v8(c)[2 * j] == byte(c, 2 * j) && v8(c)[2 * j + 1] == byte(c, 2 * j + 1));
            assert(v8(a)[2 * j] == byte(a, 2 * j) && v8(a)[2 * j + 1] == byte(a, 2 * j + 1));
            assert(v8(fe)[2 * j] == 0xfeu8 && v8(fe)[2 * j + 1] == 0xfeu8);
            let lo = byte(a, 2 * j);
            let hi = byte(a, 2 * j + 1);
            assert(lo & 0xfeu8 == lo - lo % 2 && hi & 0xfeu8 == hi - hi % 2) by (bit_vector);
            let cl = (lo - lo % 2) as int;
            let ch = (hi - hi % 2) as int;
            assert(w16(v8(c), j) == cl + 256 * ch);
            assert((cl + 256 * ch) / 2 == cl / 2 + 128 * ch);
            assert(ch % 2 == 0);
            assert((cl / 2 + 128 * ch) % 65536 == cl / 2 + 128 * ch);
            assert((cl / 2 + 128 * ch) % 256 == cl / 2);
            assert((cl / 2 + 128 * ch) / 256 == ch / 2);
            if k % 2 == 0 { assert(k == 2 * j); } else { assert(k == 2 * j + 1); }
        }
    }
    r
}

/// Each signed byte shifted right by 3 (floor division by 8): the byte
/// into the high half of a 16-bit lane, an arithmetic shift by 11, packed
/// back.
#[inline(always)]
pub fn srai3_epi8(a: __m128i) -> (r: __m128i)
    ensures forall|k: int| 0 <= k < 16 ==> #[trigger] byte(r, k) == ub(sb(byte(a, k)) / 8),
{
    let z = setzero();
    let lo = unpacklo_epi8(z, a);
    let hi = unpackhi_epi8(z, a);
    let lo2 = srai_epi16_11(lo);
    let hi2 = srai_epi16_11(hi);
    let r = packs_epi16(lo2, hi2);
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        assert forall|k: int| 0 <= k < 16 implies #[trigger] byte(r, k) == ub(sb(byte(a, k)) / 8) by {
            assert(v8(r)[k] == byte(r, k) && v8(a)[k] == byte(a, k));
            let (s, j) = if k < 8 { (lo, k) } else { (hi, k - 8) };
            let s2 = if k < 8 { lo2 } else { hi2 };
            assert(v8(s)[2 * j] == byte(s, 2 * j) && v8(s)[2 * j + 1] == byte(s, 2 * j + 1));
            assert(v8(s2)[2 * j] == byte(s2, 2 * j) && v8(s2)[2 * j + 1] == byte(s2, 2 * j + 1));
            assert(v8(z)[j] == 0u8 && v8(z)[8 + j] == 0u8);
            assert(v8(a)[j] == byte(a, j) && v8(a)[8 + j] == byte(a, 8 + j));
            let b = byte(a, k);
            assert(byte(s, 2 * j) == 0u8 && byte(s, 2 * j + 1) == b);
            assert(w16(v8(s), j) == 256 * b as int);
            assert(sw16(v8(s), j) == 256 * sb(b));
            let q = sb(b) / 8;
            assert((256 * sb(b)) / 2048 == q);
            assert(-16 <= q < 16);
            assert(sw16(v8(s2), j) == q) by {
                assert(v8(s2)[2 * j] == put16(q, 2 * j) && v8(s2)[2 * j + 1] == put16(q, 2 * j + 1));
                assert((2 * j) % 2 == 0 && (2 * j + 1) % 2 == 1 && (2 * j) / 2 == j && (2 * j + 1) / 2 == j);
            }
        }
    }
    r
}

/// An 8 x 8 byte transpose: rows r[0..8], their bytes `off .. off + 8`
/// (off 0 or 8), into four vectors of two columns each: byte m of c[t] is
/// row m % 8, column 2t + m / 8.
pub fn transpose8x8(r: &[__m128i; 8], hi: bool) -> (c: [__m128i; 4])
    ensures forall|t: int, m: int| 0 <= t < 4 && 0 <= m < 16 ==>
        #[trigger] byte(c@[t], m) == byte(r@[m % 8], (if hi { 8int } else { 0 }) + 2 * t + m / 8),
{
    let (a0, a1, a2, a3) = if hi {
        (unpackhi_epi8(r[0], r[1]), unpackhi_epi8(r[2], r[3]), unpackhi_epi8(r[4], r[5]), unpackhi_epi8(r[6], r[7]))
    } else {
        (unpacklo_epi8(r[0], r[1]), unpacklo_epi8(r[2], r[3]), unpacklo_epi8(r[4], r[5]), unpacklo_epi8(r[6], r[7]))
    };
    let ghost off: int = if hi { 8 } else { 0 };
    proof {
        let a = seq![a0, a1, a2, a3];
        assert forall|p: int, k: int| 0 <= p < 4 && 0 <= k < 16 implies #[trigger] byte(a[p], k) == byte(r@[2 * p + k % 2], off + k / 2) by {
            assert(v8(a[p])[k] == byte(a[p], k));
            assert(v8(r@[2 * p])[off + k / 2] == byte(r@[2 * p], off + k / 2));
            assert(v8(r@[2 * p + 1])[off + k / 2] == byte(r@[2 * p + 1], off + k / 2));
        }
    }
    let b0 = unpacklo_epi16(a0, a1);
    let b1 = unpackhi_epi16(a0, a1);
    let b2 = unpacklo_epi16(a2, a3);
    let b3 = unpackhi_epi16(a2, a3);
    proof {
        let a = seq![a0, a1, a2, a3];
        let b = seq![b0, b1, b2, b3];
        // b[2g + h] holds rows 4g .. 4g + 4, columns 4h .. 4h + 4.
        assert forall|q: int, k: int| 0 <= q < 4 && 0 <= k < 16 implies
            #[trigger] byte(b[q], k) == byte(r@[4 * (q / 2) + k % 4], off + 4 * (q % 2) + k / 4) by {
            let (x, y) = (a[2 * (q / 2)], a[2 * (q / 2) + 1]);
            let src = (if q % 2 == 1 { 8int } else { 0 }) + (k / 2 / 2) * 2 + k % 2;
            assert(v8(b[q])[k] == byte(b[q], k));
            assert(v8(x)[src] == byte(x, src) && v8(y)[src] == byte(y, src));
            assert(byte(x, src) == byte(r@[2 * (2 * (q / 2)) + src % 2], off + src / 2));
            assert(byte(y, src) == byte(r@[2 * (2 * (q / 2) + 1) + src % 2], off + src / 2));
        }
    }
    let c0 = unpacklo_epi32(b0, b2);
    let c1 = unpackhi_epi32(b0, b2);
    let c2 = unpacklo_epi32(b1, b3);
    let c3 = unpackhi_epi32(b1, b3);
    let c = [c0, c1, c2, c3];
    proof {
        let b = seq![b0, b1, b2, b3];
        assert forall|t: int, m: int| 0 <= t < 4 && 0 <= m < 16 implies
            #[trigger] byte(c@[t], m) == byte(r@[m % 8], off + 2 * t + m / 8) by {
            let (x, y) = (b[t / 2], b[t / 2 + 2]);
            let src = (if t % 2 == 1 { 8int } else { 0 }) + (m / 4 / 2) * 4 + m % 4;
            assert(v8(c@[t])[m] == byte(c@[t], m));
            assert(v8(x)[src] == byte(x, src) && v8(y)[src] == byte(y, src));
            assert(byte(x, src) == byte(r@[4 * ((t / 2) / 2) + src % 4], off + 4 * ((t / 2) % 2) + src / 4));
            assert(byte(y, src) == byte(r@[4 * ((t / 2 + 2) / 2) + src % 4], off + 4 * ((t / 2 + 2) % 2) + src / 4));
        }
    }
    c
}

/// Sixteen rows (bytes 0 .. 8 of each) as eight columns of 16 lanes:
/// byte j of c[k] is byte k of row j.
pub fn transpose16x8(lo: &[__m128i; 8], hi: &[__m128i; 8]) -> (c: [__m128i; 8])
    ensures forall|k: int, j: int| 0 <= k < 8 && 0 <= j < 16 ==>
        #[trigger] byte(c@[k], j) == if j < 8 { byte(lo@[j], k) } else { byte(hi@[j - 8], k) },
{
    let x = transpose8x8(lo, false);
    let y = transpose8x8(hi, false);
    let c = [unpacklo_epi64(x[0], y[0]), unpackhi_epi64(x[0], y[0]), unpacklo_epi64(x[1], y[1]), unpackhi_epi64(x[1], y[1]),
             unpacklo_epi64(x[2], y[2]), unpackhi_epi64(x[2], y[2]), unpacklo_epi64(x[3], y[3]), unpackhi_epi64(x[3], y[3])];
    proof {
        assert forall|k: int, j: int| 0 <= k < 8 && 0 <= j < 16 implies
            #[trigger] byte(c@[k], j) == if j < 8 { byte(lo@[j], k) } else { byte(hi@[j - 8], k) } by {
            let t = k / 2;
            let src = (if k % 2 == 1 { 8int } else { 0 }) + j % 8;
            assert(v8(c@[k])[j] == byte(c@[k], j));
            assert(v8(x@[t])[src] == byte(x@[t], src) && v8(y@[t])[src] == byte(y@[t], src));
            assert(byte(x@[t], src) == byte(lo@[src % 8], 2 * t + src / 8));
            assert(byte(y@[t], src) == byte(hi@[src % 8], 2 * t + src / 8));
        }
    }
    c
}

/// `transpose16x8` of either half of each row: byte j of c[k] is byte
/// k (or 8 + k) of row j.
pub fn transpose16x8h(lo: &[__m128i; 8], hi: &[__m128i; 8], upper: bool) -> (c: [__m128i; 8])
    ensures forall|k: int, j: int| 0 <= k < 8 && 0 <= j < 16 ==>
        #[trigger] byte(c@[k], j) == if j < 8 { byte(lo@[j], (if upper { 8int } else { 0 }) + k) } else { byte(hi@[j - 8], (if upper { 8int } else { 0 }) + k) },
{
    let x = transpose8x8(lo, upper);
    let y = transpose8x8(hi, upper);
    let c = [unpacklo_epi64(x[0], y[0]), unpackhi_epi64(x[0], y[0]), unpacklo_epi64(x[1], y[1]), unpackhi_epi64(x[1], y[1]),
             unpacklo_epi64(x[2], y[2]), unpackhi_epi64(x[2], y[2]), unpacklo_epi64(x[3], y[3]), unpackhi_epi64(x[3], y[3])];
    proof {
        let off: int = if upper { 8 } else { 0 };
        assert forall|k: int, j: int| 0 <= k < 8 && 0 <= j < 16 implies
            #[trigger] byte(c@[k], j) == if j < 8 { byte(lo@[j], off + k) } else { byte(hi@[j - 8], off + k) } by {
            let t = k / 2;
            let src = (if k % 2 == 1 { 8int } else { 0 }) + j % 8;
            assert(v8(c@[k])[j] == byte(c@[k], j));
            assert(v8(x@[t])[src] == byte(x@[t], src) && v8(y@[t])[src] == byte(y@[t], src));
            assert(byte(x@[t], src) == byte(lo@[src % 8], off + 2 * t + src / 8));
            assert(byte(y@[t], src) == byte(hi@[src % 8], off + 2 * t + src / 8));
        }
    }
    c
}

} // verus!
