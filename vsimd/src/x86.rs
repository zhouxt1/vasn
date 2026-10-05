//! SSE2 intrinsics, trusted: each is `external_body`, and its contract says
//! it computes one function of `spec.rs`. Those contracts are the whole
//! trusted base of this crate, and `tests/validate.rs` checks each against
//! the CPU, through the proved model of `model.rs`. Loads and stores are
//! unchecked: they are in bounds by their preconditions (`i + 16 <= len`
//! and the like), which Verus checks at every verified call site; a caller
//! that is not verified must meet them itself.
use vstd::prelude::*;
use crate::spec;
use core::arch::x86_64::*;
pub use core::arch::x86_64::__m128i;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM128i(__m128i);

/// Byte `k` (0..16, lowest first) of a vector, as the register holds it.
pub uninterp spec fn byte(v: __m128i, k: int) -> u8;

/// The vector's 16 bytes.
pub open spec fn v8(v: __m128i) -> Seq<u8> { Seq::new(16, |k: int| byte(v, k)) }

/// Lane facts in the contracts (on `v8`) reach `byte`: `broadcast use` it.
pub broadcast proof fn lemma_byte(v: __m128i, k: int)
    requires 0 <= k < 16,
    ensures #[trigger] byte(v, k) == v8(v)[k],
{}

// -------------------------------------------------------- in and out

#[verifier::external_body]
#[inline(always)]
pub fn from_bytes(a: [u8; 16]) -> (r: __m128i)
    ensures v8(r) == a@,
{
    unsafe { _mm_loadu_si128(a.as_ptr() as *const __m128i) }
}

#[verifier::external_body]
#[inline(always)]
pub fn to_bytes(v: __m128i) -> (r: [u8; 16])
    ensures r@ == v8(v),
{
    let mut a = [0u8; 16];
    unsafe { _mm_storeu_si128(a.as_mut_ptr() as *mut __m128i, v) };
    a
}

/// Bytes `i..i + 16` of `s`.
#[verifier::external_body]
#[inline(always)]
pub fn loadu(s: &[u8], i: usize) -> (r: __m128i)
    requires i + 16 <= s@.len(),
    ensures v8(r) == s@.subrange(i as int, i as int + 16),
{
    // In bounds by the precondition, which Verus checks at every call.
    unsafe { _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i) }
}

/// Write the vector at bytes `i..i + 16` of `s`.
#[verifier::external_body]
#[inline(always)]
pub fn storeu(s: &mut Vec<u8>, i: usize, v: __m128i)
    requires i + 16 <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|j: int| 0 <= j < final(s)@.len() ==> #[trigger] final(s)@[j] ==
            if i <= j < i + 16 { v8(v)[j - i] } else { old(s)@[j] },
{
    unsafe { _mm_storeu_si128(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// Write the vector at bytes `i..i + 16` of the slice `s`.
#[verifier::external_body]
#[inline(always)]
pub fn storeu_s(s: &mut [u8], i: usize, v: __m128i)
    requires i + 16 <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|j: int| 0 <= j < final(s)@.len() ==> #[trigger] final(s)@[j] ==
            if i <= j < i + 16 { v8(v)[j - i] } else { old(s)@[j] },
{
    unsafe { _mm_storeu_si128(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// `s[i..i + 4]`, four u32s (little-endian).
#[verifier::external_body]
#[inline(always)]
pub fn loadu_u32(s: &[u32], i: usize) -> (r: __m128i)
    requires i + 4 <= s@.len(),
    ensures v8(r) == spec::u32s(s@, i as int),
{
    // In bounds by the precondition, which Verus checks at every call.
    unsafe { _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i) }
}

/// Write the vector's four 32-bit lanes at `s[i..i + 4]`.
#[verifier::external_body]
#[inline(always)]
pub fn storeu_u32(s: &mut Vec<u32>, i: usize, v: __m128i)
    requires i + 4 <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|j: int| 0 <= j < final(s)@.len() ==> #[trigger] final(s)@[j] ==
            if i <= j < i + 4 { spec::w32(v8(v), j - i) as u32 } else { old(s)@[j] },
{
    unsafe { _mm_storeu_si128(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// Bytes `i..i + 8` of `s` into the low half; the high half is zero.
#[verifier::external_body]
#[inline(always)]
pub fn loadl(s: &[u8], i: usize) -> (r: __m128i)
    requires i + 8 <= s@.len(),
    ensures v8(r) == spec::lo8(s@.subrange(i as int, i as int + 8)),
{
    unsafe { _mm_loadl_epi64(s.as_ptr().add(i) as *const __m128i) }
}

/// Write the low half of the vector at bytes `i..i + 8` of `s`.
#[verifier::external_body]
#[inline(always)]
pub fn storel(s: &mut Vec<u8>, i: usize, v: __m128i)
    requires i + 8 <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|j: int| 0 <= j < final(s)@.len() ==> #[trigger] final(s)@[j] ==
            if i <= j < i + 8 { v8(v)[j - i] } else { old(s)@[j] },
{
    unsafe { _mm_storel_epi64(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// Write the high half of the vector at bytes `i..i + 8` of `s`.
#[verifier::external_body]
#[inline(always)]
pub fn storeh(s: &mut Vec<u8>, i: usize, v: __m128i)
    requires i + 8 <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|j: int| 0 <= j < final(s)@.len() ==> #[trigger] final(s)@[j] ==
            if i <= j < i + 8 { v8(v)[j - i + 8] } else { old(s)@[j] },
{
    unsafe { _mm_storeh_pd(s.as_mut_ptr().add(i) as *mut f64, _mm_castsi128_pd(v)) }
}

/// Values 4k .. 4k + 4 of `c`, one per 32-bit lane.
#[verifier::external_body]
#[inline(always)]
pub fn load_i32x4(c: &[i32; 16], k: usize) -> (r: __m128i)
    requires k < 4,
    ensures forall|j: int| 0 <= j < 4 ==> #[trigger] spec::sw32(v8(r), j) == c@[4 * k + j] as int,
{
    unsafe { _mm_loadu_si128(c.as_ptr().add(4 * k) as *const __m128i) }
}

/// Bytes `i..i + 4` of `s` into the lowest lane; the rest is zero.
#[verifier::external_body]
#[inline(always)]
pub fn load4(s: &[u8], i: usize) -> (r: __m128i)
    requires i + 4 <= s@.len(),
    ensures v8(r) == spec::lo4(s@.subrange(i as int, i as int + 4)),
{
    unsafe { _mm_cvtsi32_si128((s.as_ptr().add(i) as *const i32).read_unaligned()) }
}

/// Write the vector's bytes `4 * lane .. 4 * lane + 4` at bytes `i..i + 4` of `s`.
#[verifier::external_body]
#[inline(always)]
pub fn store4(s: &mut Vec<u8>, i: usize, v: __m128i, lane: usize)
    requires i + 4 <= old(s)@.len(), lane < 4,
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|j: int| 0 <= j < final(s)@.len() ==> #[trigger] final(s)@[j] ==
            if i <= j < i + 4 { v8(v)[4 * lane + j - i] } else { old(s)@[j] },
{
    let x = unsafe {
        match lane {
            0 => _mm_cvtsi128_si32(v),
            1 => _mm_cvtsi128_si32(_mm_srli_si128::<4>(v)),
            2 => _mm_cvtsi128_si32(_mm_srli_si128::<8>(v)),
            _ => _mm_cvtsi128_si32(_mm_srli_si128::<12>(v)),
        }
    };
    unsafe { (s.as_mut_ptr().add(i) as *mut i32).write_unaligned(x) }
}

// ------------------------------------------------------------ constants

#[verifier::external_body]
#[inline(always)]
pub fn setzero() -> (r: __m128i) ensures v8(r) == spec::set1_epi8(0) { unsafe { _mm_setzero_si128() } }

#[verifier::external_body]
#[inline(always)]
pub fn set1_epi8(x: u8) -> (r: __m128i) ensures v8(r) == spec::set1_epi8(x) { unsafe { _mm_set1_epi8(x as i8) } }

#[verifier::external_body]
#[inline(always)]
pub fn set1_epi16(x: u16) -> (r: __m128i) ensures v8(r) == spec::set1_epi16(x) { unsafe { _mm_set1_epi16(x as i16) } }

#[verifier::external_body]
#[inline(always)]
pub fn set1_epi32(x: u32) -> (r: __m128i) ensures v8(r) == spec::set1_epi32(x) { unsafe { _mm_set1_epi32(x as i32) } }

// ------------------------------------------------------ two operands

macro_rules! binop {
    ($name:ident, $intr:ident) => {
        verus! {
        #[verifier::external_body]
        #[inline(always)]
        pub fn $name(a: __m128i, b: __m128i) -> (r: __m128i)
            ensures v8(r) == spec::$name(v8(a), v8(b)),
        {
            unsafe { $intr(a, b) }
        }
        }
    };
}

binop!(subs_epu8, _mm_subs_epu8);
binop!(adds_epu8, _mm_adds_epu8);
binop!(max_epu8, _mm_max_epu8);
binop!(cmpeq_epi8, _mm_cmpeq_epi8);
binop!(and_si128, _mm_and_si128);
binop!(or_si128, _mm_or_si128);
binop!(xor_si128, _mm_xor_si128);
binop!(andnot_si128, _mm_andnot_si128);
binop!(adds_epi8, _mm_adds_epi8);
binop!(subs_epi8, _mm_subs_epi8);
binop!(add_epi8, _mm_add_epi8);
binop!(sub_epi8, _mm_sub_epi8);
binop!(avg_epu8, _mm_avg_epu8);
binop!(unpacklo_epi8, _mm_unpacklo_epi8);
binop!(unpackhi_epi8, _mm_unpackhi_epi8);
binop!(packs_epi16, _mm_packs_epi16);
binop!(unpacklo_epi16, _mm_unpacklo_epi16);
binop!(unpackhi_epi16, _mm_unpackhi_epi16);
binop!(unpacklo_epi32, _mm_unpacklo_epi32);
binop!(unpackhi_epi32, _mm_unpackhi_epi32);
binop!(unpacklo_epi64, _mm_unpacklo_epi64);
binop!(unpackhi_epi64, _mm_unpackhi_epi64);
binop!(sub_epi16, _mm_sub_epi16);
binop!(packus_epi16, _mm_packus_epi16);
binop!(add_epi32, _mm_add_epi32);
binop!(sub_epi32, _mm_sub_epi32);
binop!(packs_epi32, _mm_packs_epi32);
binop!(add_epi16, _mm_add_epi16);
binop!(mulhi_epi16, _mm_mulhi_epi16);
binop!(mulhi_epu16, _mm_mulhi_epu16);
binop!(adds_epu16, _mm_adds_epu16);
binop!(subs_epu16, _mm_subs_epu16);

// ------------------------------------------------------ shifts by a constant

macro_rules! shift {
    ($name:ident, $spec:ident, $intr:ident, $n:literal) => {
        verus! {
        #[verifier::external_body]
        #[inline(always)]
        pub fn $name(a: __m128i) -> (r: __m128i)
            ensures v8(r) == spec::$spec(v8(a), $n),
        {
            unsafe { $intr::<$n>(a) }
        }
        }
    };
}

shift!(srai_epi16_7, srai_epi16, _mm_srai_epi16, 7);
shift!(srai_epi16_11, srai_epi16, _mm_srai_epi16, 11);
shift!(srli_epi16_1, srli_epi16, _mm_srli_epi16, 1);
shift!(srai_epi16_6, srai_epi16, _mm_srai_epi16, 6);
shift!(srli_epi16_6, srli_epi16, _mm_srli_epi16, 6);
shift!(srli_epi16_4, srli_epi16, _mm_srli_epi16, 4);
shift!(srli_epi16_8, srli_epi16, _mm_srli_epi16, 8);
shift!(slli_epi16_8, slli_epi16, _mm_slli_epi16, 8);
shift!(srli_epi32_8, srli_epi32, _mm_srli_epi32, 8);
shift!(slli_epi32_16, slli_epi32, _mm_slli_epi32, 16);
shift!(srai_epi32_3, srai_epi32, _mm_srai_epi32, 3);
shift!(srai_epi32_16, srai_epi32, _mm_srai_epi32, 16);

/// Logical shift right of each 16-bit lane, by a count known only at run
/// time (`_mm_srl_epi16`, the count in the low 64 bits of a vector).
#[verifier::external_body]
#[inline(always)]
pub fn srl_epi16(a: __m128i, n: u32) -> (r: __m128i)
    requires n < 16,
    ensures v8(r) == spec::srli_epi16(v8(a), n as nat),
{
    unsafe { _mm_srl_epi16(a, _mm_cvtsi32_si128(n as i32)) }
}

} // verus!
