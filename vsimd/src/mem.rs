//! Scalar loads and stores, unchecked, as x86.rs's vector ones: trusted
//! (`external_body`), and in bounds by their preconditions, which Verus
//! checks at every verified call site. They save the bounds checks that
//! the compiler cannot see are redundant.
use vstd::prelude::*;

verus! {

/// `s[i]`.
#[verifier::external_body]
#[inline(always)]
pub fn get<T: Copy>(s: &[T], i: usize) -> (r: T)
    requires i < s@.len(),
    ensures r == s@[i as int],
{
    // In bounds by the precondition.
    unsafe { *s.get_unchecked(i) }
}

/// `&s[i]`.
#[verifier::external_body]
#[inline(always)]
pub fn get_ref<T>(s: &[T], i: usize) -> (r: &T)
    requires i < s@.len(),
    ensures *r == s@[i as int],
{
    // In bounds by the precondition.
    unsafe { s.get_unchecked(i) }
}

/// `a[i]`.
#[verifier::external_body]
#[inline(always)]
pub fn aget<T: Copy, const N: usize>(a: &[T; N], i: usize) -> (r: T)
    requires i < N,
    ensures r == a@[i as int],
{
    // In bounds by the precondition.
    unsafe { *a.get_unchecked(i) }
}

/// `a[i] = v`.
#[verifier::external_body]
#[inline(always)]
pub fn aset<T, const N: usize>(a: &mut [T; N], i: usize, v: T)
    requires i < N,
    ensures final(a)@ == old(a)@.update(i as int, v),
{
    // In bounds by the precondition.
    unsafe { *a.get_unchecked_mut(i) = v }
}

/// `s[i] = v`.
#[verifier::external_body]
#[inline(always)]
pub fn vset<T>(s: &mut Vec<T>, i: usize, v: T)
    requires i < old(s)@.len(),
    ensures final(s)@ == old(s)@.update(i as int, v),
{
    // In bounds by the precondition.
    unsafe { *s.get_unchecked_mut(i) = v }
}

/// `s[i] = v`, for a slice.
#[verifier::external_body]
#[inline(always)]
pub fn sset<T>(s: &mut [T], i: usize, v: T)
    requires i < old(s)@.len(),
    ensures final(s)@ == old(s)@.update(i as int, v),
{
    // In bounds by the precondition.
    unsafe { *s.get_unchecked_mut(i) = v }
}

/// `s[i..i + 4]` = the four little-endian bytes of `v`, in one store.
#[verifier::external_body]
#[inline(always)]
pub fn sset_u32le(s: &mut [u8], i: usize, v: u32)
    requires i + 4 <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|j: int| 0 <= j < old(s)@.len() ==> #[trigger] final(s)@[j] ==
            if i <= j < i + 4 { ((v >> (8 * (j - i)) as u32) & 0xffu32) as u8 } else { old(s)@[j] },
{
    // In bounds by the precondition.
    unsafe { (s.as_mut_ptr().add(i) as *mut u32).write_unaligned(v.to_le()) }
}

/// `v[dst..dst + n] = v[src..src + n]` (a memmove: the ranges may overlap).
#[verifier::external_body]
#[inline(always)]
pub fn copy_within(v: &mut Vec<u8>, src: usize, dst: usize, n: usize)
    requires src + n <= old(v)@.len(), dst + n <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|j: int| 0 <= j < old(v)@.len() ==> #[trigger] final(v)@[j] ==
            if dst <= j < dst + n { old(v)@[src + j - dst] } else { old(v)@[j] },
{
    v.copy_within(src..src + n, dst)
}

} // verus!
