//! The terminal formats X.691 encodes the same way in both variants, lifted
//! from UPER: the n-bit field, BOOLEAN, a constrained whole number whose range
//! is at most 255 (11.5.7.1: "a bit-field of the minimum size for the range",
//! as in UPER), and the octet as an element of a list.
//!
//! Each is UPER's format under `lift`, so its proof is UPER's plus one
//! application of `lemma_lift_format`, and the exec reads and writes are
//! UPER's cursor methods: `lift_dec(d)(r.at())` is `d(r.rem())`.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::aper::format::*;
use crate::uper::prim as up;
use crate::uper::term as ut;

verus! {

broadcast use {format_steps, map_steps};

// ------------------------------------------------------- unsigned n-bit field

pub open spec fn uint_wf(n: nat) -> Wf<u64> { up::uint_wf(n) }
pub open spec fn uint_enc(n: nat) -> Enc<u64> { lift_enc(up::uint_enc(n)) }
pub open spec fn uint_dec(n: nat) -> Dec<u64> { lift_dec(up::uint_dec(n)) }

pub proof fn lemma_uint_format(n: nat)
    requires 1 <= n <= 64,
    ensures is_format(uint_wf(n), uint_enc(n), uint_dec(n)),
{
    up::lemma_uint_format(n);
    lemma_lift_format(up::uint_wf(n), up::uint_enc(n), up::uint_dec(n));
}

pub proof fn lemma_uint_enc_len(n: nat, pos: nat, v: u64)
    ensures uint_enc(n)(pos, v).len() == n,
{
}

// ------------------------------------------------------------------ BOOLEAN

pub open spec fn bool_wf() -> Wf<bool> { ut::bool_wf() }
pub open spec fn bool_enc() -> Enc<bool> { lift_enc(ut::bool_enc()) }
pub open spec fn bool_dec() -> Dec<bool> { lift_dec(ut::bool_dec()) }

pub proof fn lemma_bool_format()
    ensures is_format(bool_wf(), bool_enc(), bool_dec()),
{
    ut::lemma_bool_format();
    lemma_lift_format(ut::bool_wf(), ut::bool_enc(), ut::bool_dec());
}

pub proof fn lemma_bool_wf_all(b: bool)
    ensures bool_wf()(b),
{
    ut::lemma_bool_wf_all(b);
}

pub proof fn lemma_bool_enc_len(pos: nat, b: bool)
    ensures bool_enc()(pos, b).len() == 1,
{
    ut::lemma_bool_enc_len(b);
}

/// A `bool` encodes to the one-element sequence holding it, at any position.
pub proof fn lemma_bool_enc_seq(b: bool)
    ensures
        ut::bool_enc()(b) =~= seq![b],
        forall|pos: nat| #[trigger] bool_enc()(pos, b) =~= seq![b],
{
    ut::lemma_bool_enc_seq(b);
}

/// A `bool` decode hands back the leading bit itself.
pub proof fn lemma_bool_dec_bit(i: In)
    requires i.1.len() >= 1,
    ensures bool_dec()(i) == Some::<(bool, nat, Flg)>((i.1[0], 1nat, Flg::SameVer)),
{
    ut::lemma_bool_dec_bit(i.1);
}

pub proof fn lemma_bool_dec_same(i: In)
    ensures bool_dec()(i) is Some ==> bool_dec()(i).unwrap().2 is SameVer,
{
    ut::lemma_bool_dec_same(i.1);
}

// ------------------------------------------ INTEGER (lb..ub), 1 < range <= 255
//
// UPER's format is correct for any range. The ALIGNED variant uses it only up
// to 255 (11.5.7.1); `cwn` in `aper::intx` is the rest.

pub open spec fn int_range_wf(lb: int, ub: int, n: nat) -> Wf<i64> { ut::int_range_wf(lb, ub, n) }
pub open spec fn int_range_enc(lb: int, ub: int, n: nat) -> Enc<i64> {
    lift_enc(ut::int_range_enc(lb, ub, n))
}
pub open spec fn int_range_dec(lb: int, ub: int, n: nat) -> Dec<i64> {
    lift_dec(ut::int_range_dec(lb, ub, n))
}

pub proof fn lemma_int_range_format(lb: int, ub: int, n: nat)
    requires
        1 <= n <= 56,
        lb < ub,
        ub - lb < p2(n),
        i64::MIN <= lb,
        ub <= i64::MAX,
    ensures is_format(int_range_wf(lb, ub, n), int_range_enc(lb, ub, n), int_range_dec(lb, ub, n)),
{
    ut::lemma_int_range_format(lb, ub, n);
    lemma_lift_format(ut::int_range_wf(lb, ub, n), ut::int_range_enc(lb, ub, n),
                      ut::int_range_dec(lb, ub, n));
}

pub proof fn lemma_int_range_wf_iff(lb: int, ub: int, n: nat, x: i64)
    requires 1 <= n <= 56, lb < ub, ub - lb < p2(n), i64::MIN <= lb, ub <= i64::MAX,
    ensures int_range_wf(lb, ub, n)(x) <==> (lb <= x as int <= ub),
{
    ut::lemma_int_range_wf_iff(lb, ub, n, x);
}

// ------------------------------------------- OCTET STRING element: one byte

pub open spec fn byte_wf() -> Wf<u8> { ut::byte_wf() }
pub open spec fn byte_enc() -> Enc<u8> { lift_enc(ut::byte_enc()) }
pub open spec fn byte_dec() -> Dec<u8> { lift_dec(ut::byte_dec()) }

pub proof fn lemma_byte_format()
    ensures is_format(byte_wf(), byte_enc(), byte_dec()),
{
    ut::lemma_byte_format();
    lemma_lift_format(ut::byte_wf(), ut::byte_enc(), ut::byte_dec());
}

pub proof fn lemma_byte_dec_same(i: In)
    ensures byte_dec()(i) is Some ==> byte_dec()(i).unwrap().2 is SameVer,
{
    ut::lemma_byte_dec_same(i.1);
}

pub proof fn lemma_byte_wf_all(b: u8)
    ensures byte_wf()(b),
{
    ut::lemma_byte_wf_all(b);
}

} // verus!
