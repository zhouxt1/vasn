//! Terminal ASN.1 formats built from `uint` by the composition lemmas.
//! Generated code references these rather than re-deriving them per type.
//!
//! Every spec function is routed through a named accessor returning a
//! `spec_fn`, so that the same closure value can be named at a use site and at
//! a step-lemma application. Generated code follows the same convention.
use vstd::prelude::*;
use crate::bitspec::*;
use crate::format::*;
use crate::prim::*;

verus! {

broadcast use {format_steps, map_steps};

// ------------------------------------------------------------------ BOOLEAN

pub open spec fn bool_to(v: u64) -> bool { v == 1 }
pub open spec fn bool_from(b: bool) -> u64 { if b { 1u64 } else { 0u64 } }

pub open spec fn bool_to_f() -> spec_fn(u64) -> bool { |v: u64| bool_to(v) }
pub open spec fn bool_from_f() -> spec_fn(bool) -> u64 { |b: bool| bool_from(b) }

pub open spec fn bool_wf() -> Wf<bool> { map_wf(uint_wf(1), bool_to_f(), bool_from_f()) }
pub open spec fn bool_enc() -> Enc<bool> { map_enc(uint_enc(1), bool_from_f()) }
pub open spec fn bool_dec() -> Dec<bool> { map_dec(uint_dec(1), bool_to_f()) }

pub proof fn lemma_bool_format()
    ensures is_format(bool_wf(), bool_enc(), bool_dec()),
{
    lemma_uint_format(1);
    assert forall|v: u64| uint_wf(1)(v) implies
        #[trigger] bool_from_f()(bool_to_f()(v)) == v
    by {
        reveal_with_fuel(p2, 3);
    }
    lemma_map_format(uint_wf(1), uint_enc(1), uint_dec(1), bool_to_f(), bool_from_f());
}

/// Every Rust `bool` is a well-formed ASN.1 BOOLEAN.
pub proof fn lemma_bool_wf_all(b: bool)
    ensures bool_wf()(b),
{
    reveal_with_fuel(p2, 3);
}

pub proof fn lemma_bool_enc_len(b: bool)
    ensures bool_enc()(b).len() == 1,
{
    reveal(map_enc);
    lemma_uint_enc_len(1, bool_from(b));
}

/// A `bool` encodes to the one-element sequence holding it. Needed wherever a
/// generated encoder has to match a spec written with `seq![...]` literals --
/// the extension bit, and the extension bitmap.
pub proof fn lemma_bool_enc_seq(b: bool)
    ensures bool_enc()(b) =~= seq![b],
{
    reveal(map_enc);
    lemma_bool_enc_len(b);
    assert(bool_enc()(b)[0] == b) by { reveal_with_fuel(p2, 3); }
}

/// A `bool` decode hands back the leading bit itself. Reading padding, which
/// has to be checked rather than decoded, is where this is needed.
pub proof fn lemma_bool_dec_bit(s: Seq<bool>)
    requires s.len() >= 1,
    ensures bool_dec()(s) == Some::<(bool, nat, Flg)>((s[0], 1nat, Flg::SameVer)),
{
    reveal(map_dec);
    let t = s.take(1);
    assert(t.len() == 1 && t[0] == s[0] && t.last() == s[0]);
    assert(t.drop_last() =~= Seq::<bool>::empty());
    reveal_with_fuel(bits_val, 2);
    assert(bits_val(Seq::<bool>::empty()) == 0);
}

pub proof fn lemma_bool_dec_same(b: Seq<bool>)
    ensures bool_dec()(b) is Some ==> bool_dec()(b).unwrap().2 is SameVer,
{
    reveal(map_dec);
}

// -------------------------------------------------- INTEGER (lb..ub), lb < ub

pub open spec fn ir_max(lb: int, ub: int) -> u64 { (ub - lb) as u64 }

pub open spec fn ir_to(lb: int) -> spec_fn(u64) -> i64 { |v: u64| (lb + v as int) as i64 }
pub open spec fn ir_from(lb: int) -> spec_fn(i64) -> u64 { |x: i64| (x as int - lb) as u64 }
pub open spec fn ir_ok(lb: int, ub: int) -> spec_fn(u64) -> bool {
    |v: u64| v <= ir_max(lb, ub)
}

pub open spec fn ir_base_wf(lb: int, ub: int, n: nat) -> Wf<u64> {
    restrict_wf(uint_wf(n), ir_ok(lb, ub))
}
pub open spec fn ir_base_dec(lb: int, ub: int, n: nat) -> Dec<u64> {
    restrict_dec(uint_dec(n), ir_ok(lb, ub))
}

pub open spec fn int_range_wf(lb: int, ub: int, n: nat) -> Wf<i64> {
    map_wf(ir_base_wf(lb, ub, n), ir_to(lb), ir_from(lb))
}
pub open spec fn int_range_enc(lb: int, ub: int, n: nat) -> Enc<i64> {
    map_enc(uint_enc(n), ir_from(lb))
}
pub open spec fn int_range_dec(lb: int, ub: int, n: nat) -> Dec<i64> {
    map_dec(ir_base_dec(lb, ub, n), ir_to(lb))
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
    lemma_uint_format(n);
    lemma_restrict_format(uint_wf(n), uint_enc(n), uint_dec(n), ir_ok(lb, ub));
    assert forall|v: u64| ir_base_wf(lb, ub, n)(v) implies
        #[trigger] ir_from(lb)(ir_to(lb)(v)) == v
    by {
        assert(v <= ir_max(lb, ub));
        assert(lb + v as int <= ub);
    }
    lemma_map_format(ir_base_wf(lb, ub, n), uint_enc(n), ir_base_dec(lb, ub, n),
                     ir_to(lb), ir_from(lb));
}

/// The well-formed values are exactly the ones inside the ASN.1 constraint.
pub proof fn lemma_int_range_wf_iff(lb: int, ub: int, n: nat, x: i64)
    requires 1 <= n <= 56, lb < ub, ub - lb < p2(n), i64::MIN <= lb, ub <= i64::MAX,
    ensures int_range_wf(lb, ub, n)(x) <==> (lb <= x as int <= ub),
{
    if lb <= x as int <= ub {
        assert(ir_from(lb)(x) == (x as int - lb) as u64);
        assert((x as int - lb) <= ub - lb);
    }
}

} // verus!

verus! {

// ------------------------------------------- OCTET STRING element: one byte

pub open spec fn byte_to() -> spec_fn(u64) -> u8 { |v: u64| v as u8 }
pub open spec fn byte_from() -> spec_fn(u8) -> u64 { |b: u8| b as u64 }

pub open spec fn byte_wf() -> Wf<u8> { map_wf(uint_wf(8), byte_to(), byte_from()) }
pub open spec fn byte_enc() -> Enc<u8> { map_enc(uint_enc(8), byte_from()) }
pub open spec fn byte_dec() -> Dec<u8> { map_dec(uint_dec(8), byte_to()) }

pub proof fn lemma_byte_format()
    ensures is_format(byte_wf(), byte_enc(), byte_dec()),
{
    lemma_uint_format(8);
    assert forall|v: u64| uint_wf(8)(v) implies #[trigger] byte_from()(byte_to()(v)) == v by {
        reveal_with_fuel(p2, 10);
        assert(p2(8) == 256);
    }
    lemma_map_format(uint_wf(8), uint_enc(8), uint_dec(8), byte_to(), byte_from());
}

/// BOOLEAN, INTEGER and the byte format are all `uint` underneath, so none of
/// them can report `DiffVer`.
pub proof fn lemma_byte_dec_same(b: Seq<bool>)
    ensures byte_dec()(b) is Some ==> byte_dec()(b).unwrap().2 is SameVer,
{
    reveal(map_dec);
}

pub proof fn lemma_byte_wf_all(b: u8)
    ensures byte_wf()(b),
{
    reveal_with_fuel(p2, 10);
    assert(p2(8) == 256);
}

} // verus!
