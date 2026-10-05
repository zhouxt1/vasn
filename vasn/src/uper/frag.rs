//! Fragmented length determinants (X.691 11.9.3.8).
//!
//! A length of 16K or more is not encodable in one determinant. Instead the
//! content is broken into fragments: a one-octet header announcing `m` blocks
//! of 16K units (`m` is 1 to 4, so at most 64K per fragment), that many units,
//! and then **another length determinant for what is left** -- recursively,
//! until a remainder below 16K closes it off with an ordinary determinant.
//! 11.9.3.8.3's note spells out the edge case: a content length that is an
//! exact multiple of 16K ends with a single zero-length octet.
//!
//! 11.9.3.8.1 is what makes it canonical: `m` "shall be the maximum allowed
//! value such that the associated field or list of fields contains more than or
//! exactly `m` octets", i.e. `m = min(4, total / 16K)`. A decoder that accepts
//! a smaller `m` accepts two encodings of one value, so the check is not
//! optional here.
//!
//! VUPER does not implement this: `Term/LengthDet.v` says "we do not consider
//! the case where n > 16K", and `format_correct_inj_diff` carries a matching
//! escape hatch. Covering it is what lets an open type carry content of any
//! size, and so removes the size hypothesis from `lemma_open_format`.
//!
//! Units: this module counts **octets**, which is what open types and OCTET
//! STRING need (11.9.3.8.2 a). The bit-counted and component-counted variants
//! (b and c) share the header but fragment different things.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::uper::format::*;
use crate::uper::prim::*;
use crate::uper::term::*;
use crate::uper::opt::*;
use crate::uper::list::*;
use crate::uper::lendet::*;

verus! {

broadcast use {format_steps, map_steps, unit_steps, list_steps};

/// One fragment block, in octets.
pub open spec fn frag_unit() -> nat { 16384 }

/// A length determinant's leading field: either the whole remaining length, or
/// the announcement of a fragment with more to follow.
#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum LenHead {
    Final(u64),
    Frag(u64),
}

pub open spec fn lh_lo() -> spec_fn(u64) -> bool { |v: u64| v < 128 }
pub open spec fn lh_mid() -> spec_fn(u64) -> bool { |v: u64| 128 <= v < 16384 }
pub open spec fn lh_blocks() -> spec_fn(u64) -> bool { |v: u64| 1 <= v <= 4 }

// The three forms differ in field width, so the second selector bit is only
// present in the long branch. The short branch pins it with the 0-bit unit
// format, which costs no bits and gives both branches the same value shape.
pub open spec fn lh_in_wf() -> spec_fn(bool) -> Wf<(bool, u64)> {
    |b0: bool| if b0 {
        dep_wf(bool_wf(), lh_w2())
    } else {
        pair_wf(unit_wf(false), restrict_wf(uint_wf(7), lh_lo()))
    }
}
pub open spec fn lh_in_enc() -> spec_fn(bool) -> Enc<(bool, u64)> {
    |b0: bool| if b0 {
        dep_enc(bool_enc(), lh_e2())
    } else {
        pair_enc(unit_enc(), uint_enc(7))
    }
}
pub open spec fn lh_in_dec() -> spec_fn(bool) -> Dec<(bool, u64)> {
    |b0: bool| if b0 {
        dep_dec(bool_dec(), lh_d2())
    } else {
        pair_dec(unit_dec(false), restrict_dec(uint_dec(7), lh_lo()))
    }
}

/// `11` announces a fragment count in 6 bits; `10` a 14-bit length.
pub open spec fn lh_w2() -> spec_fn(bool) -> Wf<u64> {
    |b1: bool| if b1 { restrict_wf(uint_wf(6), lh_blocks()) }
               else { restrict_wf(uint_wf(14), lh_mid()) }
}
pub open spec fn lh_e2() -> spec_fn(bool) -> Enc<u64> {
    |b1: bool| if b1 { uint_enc(6) } else { uint_enc(14) }
}
pub open spec fn lh_d2() -> spec_fn(bool) -> Dec<u64> {
    |b1: bool| if b1 { restrict_dec(uint_dec(6), lh_blocks()) }
               else { restrict_dec(uint_dec(14), lh_mid()) }
}

pub open spec fn lh_to() -> spec_fn((bool, (bool, u64))) -> LenHead {
    |t: (bool, (bool, u64))| if t.0 && t.1.0 { LenHead::Frag(t.1.1) } else { LenHead::Final(t.1.1) }
}
pub open spec fn lh_from() -> spec_fn(LenHead) -> (bool, (bool, u64)) {
    |h: LenHead| match h {
        LenHead::Final(n) => if n < 128 { (false, (false, n)) } else { (true, (false, n)) },
        LenHead::Frag(m) => (true, (true, m)),
    }
}

pub open spec fn lh_full_wf() -> Wf<(bool, (bool, u64))> { dep_wf(bool_wf(), lh_in_wf()) }
pub open spec fn lh_full_enc() -> Enc<(bool, (bool, u64))> { dep_enc(bool_enc(), lh_in_enc()) }
pub open spec fn lh_full_dec() -> Dec<(bool, (bool, u64))> { dep_dec(bool_dec(), lh_in_dec()) }

pub open spec fn lh_wf() -> Wf<LenHead> { map_wf(lh_full_wf(), lh_to(), lh_from()) }
pub open spec fn lh_enc() -> Enc<LenHead> { map_enc(lh_full_enc(), lh_from()) }
pub open spec fn lh_dec() -> Dec<LenHead> { map_dec(lh_full_dec(), lh_to()) }

pub proof fn lemma_lh_p2()
    ensures p2(6) == 64, p2(7) == 128, p2(14) == 16384,
{
    reveal_with_fuel(p2, 16);
}

pub proof fn lemma_lh_in_format(b0: bool)
    ensures is_format(lh_in_wf()(b0), lh_in_enc()(b0), lh_in_dec()(b0)),
{
    if b0 {
        lemma_bool_format();
        assert forall|b1: bool| bool_wf()(b1) implies
            is_format(#[trigger] lh_w2()(b1), lh_e2()(b1), lh_d2()(b1))
        by {
            if b1 {
                lemma_uint_format(6);
                lemma_restrict_format(uint_wf(6), uint_enc(6), uint_dec(6), lh_blocks());
            } else {
                lemma_uint_format(14);
                lemma_restrict_format(uint_wf(14), uint_enc(14), uint_dec(14), lh_mid());
            }
        }
        lemma_dep_format(bool_wf(), bool_enc(), bool_dec(), lh_w2(), lh_e2(), lh_d2());
    } else {
        lemma_unit_format(false);
        lemma_uint_format(7);
        lemma_restrict_format(uint_wf(7), uint_enc(7), uint_dec(7), lh_lo());
        lemma_pair_format(unit_wf(false), unit_enc(), unit_dec(false),
                          restrict_wf(uint_wf(7), lh_lo()), uint_enc(7),
                          restrict_dec(uint_dec(7), lh_lo()));
    }
}

pub proof fn lemma_lh_format()
    ensures is_format(lh_wf(), lh_enc(), lh_dec()),
{
    lemma_bool_format();
    assert forall|b0: bool| bool_wf()(b0) implies
        is_format(#[trigger] lh_in_wf()(b0), lh_in_enc()(b0), lh_in_dec()(b0))
    by { lemma_lh_in_format(b0); }
    lemma_dep_format(bool_wf(), bool_enc(), bool_dec(), lh_in_wf(), lh_in_enc(), lh_in_dec());
    assert forall|t: (bool, (bool, u64))| lh_full_wf()(t) implies
        #[trigger] lh_from()(lh_to()(t)) == t
    by {
        lemma_dep_wf_val(bool_wf(), lh_in_wf(), t.0, t.1);
        if t.0 {
            lemma_dep_wf_val(bool_wf(), lh_w2(), t.1.0, t.1.1);
            if t.1.0 {
                lemma_restrict_wf_val(uint_wf(6), lh_blocks(), t.1.1);
            } else {
                lemma_restrict_wf_val(uint_wf(14), lh_mid(), t.1.1);
            }
        } else {
            lemma_pair_wf_val(unit_wf(false), restrict_wf(uint_wf(7), lh_lo()), t.1.0, t.1.1);
            lemma_unit_wf_val(false, t.1.0);
            lemma_restrict_wf_val(uint_wf(7), lh_lo(), t.1.1);
        }
        assert(t == (t.0, (t.1.0, t.1.1)));
    }
    lemma_map_format(lh_full_wf(), lh_full_enc(), lh_full_dec(), lh_to(), lh_from());
}

/// The head admits exactly the lengths below 16K and the block counts 1..4.
pub proof fn lemma_lh_wf_iff(h: LenHead)
    ensures lh_wf()(h) <==> (match h {
        LenHead::Final(n) => n < 16384,
        LenHead::Frag(m) => 1 <= m <= 4,
    }),
{
    lemma_lh_p2();
    lemma_bool_wf_all(true);
    lemma_bool_wf_all(false);
    let t = lh_from()(h);
    lemma_map_wf_val(lh_full_wf(), lh_to(), lh_from(), h);
    lemma_dep_wf_val(bool_wf(), lh_in_wf(), t.0, t.1);
    lemma_dep_wf_val(bool_wf(), lh_w2(), t.1.0, t.1.1);
    lemma_pair_wf_val(unit_wf(false), restrict_wf(uint_wf(7), lh_lo()), t.1.0, t.1.1);
    lemma_unit_wf_val(false, t.1.0);
    lemma_restrict_wf_val(uint_wf(7), lh_lo(), t.1.1);
    lemma_restrict_wf_val(uint_wf(14), lh_mid(), t.1.1);
    lemma_restrict_wf_val(uint_wf(6), lh_blocks(), t.1.1);
}

} // verus!

verus! {

/// A head is one octet, or two for a 14-bit length.
pub proof fn lemma_lh_enc_len(h: LenHead)
    requires lh_wf()(h),
    ensures lh_enc()(h).len() == (match h {
        LenHead::Final(n) => if n < 128 { 8int } else { 16int },
        LenHead::Frag(_) => 8int,
    }),
{
    lemma_lh_wf_iff(h);
    let t = lh_from()(h);
    lemma_map_enc_val(lh_full_enc(), lh_from(), h);
    lemma_dep_enc_val(bool_enc(), lh_in_enc(), t.0, t.1);
    lemma_bool_enc_len(t.0);
    if t.0 {
        lemma_dep_enc_val(bool_enc(), lh_e2(), t.1.0, t.1.1);
        lemma_bool_enc_len(t.1.0);
        lemma_uint_enc_len(if t.1.0 { 6nat } else { 14nat }, t.1.1);
    } else {
        lemma_pair_enc_val(unit_enc(), uint_enc(7), t.1.0, t.1.1);
        lemma_unit_enc_val::<bool>(t.1.0);
        lemma_uint_enc_len(7, t.1.1);
    }
}

pub proof fn lemma_lh_enc_len_bounds(h: LenHead)
    requires lh_wf()(h),
    ensures 8 <= lh_enc()(h).len() <= 16,
{
    lemma_lh_enc_len(h);
}

/// The head is built only from `uint`, so it never reports `DiffVer`.
pub proof fn lemma_lh_dec_same(b: Seq<bool>)
    ensures lh_dec()(b) is Some ==> lh_dec()(b).unwrap().2 is SameVer,
{
    reveal(map_dec);
    reveal(dep_dec);
    reveal(pair_dec);
    reveal(restrict_dec);
    reveal(unit_dec);
}

} // verus!

verus! {

// ------------------------------------------------ the fragmented octet string
//
// The content is carried as bits that happen to be a whole number of octets,
// rather than as a `Seq<u8>`. Everything else in the library already speaks
// bits, and a fragment boundary is at an octet -- so a fragment is a `take` on
// the bit sequence and the octets/bits conversion never has to be written down.

/// Blocks in the leading fragment. 11.9.3.8.1: `m` "shall be the maximum
/// allowed value such that the associated field or list of fields contains
/// more than or exactly `m` octets", capped at 4 by 11.9.3.8.
pub open spec fn frag_blocks(l: nat) -> nat {
    if l / 16384 >= 4 { 4 } else { l / 16384 }
}

/// Octets in a fragment of `m` blocks.
pub open spec fn frag_octets(m: nat) -> nat { m * 16384 }

/// ... and its bits, which is what the content is measured in here.
pub open spec fn frag_bits(m: nat) -> nat { 8 * frag_octets(m) }

pub proof fn lemma_frag_bits(m: nat)
    ensures frag_bits(m) % 8 == 0, frag_bits(m) / 8 == frag_octets(m),
{
    assert(frag_bits(m) == 8 * frag_octets(m));
    assert((8 * frag_octets(m)) % 8 == 0) by (nonlinear_arith) {}
    assert((8 * frag_octets(m)) / 8 == frag_octets(m)) by (nonlinear_arith) {}
}

/// Splitting an octet-aligned sequence at a fragment boundary leaves both
/// halves octet-aligned, and the octet counts add up.
pub proof fn lemma_frag_split(total: nat, m: nat, rest: nat)
    requires total % 8 == 0, rest % 8 == 0, total == frag_bits(m) + rest,
    ensures total / 8 == frag_octets(m) + rest / 8,
{
    lemma_frag_bits(m);
    assert(total / 8 == frag_octets(m) + rest / 8) by (nonlinear_arith)
        requires total == 8 * frag_octets(m) + rest, rest % 8 == 0;
    {}
}

pub open spec fn frag_enc_rec(c: Seq<bool>) -> Seq<bool>
    decreases c.len(),
{
    let l = c.len() / 8;
    if l < 16384 {
        lh_enc()(LenHead::Final(l as u64)) + c
    } else {
        let m = frag_blocks(l);
        let n = frag_bits(m) as int;
        lh_enc()(LenHead::Frag(m as u64)) + c.take(n) + frag_enc_rec(c.skip(n))
    }
}

pub open spec fn frag_dec_rec(b: Seq<bool>) -> Option<(Seq<bool>, nat)>
    decreases b.len(),
{
    match lh_dec()(b) {
        Some((h, k, _)) => {
            if k == 0 || k > b.len() {
                None
            } else {
                match h {
                    LenHead::Final(n) => {
                        let bits = 8 * (n as nat);
                        if k + bits > b.len() {
                            None
                        } else {
                            Some((b.skip(k as int).take(bits as int), (k + bits) as nat))
                        }
                    },
                    LenHead::Frag(m) => {
                        let bits = frag_bits(m as nat);
                        if k + bits > b.len() {
                            None
                        } else {
                            match frag_dec_rec(b.skip((k + bits) as int)) {
                                // 11.9.3.8.1: `m` had to be maximal, so either
                                // it is capped or what follows is under a block
                                Some((c2, k3)) => if m == 4 || c2.len() / 8 < 16384 {
                                    Some((b.skip(k as int).take(bits as int) + c2,
                                          (k + bits + k3) as nat))
                                } else {
                                    None
                                },
                                None => None,
                            }
                        }
                    },
                }
            }
        },
        None => None,
    }
}

/// An open type's content is a whole number of octets (11.1.3.1), which is
/// exactly what the length determinant counts.
#[verifier::opaque]
pub open spec fn frag_wf() -> Wf<Seq<bool>> { |c: Seq<bool>| c.len() % 8 == 0 }

#[verifier::opaque]
pub open spec fn frag_enc() -> Enc<Seq<bool>> { |c: Seq<bool>| frag_enc_rec(c) }

#[verifier::opaque]
pub open spec fn frag_dec() -> Dec<Seq<bool>> {
    |b: Seq<bool>| match frag_dec_rec(b) {
        Some((c, k)) => Some((c, k, Flg::SameVer)),
        None => None,
    }
}

/// A fragment count below the cap pins the remainder under one block, and a
/// count at the cap needs no pinning -- the arithmetic behind the canonicity
/// check in `frag_dec_rec`.
pub proof fn lemma_frag_blocks(m: nat, r: nat)
    requires 1 <= m <= 4, m == 4 || r < 16384,
    ensures frag_blocks((m * 16384 + r) as nat) == m,
{
    let l = (m * 16384 + r) as nat;
    if m == 4 {
        assert(l / 16384 >= 4) by (nonlinear_arith)
            requires l >= 4 * 16384;
        {}
    } else {
        assert(l / 16384 == m) by (nonlinear_arith)
            requires r < 16384, l == m * 16384 + r;
        {}
    }
}

pub proof fn lemma_frag_len_ge(l: nat)
    requires l >= 16384,
    ensures 1 <= frag_blocks(l) <= 4, frag_blocks(l) * 16384 <= l,
{
    assert(l / 16384 >= 1) by (nonlinear_arith)
        requires l >= 16384;
    {}
    assert((l / 16384) * 16384 <= l) by (nonlinear_arith) {}
    if l / 16384 >= 4 {
        assert(4 * 16384 <= l) by (nonlinear_arith)
            requires l / 16384 >= 4;
        {}
    }
}

} // verus!

verus! {

/// The unfragmented branch: the content fits in one determinant, so the whole
/// thing is a `LenHead::Final` and the content itself.
///
/// Split out from `lemma_frag_surj` rather than inlined. The two branches share
/// nothing but `lemma_lh_format`, and proved together they make one query whose
/// cost lands close enough to the default rlimit that *the order of the `pub
/// mod` lines in `lib.rs`* decides whether it passes -- 2x the default in the
/// unlucky order. Two small queries have room to spare in either.
pub proof fn lemma_frag_surj_final(c: Seq<bool>, rest: Seq<bool>)
    requires c.len() % 8 == 0, c.len() / 8 < 16384,
    ensures frag_dec_rec(frag_enc_rec(c) + rest)
        == Some::<(Seq<bool>, nat)>((c, frag_enc_rec(c).len())),
{
    lemma_lh_format();
    let l = c.len() / 8;
    let b = frag_enc_rec(c) + rest;
    let h = LenHead::Final(l as u64);
    lemma_lh_wf_iff(h);
    lemma_lh_enc_len_bounds(h);
    let g = lh_enc()(h);
    assert(b =~= g + (c + rest));
    assert(lh_dec()(b) == Some::<(LenHead, nat, Flg)>((h, g.len(), Flg::SameVer)));
    lemma_take_add(g, c + rest);
    assert(b.skip(g.len() as int) =~= c + rest);
    assert(8 * l == c.len());
    lemma_take_add(c, rest);
    assert(b.skip(g.len() as int).take(c.len() as int) =~= c);
    assert(b.len() >= g.len() + c.len());
}

pub proof fn lemma_frag_surj(c: Seq<bool>, rest: Seq<bool>)
    requires c.len() % 8 == 0,
    ensures frag_dec_rec(frag_enc_rec(c) + rest)
        == Some::<(Seq<bool>, nat)>((c, frag_enc_rec(c).len())),
    decreases c.len(),
{
    let l = c.len() / 8;
    let b = frag_enc_rec(c) + rest;
    if l < 16384 {
        lemma_frag_surj_final(c, rest);
    } else {
        lemma_lh_format();
        lemma_frag_len_ge(l);
        let m = frag_blocks(l);
        let n = frag_bits(m) as int;
        let h = LenHead::Frag(m as u64);
        lemma_lh_wf_iff(h);
        lemma_lh_enc_len_bounds(h);
        let g = lh_enc()(h);
        let head = c.take(n);
        let tail = c.skip(n);
        lemma_frag_bits(m);
        assert(c.len() == 8 * l) by (nonlinear_arith)
            requires c.len() % 8 == 0, l == c.len() / 8;
        {}
        assert(frag_octets(m) <= l);
        assert(n <= c.len()) by (nonlinear_arith)
            requires frag_octets(m) <= l, c.len() == 8 * l, n == 8 * frag_octets(m);
        {}
        assert(head.len() == n);
        assert(tail.len() == c.len() - n);
        assert(tail.len() % 8 == 0) by (nonlinear_arith)
            requires c.len() % 8 == 0, n == 8 * frag_octets(m), tail.len() == c.len() - n;
        {}
        assert(b =~= g + (head + (frag_enc_rec(tail) + rest)));
        assert(lh_dec()(b) == Some::<(LenHead, nat, Flg)>((h, g.len(), Flg::SameVer)));
        lemma_take_add(g, head + (frag_enc_rec(tail) + rest));
        assert(b.skip(g.len() as int) =~= head + (frag_enc_rec(tail) + rest));
        lemma_take_add(head, frag_enc_rec(tail) + rest);
        assert(b.skip(g.len() as int).take(n) =~= head);
        assert(b.skip((g.len() + n) as int) =~= frag_enc_rec(tail) + rest);
        lemma_frag_surj(tail, rest);
        // `m` was chosen maximal, so the canonicity check passes
        if m < 4 {
            assert(l / 16384 == m);
            lemma_frag_split(c.len(), m, tail.len());
            assert(tail.len() / 8 == l - frag_octets(m));
            assert(l - m * 16384 < 16384) by (nonlinear_arith)
                requires l / 16384 == m;
            {}
        }
        assert(head + tail =~= c);
        assert(b.len() >= g.len() + n);
    }
}

pub proof fn lemma_frag_inj(b: Seq<bool>)
    requires frag_dec_rec(b).is_some(),
    ensures ({
        let c = frag_dec_rec(b).unwrap().0;
        let k = frag_dec_rec(b).unwrap().1;
        c.len() % 8 == 0 && k <= b.len() && b.take(k as int) == frag_enc_rec(c)
    }),
    decreases b.len(),
{
    lemma_lh_format();
    lemma_lh_dec_same(b);
    assert(lh_dec()(b).is_some());
    let h = lh_dec()(b).unwrap().0;
    let k = lh_dec()(b).unwrap().1;
    lemma_lh_wf_iff(h);
    lemma_lh_enc_len_bounds(h);
    assert(k <= b.len());
    assert(b.take(k as int) == lh_enc()(h));
    assert(b.take(k as int).len() == k);
    assert(k >= 8);
    match h {
        LenHead::Final(n) => {
            let bits = 8 * (n as nat);
            let c = b.skip(k as int).take(bits as int);
            assert(c.len() == bits);
            assert(c.len() / 8 == n as nat) by (nonlinear_arith)
                requires c.len() == 8 * (n as nat);
            {}
            lemma_take_split(b, k, bits);
            assert(b.take((k + bits) as int) =~= lh_enc()(h) + c);
            assert(frag_enc_rec(c) =~= lh_enc()(h) + c);
        },
        LenHead::Frag(m) => {
            let bits = frag_bits(m as nat);
            let c1 = b.skip(k as int).take(bits as int);
            let tailb = b.skip((k + bits) as int);
            lemma_frag_inj(tailb);
            let c2 = frag_dec_rec(tailb).unwrap().0;
            let k3 = frag_dec_rec(tailb).unwrap().1;
            let c = c1 + c2;
            assert(c1.len() == bits);
            lemma_frag_bits(m as nat);
            assert(c.len() == bits + c2.len());
            assert(c.len() % 8 == 0) by (nonlinear_arith)
                requires c2.len() % 8 == 0, bits == 8 * frag_octets(m as nat),
                         c.len() == bits + c2.len();
            {}
            lemma_frag_split(c.len(), m as nat, c2.len());
            lemma_frag_blocks(m as nat, (c2.len() / 8) as nat);
            assert(c.len() / 8 == (m as nat) * 16384 + c2.len() / 8);
            assert(c.len() / 8 >= 16384);
            assert(frag_blocks((c.len() / 8) as nat) == m as nat);
            assert(c.take(bits as int) =~= c1);
            assert(c.skip(bits as int) =~= c2);
            lemma_take_split(b, k, bits);
            lemma_take_split(b, (k + bits) as nat, k3);
            assert(b.take((k + bits) as int) =~= lh_enc()(h) + c1);
            assert(b.take((k + bits + k3) as int) =~= (lh_enc()(h) + c1) + frag_enc_rec(c2));
            assert(frag_enc_rec(c) =~= lh_enc()(h) + c1 + frag_enc_rec(c2));
        },
    }
}

/// The fragmented determinant is built only from `uint`, so it never reports
/// `DiffVer` -- an open type's flag always comes from its content.
pub proof fn lemma_frag_dec_same(b: Seq<bool>)
    ensures frag_dec()(b) is Some ==> frag_dec()(b).unwrap().2 is SameVer,
{
    reveal(frag_dec);
}

pub proof fn lemma_frag_format()
    ensures is_format(frag_wf(), frag_enc(), frag_dec()),
{
    reveal(frag_wf); reveal(frag_enc); reveal(frag_dec);
    assert forall|c: Seq<bool>, rest: Seq<bool>| frag_wf()(c) implies
        #[trigger] frag_dec()(frag_enc()(c) + rest)
            == Some::<(Seq<bool>, nat, Flg)>((c, frag_enc()(c).len(), Flg::SameVer))
    by {
        lemma_frag_surj(c, rest);
    }
    assert forall|b: Seq<bool>| (#[trigger] frag_dec()(b)).is_some() implies {
        let c = frag_dec()(b).unwrap().0;
        let k = frag_dec()(b).unwrap().1;
        &&& frag_wf()(c) && k <= b.len()
        &&& frag_dec()(b).unwrap().2 is SameVer ==> b.take(k as int) == frag_enc()(c)
    } by {
        lemma_frag_inj(b);
    }
}

} // verus!

verus! {

// ------------------------------------------------------------ worked examples
//
// The two examples the standard spells out, checked against the definition
// rather than against the eye.

/// 11.9.3.8.1 NOTE 2: a value of 144K + 1 (= 64K + 64K + 16K + 1) units is
/// fragmented with headers `11 000100`, `11 000100`, `11 000001`, then a final
/// `0 0000001`. So the block counts are 4, 4, 1 and the tail is one unit.
pub proof fn lemma_frag_example_144k()
    ensures
        frag_blocks(147457) == 4,
        147457 - frag_octets(4) == 81921,
        frag_blocks(81921) == 4,
        81921 - frag_octets(4) == 16385,
        frag_blocks(16385) == 1,
        16385 - frag_octets(1) == 1,
        1 < 16384,
{
}

/// 11.9.3.8.3 NOTE: "If the last fragment that contains part of the encoded
/// value has a length that is an exact multiple of 16K, it is followed by a
/// final fragment that consists only of a single octet length component set to
/// 0." One block, then a `Final(0)` head and no content.
pub proof fn lemma_frag_example_exact_multiple()
    ensures
        frag_blocks(16384) == 1,
        16384 - frag_octets(1) == 0,
        lh_enc()(LenHead::Final(0)).len() == 8,
{
    lemma_lh_wf_iff(LenHead::Final(0));
    lemma_lh_enc_len(LenHead::Final(0));
}

} // verus!

verus! {

// --------------------------------------------- agreement with `lendet`'s form
//
// There are two spellings of the non-fragmenting determinant: `gld` in
// `lendet.rs`, factored as one bit plus a 15-bit field, and `LenHead::Final`
// here, factored as `0` + 7 bits or `10` + 14 bits. They are the same bits --
// `gld`'s 15-bit field is below 2^14, so its top bit is always the `0` of
// `10`. `nsld` still builds on `gld` because an extension addition count that
// fragments would need 16384 additions in one SEQUENCE; this lemma is what
// stops the two from drifting apart unnoticed if either is ever touched.

pub proof fn lemma_bits_seq_widen(v: u64, n: nat)
    requires (v as nat) < p2(n),
    ensures crate::bits::prim_write::bits_seq(v, (n + 1) as nat)
        =~= seq![false] + crate::bits::prim_write::bits_seq(v, n),
{
    let wide = crate::bits::prim_write::bits_seq(v, (n + 1) as nat);
    let narrow = seq![false] + crate::bits::prim_write::bits_seq(v, n);
    assert(wide.len() == narrow.len());
    assert forall|i: int| 0 <= i < wide.len() implies wide[i] == narrow[i] by {
        if i == 0 {
            // the leading bit of the wider field is (v / 2^n) mod 2, and v < 2^n
            lemma_p2_pos(n);
            assert((v as nat) / p2(n) == 0) by (nonlinear_arith)
                requires (v as nat) < p2(n), p2(n) > 0;
            {}
        }
    }
}

pub proof fn lemma_gld_lh_agree(n: u64)
    requires n < 16384,
    ensures gld_enc()(n) =~= lh_enc()(LenHead::Final(n)),
{
    lemma_lh_p2();
    lemma_gld_wf_iff(n);
    lemma_lh_wf_iff(LenHead::Final(n));
    lemma_map_enc_val(gld_full_enc(), gld_from(), n);
    lemma_dep_enc_val(bool_enc(), gld_part_enc(), n >= 128, n);
    let t = lh_from()(LenHead::Final(n));
    lemma_map_enc_val(lh_full_enc(), lh_from(), LenHead::Final(n));
    lemma_dep_enc_val(bool_enc(), lh_in_enc(), t.0, t.1);
    if n < 128 {
        lemma_pair_enc_val(unit_enc(), uint_enc(7), t.1.0, t.1.1);
        lemma_unit_enc_val::<bool>(t.1.0);
        assert(Seq::<bool>::empty() + uint_enc(7)(n) =~= uint_enc(7)(n));
    } else {
        lemma_dep_enc_val(bool_enc(), lh_e2(), t.1.0, t.1.1);
        lemma_bits_seq_widen(n, 14);
        assert(uint_enc(15)(n) =~= crate::bits::prim_write::bits_seq(n, 15));
        assert(bool_enc()(false) =~= seq![false]) by {
            reveal(map_enc);
            assert(crate::bits::prim_write::bits_seq(0u64, 1) =~= seq![false]);
        }
    }
}

} // verus!

verus! {

use crate::uper::cursor::*;

// ------------------------------------------------------- the head, runnable
//
// Written and read field by field rather than as one 8- or 16-bit word. The
// bits are the same either way, but this way `written()` accumulates in
// exactly the shape `lh_enc` unfolds to, so the proof is the composition
// lemmas and nothing else.

impl BitWriter {
    #[inline]
    pub fn write_lh(&mut self, h: LenHead) -> (ok: bool)
        requires old(self).wf(), lh_wf()(h),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> {
                &&& final(self).written() =~= old(self).written() + lh_enc()(h)
                &&& final(self).pos == old(self).pos + lh_enc()(h).len()
            },
    {
        proof {
            lemma_lh_p2();
            lemma_lh_wf_iff(h);
            lemma_lh_enc_len(h);
            let t = lh_from()(h);
            lemma_map_enc_val(lh_full_enc(), lh_from(), h);
            lemma_dep_enc_val(bool_enc(), lh_in_enc(), t.0, t.1);
            if t.0 {
                lemma_dep_enc_val(bool_enc(), lh_e2(), t.1.0, t.1.1);
            } else {
                lemma_pair_enc_val(unit_enc(), uint_enc(7), t.1.0, t.1.1);
                lemma_unit_enc_val::<bool>(t.1.0);
            }
        }
        let ghost w0 = *self;
        match h {
            LenHead::Final(n) => {
                if n < 128 {
                    if !self.write_bool(false) { return false; }
                    if !self.write_uint(7, n) { return false; }
                    proof {
                        assert(w0.written() + bool_enc()(false) + uint_enc(7)(n)
                               =~= w0.written() + lh_enc()(h));
                    }
                    true
                } else {
                    if !self.write_bool(true) { return false; }
                    if !self.write_bool(false) { return false; }
                    if !self.write_uint(14, n) { return false; }
                    proof {
                        assert(w0.written() + bool_enc()(true) + bool_enc()(false)
                               + uint_enc(14)(n) =~= w0.written() + lh_enc()(h));
                    }
                    true
                }
            },
            LenHead::Frag(m) => {
                if !self.write_bool(true) { return false; }
                if !self.write_bool(true) { return false; }
                if !self.write_uint(6, m) { return false; }
                proof {
                    assert(w0.written() + bool_enc()(true) + bool_enc()(true)
                           + uint_enc(6)(m) =~= w0.written() + lh_enc()(h));
                }
                true
            },
        }
    }
}

} // verus!

verus! {

impl<'a> BitReader<'a> {
    /// Refines `lh_dec()`. The range checks -- 128..16383 for the 14-bit form
    /// and 1..4 for the block count -- are what make the head canonical: a
    /// length the 7-bit form could carry, spelled in 14 bits, is rejected.
    #[inline]
    pub fn read_lh(&mut self) -> (res: Option<LenHead>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(h) => lh_dec()(old(self).rem())
                    == Some::<(LenHead, nat, Flg)>(
                        (h, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => lh_dec()(old(self).rem()).is_none(),
            },
    {
        proof { lemma_lh_p2(); lemma_uint_format(7); }
        let ghost start = self.rem();
        let ghost p0 = self.pos;
        let b0 = match self.read_bool() {
            Some(b) => b,
            None => {
                proof {
                    lemma_dep_dec_none_fst(bool_dec(), lh_in_dec(), start);
                    lemma_map_dec_none(lh_full_dec(), lh_to(), start);
                }
                return None;
            },
        };
        proof { lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat); }
        let ghost k0 = (self.pos - p0) as nat;
        let ghost mid = start.skip(k0 as int);
        let ghost p1 = self.pos;

        if !b0 {
            // `0` then a 7-bit length; the unit format supplies the value's
            // first component without consuming a bit
            match self.read_uint(7) {
                Some(v) => {
                    proof {
                        assert(mid.skip(0) =~= mid);
                        lemma_unit_dec_val(false, mid);
                        // a 7-bit field is below 128 by construction, which is
                        // exactly the short form's range restriction
                        assert(uint_wf(7)(v));
                        lemma_restrict_dec_some(uint_dec(7), lh_lo(), mid, v, 7, Flg::SameVer);
                        lemma_pair_dec_some(unit_dec(false), restrict_dec(uint_dec(7), lh_lo()),
                                            mid, false, 0nat, Flg::SameVer, v, 7nat, Flg::SameVer);
                        lemma_dep_dec_some(bool_dec(), lh_in_dec(), start, false, k0,
                                           Flg::SameVer, (false, v), 7nat, Flg::SameVer);
                        lemma_map_dec_some(lh_full_dec(), lh_to(), start, (false, (false, v)),
                                           (k0 + 7) as nat, Flg::SameVer);
                    }
                    Some(LenHead::Final(v))
                },
                None => {
                    proof {
                        assert(mid.skip(0) =~= mid);
                        lemma_unit_dec_val(false, mid);
                        lemma_restrict_dec_none(uint_dec(7), lh_lo(), mid);
                        lemma_pair_dec_none_snd(unit_dec(false),
                                                restrict_dec(uint_dec(7), lh_lo()),
                                                mid, false, 0nat, Flg::SameVer);
                        lemma_dep_dec_none_snd(bool_dec(), lh_in_dec(), start, false, k0,
                                               Flg::SameVer);
                        lemma_map_dec_none(lh_full_dec(), lh_to(), start);
                    }
                    None
                },
            }
        } else {
            let b1 = match self.read_bool() {
                Some(b) => b,
                None => {
                    proof {
                        lemma_dep_dec_none_fst(bool_dec(), lh_d2(), mid);
                        lemma_dep_dec_none_snd(bool_dec(), lh_in_dec(), start, true, k0,
                                               Flg::SameVer);
                        lemma_map_dec_none(lh_full_dec(), lh_to(), start);
                    }
                    return None;
                },
            };
            proof { lemma_rem_skip(self.buf@, p1 as nat, (self.pos - p1) as nat); }
            let ghost k1 = (self.pos - p1) as nat;
            let ghost inner = mid.skip(k1 as int);
            let ghost p2p = self.pos;
            // `11` is a fragment count in 6 bits, `10` a 14-bit length
            let n: usize = if b1 { 6 } else { 14 };
            let ok = |v: u64| -> (r: bool)
                ensures r == (if b1 { lh_blocks()(v) } else { lh_mid()(v) })
                { if b1 { 1 <= v && v <= 4 } else { 128 <= v && v < 16384 } };
            match self.read_uint(n) {
                Some(v) => if ok(v) {
                    proof {
                        lemma_restrict_dec_some(uint_dec(n as nat),
                                                if b1 { lh_blocks() } else { lh_mid() },
                                                inner, v, n as nat, Flg::SameVer);
                        lemma_dep_dec_some(bool_dec(), lh_d2(), mid, b1, k1, Flg::SameVer,
                                           v, n as nat, Flg::SameVer);
                        lemma_dep_dec_some(bool_dec(), lh_in_dec(), start, true, k0,
                                           Flg::SameVer, (b1, v), (k1 + n) as nat, Flg::SameVer);
                        lemma_map_dec_some(lh_full_dec(), lh_to(), start, (true, (b1, v)),
                                           (k0 + k1 + n) as nat, Flg::SameVer);
                    }
                    Some(if b1 { LenHead::Frag(v) } else { LenHead::Final(v) })
                } else {
                    proof {
                        lemma_restrict_dec_none(uint_dec(n as nat),
                                                if b1 { lh_blocks() } else { lh_mid() }, inner);
                        lemma_dep_dec_none_snd(bool_dec(), lh_d2(), mid, b1, k1, Flg::SameVer);
                        lemma_dep_dec_none_snd(bool_dec(), lh_in_dec(), start, true, k0,
                                               Flg::SameVer);
                        lemma_map_dec_none(lh_full_dec(), lh_to(), start);
                    }
                    None
                },
                None => {
                    proof {
                        lemma_restrict_dec_none(uint_dec(n as nat),
                                                if b1 { lh_blocks() } else { lh_mid() }, inner);
                        lemma_dep_dec_none_snd(bool_dec(), lh_d2(), mid, b1, k1, Flg::SameVer);
                        lemma_dep_dec_none_snd(bool_dec(), lh_in_dec(), start, true, k0,
                                               Flg::SameVer);
                        lemma_map_dec_none(lh_full_dec(), lh_to(), start);
                    }
                    None
                },
            }
        }
    }
}

} // verus!

verus! {

// ------------------------------------------------- the recursion, runnable

/// One turn of the encoder's loop, as an equation on the spec. Split out of
/// `write_frag` because proving it inline, on top of the two writer calls and
/// the loop invariant, is more than one query's worth.
pub proof fn lemma_frag_enc_step(content: Seq<bool>, off: nat, m: nat, n: nat)
    requires
        off % 8 == 0,
        off <= content.len(),
        (content.len() - off) % 8 == 0,
        ((content.len() - off) / 8) >= 16384,
        m == frag_blocks(((content.len() - off) / 8) as nat),
        n == frag_bits(m),
    ensures
        1 <= m <= 4,
        off + n <= content.len(),
        frag_enc_rec(content.skip(off as int))
            =~= lh_enc()(LenHead::Frag(m as u64)) + content.skip(off as int).take(n as int)
                + frag_enc_rec(content.skip((off + n) as int)),
{
    let rest = content.skip(off as int);
    let l = rest.len() / 8;
    assert(rest.len() == content.len() - off);
    lemma_frag_len_ge(l);
    lemma_frag_bits(m);
    assert(frag_octets(m) <= l);
    assert(n <= rest.len()) by (nonlinear_arith)
        requires frag_octets(m) <= l, rest.len() == 8 * l, n == 8 * frag_octets(m);
    assert(content.skip((off + n) as int) =~= rest.skip(n as int));
}

/// The window `write_slice` reports, in terms of the content the loop tracks.
pub proof fn lemma_frag_src_window(sb: Seq<bool>, from: nat, nbits: nat, off: nat, n: nat)
    requires from + nbits <= sb.len(), off + n <= nbits,
    ensures sb.skip((from + off) as int).take(n as int)
        =~= sb.skip(from as int).take(nbits as int).skip(off as int).take(n as int),
{
}

/// One turn of the loop as a single implication on `written()`. Everything the
/// step needs -- the fragment equation, the window `write_slice` reports, and
/// the invariant's arithmetic -- is discharged here, so the loop's own query
/// stays small enough to fit the default rlimit.
pub proof fn lemma_frag_loop_step(
    wbefore: Seq<bool>, wafter: Seq<bool>, w0: Seq<bool>,
    content: Seq<bool>, sb: Seq<bool>, from: nat, nbits: nat, off: nat, m: nat, n: nat,
)
    requires
        content == sb.skip(from as int).take(nbits as int),
        content.len() == nbits,
        from + nbits <= sb.len(),
        off % 8 == 0,
        off <= nbits,
        (nbits - off) % 8 == 0,
        ((nbits - off) / 8) >= 16384,
        m == frag_blocks(((nbits - off) / 8) as nat),
        n == frag_bits(m),
        wafter =~= wbefore + lh_enc()(LenHead::Frag(m as u64))
            + sb.skip((from + off) as int).take(n as int),
        wbefore + frag_enc_rec(content.skip(off as int)) =~= w0 + frag_enc_rec(content),
    ensures
        off + n <= nbits,
        1 <= m <= 4,
        wafter + frag_enc_rec(content.skip((off + n) as int)) =~= w0 + frag_enc_rec(content),
{
    lemma_frag_enc_step(content, off, m, n);
    lemma_frag_src_window(sb, from, nbits, off, n);
    let rest = content.skip(off as int);
    assert(wafter =~= wbefore + lh_enc()(LenHead::Frag(m as u64)) + rest.take(n as int));
    assert(wafter + frag_enc_rec(content.skip((off + n) as int))
           =~= wbefore + frag_enc_rec(rest));
}

/// The last turn: a remainder under one block is a `Final` head and the bits.
pub proof fn lemma_frag_enc_last(content: Seq<bool>, off: nat)
    requires
        off <= content.len(),
        (content.len() - off) % 8 == 0,
        ((content.len() - off) / 8) < 16384,
    ensures
        frag_enc_rec(content.skip(off as int))
            =~= lh_enc()(LenHead::Final((((content.len() - off) / 8)) as u64))
                + content.skip(off as int),
{
}

impl BitWriter {
    /// Write `nbits` bits of content from `src`, with the fragmenting length
    /// determinant in front. Refines `frag_enc()`.
    ///
    /// The loop is the spec's recursion read forwards: each turn writes one
    /// `Frag(m)` head and `m` blocks, and the invariant says the bits written
    /// so far, followed by the encoding of what is left, are the encoding of
    /// the whole. 11.9.3.8.3's note falls out of the shape -- the loop always
    /// exits through a `Final` head, so an exact multiple of 16K ends with a
    /// zero-length octet.
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn write_frag(&mut self, src: &[u8], from: usize, nbits: usize) -> (ok: bool)
        requires
            old(self).wf(),
            nbits % 8 == 0,
            from + nbits <= 8 * src@.len(),
            8 * src@.len() <= usize::MAX,
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written()
                =~= old(self).written()
                    + frag_enc_rec(bits_of(src@).skip(from as int).take(nbits as int)),
    {
        proof { lemma_lh_p2(); }
        let ghost w0 = *self;
        let ghost content = bits_of(src@).skip(from as int).take(nbits as int);
        let mut off: usize = 0;
        let mut left: usize = nbits / 8;
        assert(left * 8 == nbits) by (nonlinear_arith) requires left == nbits / 8, nbits % 8 == 0;
        assert(content.len() == nbits);
        assert(content.skip(0) =~= content);
        while left >= 16384
            invariant
                self.wf(),
                self.buf@.len() == w0.buf@.len(),
                off + 8 * left == nbits,
                off % 8 == 0,
                nbits % 8 == 0,
                from + nbits <= 8 * src@.len(),
                8 * src@.len() <= usize::MAX,
                content == bits_of(src@).skip(from as int).take(nbits as int),
                content.len() == nbits,
                self.written() + frag_enc_rec(content.skip(off as int))
                    =~= w0.written() + frag_enc_rec(content),
            decreases left,
        {
            let m: usize = if left / 16384 >= 4 { 4 } else { left / 16384 };
            let n: usize = m * 16384 * 8;
            proof {
                assert((nbits - off) / 8 == left) by (nonlinear_arith)
                    requires nbits - off == 8 * left;
                {}
                lemma_frag_enc_step(content, off as nat, m as nat, n as nat);
                lemma_lh_wf_iff(LenHead::Frag(m as u64));
            }
            let ghost before = self.written();
            if !self.write_lh(LenHead::Frag(m as u64)) { return false; }
            if !self.write_slice(src, from + off, n) { return false; }
            proof {
                lemma_frag_loop_step(before, self.written(), w0.written(), content,
                                     bits_of(src@), from as nat, nbits as nat,
                                     off as nat, m as nat, n as nat);
            }
            off = off + n;
            left = left - m * 16384;
        }
        // the remainder, under one block: a `Final` head and the bits
        let ghost rest = content.skip(off as int);
        proof {
            assert(rest.len() == 8 * left);
            assert(rest.len() / 8 == left) by (nonlinear_arith)
                requires rest.len() == 8 * left;
            {}
            lemma_frag_enc_last(content, off as nat);
            lemma_lh_wf_iff(LenHead::Final(left as u64));
        }
        if !self.write_lh(LenHead::Final(left as u64)) { return false; }
        if !self.write_slice(src, from + off, 8 * left) { return false; }
        proof {
            lemma_frag_src_window(bits_of(src@), from as nat, nbits as nat,
                                  off as nat, (8 * left) as nat);
            assert(rest.take((8 * left) as int) =~= rest);
        }
        true
    }
}

} // verus!

verus! {

/// What the decoder still owes when it is part-way through a fragmented value:
/// the octets already reassembled, the bits already consumed, and whether the
/// last fragment was below the cap -- in which case 11.9.3.8.1 says what
/// follows must fit in a single block, so another fragment is not a legal
/// continuation.
pub open spec fn frag_cont(
    acc: Seq<bool>, consumed: nat, pending: bool, r: Option<(Seq<bool>, nat)>,
) -> Option<(Seq<bool>, nat)> {
    match r {
        Some((c2, k2)) =>
            if pending && c2.len() / 8 >= 16384 {
                None
            } else {
                Some((acc + c2, (consumed + k2) as nat))
            },
        None => None,
    }
}

/// A head is 8 or 16 bits, so it is neither empty nor longer than what it was
/// read from -- the two guards `frag_dec_rec` puts in front of the branch.
pub proof fn lemma_lh_dec_k(b: Seq<bool>)
    requires lh_dec()(b) is Some,
    ensures
        lh_wf()(lh_dec()(b).unwrap().0),
        8 <= lh_dec()(b).unwrap().1 <= b.len(),
{
    lemma_lh_format();
    lemma_lh_dec_same(b);
    let h = lh_dec()(b).unwrap().0;
    let k = lh_dec()(b).unwrap().1;
    assert(b.take(k as int) == lh_enc()(h));
    lemma_lh_enc_len_bounds(h);
}

/// A `Frag` head is followed by at least one whole block, so whatever it
/// introduces is 16K octets or more. That is what makes 11.9.3.8.1's
/// maximality check fail for a *previous* fragment below the cap -- and so
/// what lets the loop reject a second below-cap fragment on the spot.
pub proof fn lemma_frag_dec_block(cur: Seq<bool>, m: nat, k: nat)
    requires
        lh_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Frag(m as u64), k, Flg::SameVer)),
        1 <= m <= 4,
    ensures
        frag_dec_rec(cur) is None || frag_dec_rec(cur).unwrap().0.len() / 8 >= 16384,
{
    lemma_lh_dec_k(cur);
    let bits = frag_bits(m);
    if k + bits <= cur.len() {
        match frag_dec_rec(cur.skip((k + bits) as int)) {
            Some((c2, k3)) => {
                if m == 4 || c2.len() / 8 < 16384 {
                    let whole = cur.skip(k as int).take(bits as int) + c2;
                    assert(whole.len() >= bits);
                    assert(bits == 8 * (m * 16384));
                    assert(whole.len() / 8 >= 16384) by (nonlinear_arith)
                        requires whole.len() >= 8 * (m * 16384), m >= 1;
                }
            },
            None => {},
        }
    }
}

/// One turn of the reassembly loop, on a `Frag` head.
pub proof fn lemma_frag_dec_step_frag(
    start: Seq<bool>, cur: Seq<bool>, acc: Seq<bool>, consumed: nat, pending: bool,
    m: nat, k: nat, bits: nat,
)
    requires
        cur == start.skip(consumed as int),
        consumed + cur.len() == start.len(),
        lh_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Frag(m as u64), k, Flg::SameVer)),
        1 <= m <= 4,
        bits == frag_bits(m),
        k + bits <= cur.len(),
        frag_dec_rec(start) == frag_cont(acc, consumed, pending, frag_dec_rec(cur)),
        !pending,
    ensures
        frag_dec_rec(start)
            == frag_cont(acc + cur.skip(k as int).take(bits as int),
                         (consumed + k + bits) as nat, m < 4,
                         frag_dec_rec(start.skip((consumed + k + bits) as int))),
{
    lemma_lh_dec_k(cur);
    let cur2 = cur.skip((k + bits) as int);
    assert(cur2 =~= start.skip((consumed + k + bits) as int));
    let head = cur.skip(k as int).take(bits as int);
    match frag_dec_rec(cur2) {
        Some((c2, k3)) => {
            assert((acc + head) + c2 =~= acc + (head + c2));
        },
        None => {},
    }
}

/// And on a `Final` head, which ends it.
pub proof fn lemma_frag_dec_step_final(
    start: Seq<bool>, cur: Seq<bool>, acc: Seq<bool>, consumed: nat, pending: bool,
    n: nat, k: nat,
)
    requires
        cur == start.skip(consumed as int),
        consumed + cur.len() == start.len(),
        lh_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Final(n as u64), k, Flg::SameVer)),
        n < 16384,
        k + 8 * n <= cur.len(),
        frag_dec_rec(start) == frag_cont(acc, consumed, pending, frag_dec_rec(cur)),
    ensures
        frag_dec_rec(start)
            == Some::<(Seq<bool>, nat)>((acc + cur.skip(k as int).take((8 * n) as int),
                                         (consumed + k + 8 * n) as nat)),
{
    lemma_lh_dec_k(cur);
    let c2 = cur.skip(k as int).take((8 * n) as int);
    assert(c2.len() == 8 * n);
    assert(c2.len() / 8 == n) by (nonlinear_arith) requires c2.len() == 8 * n;
}

impl<'a> BitReader<'a> {
    /// Read a fragmented length determinant and the content it introduces,
    /// returning the content as octets. Refines `frag_dec()`.
    ///
    /// The content is copied out rather than left in place. `frag_dec` is
    /// stated over the *reassembled* content -- fragmentation interleaves
    /// determinants with content, so the bits of a long value are not
    /// contiguous on the wire and there is nothing to point at.
    ///
    /// The spec recurses from the outside in and checks 11.9.3.8.1's
    /// maximality on the length of everything that follows; the loop runs
    /// forwards, so the same check reads as "a fragment below the cap must be
    /// the last one" -- which is the same condition, since any further
    /// fragment contributes a whole block on its own.
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn read_frag(&mut self) -> (res: Option<Vec<u8>>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& frag_dec()(old(self).rem())
                        == Some::<(Seq<bool>, nat, Flg)>(
                            (bits_of(v@), (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    // the content came out of the buffer, so it is no bigger:
                    // a caller can size an inner reader without a bounds check
                    &&& v@.len() <= old(self).buf@.len()
                },
                None => frag_dec()(old(self).rem()) is None,
            },
    {
        reveal(frag_dec);
        let ghost r0 = *self;
        let ghost start = r0.rem();
        let mut out: Vec<u8> = Vec::new();
        let mut pending: bool = false;
        loop
            invariant
                self.wf(),
                self.buf == r0.buf,
                r0.pos <= self.pos,
                self.rem() == start.skip((self.pos - r0.pos) as int),
                (self.pos - r0.pos) + self.rem().len() == start.len(),
                frag_dec_rec(start)
                    == frag_cont(bits_of(out@), (self.pos - r0.pos) as nat, pending,
                                 frag_dec_rec(self.rem())),
                8 * out@.len() <= self.pos - r0.pos,
            decreases 8 * self.buf@.len() - self.pos,
        {
            let ghost cur = self.rem();
            let ghost consumed = (self.pos - r0.pos) as nat;
            let ghost acc = bits_of(out@);
            let p0 = self.pos;
            let h = match self.read_lh() {
                Some(h) => h,
                None => return None,
            };
            proof { lemma_lh_dec_k(cur); lemma_lh_wf_iff(h); }
            let k = self.pos - p0;
            match h {
                LenHead::Final(n) => {
                    if 8 * (n as usize) > self.buf.len() * 8 - self.pos {
                        assert(k + 8 * n > cur.len());
                        return None;
                    }
                    proof { lemma_rem_skip(self.buf@, p0 as nat, k as nat); }
                    let ghost body = self.rem();
                    if !self.read_octets(n as usize, &mut out) { return None; }
                    proof {
                        lemma_bits_of_push(Seq::<u8>::empty(), 0u8);
                        assert(body =~= cur.skip(k as int));
                        lemma_frag_dec_step_final(start, cur, acc, consumed, pending,
                                                  n as nat, k as nat);
                    }
                    return Some(out);
                },
                LenHead::Frag(m) => {
                    // a fragment below the cap has to be the last one
                    if pending {
                        proof { lemma_frag_dec_block(cur, m as nat, k as nat); }
                        return None;
                    }
                    let bits: usize = (m as usize) * 16384 * 8;
                    if bits > self.buf.len() * 8 - self.pos {
                        assert(frag_bits(m as nat) == bits as nat);
                        assert(k + bits > cur.len());
                        return None;
                    }
                    proof { lemma_rem_skip(self.buf@, p0 as nat, k as nat); }
                    let ghost body = self.rem();
                    if !self.read_octets((m as usize) * 16384, &mut out) { return None; }
                    proof {
                        assert(body =~= cur.skip(k as int));
                        assert(frag_bits(m as nat) == bits as nat);
                        lemma_frag_dec_step_frag(start, cur, acc, consumed, pending,
                                                 m as nat, k as nat, bits as nat);
                        lemma_rem_skip(self.buf@, r0.pos as nat,
                                       (self.pos - r0.pos) as nat);
                    }
                    pending = m < 4;
                },
            }
        }
    }
}

/// An open type's content, as `read_frag_ref` gives it: the reader's own
/// octets when they lie there whole, else a copy.
pub enum Octets<'a> {
    Borrowed(&'a [u8]),
    Owned(Vec<u8>),
}

impl<'a> View for Octets<'a> {
    type V = Seq<u8>;

    open spec fn view(&self) -> Seq<u8> {
        match self {
            Octets::Borrowed(s) => s@,
            Octets::Owned(v) => v@,
        }
    }
}

impl<'a> Octets<'a> {
    #[inline]
    pub fn as_slice(&self) -> (s: &[u8])
        ensures s@ == self@,
    {
        match self {
            Octets::Borrowed(s) => s,
            Octets::Owned(v) => v.as_slice(),
        }
    }

    #[inline]
    pub fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    {
        match self {
            Octets::Borrowed(s) => s.len(),
            Octets::Owned(v) => v.len(),
        }
    }
}

impl<'a> BitReader<'a> {
    /// `read_frag`, but a content of one fragment that starts on an octet
    /// boundary is not copied: it is that slice of the buffer. An open
    /// type's content in APER always starts on one, and is one fragment
    /// below 16K octets. Refines `frag_dec()`, as `read_frag` does.
    #[inline]
    pub fn read_frag_ref(&mut self) -> (res: Option<Octets<'a>>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& frag_dec()(old(self).rem())
                        == Some::<(Seq<bool>, nat, Flg)>(
                            (bits_of(v@), (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& v@.len() <= old(self).buf@.len()
                },
                None => frag_dec()(old(self).rem()) is None,
            },
    {
        let ghost start = self.rem();
        let p0 = self.pos;
        if let Some(h) = self.read_lh() {
            proof { lemma_lh_dec_k(start); lemma_lh_wf_iff(h); }
            let k = self.pos - p0;
            if let LenHead::Final(n) = h {
                if self.pos % 8 == 0 && 8 * (n as usize) <= self.buf.len() * 8 - self.pos {
                    let j = self.pos / 8;
                    assert(j + n <= self.buf.len()) by (nonlinear_arith)
                        requires j == self.pos / 8, self.pos % 8 == 0,
                                 8 * n <= 8 * self.buf@.len() - self.pos;
                    let c = vstd::slice::slice_subrange(self.buf, j, j + (n as usize));
                    proof {
                        reveal(frag_dec);
                        assert(start.skip(0) =~= start);
                        assert(Seq::<bool>::empty() + start.skip(k as int).take((8 * n) as int)
                               =~= start.skip(k as int).take((8 * n) as int));
                        lemma_frag_dec_step_final(start, start, Seq::<bool>::empty(), 0, false,
                                                  n as nat, k as nat);
                        crate::uper::fast::lemma_bits_of_subrange(self.buf@, j as int, (j + n) as int);
                        assert(8 * j == self.pos);
                        assert(start.skip(k as int).take((8 * n) as int)
                               =~= bits_of(self.buf@).subrange(8 * j as int, 8 * (j + n) as int));
                    }
                    self.pos = self.pos + 8 * (n as usize);
                    return Some(Octets::Borrowed(c));
                }
            }
        }
        // anything else as `read_frag` reads it, from the start
        self.pos = p0;
        assert(self.rem() == start);
        match self.read_frag() {
            Some(v) => Some(Octets::Owned(v)),
            None => None,
        }
    }
}

} // verus!
