//! OPTIONAL fields.
//!
//! A UPER SEQUENCE puts a presence bitmap in front of its fields: one bit per
//! OPTIONAL (or DEFAULT) field in the extension root, then the fields
//! themselves, with absent ones contributing nothing.
//!
//! The bitmap is modelled as a right-nested tuple of `bool` built from the
//! ordinary `bool` format with `pair`, not as a packed integer. On the wire
//! that is the same k consecutive bits either way, but it makes the obligation
//! "the bitmap agrees with which fields are present" a structural equality
//! rather than an arithmetic one about set bits and powers of two -- which is
//! what keeps the generated proof linear and fuel-free.
use vstd::prelude::*;
use crate::format::*;

verus! {

#[verifier::opaque]
pub open spec fn opt_wf<A>(present: bool, w: Wf<A>) -> Wf<Option<A>> {
    |o: Option<A>| if present { o is Some && w(o->Some_0) } else { o is None }
}

#[verifier::opaque]
pub open spec fn opt_enc<A>(present: bool, e: Enc<A>) -> Enc<Option<A>> {
    |o: Option<A>| if present && o is Some { e(o->Some_0) } else { Seq::<bool>::empty() }
}

#[verifier::opaque]
pub open spec fn opt_dec<A>(present: bool, d: Dec<A>) -> Dec<Option<A>> {
    |b: Seq<bool>| if present {
        match d(b) {
            Some((v, k, f)) => Some((Some(v), k, f)),
            None => None,
        }
    } else {
        Some((None::<A>, 0nat, Flg::SameVer))
    }
}

pub proof fn lemma_opt_format<A>(present: bool, w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(opt_wf(present, w), opt_enc(present, e), opt_dec(present, d)),
{
    reveal(opt_wf); reveal(opt_enc); reveal(opt_dec);
    let w2 = opt_wf(present, w);
    let e2 = opt_enc(present, e);
    let d2 = opt_dec(present, d);
    assert forall|o: Option<A>, rest: Seq<bool>| w2(o) implies
        #[trigger] d2(e2(o) + rest) == Some::<(Option<A>, nat, Flg)>((o, e2(o).len(), Flg::SameVer))
    by {
        if present {
            assert(d(e(o->Some_0) + rest)
                   == Some::<(A, nat, Flg)>((o->Some_0, e(o->Some_0).len(), Flg::SameVer)));
        }
    }
    assert forall|b: Seq<bool>| (#[trigger] d2(b)).is_some() implies {
        let o = d2(b).unwrap().0;
        let k = d2(b).unwrap().1;
        &&& w2(o) && k <= b.len()
        &&& d2(b).unwrap().2 is SameVer ==> b.take(k as int) == e2(o)
    } by {
        if present {
            assert(d(b).is_some());
        } else {
            assert(b.take(0) =~= Seq::<bool>::empty());
        }
    }
}

// ------------------------------------------------------------- step lemmas

pub broadcast proof fn lemma_opt_wf_val<A>(present: bool, w: Wf<A>, o: Option<A>)
    ensures #[trigger] opt_wf(present, w)(o)
        == (if present { o is Some && w(o->Some_0) } else { o is None }),
{
    reveal(opt_wf);
}

pub broadcast proof fn lemma_opt_enc_val<A>(present: bool, e: Enc<A>, o: Option<A>)
    ensures #[trigger] opt_enc(present, e)(o)
        == (if present && o is Some { e(o->Some_0) } else { Seq::<bool>::empty() }),
{
    reveal(opt_enc);
}

pub proof fn lemma_opt_dec_some<A>(e: Enc<A>, d: Dec<A>, b: Seq<bool>, v: A, k: nat, f: Flg)
    requires d(b) == Some::<(A, nat, Flg)>((v, k, f)),
    ensures opt_dec(true, d)(b) == Some::<(Option<A>, nat, Flg)>((Some(v), k, f)),
{
    reveal(opt_dec);
}

pub proof fn lemma_opt_dec_fail<A>(d: Dec<A>, b: Seq<bool>)
    requires d(b).is_none(),
    ensures opt_dec(true, d)(b).is_none(),
{
    reveal(opt_dec);
}

pub proof fn lemma_opt_dec_absent<A>(d: Dec<A>, b: Seq<bool>)
    ensures opt_dec(false, d)(b) == Some::<(Option<A>, nat, Flg)>((None::<A>, 0nat, Flg::SameVer)),
{
    reveal(opt_dec);
}

pub broadcast group opt_steps {
    lemma_opt_wf_val,
    lemma_opt_enc_val,
}

} // verus!

verus! {

// ------------------------------------------------------------ the 0-bit format
//
// A type with exactly one value carries no information, and X.691 encodes it
// in no bits at all: a constrained whole number whose range is 1 contributes
// nothing, and so does a SEQUENCE with no fields. 3GPP RRC leans on this
// heavily -- `ENUMERATED { true }` as a bare presence flag is everywhere.

#[verifier::opaque]
pub open spec fn unit_wf<A>(a0: A) -> Wf<A> { |a: A| a == a0 }

#[verifier::opaque]
pub open spec fn unit_enc<A>() -> Enc<A> { |a: A| Seq::<bool>::empty() }

#[verifier::opaque]
pub open spec fn unit_dec<A>(a0: A) -> Dec<A> { |b: Seq<bool>| Some((a0, 0nat, Flg::SameVer)) }

pub proof fn lemma_unit_format<A>(a0: A)
    ensures is_format(unit_wf(a0), unit_enc(), unit_dec(a0)),
{
    reveal(unit_wf); reveal(unit_enc); reveal(unit_dec);
    assert forall|a: A, rest: Seq<bool>| unit_wf(a0)(a) implies
        #[trigger] unit_dec(a0)(unit_enc()(a) + rest)
            == Some::<(A, nat, Flg)>((a, unit_enc()(a).len(), Flg::SameVer))
    by { }
    assert forall|b: Seq<bool>| (#[trigger] unit_dec(a0)(b)).is_some() implies {
        let a = unit_dec(a0)(b).unwrap().0;
        let k = unit_dec(a0)(b).unwrap().1;
        &&& unit_wf(a0)(a) && k <= b.len()
        &&& unit_dec(a0)(b).unwrap().2 is SameVer ==> b.take(k as int) == unit_enc()(a)
    } by {
        assert(b.take(0) =~= Seq::<bool>::empty());
    }
}

pub broadcast proof fn lemma_unit_wf_val<A>(a0: A, a: A)
    ensures #[trigger] unit_wf(a0)(a) == (a == a0),
{
    reveal(unit_wf);
}

pub broadcast proof fn lemma_unit_enc_val<A>(a: A)
    ensures #[trigger] unit_enc::<A>()(a) == Seq::<bool>::empty(),
{
    reveal(unit_enc);
}

pub proof fn lemma_unit_dec_val<A>(a0: A, b: Seq<bool>)
    ensures unit_dec(a0)(b) == Some::<(A, nat, Flg)>((a0, 0nat, Flg::SameVer)),
{
    reveal(unit_dec);
}

pub broadcast group unit_steps {
    lemma_unit_wf_val,
    lemma_unit_enc_val,
}

} // verus!

verus! {

/// ASN.1 NULL: one value, no bits. Common in 3GPP as a CHOICE alternative,
/// `SetupRelease { X } ::= CHOICE { release NULL, setup X }`.
#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub struct Null;

pub open spec fn null_wf() -> Wf<Null> { unit_wf(Null) }
pub open spec fn null_enc() -> Enc<Null> { unit_enc() }
pub open spec fn null_dec() -> Dec<Null> { unit_dec(Null) }

pub proof fn lemma_null_format()
    ensures is_format(null_wf(), null_enc(), null_dec()),
{
    lemma_unit_format(Null);
}

} // verus!
