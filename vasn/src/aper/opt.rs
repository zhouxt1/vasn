//! OPTIONAL fields and the 0-bit formats, as in `uper::opt`. A SEQUENCE's
//! presence bitmap is the same bits in both variants; what the port adds is
//! the position, which an absent field passes along unchanged.
use vstd::prelude::*;
use crate::aper::format::*;
pub use crate::uper::opt::Null;

verus! {

#[verifier::opaque]
pub open spec fn opt_wf<A>(present: bool, w: Wf<A>) -> Wf<Option<A>> {
    |o: Option<A>| if present { o is Some && w(o->Some_0) } else { o is None }
}

#[verifier::opaque]
pub open spec fn opt_enc<A>(present: bool, e: Enc<A>) -> Enc<Option<A>> {
    |pos: nat, o: Option<A>| if present && o is Some { e(pos, o->Some_0) } else { Seq::<bool>::empty() }
}

#[verifier::opaque]
pub open spec fn opt_dec<A>(present: bool, d: Dec<A>) -> Dec<Option<A>> {
    |i: In| if present {
        match d(i) {
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
    assert forall|pos: nat, o: Option<A>, rest: Seq<bool>| w2(o) implies
        #[trigger] d2((pos, e2(pos, o) + rest))
            == Some::<(Option<A>, nat, Flg)>((o, e2(pos, o).len(), Flg::SameVer))
    by {
        if present {
            assert(d((pos, e(pos, o->Some_0) + rest))
                   == Some::<(A, nat, Flg)>((o->Some_0, e(pos, o->Some_0).len(), Flg::SameVer)));
        }
    }
    assert forall|i: In| (#[trigger] d2(i)).is_some() implies {
        let o = d2(i).unwrap().0;
        let k = d2(i).unwrap().1;
        &&& w2(o) && k <= i.1.len()
        &&& d2(i).unwrap().2 is SameVer ==> i.1.take(k as int) == e2(i.0, o)
    } by {
        if present {
            assert(d(i).is_some());
        } else {
            assert(i.1.take(0) =~= Seq::<bool>::empty());
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

pub broadcast proof fn lemma_opt_enc_val<A>(present: bool, e: Enc<A>, pos: nat, o: Option<A>)
    ensures #[trigger] opt_enc(present, e)(pos, o)
        == (if present && o is Some { e(pos, o->Some_0) } else { Seq::<bool>::empty() }),
{
    reveal(opt_enc);
}

pub proof fn lemma_opt_dec_some<A>(e: Enc<A>, d: Dec<A>, b: In, v: A, k: nat, f: Flg)
    requires d(b) == Some::<(A, nat, Flg)>((v, k, f)),
    ensures opt_dec(true, d)(b) == Some::<(Option<A>, nat, Flg)>((Some(v), k, f)),
{
    reveal(opt_dec);
}

pub proof fn lemma_opt_dec_fail<A>(d: Dec<A>, b: In)
    requires d(b).is_none(),
    ensures opt_dec(true, d)(b).is_none(),
{
    reveal(opt_dec);
}

pub proof fn lemma_opt_dec_absent<A>(d: Dec<A>, b: In)
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

#[verifier::opaque]
pub open spec fn unit_wf<A>(a0: A) -> Wf<A> { |a: A| a == a0 }

#[verifier::opaque]
pub open spec fn unit_enc<A>() -> Enc<A> { |pos: nat, a: A| Seq::<bool>::empty() }

#[verifier::opaque]
pub open spec fn unit_dec<A>(a0: A) -> Dec<A> { |i: In| Some((a0, 0nat, Flg::SameVer)) }

pub proof fn lemma_unit_format<A>(a0: A)
    ensures is_format(unit_wf(a0), unit_enc(), unit_dec(a0)),
{
    reveal(unit_wf); reveal(unit_enc); reveal(unit_dec);
    assert forall|pos: nat, a: A, rest: Seq<bool>| unit_wf(a0)(a) implies
        #[trigger] unit_dec(a0)((pos, unit_enc()(pos, a) + rest))
            == Some::<(A, nat, Flg)>((a, unit_enc()(pos, a).len(), Flg::SameVer))
    by { }
    assert forall|i: In| (#[trigger] unit_dec(a0)(i)).is_some() implies {
        let a = unit_dec(a0)(i).unwrap().0;
        let k = unit_dec(a0)(i).unwrap().1;
        &&& unit_wf(a0)(a) && k <= i.1.len()
        &&& unit_dec(a0)(i).unwrap().2 is SameVer ==> i.1.take(k as int) == unit_enc()(i.0, a)
    } by {
        assert(i.1.take(0) =~= Seq::<bool>::empty());
    }
}

pub broadcast proof fn lemma_unit_wf_val<A>(a0: A, a: A)
    ensures #[trigger] unit_wf(a0)(a) == (a == a0),
{
    reveal(unit_wf);
}

pub broadcast proof fn lemma_unit_enc_val<A>(pos: nat, a: A)
    ensures #[trigger] unit_enc::<A>()(pos, a) == Seq::<bool>::empty(),
{
    reveal(unit_enc);
}

pub proof fn lemma_unit_dec_val<A>(a0: A, b: In)
    ensures unit_dec(a0)(b) == Some::<(A, nat, Flg)>((a0, 0nat, Flg::SameVer)),
{
    reveal(unit_dec);
}

pub broadcast group unit_steps {
    lemma_unit_wf_val,
    lemma_unit_enc_val,
}

// ------------------------------------------------------------------- NULL
//
// Lifted rather than built on this module's `unit`, so that UPER's
// `read_null`/`write_null` refine it as they stand.

pub open spec fn null_wf() -> Wf<Null> { crate::uper::opt::null_wf() }
pub open spec fn null_enc() -> Enc<Null> { lift_enc(crate::uper::opt::null_enc()) }
pub open spec fn null_dec() -> Dec<Null> { lift_dec(crate::uper::opt::null_dec()) }

pub proof fn lemma_null_format()
    ensures is_format(null_wf(), null_enc(), null_dec()),
{
    crate::uper::opt::lemma_null_format();
    lemma_lift_format(crate::uper::opt::null_wf(), crate::uper::opt::null_enc(),
                      crate::uper::opt::null_dec());
}

} // verus!
