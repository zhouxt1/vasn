//! What it means to be an aligned-PER format, and how formats compose.
//!
//! An APER encoding depends on where it starts. X.691 aligns some fields to an
//! octet boundary (constrained whole numbers with a range over 255, length
//! determinants, strings longer than 16 bits), and the number of padding bits
//! in front of such a field is decided by the position it would otherwise
//! start at. So a value no longer has one encoding: it has one per starting
//! position.
//!
//! This module is `uper::format` with that position made explicit. An encoder
//! takes `pos`, the absolute bit position the encoding starts at, counted from
//! the start of the outermost encoding (X.691 11.1.4; an open type's content
//! starts again at 0). A decoder takes an `In`: that position, and the bits
//! from there on. Only `align` looks at the position, through `pos % 8`;
//! every combinator just passes `pos + k` along, where `k` is the number of
//! bits the parts before have taken. Keeping it absolute rather than reducing
//! it mod 8 at each step keeps modular arithmetic out of every combinator's
//! proof.
//!
//! The three properties are UPER's, stated at every position:
//!
//!   * **surjection** — `dec((pos, enc(pos, a) + rest))` returns `a`, the
//!     length of `enc(pos, a)` and `SameVer`;
//!   * **injection** — anything `dec((pos, _))` accepts as `SameVer` begins
//!     with `enc(pos, a)` for the `a` it returned;
//!   * **weak injection** — anything `dec` accepts is well formed and was
//!     decoded from bits it had.
//!
//! Well-formedness is a property of the value alone, so `Wf` is UPER's.
//!
//! A UPER format is an APER format that ignores the position (`lift`). That
//! is how the fields X.691 encodes the same way in both variants (a BOOLEAN,
//! a constrained whole number of range up to 255, a presence bitmap, a CHOICE
//! index, the extension bit) come across with their proofs unchanged.
//!
//! The names are UPER's on purpose. Generated APER code is generated UPER code
//! with `vasn::aper` imported in place of `vasn::uper`, a decoder's input
//! written `r.at()` where UPER has `r.rem()`, and an encoder's output
//! `e(pos, v)` where UPER has `e(v)`.
use vstd::prelude::*;
use crate::uper::format as u;
pub use crate::uper::format::{Flg, flg_join, with_same, Wf};
#[cfg(verus_keep_ghost)] // spec and proof items: erased from a plain build
pub use crate::uper::format::{flg_add, lemma_take_add, lemma_take_split};
#[cfg(verus_keep_ghost)]
pub use crate::uper::opentype::zeros;

verus! {

/// What a decoder reads: the bit position it starts at, and the bits from
/// there on.
pub type In = (nat, Seq<bool>);

/// `k` bits further on.
pub open spec fn adv(i: In, k: nat) -> In { ((i.0 + k) as nat, i.1.skip(k as int)) }

pub type Enc<A> = spec_fn(nat, A) -> Seq<bool>;
pub type Dec<A> = spec_fn(In) -> Option<(A, nat, Flg)>;

pub open spec fn surjective<A>(wf: Wf<A>, enc: Enc<A>, dec: Dec<A>) -> bool {
    forall|pos: nat, a: A, rest: Seq<bool>|
        wf(a) ==> #[trigger] dec((pos, enc(pos, a) + rest))
            == Some::<(A, nat, Flg)>((a, enc(pos, a).len(), Flg::SameVer))
}

/// Non-malleability, and it only holds for a same-version decode.
pub open spec fn injective<A>(wf: Wf<A>, enc: Enc<A>, dec: Dec<A>) -> bool {
    forall|i: In|
        (#[trigger] dec(i)).is_some() && dec(i).unwrap().2 is SameVer ==> {
            let a = dec(i).unwrap().0;
            let k = dec(i).unwrap().1;
            i.1.take(k as int) == enc(i.0, a)
        }
}

/// What survives a different-version decode: the value is well formed, and
/// the decoder consumed only bits that were there.
pub open spec fn weak_injective<A>(wf: Wf<A>, enc: Enc<A>, dec: Dec<A>) -> bool {
    forall|i: In| (#[trigger] dec(i)).is_some() ==> {
        let a = dec(i).unwrap().0;
        let k = dec(i).unwrap().1;
        wf(a) && k <= i.1.len()
    }
}

pub open spec fn is_format<A>(wf: Wf<A>, enc: Enc<A>, dec: Dec<A>) -> bool {
    &&& surjective(wf, enc, dec)
    &&& injective(wf, enc, dec)
    &&& weak_injective(wf, enc, dec)
}

// ------------------------------------------------------------------ lift

/// A UPER format, read as an APER format that does not depend on position.
#[verifier::opaque]
pub open spec fn lift_enc<A>(e: u::Enc<A>) -> Enc<A> {
    |pos: nat, a: A| e(a)
}

#[verifier::opaque]
pub open spec fn lift_dec<A>(d: u::Dec<A>) -> Dec<A> {
    |i: In| d(i.1)
}

pub proof fn lemma_lift_format<A>(w: Wf<A>, e: u::Enc<A>, d: u::Dec<A>)
    requires u::is_format(w, e, d),
    ensures is_format(w, lift_enc(e), lift_dec(d)),
{
    reveal(lift_enc); reveal(lift_dec);
    let e2 = lift_enc(e);
    let d2 = lift_dec(d);
    assert forall|pos: nat, a: A, rest: Seq<bool>| w(a) implies
        #[trigger] d2((pos, e2(pos, a) + rest))
            == Some::<(A, nat, Flg)>((a, e2(pos, a).len(), Flg::SameVer))
    by {
        assert(d(e(a) + rest) == Some::<(A, nat, Flg)>((a, e(a).len(), Flg::SameVer)));
    }
    assert forall|i: In| (#[trigger] d2(i)).is_some() implies {
        let a = d2(i).unwrap().0;
        let k = d2(i).unwrap().1;
        &&& w(a) && k <= i.1.len()
        &&& d2(i).unwrap().2 is SameVer ==> i.1.take(k as int) == e2(i.0, a)
    } by {
        assert(d(i.1).is_some());
    }
}

// ------------------------------------------------------------------ align

/// The number of zero bits that bring `pos` to the next octet boundary: 0 if
/// it is on one already.
pub open spec fn pad(pos: nat) -> nat { ((8 - pos % 8) as nat) % 8 }

pub proof fn lemma_pad(pos: nat)
    ensures
        pad(pos) < 8,
        (pos + pad(pos)) % 8 == 0,
        pos % 8 == 0 ==> pad(pos) == 0,
{
}

pub open spec fn align_wf() -> Wf<()> { |v: ()| true }

/// X.691 11.1.4 (and 3.7.17, "octet-aligned"): padding bits in front of an
/// octet-aligned field, set to 0.
pub open spec fn align_enc() -> Enc<()> { |pos: nat, v: ()| zeros(pad(pos)) }

/// Padding that is not all zeros is rejected. X.691 says the bits are zero;
/// accepting others would give one value two encodings, and injection would
/// fail.
pub open spec fn align_dec() -> Dec<()> {
    |i: In|
        if i.1.len() >= pad(i.0) && i.1.take(pad(i.0) as int) == zeros(pad(i.0)) {
            Some(((), pad(i.0), Flg::SameVer))
        } else {
            None
        }
}

pub proof fn lemma_align_format()
    ensures is_format(align_wf(), align_enc(), align_dec()),
{
    let w = align_wf();
    let e = align_enc();
    let d = align_dec();
    assert forall|pos: nat, v: (), rest: Seq<bool>| w(v) implies
        #[trigger] d((pos, e(pos, v) + rest))
            == Some::<((), nat, Flg)>((v, e(pos, v).len(), Flg::SameVer))
    by {
        lemma_take_add(zeros(pad(pos)), rest);
    }
}

// ------------------------------------------------------------------ the pair

#[verifier::opaque]
pub open spec fn pair_wf<A, B>(w1: Wf<A>, w2: Wf<B>) -> Wf<(A, B)> {
    |p: (A, B)| w1(p.0) && w2(p.1)
}

/// The second component starts where the first ends.
#[verifier::opaque]
pub open spec fn pair_enc<A, B>(e1: Enc<A>, e2: Enc<B>) -> Enc<(A, B)> {
    |pos: nat, p: (A, B)| e1(pos, p.0) + e2(pos + e1(pos, p.0).len(), p.1)
}

#[verifier::opaque]
pub open spec fn pair_dec<A, B>(d1: Dec<A>, d2: Dec<B>) -> Dec<(A, B)> {
    |i: In|
        match d1(i) {
            Some((x, k1, f1)) => match d2(adv(i, k1)) {
                Some((y, k2, f2)) => Some(((x, y), (k1 + k2) as nat, flg_add(f1, f2))),
                None => None,
            },
            None => None,
        }
}

/// Concatenating two formats yields a format. The one fact this needs beyond
/// the UPER proof: the encoder starts the second component at
/// `pos + |e1(pos, x)|` and the decoder at `pos + k1`, and those agree because
/// a same-version decode consumed exactly the encoding.
pub proof fn lemma_pair_format<A, B>(w1: Wf<A>, e1: Enc<A>, d1: Dec<A>,
                                     w2: Wf<B>, e2: Enc<B>, d2: Dec<B>)
    requires is_format(w1, e1, d1), is_format(w2, e2, d2),
    ensures is_format(pair_wf(w1, w2), pair_enc(e1, e2), pair_dec(d1, d2)),
{
    reveal(pair_wf); reveal(pair_enc); reveal(pair_dec);
    let w = pair_wf(w1, w2);
    let e = pair_enc(e1, e2);
    let d = pair_dec(d1, d2);

    assert forall|pos: nat, p: (A, B), rest: Seq<bool>| w(p) implies
        #[trigger] d((pos, e(pos, p) + rest))
            == Some::<((A, B), nat, Flg)>((p, e(pos, p).len(), Flg::SameVer))
    by {
        let s1 = e1(pos, p.0);
        let pos2 = pos + s1.len();
        let s2 = e2(pos2, p.1);
        let b = e(pos, p) + rest;
        assert(b =~= s1 + (s2 + rest));
        assert(d1((pos, b)) == Some::<(A, nat, Flg)>((p.0, s1.len(), Flg::SameVer)));
        lemma_take_add(s1, s2 + rest);
        assert(adv((pos, b), s1.len()) =~= (pos2, s2 + rest));
        assert(d2((pos2, s2 + rest)) == Some::<(B, nat, Flg)>((p.1, s2.len(), Flg::SameVer)));
    }

    assert forall|i: In| (#[trigger] d(i)).is_some() implies {
        let p = d(i).unwrap().0;
        let k = d(i).unwrap().1;
        &&& w(p) && k <= i.1.len()
        &&& d(i).unwrap().2 is SameVer ==> i.1.take(k as int) == e(i.0, p)
    } by {
        let b = i.1;
        assert(d1(i).is_some());
        let x = d1(i).unwrap().0;
        let k1 = d1(i).unwrap().1;
        let f1 = d1(i).unwrap().2;
        let t = adv(i, k1);
        assert(d2(t).is_some());
        let y = d2(t).unwrap().0;
        let k2 = d2(t).unwrap().1;
        let f2 = d2(t).unwrap().2;
        assert(k1 <= b.len());
        assert(k2 <= t.1.len());
        if d(i).unwrap().2 is SameVer {
            assert(f1 is SameVer && f2 is SameVer);
            assert(b.take(k1 as int) == e1(i.0, x));
            assert(e1(i.0, x).len() == k1);
            assert(t.1.take(k2 as int) == e2(t.0, y));
            lemma_take_split(b, k1, k2);
            assert(b.take((k1 + k2) as int) =~= e1(i.0, x) + e2(i.0 + k1, y));
        }
    }
}

// ---------------------------------------------------------------- restriction

#[verifier::opaque]
pub open spec fn restrict_wf<A>(w: Wf<A>, p: spec_fn(A) -> bool) -> Wf<A> {
    |a: A| w(a) && p(a)
}

#[verifier::opaque]
pub open spec fn restrict_dec<A>(d: Dec<A>, p: spec_fn(A) -> bool) -> Dec<A> {
    |i: In| match d(i) {
        Some((a, k, f)) => if p(a) { Some((a, k, f)) } else { None },
        None => None,
    }
}

pub proof fn lemma_restrict_format<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>, p: spec_fn(A) -> bool)
    requires is_format(w, e, d),
    ensures is_format(restrict_wf(w, p), e, restrict_dec(d, p)),
{
    reveal(restrict_wf); reveal(restrict_dec);
    let w2 = restrict_wf(w, p);
    let d2 = restrict_dec(d, p);
    assert forall|pos: nat, a: A, rest: Seq<bool>| w2(a) implies
        #[trigger] d2((pos, e(pos, a) + rest))
            == Some::<(A, nat, Flg)>((a, e(pos, a).len(), Flg::SameVer))
    by {
        assert(d((pos, e(pos, a) + rest))
               == Some::<(A, nat, Flg)>((a, e(pos, a).len(), Flg::SameVer)));
    }
    assert forall|i: In| (#[trigger] d2(i)).is_some() implies {
        let a = d2(i).unwrap().0;
        let k = d2(i).unwrap().1;
        &&& w2(a) && k <= i.1.len()
        &&& d2(i).unwrap().2 is SameVer ==> i.1.take(k as int) == e(i.0, a)
    } by {
        assert(d(i).is_some());
    }
}

// ------------------------------------------------------------ dependent pair

#[verifier::opaque]
pub open spec fn dep_wf<A, B>(w1: Wf<A>, w2: spec_fn(A) -> Wf<B>) -> Wf<(A, B)> {
    |p: (A, B)| w1(p.0) && w2(p.0)(p.1)
}

#[verifier::opaque]
pub open spec fn dep_enc<A, B>(e1: Enc<A>, e2: spec_fn(A) -> Enc<B>) -> Enc<(A, B)> {
    |pos: nat, p: (A, B)| e1(pos, p.0) + e2(p.0)(pos + e1(pos, p.0).len(), p.1)
}

#[verifier::opaque]
pub open spec fn dep_dec<A, B>(d1: Dec<A>, d2: spec_fn(A) -> Dec<B>) -> Dec<(A, B)> {
    |i: In|
        match d1(i) {
            Some((x, k1, f1)) => match d2(x)(adv(i, k1)) {
                Some((y, k2, f2)) => Some(((x, y), (k1 + k2) as nat, flg_add(f1, f2))),
                None => None,
            },
            None => None,
        }
}

/// The dependent version of `lemma_pair_format`: the first value chooses the
/// second format. As in UPER, `weak_injective` supplies the `w1(x)` that makes
/// the chosen format a format even on a different-version decode.
pub proof fn lemma_dep_format<A, B>(w1: Wf<A>, e1: Enc<A>, d1: Dec<A>,
                                    w2: spec_fn(A) -> Wf<B>,
                                    e2: spec_fn(A) -> Enc<B>,
                                    d2: spec_fn(A) -> Dec<B>)
    requires
        is_format(w1, e1, d1),
        forall|a: A| w1(a) ==> is_format(#[trigger] w2(a), e2(a), d2(a)),
    ensures is_format(dep_wf(w1, w2), dep_enc(e1, e2), dep_dec(d1, d2)),
{
    reveal(dep_wf); reveal(dep_enc); reveal(dep_dec);
    let w = dep_wf(w1, w2);
    let e = dep_enc(e1, e2);
    let d = dep_dec(d1, d2);

    assert forall|pos: nat, p: (A, B), rest: Seq<bool>| w(p) implies
        #[trigger] d((pos, e(pos, p) + rest))
            == Some::<((A, B), nat, Flg)>((p, e(pos, p).len(), Flg::SameVer))
    by {
        let s1 = e1(pos, p.0);
        let pos2 = pos + s1.len();
        let s2 = e2(p.0)(pos2, p.1);
        let b = e(pos, p) + rest;
        assert(b =~= s1 + (s2 + rest));
        assert(d1((pos, b)) == Some::<(A, nat, Flg)>((p.0, s1.len(), Flg::SameVer)));
        lemma_take_add(s1, s2 + rest);
        assert(adv((pos, b), s1.len()) =~= (pos2, s2 + rest));
        assert(is_format(w2(p.0), e2(p.0), d2(p.0)));
        assert(d2(p.0)((pos2, s2 + rest)) == Some::<(B, nat, Flg)>((p.1, s2.len(), Flg::SameVer)));
    }

    assert forall|i: In| (#[trigger] d(i)).is_some() implies {
        let p = d(i).unwrap().0;
        let k = d(i).unwrap().1;
        &&& w(p) && k <= i.1.len()
        &&& d(i).unwrap().2 is SameVer ==> i.1.take(k as int) == e(i.0, p)
    } by {
        let b = i.1;
        assert(d1(i).is_some());
        let x = d1(i).unwrap().0;
        let k1 = d1(i).unwrap().1;
        let f1 = d1(i).unwrap().2;
        let t = adv(i, k1);
        assert(w1(x));
        assert(is_format(w2(x), e2(x), d2(x)));
        assert(d2(x)(t).is_some());
        let y = d2(x)(t).unwrap().0;
        let k2 = d2(x)(t).unwrap().1;
        let f2 = d2(x)(t).unwrap().2;
        assert(k1 <= b.len());
        assert(k2 <= t.1.len());
        if d(i).unwrap().2 is SameVer {
            assert(f1 is SameVer && f2 is SameVer);
            assert(b.take(k1 as int) == e1(i.0, x));
            assert(e1(i.0, x).len() == k1);
            assert(t.1.take(k2 as int) == e2(x)(t.0, y));
            lemma_take_split(b, k1, k2);
            assert(b.take((k1 + k2) as int) =~= e1(i.0, x) + e2(x)(i.0 + k1, y));
        }
    }
}

// -------------------------------------------------------------- map (project)

#[verifier::opaque]
pub open spec fn map_wf<A, B>(wa: Wf<A>, to: spec_fn(A) -> B, from: spec_fn(B) -> A) -> Wf<B> {
    |b: B| wa(from(b)) && to(from(b)) == b
}

#[verifier::opaque]
pub open spec fn map_enc<A, B>(ea: Enc<A>, from: spec_fn(B) -> A) -> Enc<B> {
    |pos: nat, b: B| ea(pos, from(b))
}

#[verifier::opaque]
pub open spec fn map_dec<A, B>(da: Dec<A>, to: spec_fn(A) -> B) -> Dec<B> {
    |i: In| match da(i) {
        Some((a, k, f)) => Some((to(a), k, f)),
        None => None,
    }
}

pub proof fn lemma_map_format<A, B>(wa: Wf<A>, ea: Enc<A>, da: Dec<A>,
                                    to: spec_fn(A) -> B, from: spec_fn(B) -> A)
    requires
        is_format(wa, ea, da),
        forall|a: A| wa(a) ==> #[trigger] from(to(a)) == a,
    ensures
        is_format(map_wf(wa, to, from), map_enc(ea, from), map_dec(da, to)),
{
    reveal(map_wf); reveal(map_enc); reveal(map_dec);
    let w = map_wf(wa, to, from);
    let e = map_enc(ea, from);
    let d = map_dec(da, to);
    assert forall|pos: nat, b: B, rest: Seq<bool>| w(b) implies
        #[trigger] d((pos, e(pos, b) + rest))
            == Some::<(B, nat, Flg)>((b, e(pos, b).len(), Flg::SameVer))
    by {
        assert(da((pos, ea(pos, from(b)) + rest))
               == Some::<(A, nat, Flg)>((from(b), ea(pos, from(b)).len(), Flg::SameVer)));
    }
    assert forall|i: In| (#[trigger] d(i)).is_some() implies {
        let v = d(i).unwrap().0;
        let k = d(i).unwrap().1;
        &&& w(v) && k <= i.1.len()
        &&& d(i).unwrap().2 is SameVer ==> i.1.take(k as int) == e(i.0, v)
    } by {
        assert(da(i).is_some());
        let a = da(i).unwrap().0;
        assert(wa(a));
        assert(from(to(a)) == a);
    }
}

// ------------------------------------------------------------------ aligned

/// A format preceded by the padding to the next octet boundary: how X.691
/// octet-aligns a field. The value is `a` itself, not `((), a)`.
pub open spec fn aligned_to<A>() -> spec_fn(((), A)) -> A { |p: ((), A)| p.1 }
pub open spec fn aligned_from<A>() -> spec_fn(A) -> ((), A) { |a: A| ((), a) }

pub open spec fn aligned_wf<A>(w: Wf<A>) -> Wf<A> {
    map_wf(pair_wf(align_wf(), w), aligned_to(), aligned_from())
}

pub open spec fn aligned_enc<A>(e: Enc<A>) -> Enc<A> {
    map_enc(pair_enc(align_enc(), e), aligned_from())
}

pub open spec fn aligned_dec<A>(d: Dec<A>) -> Dec<A> {
    map_dec(pair_dec(align_dec(), d), aligned_to())
}

pub proof fn lemma_aligned_format<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(aligned_wf(w), aligned_enc(e), aligned_dec(d)),
{
    lemma_align_format();
    lemma_pair_format(align_wf(), align_enc(), align_dec(), w, e, d);
    assert forall|p: ((), A)| #[trigger] aligned_from::<A>()(aligned_to::<A>()(p)) == p by {
        let () = p.0;
    }
    lemma_map_format(pair_wf(align_wf(), w), pair_enc(align_enc(), e), pair_dec(align_dec(), d),
                     aligned_to::<A>(), aligned_from::<A>());
}

/// What `aligned` does, unfolded: the padding, then the content starting on an
/// octet boundary.
pub proof fn lemma_aligned_enc_val<A>(e: Enc<A>, pos: nat, a: A)
    ensures
        aligned_enc(e)(pos, a) == zeros(pad(pos)) + e(pos + pad(pos), a),
        (pos + pad(pos)) % 8 == 0,
{
    reveal(map_enc); reveal(pair_enc);
    lemma_pad(pos);
}

pub proof fn lemma_aligned_wf_val<A>(w: Wf<A>, a: A)
    ensures aligned_wf(w)(a) == w(a),
{
    reveal(map_wf); reveal(pair_wf);
}

/// ... and the decoder: the padding checked, then the content decoded from the
/// octet boundary.
pub proof fn lemma_aligned_dec_val<A>(d: Dec<A>, i: In)
    ensures aligned_dec(d)(i) == (
        if i.1.len() >= pad(i.0) && i.1.take(pad(i.0) as int) == zeros(pad(i.0)) {
            match d(adv(i, pad(i.0))) {
                Some((a, k, f)) => Some((a, (pad(i.0) + k) as nat, f)),
                None => None,
            }
        } else {
            None
        }),
{
    reveal(map_dec); reveal(pair_dec);
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Step lemmas, as in `uper::format`: the combinators are opaque, and generated
// code walks one level of a nest at a time with these.

pub broadcast proof fn lemma_pair_wf_val<A, B>(w1: Wf<A>, w2: Wf<B>, x: A, y: B)
    ensures #[trigger] pair_wf(w1, w2)((x, y)) == (w1(x) && w2(y)),
{
    reveal(pair_wf);
}

pub broadcast proof fn lemma_pair_enc_val<A, B>(e1: Enc<A>, e2: Enc<B>, pos: nat, x: A, y: B)
    ensures #[trigger] pair_enc(e1, e2)(pos, (x, y)) == e1(pos, x) + e2(pos + e1(pos, x).len(), y),
{
    reveal(pair_enc);
}

pub proof fn lemma_pair_dec_some<A, B>(d1: Dec<A>, d2: Dec<B>, b: In,
                                       x: A, k1: nat, f1: Flg, y: B, k2: nat, f2: Flg)
    requires
        d1(b) == Some::<(A, nat, Flg)>((x, k1, f1)),
        d2(adv(b, k1)) == Some::<(B, nat, Flg)>((y, k2, f2)),
    ensures pair_dec(d1, d2)(b)
        == Some::<((A, B), nat, Flg)>(((x, y), (k1 + k2) as nat, flg_add(f1, f2))),
{
    reveal(pair_dec);
}

pub proof fn lemma_pair_dec_none_fst<A, B>(d1: Dec<A>, d2: Dec<B>, b: In)
    requires d1(b).is_none(),
    ensures pair_dec(d1, d2)(b).is_none(),
{
    reveal(pair_dec);
}

pub proof fn lemma_pair_dec_none_snd<A, B>(d1: Dec<A>, d2: Dec<B>, b: In,
                                           x: A, k1: nat, f1: Flg)
    requires
        d1(b) == Some::<(A, nat, Flg)>((x, k1, f1)),
        d2(adv(b, k1)).is_none(),
    ensures pair_dec(d1, d2)(b).is_none(),
{
    reveal(pair_dec);
}

pub broadcast proof fn lemma_restrict_wf_val<A>(w: Wf<A>, p: spec_fn(A) -> bool, a: A)
    ensures #[trigger] restrict_wf(w, p)(a) == (w(a) && p(a)),
{
    reveal(restrict_wf);
}

pub proof fn lemma_restrict_dec_some<A>(d: Dec<A>, p: spec_fn(A) -> bool, b: In,
                                        a: A, k: nat, f: Flg)
    requires d(b) == Some::<(A, nat, Flg)>((a, k, f)), p(a),
    ensures restrict_dec(d, p)(b) == Some::<(A, nat, Flg)>((a, k, f)),
{
    reveal(restrict_dec);
}

pub proof fn lemma_restrict_dec_none<A>(d: Dec<A>, p: spec_fn(A) -> bool, b: In)
    requires d(b).is_none() || !p(d(b).unwrap().0),
    ensures restrict_dec(d, p)(b).is_none(),
{
    reveal(restrict_dec);
}

pub broadcast proof fn lemma_dep_wf_val<A, B>(w1: Wf<A>, w2: spec_fn(A) -> Wf<B>, x: A, y: B)
    ensures #[trigger] dep_wf(w1, w2)((x, y)) == (w1(x) && w2(x)(y)),
{
    reveal(dep_wf);
}

pub broadcast proof fn lemma_dep_enc_val<A, B>(e1: Enc<A>, e2: spec_fn(A) -> Enc<B>, pos: nat, x: A, y: B)
    ensures #[trigger] dep_enc(e1, e2)(pos, (x, y)) == e1(pos, x) + e2(x)(pos + e1(pos, x).len(), y),
{
    reveal(dep_enc);
}

pub proof fn lemma_dep_dec_some<A, B>(d1: Dec<A>, d2: spec_fn(A) -> Dec<B>, b: In,
                                      x: A, k1: nat, f1: Flg, y: B, k2: nat, f2: Flg)
    requires
        d1(b) == Some::<(A, nat, Flg)>((x, k1, f1)),
        d2(x)(adv(b, k1)) == Some::<(B, nat, Flg)>((y, k2, f2)),
    ensures dep_dec(d1, d2)(b)
        == Some::<((A, B), nat, Flg)>(((x, y), (k1 + k2) as nat, flg_add(f1, f2))),
{
    reveal(dep_dec);
}

pub proof fn lemma_dep_dec_none_fst<A, B>(d1: Dec<A>, d2: spec_fn(A) -> Dec<B>, b: In)
    requires d1(b).is_none(),
    ensures dep_dec(d1, d2)(b).is_none(),
{
    reveal(dep_dec);
}

pub proof fn lemma_dep_dec_none_snd<A, B>(d1: Dec<A>, d2: spec_fn(A) -> Dec<B>, b: In,
                                          x: A, k1: nat, f1: Flg)
    requires
        d1(b) == Some::<(A, nat, Flg)>((x, k1, f1)),
        d2(x)(adv(b, k1)).is_none(),
    ensures dep_dec(d1, d2)(b).is_none(),
{
    reveal(dep_dec);
}

pub broadcast proof fn lemma_map_wf_val<A, B>(wa: Wf<A>, to: spec_fn(A) -> B,
                                              from: spec_fn(B) -> A, b: B)
    ensures #[trigger] map_wf(wa, to, from)(b) == (wa(from(b)) && to(from(b)) == b),
{
    reveal(map_wf);
}

pub broadcast proof fn lemma_map_enc_val<A, B>(ea: Enc<A>, from: spec_fn(B) -> A, pos: nat, b: B)
    ensures #[trigger] map_enc(ea, from)(pos, b) == ea(pos, from(b)),
{
    reveal(map_enc);
}

pub proof fn lemma_map_dec_some<A, B>(da: Dec<A>, to: spec_fn(A) -> B, bits: In,
                                      a: A, k: nat, f: Flg)
    requires da(bits) == Some::<(A, nat, Flg)>((a, k, f)),
    ensures map_dec(da, to)(bits) == Some::<(B, nat, Flg)>((to(a), k, f)),
{
    reveal(map_dec);
}

pub proof fn lemma_map_dec_none<A, B>(da: Dec<A>, to: spec_fn(A) -> B, bits: In)
    requires da(bits).is_none(),
    ensures map_dec(da, to)(bits).is_none(),
{
    reveal(map_dec);
}

pub broadcast proof fn lemma_lift_enc_val<A>(e: u::Enc<A>, pos: nat, a: A)
    ensures #[trigger] lift_enc(e)(pos, a) == e(a),
{
    reveal(lift_enc);
}

pub broadcast proof fn lemma_lift_dec_val<A>(d: u::Dec<A>, i: In)
    ensures #[trigger] lift_dec(d)(i) == d(i.1),
{
    reveal(lift_dec);
}

/// Bundled for `broadcast use` at the top of generated modules.
/// UPER's are included: the formats lifted from UPER are built from its
/// combinators, and their well-formedness is UPER's.
pub broadcast group format_steps {
    u::format_steps,
    lemma_pair_wf_val,
    lemma_pair_enc_val,
    lemma_restrict_wf_val,
    lemma_dep_wf_val,
    lemma_dep_enc_val,
    lemma_lift_enc_val,
    lemma_lift_dec_val,
}

/// UPER keeps `map`'s step lemmas in `prim`; generated code names this group.
pub broadcast group map_steps {
    crate::uper::prim::map_steps,
    lemma_map_wf_val,
    lemma_map_enc_val,
}

} // verus!

verus! {

// ------------------------------------------------------------------ example
//
// What the definitions say about a concrete case, as a check on them: a
// 1-bit field, then a 16-bit field X.691 octet-aligns (a constrained whole
// number of range 257..65536, 11.5.7.3). Started at bit 0 the second field
// gets 7 bits of padding; started at bit 3 it gets 4; either way it ends on
// an octet boundary.

pub open spec fn example_enc() -> Enc<(u64, u64)> {
    pair_enc(lift_enc(crate::uper::prim::uint_enc(1)),
             aligned_enc(lift_enc(crate::uper::prim::uint_enc(16))))
}

pub proof fn lemma_example(x: u64, v: u64)
    ensures
        example_enc()(0, (x, v)).len() == 24,
        example_enc()(3, (x, v)).len() == 21,
        example_enc()(3, (x, v)) == crate::uper::prim::uint_enc(1)(x) + zeros(4)
                                    + crate::uper::prim::uint_enc(16)(v),
{
    reveal(pair_enc); reveal(lift_enc);
    let e16 = lift_enc(crate::uper::prim::uint_enc(16));
    lemma_aligned_enc_val(e16, 1, v);
    lemma_aligned_enc_val(e16, 4, v);
    crate::uper::prim::lemma_uint_enc_len(1, x);
    crate::uper::prim::lemma_uint_enc_len(16, v);
}

} // verus!
