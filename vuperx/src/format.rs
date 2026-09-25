//! What it means to *be* a format, and how formats compose.
//!
//! A format is three spec functions: a well-formedness predicate on values, an
//! encoder from values to bits, and a decoder from bits to a value, a count of
//! bits consumed, and a *version flag*.
//!
//! The flag is what extensibility costs. When a decoder meets extension
//! additions its schema does not know, it skips them, and the value it returns
//! no longer re-encodes to the bits it came from -- the unknown additions are
//! gone. So non-malleability cannot hold unconditionally. `is_format` splits
//! into three properties:
//!
//!   * **surjection** — encoding then decoding round-trips *as the same
//!     version*, and the decoder is not confused by whatever follows;
//!   * **injection** — anything the decoder accepts **as `SameVer`** was the
//!     canonical encoding of the value it returned;
//!   * **weak injection** — anything the decoder accepts at all is a
//!     well-formed value, and was decoded from bits it actually had.
//!
//! This mirrors VUPER's `format_correct_surj` / `format_correct_inj_same` /
//! `format_correct_inj_diff` (`Formats/Comb.v`). VUPER's `inj_diff` says an
//! encoding of the decoded value *exists* and fits in a bounded space; here
//! `enc` is a total function of the value, so the whole content of that
//! property is `wf(a)` -- the value we hand back is one the encoder accepts.
//!
//! VUPER's `local_write`, `encode_consistent`, `encode_invariance`,
//! `decode_invariance` and `format_to_len_correct` are all definitional here,
//! because `enc` is a function of the value alone and `dec` of the bits alone.
use vstd::prelude::*;

verus! {

/// Whether a decode saw exactly the version its schema describes. `DiffVer`
/// means extension additions were added or removed relative to this schema, so
/// the value that came back is *not* a faithful record of the bits.
#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum Flg {
    SameVer,
    DiffVer,
}

/// A composite decode is `SameVer` only if every part was.
pub open spec fn flg_add(f1: Flg, f2: Flg) -> Flg {
    if f1 is SameVer && f2 is SameVer { Flg::SameVer } else { Flg::DiffVer }
}

/// Executable counterpart of `flg_add`, for threading the flag through
/// generated decoders.
#[inline]
pub fn flg_join(f1: Flg, f2: Flg) -> (f: Flg)
    ensures f == flg_add(f1, f2),
{
    match (f1, f2) {
        (Flg::SameVer, Flg::SameVer) => Flg::SameVer,
        _ => Flg::DiffVer,
    }
}

/// Lift a flagless decode result -- every terminal format is `SameVer` by
/// construction -- into the flagged shape the composition lemmas expect, so
/// generated code has one uniform decode shape to consume.
#[inline]
pub fn with_same<A>(o: Option<A>) -> (res: Option<(A, Flg)>)
    ensures
        match o {
            Some(v) => res == Some::<(A, Flg)>((v, Flg::SameVer)),
            None => res is None,
        },
{
    match o {
        Some(v) => Some((v, Flg::SameVer)),
        None => None,
    }
}

pub type Enc<A> = spec_fn(A) -> Seq<bool>;
pub type Dec<A> = spec_fn(Seq<bool>) -> Option<(A, nat, Flg)>;
pub type Wf<A> = spec_fn(A) -> bool;

pub open spec fn surjective<A>(wf: Wf<A>, enc: Enc<A>, dec: Dec<A>) -> bool {
    forall|a: A, rest: Seq<bool>|
        wf(a) ==> #[trigger] dec(enc(a) + rest)
            == Some::<(A, nat, Flg)>((a, enc(a).len(), Flg::SameVer))
}

/// Non-malleability, and it only holds for a same-version decode.
pub open spec fn injective<A>(wf: Wf<A>, enc: Enc<A>, dec: Dec<A>) -> bool {
    forall|b: Seq<bool>|
        (#[trigger] dec(b)).is_some() && dec(b).unwrap().2 is SameVer ==> {
            let a = dec(b).unwrap().0;
            let k = dec(b).unwrap().1;
            b.take(k as int) == enc(a)
        }
}

/// What survives a different-version decode: the value is well formed, so it
/// can be re-encoded, and the decoder consumed only bits that were there.
pub open spec fn weak_injective<A>(wf: Wf<A>, enc: Enc<A>, dec: Dec<A>) -> bool {
    forall|b: Seq<bool>| (#[trigger] dec(b)).is_some() ==> {
        let a = dec(b).unwrap().0;
        let k = dec(b).unwrap().1;
        wf(a) && k <= b.len()
    }
}

pub open spec fn is_format<A>(wf: Wf<A>, enc: Enc<A>, dec: Dec<A>) -> bool {
    &&& surjective(wf, enc, dec)
    &&& injective(wf, enc, dec)
    &&& weak_injective(wf, enc, dec)
}

// ------------------------------------------------------------------ seq facts

pub proof fn lemma_take_add<T>(s1: Seq<T>, s2: Seq<T>)
    ensures (s1 + s2).take(s1.len() as int) =~= s1,
            (s1 + s2).skip(s1.len() as int) =~= s2,
{
}

pub proof fn lemma_take_split<T>(b: Seq<T>, k1: nat, k2: nat)
    requires k1 + k2 <= b.len(),
    ensures b.take((k1 + k2) as int) =~= b.take(k1 as int) + b.skip(k1 as int).take(k2 as int),
{
}

// ------------------------------------------------------------------ the pair

#[verifier::opaque]
pub open spec fn pair_wf<A, B>(w1: Wf<A>, w2: Wf<B>) -> Wf<(A, B)> {
    |p: (A, B)| w1(p.0) && w2(p.1)
}

#[verifier::opaque]
pub open spec fn pair_enc<A, B>(e1: Enc<A>, e2: Enc<B>) -> Enc<(A, B)> {
    |p: (A, B)| e1(p.0) + e2(p.1)
}

#[verifier::opaque]
pub open spec fn pair_dec<A, B>(d1: Dec<A>, d2: Dec<B>) -> Dec<(A, B)> {
    |b: Seq<bool>|
        match d1(b) {
            Some((x, k1, f1)) => match d2(b.skip(k1 as int)) {
                Some((y, k2, f2)) => Some(((x, y), (k1 + k2) as nat, flg_add(f1, f2))),
                None => None,
            },
            None => None,
        }
}

/// Concatenating two formats yields a format. Generated SEQUENCE proofs are a
/// chain of applications of this one lemma.
pub proof fn lemma_pair_format<A, B>(w1: Wf<A>, e1: Enc<A>, d1: Dec<A>,
                                     w2: Wf<B>, e2: Enc<B>, d2: Dec<B>)
    requires is_format(w1, e1, d1), is_format(w2, e2, d2),
    ensures is_format(pair_wf(w1, w2), pair_enc(e1, e2), pair_dec(d1, d2)),
{
    reveal(pair_wf); reveal(pair_enc); reveal(pair_dec);
    let w = pair_wf(w1, w2);
    let e = pair_enc(e1, e2);
    let d = pair_dec(d1, d2);

    assert forall|p: (A, B), rest: Seq<bool>| w(p) implies
        #[trigger] d(e(p) + rest) == Some::<((A, B), nat, Flg)>((p, e(p).len(), Flg::SameVer))
    by {
        let b = e(p) + rest;
        assert(b =~= e1(p.0) + (e2(p.1) + rest));
        assert(d1(b) == Some::<(A, nat, Flg)>((p.0, e1(p.0).len(), Flg::SameVer)));
        lemma_take_add(e1(p.0), e2(p.1) + rest);
        assert(b.skip(e1(p.0).len() as int) =~= e2(p.1) + rest);
        assert(d2(b.skip(e1(p.0).len() as int))
               == Some::<(B, nat, Flg)>((p.1, e2(p.1).len(), Flg::SameVer)));
        assert(e(p).len() == e1(p.0).len() + e2(p.1).len());
    }

    // The two injection properties share all their plumbing: both need to see
    // through `d` to the two component decodes. Only the final equation differs.
    assert forall|b: Seq<bool>| (#[trigger] d(b)).is_some() implies {
        let p = d(b).unwrap().0;
        let k = d(b).unwrap().1;
        &&& w(p) && k <= b.len()
        &&& d(b).unwrap().2 is SameVer ==> b.take(k as int) == e(p)
    } by {
        let p = d(b).unwrap().0;
        let k = d(b).unwrap().1;
        assert(d1(b).is_some());
        let k1 = d1(b).unwrap().1;
        let x = d1(b).unwrap().0;
        let f1 = d1(b).unwrap().2;
        let tail = b.skip(k1 as int);
        assert(d2(tail).is_some());
        let k2 = d2(tail).unwrap().1;
        let y = d2(tail).unwrap().0;
        let f2 = d2(tail).unwrap().2;
        assert(p == (x, y));
        assert(k == k1 + k2);
        assert(k1 <= b.len());
        assert(k2 <= tail.len());
        if d(b).unwrap().2 is SameVer {
            assert(f1 is SameVer && f2 is SameVer);
            assert(b.take(k1 as int) == e1(x));
            assert(tail.take(k2 as int) == e2(y));
            lemma_take_split(b, k1, k2);
            assert(b.take(k as int) =~= e1(x) + e2(y));
            assert(e(p) =~= e1(x) + e2(y));
        }
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------- restriction

#[verifier::opaque]
pub open spec fn restrict_wf<A>(w: Wf<A>, p: spec_fn(A) -> bool) -> Wf<A> {
    |a: A| w(a) && p(a)
}

#[verifier::opaque]
pub open spec fn restrict_dec<A>(d: Dec<A>, p: spec_fn(A) -> bool) -> Dec<A> {
    |b: Seq<bool>| match d(b) {
        Some((a, k, f)) => if p(a) { Some((a, k, f)) } else { None },
        None => None,
    }
}

/// Narrowing the accepted value set yields a format. This is how ASN.1 value
/// constraints (and the unused tail of an ENUMERATED's bit field) are rejected.
pub proof fn lemma_restrict_format<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>, p: spec_fn(A) -> bool)
    requires is_format(w, e, d),
    ensures is_format(restrict_wf(w, p), e, restrict_dec(d, p)),
{
    reveal(restrict_wf); reveal(restrict_dec);
    let w2 = restrict_wf(w, p);
    let d2 = restrict_dec(d, p);
    assert forall|a: A, rest: Seq<bool>| w2(a) implies
        #[trigger] d2(e(a) + rest) == Some::<(A, nat, Flg)>((a, e(a).len(), Flg::SameVer))
    by {
        assert(d(e(a) + rest) == Some::<(A, nat, Flg)>((a, e(a).len(), Flg::SameVer)));
    }
    assert forall|b: Seq<bool>| (#[trigger] d2(b)).is_some() implies {
        let a = d2(b).unwrap().0;
        let k = d2(b).unwrap().1;
        &&& w2(a) && k <= b.len()
        &&& d2(b).unwrap().2 is SameVer ==> b.take(k as int) == e(a)
    } by {
        assert(d(b).is_some());
    }
}

// ------------------------------------------------------------ dependent pair

#[verifier::opaque]
pub open spec fn dep_wf<A, B>(w1: Wf<A>, w2: spec_fn(A) -> Wf<B>) -> Wf<(A, B)> {
    |p: (A, B)| w1(p.0) && w2(p.0)(p.1)
}

#[verifier::opaque]
pub open spec fn dep_enc<A, B>(e1: Enc<A>, e2: spec_fn(A) -> Enc<B>) -> Enc<(A, B)> {
    |p: (A, B)| e1(p.0) + e2(p.0)(p.1)
}

#[verifier::opaque]
pub open spec fn dep_dec<A, B>(d1: Dec<A>, d2: spec_fn(A) -> Dec<B>) -> Dec<(A, B)> {
    |b: Seq<bool>|
        match d1(b) {
            Some((x, k1, f1)) => match d2(x)(b.skip(k1 as int)) {
                Some((y, k2, f2)) => Some(((x, y), (k1 + k2) as nat, flg_add(f1, f2))),
                None => None,
            },
            None => None,
        }
}

/// The dependent version of `lemma_pair_format`: the second format may be
/// chosen by the first value. SEQUENCE uses this to make the body depend on the
/// OPTIONAL/DEFAULT presence bitmap that precedes it, and SEQUENCE OF uses it
/// to make the element count depend on the length determinant.
///
/// Note where the flag enters: the first component's *value* selects the second
/// format, and it is `weak_injective` -- not `injective` -- that supplies the
/// `w1(x)` needed to know that second format is a format at all. That is why
/// `weak_injective` has to carry `wf`, and it is what lets the extension count
/// (which may exceed anything this schema knows) drive the rest of the decode.
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

    assert forall|p: (A, B), rest: Seq<bool>| w(p) implies
        #[trigger] d(e(p) + rest) == Some::<((A, B), nat, Flg)>((p, e(p).len(), Flg::SameVer))
    by {
        let b = e(p) + rest;
        assert(b =~= e1(p.0) + (e2(p.0)(p.1) + rest));
        assert(d1(b) == Some::<(A, nat, Flg)>((p.0, e1(p.0).len(), Flg::SameVer)));
        lemma_take_add(e1(p.0), e2(p.0)(p.1) + rest);
        assert(b.skip(e1(p.0).len() as int) =~= e2(p.0)(p.1) + rest);
        assert(is_format(w2(p.0), e2(p.0), d2(p.0)));
        assert(d2(p.0)(b.skip(e1(p.0).len() as int))
               == Some::<(B, nat, Flg)>((p.1, e2(p.0)(p.1).len(), Flg::SameVer)));
        assert(e(p).len() == e1(p.0).len() + e2(p.0)(p.1).len());
    }

    assert forall|b: Seq<bool>| (#[trigger] d(b)).is_some() implies {
        let p = d(b).unwrap().0;
        let k = d(b).unwrap().1;
        &&& w(p) && k <= b.len()
        &&& d(b).unwrap().2 is SameVer ==> b.take(k as int) == e(p)
    } by {
        assert(d1(b).is_some());
        let k1 = d1(b).unwrap().1;
        let x = d1(b).unwrap().0;
        let f1 = d1(b).unwrap().2;
        let tail = b.skip(k1 as int);
        assert(w1(x));
        assert(is_format(w2(x), e2(x), d2(x)));
        assert(d2(x)(tail).is_some());
        let k2 = d2(x)(tail).unwrap().1;
        let y = d2(x)(tail).unwrap().0;
        let f2 = d2(x)(tail).unwrap().2;
        assert(k1 <= b.len());
        assert(k2 <= tail.len());
        if d(b).unwrap().2 is SameVer {
            assert(f1 is SameVer && f2 is SameVer);
            assert(b.take(k1 as int) == e1(x));
            assert(tail.take(k2 as int) == e2(x)(y));
            lemma_take_split(b, k1, k2);
            assert(b.take((k1 + k2) as int) =~= e1(x) + e2(x)(y));
        }
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Step lemmas.
//
// The composition combinators above are opaque, so a caller cannot see through
// `pair_dec(d1, pair_dec(d2, d3))` by unfolding -- which is the point. A
// generated decoder for an n-field SEQUENCE would otherwise hand the solver an
// n-deep nest of closure applications to unfold eagerly, and the cost grows
// with field count until it blows the resource limit.
//
// Instead, generated code walks the nest one level at a time with these
// lemmas. Each is a single reveal, and each application is O(1) for the
// solver, so a type's proof cost stays linear in its field count.

// ------------------------------------------------------------------- pair

pub broadcast proof fn lemma_pair_wf_val<A, B>(w1: Wf<A>, w2: Wf<B>, x: A, y: B)
    ensures #[trigger] pair_wf(w1, w2)((x, y)) == (w1(x) && w2(y)),
{
    reveal(pair_wf);
}

pub broadcast proof fn lemma_pair_enc_val<A, B>(e1: Enc<A>, e2: Enc<B>, x: A, y: B)
    ensures #[trigger] pair_enc(e1, e2)((x, y)) == e1(x) + e2(y),
{
    reveal(pair_enc);
}

pub proof fn lemma_pair_dec_some<A, B>(d1: Dec<A>, d2: Dec<B>, b: Seq<bool>,
                                       x: A, k1: nat, f1: Flg, y: B, k2: nat, f2: Flg)
    requires
        d1(b) == Some::<(A, nat, Flg)>((x, k1, f1)),
        d2(b.skip(k1 as int)) == Some::<(B, nat, Flg)>((y, k2, f2)),
    ensures pair_dec(d1, d2)(b)
        == Some::<((A, B), nat, Flg)>(((x, y), (k1 + k2) as nat, flg_add(f1, f2))),
{
    reveal(pair_dec);
}

pub proof fn lemma_pair_dec_none_fst<A, B>(d1: Dec<A>, d2: Dec<B>, b: Seq<bool>)
    requires d1(b).is_none(),
    ensures pair_dec(d1, d2)(b).is_none(),
{
    reveal(pair_dec);
}

pub proof fn lemma_pair_dec_none_snd<A, B>(d1: Dec<A>, d2: Dec<B>, b: Seq<bool>,
                                           x: A, k1: nat, f1: Flg)
    requires
        d1(b) == Some::<(A, nat, Flg)>((x, k1, f1)),
        d2(b.skip(k1 as int)).is_none(),
    ensures pair_dec(d1, d2)(b).is_none(),
{
    reveal(pair_dec);
}

// -------------------------------------------------------------- restriction

pub broadcast proof fn lemma_restrict_wf_val<A>(w: Wf<A>, p: spec_fn(A) -> bool, a: A)
    ensures #[trigger] restrict_wf(w, p)(a) == (w(a) && p(a)),
{
    reveal(restrict_wf);
}

pub proof fn lemma_restrict_dec_some<A>(d: Dec<A>, p: spec_fn(A) -> bool, b: Seq<bool>,
                                        a: A, k: nat, f: Flg)
    requires d(b) == Some::<(A, nat, Flg)>((a, k, f)), p(a),
    ensures restrict_dec(d, p)(b) == Some::<(A, nat, Flg)>((a, k, f)),
{
    reveal(restrict_dec);
}

pub proof fn lemma_restrict_dec_none<A>(d: Dec<A>, p: spec_fn(A) -> bool, b: Seq<bool>)
    requires d(b).is_none() || !p(d(b).unwrap().0),
    ensures restrict_dec(d, p)(b).is_none(),
{
    reveal(restrict_dec);
}

// -------------------------------------------------------------- dependent

pub broadcast proof fn lemma_dep_wf_val<A, B>(w1: Wf<A>, w2: spec_fn(A) -> Wf<B>, x: A, y: B)
    ensures #[trigger] dep_wf(w1, w2)((x, y)) == (w1(x) && w2(x)(y)),
{
    reveal(dep_wf);
}

pub broadcast proof fn lemma_dep_enc_val<A, B>(e1: Enc<A>, e2: spec_fn(A) -> Enc<B>, x: A, y: B)
    ensures #[trigger] dep_enc(e1, e2)((x, y)) == e1(x) + e2(x)(y),
{
    reveal(dep_enc);
}

pub proof fn lemma_dep_dec_some<A, B>(d1: Dec<A>, d2: spec_fn(A) -> Dec<B>, b: Seq<bool>,
                                      x: A, k1: nat, f1: Flg, y: B, k2: nat, f2: Flg)
    requires
        d1(b) == Some::<(A, nat, Flg)>((x, k1, f1)),
        d2(x)(b.skip(k1 as int)) == Some::<(B, nat, Flg)>((y, k2, f2)),
    ensures dep_dec(d1, d2)(b)
        == Some::<((A, B), nat, Flg)>(((x, y), (k1 + k2) as nat, flg_add(f1, f2))),
{
    reveal(dep_dec);
}

pub proof fn lemma_dep_dec_none_fst<A, B>(d1: Dec<A>, d2: spec_fn(A) -> Dec<B>, b: Seq<bool>)
    requires d1(b).is_none(),
    ensures dep_dec(d1, d2)(b).is_none(),
{
    reveal(dep_dec);
}

pub proof fn lemma_dep_dec_none_snd<A, B>(d1: Dec<A>, d2: spec_fn(A) -> Dec<B>, b: Seq<bool>,
                                          x: A, k1: nat, f1: Flg)
    requires
        d1(b) == Some::<(A, nat, Flg)>((x, k1, f1)),
        d2(x)(b.skip(k1 as int)).is_none(),
    ensures dep_dec(d1, d2)(b).is_none(),
{
    reveal(dep_dec);
}

/// Bundled for `broadcast use` at the top of generated modules.
pub broadcast group format_steps {
    lemma_pair_wf_val,
    lemma_pair_enc_val,
    lemma_restrict_wf_val,
    lemma_dep_wf_val,
    lemma_dep_enc_val,
}

} // verus!
