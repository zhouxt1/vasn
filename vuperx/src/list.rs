//! Fixed-length lists.
//!
//! This is the first recursive format, and the one SEQUENCE OF, BIT STRING and
//! OCTET STRING all sit on top of: pair a length determinant with a list of
//! that many elements using `dep`, and the length dependency is discharged by a
//! lemma that is already proved.
use vstd::prelude::*;
use crate::format::*;

verus! {

broadcast use {format_steps, crate::prim::map_steps};

/// Concatenated encodings of every element.
pub open spec fn list_enc_rec<A>(l: Seq<A>, e: Enc<A>) -> Seq<bool>
    decreases l.len(),
{
    if l.len() == 0 {
        Seq::<bool>::empty()
    } else {
        e(l[0]) + list_enc_rec(l.skip(1), e)
    }
}

/// Decode exactly `n` elements, left to right.
pub open spec fn list_dec_rec<A>(n: nat, d: Dec<A>, b: Seq<bool>) -> Option<(Seq<A>, nat, Flg)>
    decreases n,
{
    if n == 0 {
        Some((Seq::<A>::empty(), 0nat, Flg::SameVer))
    } else {
        match d(b) {
            Some((v, k, f)) => match list_dec_rec((n - 1) as nat, d, b.skip(k as int)) {
                Some((rest, k2, f2)) => Some((seq![v] + rest, (k + k2) as nat, flg_add(f, f2))),
                None => None,
            },
            None => None,
        }
    }
}

/// A list of fixed-width elements is exactly as wide as the arithmetic says.
/// The extension bitmap needs this: `c` bits, one per addition (19.7).
pub proof fn lemma_list_enc_rec_len<A>(l: Seq<A>, e: Enc<A>, m: nat)
    requires forall|a: A| (#[trigger] e(a)).len() == m,
    ensures list_enc_rec(l, e).len() == l.len() * m,
    decreases l.len(),
{
    if l.len() > 0 {
        lemma_list_enc_rec_len(l.skip(1), e, m);
        assert(l.len() * m == m + (l.len() - 1) * m) by (nonlinear_arith);
    }
}

#[verifier::opaque]
pub open spec fn list_wf<A>(n: nat, w: Wf<A>) -> Wf<Seq<A>> {
    |l: Seq<A>| l.len() == n && forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])
}

#[verifier::opaque]
pub open spec fn list_enc<A>(n: nat, e: Enc<A>) -> Enc<Seq<A>> {
    |l: Seq<A>| list_enc_rec(l, e)
}

#[verifier::opaque]
pub open spec fn list_dec<A>(n: nat, d: Dec<A>) -> Dec<Seq<A>> {
    |b: Seq<bool>| list_dec_rec(n, d, b)
}

pub proof fn lemma_list_format<A>(n: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(list_wf(n, w), list_enc(n, e), list_dec(n, d)),
{
    reveal(list_wf); reveal(list_enc); reveal(list_dec);
    assert forall|l: Seq<A>, rest: Seq<bool>| list_wf(n, w)(l) implies
        #[trigger] list_dec(n, d)(list_enc(n, e)(l) + rest)
            == Some::<(Seq<A>, nat, Flg)>((l, list_enc(n, e)(l).len(), Flg::SameVer))
    by {
        lemma_list_surj(n, w, e, d, l, rest);
    }
    assert forall|b: Seq<bool>| (#[trigger] list_dec(n, d)(b)).is_some() implies {
        let l = list_dec(n, d)(b).unwrap().0;
        let k = list_dec(n, d)(b).unwrap().1;
        &&& list_wf(n, w)(l) && k <= b.len()
        &&& list_dec(n, d)(b).unwrap().2 is SameVer ==> b.take(k as int) == list_enc(n, e)(l)
    } by {
        lemma_list_inj(n, w, e, d, b);
    }
}

pub proof fn lemma_list_surj<A>(n: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>, l: Seq<A>, rest: Seq<bool>)
    requires
        is_format(w, e, d),
        l.len() == n,
        forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i]),
    ensures
        list_dec_rec(n, d, list_enc_rec(l, e) + rest)
            == Some::<(Seq<A>, nat, Flg)>((l, list_enc_rec(l, e).len(), Flg::SameVer)),
    decreases n,
{
    if n == 0 {
        assert(l =~= Seq::<A>::empty());
        assert(list_enc_rec(l, e) =~= Seq::<bool>::empty());
    } else {
        let head = e(l[0]);
        let tail = list_enc_rec(l.skip(1), e);
        assert(list_enc_rec(l, e) =~= head + tail);
        let b = list_enc_rec(l, e) + rest;
        assert(b =~= head + (tail + rest));
        assert(d(b) == Some::<(A, nat, Flg)>((l[0], head.len(), Flg::SameVer)));
        lemma_take_add(head, tail + rest);
        assert(b.skip(head.len() as int) =~= tail + rest);
        assert forall|i: int| 0 <= i < l.skip(1).len() implies w(#[trigger] l.skip(1)[i]) by {
            assert(l.skip(1)[i] == l[i + 1]);
        }
        lemma_list_surj((n - 1) as nat, w, e, d, l.skip(1), rest);
        assert(seq![l[0]] + l.skip(1) =~= l);
    }
}

pub proof fn lemma_list_inj<A>(n: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>, b: Seq<bool>)
    requires is_format(w, e, d), list_dec_rec(n, d, b).is_some(),
    ensures
        ({
            let l = list_dec_rec(n, d, b).unwrap().0;
            let k = list_dec_rec(n, d, b).unwrap().1;
            &&& l.len() == n
            &&& forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])
            &&& k <= b.len()
            &&& list_dec_rec(n, d, b).unwrap().2 is SameVer ==> b.take(k as int) == list_enc_rec(l, e)
        }),
    decreases n,
{
    if n == 0 {
        assert(b.take(0) =~= Seq::<bool>::empty());
        assert(list_enc_rec(Seq::<A>::empty(), e) =~= Seq::<bool>::empty());
    } else {
        let v = d(b).unwrap().0;
        let k1 = d(b).unwrap().1;
        let f1 = d(b).unwrap().2;
        let tailb = b.skip(k1 as int);
        lemma_list_inj((n - 1) as nat, w, e, d, tailb);
        let rest = list_dec_rec((n - 1) as nat, d, tailb).unwrap().0;
        let k2 = list_dec_rec((n - 1) as nat, d, tailb).unwrap().1;
        let f2 = list_dec_rec((n - 1) as nat, d, tailb).unwrap().2;
        let l = seq![v] + rest;
        assert(l.len() == n);
        assert forall|i: int| 0 <= i < l.len() implies w(#[trigger] l[i]) by {
            if i > 0 {
                assert(l[i] == rest[i - 1]);
            }
        }
        lemma_take_split(b, k1, k2);
        assert(l.skip(1) =~= rest);
        assert(l[0] == v);
        if flg_add(f1, f2) is SameVer {
            assert(b.take(k1 as int) == e(v));
            assert(tailb.take(k2 as int) == list_enc_rec(rest, e));
            assert(list_enc_rec(l, e) =~= e(v) + list_enc_rec(rest, e));
        }
    }
}

/// A list of an element format that never reports `DiffVer` never does
/// either. Needed wherever the list's bits have to be pinned down, since
/// non-malleability only holds for a same-version decode.
pub proof fn lemma_list_dec_same<A>(n: nat, d: Dec<A>, b: Seq<bool>)
    requires forall|s: Seq<bool>| (#[trigger] d(s)) is Some ==> d(s).unwrap().2 is SameVer,
    ensures list_dec_rec(n, d, b) is Some ==> list_dec_rec(n, d, b).unwrap().2 is SameVer,
    decreases n,
{
    if n > 0 && d(b) is Some {
        lemma_list_dec_same((n - 1) as nat, d, b.skip(d(b).unwrap().1 as int));
    }
}

// ------------------------------------------------------------- step lemmas

pub broadcast proof fn lemma_list_wf_val<A>(n: nat, w: Wf<A>, l: Seq<A>)
    ensures #[trigger] list_wf(n, w)(l)
        == (l.len() == n && forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])),
{
    reveal(list_wf);
}

pub broadcast proof fn lemma_list_enc_val<A>(n: nat, e: Enc<A>, l: Seq<A>)
    ensures #[trigger] list_enc(n, e)(l) == list_enc_rec(l, e),
{
    reveal(list_enc);
}

pub broadcast proof fn lemma_list_dec_val<A>(n: nat, d: Dec<A>, b: Seq<bool>)
    ensures #[trigger] list_dec(n, d)(b) == list_dec_rec(n, d, b),
{
    reveal(list_dec);
}

/// One element of the recursion, for the exec loop's invariant.
pub proof fn lemma_list_dec_step<A>(n: nat, d: Dec<A>, b: Seq<bool>, v: A, k: nat, f: Flg)
    requires n > 0, d(b) == Some::<(A, nat, Flg)>((v, k, f)),
    ensures
        list_dec_rec(n, d, b) == (match list_dec_rec((n - 1) as nat, d, b.skip(k as int)) {
            Some((rest, k2, f2)) => Some((seq![v] + rest, (k + k2) as nat, flg_add(f, f2))),
            None => None,
        }),
{
}

pub proof fn lemma_list_dec_fail<A>(n: nat, d: Dec<A>, b: Seq<bool>)
    requires n > 0, d(b).is_none(),
    ensures list_dec_rec(n, d, b).is_none(),
{
}

pub broadcast group list_steps {
    lemma_list_wf_val,
    lemma_list_enc_val,
    lemma_list_dec_val,
}

} // verus!

verus! {

use crate::bitspec::*;
use crate::prim::*;

// --------------------------------------------- constrained length determinant
//
// X.691: a SIZE (lb..ub) constraint with ub below 64K encodes the count as a
// constrained whole number over that range -- in UPER, the minimum number of
// bits and no alignment. A fixed size (lb == ub) contributes no length
// determinant at all, which is the `list` format on its own.

pub open spec fn ulen_ok(lb: nat, ub: nat) -> spec_fn(u64) -> bool {
    |v: u64| (v as nat) + lb <= ub
}
pub open spec fn ulen_to(lb: nat) -> spec_fn(u64) -> u64 { |v: u64| (v as nat + lb) as u64 }
pub open spec fn ulen_from(lb: nat) -> spec_fn(u64) -> u64 { |x: u64| (x as nat - lb) as u64 }

pub open spec fn ulen_base_wf(lb: nat, ub: nat, n: nat) -> Wf<u64> {
    restrict_wf(uint_wf(n), ulen_ok(lb, ub))
}
pub open spec fn ulen_base_dec(lb: nat, ub: nat, n: nat) -> Dec<u64> {
    restrict_dec(uint_dec(n), ulen_ok(lb, ub))
}

pub open spec fn ulen_wf(lb: nat, ub: nat, n: nat) -> Wf<u64> {
    map_wf(ulen_base_wf(lb, ub, n), ulen_to(lb), ulen_from(lb))
}
pub open spec fn ulen_enc(lb: nat, ub: nat, n: nat) -> Enc<u64> {
    map_enc(uint_enc(n), ulen_from(lb))
}
pub open spec fn ulen_dec(lb: nat, ub: nat, n: nat) -> Dec<u64> {
    map_dec(ulen_base_dec(lb, ub, n), ulen_to(lb))
}

pub proof fn lemma_ulen_format(lb: nat, ub: nat, n: nat)
    requires 1 <= n <= 56, lb <= ub, ub - lb < p2(n), ub < p2(56),
    ensures is_format(ulen_wf(lb, ub, n), ulen_enc(lb, ub, n), ulen_dec(lb, ub, n)),
{
    let to = ulen_to(lb);
    let from = ulen_from(lb);
    lemma_uint_format(n);
    lemma_restrict_format(uint_wf(n), uint_enc(n), uint_dec(n), ulen_ok(lb, ub));
    assert forall|v: u64| ulen_base_wf(lb, ub, n)(v) implies #[trigger] from(to(v)) == v by {
        crate::prim_read::lemma_p2_mono(56, 64);
        crate::prim_read::lemma_p2_64();
        lemma_restrict_wf_val(uint_wf(n), ulen_ok(lb, ub), v);
        assert(ulen_ok(lb, ub)(v));
    }
    lemma_map_format(ulen_base_wf(lb, ub, n), uint_enc(n), ulen_base_dec(lb, ub, n), to, from);
}

/// The decoded length is inside the schema's SIZE constraint, which is what
/// bounds the element loop and the allocation.
pub proof fn lemma_ulen_wf_bound(lb: nat, ub: nat, n: nat, x: u64)
    requires ulen_wf(lb, ub, n)(x), ub < p2(56),
    ensures lb <= x as nat <= ub,
{
    crate::prim_read::lemma_p2_mono(56, 64);
    crate::prim_read::lemma_p2_64();
    lemma_map_wf_val(ulen_base_wf(lb, ub, n), ulen_to(lb), ulen_from(lb), x);
    let v = ulen_from(lb)(x);
    lemma_restrict_wf_val(uint_wf(n), ulen_ok(lb, ub), v);
    // ok(v) bounds v + lb below 2^64, so the cast in `to` is the identity
    assert((v as nat) + lb <= ub);
    assert(ulen_to(lb)(v) == x);
    assert(x as nat == (v as nat) + lb);
}

/// ... and conversely: every value inside the constraint is well formed, which
/// is what an encoder needs before it may write the determinant.
pub proof fn lemma_ulen_wf_iff(lb: nat, ub: nat, n: nat, x: u64)
    requires 1 <= n <= 56, lb <= ub, ub - lb < p2(n), ub < p2(56),
    ensures ulen_wf(lb, ub, n)(x) <==> lb <= x as nat <= ub,
{
    crate::prim_read::lemma_p2_mono(56, 64);
    crate::prim_read::lemma_p2_64();
    if lb <= x as nat <= ub {
        lemma_map_wf_val(ulen_base_wf(lb, ub, n), ulen_to(lb), ulen_from(lb), x);
        let v = ulen_from(lb)(x);
        assert(v as nat == x as nat - lb);
        lemma_restrict_wf_val(uint_wf(n), ulen_ok(lb, ub), v);
        crate::prim_read::lemma_p2_mono(n, 56);
    } else if ulen_wf(lb, ub, n)(x) {
        lemma_ulen_wf_bound(lb, ub, n, x);
    }
}

// ------------------------------------- SIZE (lb..ub) followed by the elements

/// Named so that the same closure value can be referred to at a use site and
/// at a step-lemma application.
pub open spec fn list_wf_f<A>(w: Wf<A>) -> spec_fn(u64) -> Wf<Seq<A>> {
    |c: u64| list_wf(c as nat, w)
}
pub open spec fn list_enc_f<A>(e: Enc<A>) -> spec_fn(u64) -> Enc<Seq<A>> {
    |c: u64| list_enc(c as nat, e)
}
pub open spec fn list_dec_f<A>(d: Dec<A>) -> spec_fn(u64) -> Dec<Seq<A>> {
    |c: u64| list_dec(c as nat, d)
}

pub open spec fn sized_wf<A>(lb: nat, ub: nat, n: nat, w: Wf<A>) -> Wf<(u64, Seq<A>)> {
    dep_wf(ulen_wf(lb, ub, n), list_wf_f(w))
}
pub open spec fn sized_enc<A>(lb: nat, ub: nat, n: nat, e: Enc<A>) -> Enc<(u64, Seq<A>)> {
    dep_enc(ulen_enc(lb, ub, n), list_enc_f(e))
}
pub open spec fn sized_dec<A>(lb: nat, ub: nat, n: nat, d: Dec<A>) -> Dec<(u64, Seq<A>)> {
    dep_dec(ulen_dec(lb, ub, n), list_dec_f(d))
}

pub proof fn lemma_sized_format<A>(lb: nat, ub: nat, n: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d), 1 <= n <= 56, lb <= ub, ub - lb < p2(n), ub < p2(56),
    ensures is_format(sized_wf(lb, ub, n, w), sized_enc(lb, ub, n, e), sized_dec(lb, ub, n, d)),
{
    lemma_ulen_format(lb, ub, n);
    assert forall|c: u64| ulen_wf(lb, ub, n)(c) implies
        is_format(#[trigger] list_wf_f(w)(c), list_enc_f(e)(c), list_dec_f(d)(c))
    by {
        lemma_list_format(c as nat, w, e, d);
    }
    lemma_dep_format(ulen_wf(lb, ub, n), ulen_enc(lb, ub, n), ulen_dec(lb, ub, n),
                     list_wf_f(w), list_enc_f(e), list_dec_f(d));
}

} // verus!

verus! {

// ------------------------------------------------- lemmas for the exec loop
//
// The spec decoder recurses; the generated decoder loops. These three lemmas
// are the bridge: the invariant says "what the whole list decodes to equals
// what has been accumulated so far, composed with what the remaining suffix
// decodes to", and each iteration advances it by one element.

pub open spec fn list_cont<A>(acc: Seq<A>, c: nat, fa: Flg,
                              o: Option<(Seq<A>, nat, Flg)>) -> Option<(Seq<A>, nat, Flg)> {
    match o {
        Some((rest, k, f)) => Some((acc + rest, (c + k) as nat, flg_add(fa, f))),
        None => None,
    }
}

/// Entering the loop: nothing accumulated yet.
pub proof fn lemma_list_loop_start<A>(n: nat, d: Dec<A>, b: Seq<bool>)
    ensures list_dec_rec(n, d, b)
        == list_cont(Seq::<A>::empty(), 0nat, Flg::SameVer, list_dec_rec(n, d, b)),
{
    if let Some((rest, k, f)) = list_dec_rec(n, d, b) {
        assert(Seq::<A>::empty() + rest =~= rest);
    }
}

/// One element consumed.
pub proof fn lemma_list_loop_step<A>(total: nat, d: Dec<A>, b0: Seq<bool>, acc: Seq<A>, c: nat,
                                     fa: Flg, n: nat, b: Seq<bool>, v: A, k: nat, f: Flg)
    requires
        n > 0,
        d(b) == Some::<(A, nat, Flg)>((v, k, f)),
        list_dec_rec(total, d, b0) == list_cont(acc, c, fa, list_dec_rec(n, d, b)),
    ensures
        list_dec_rec(total, d, b0)
            == list_cont(acc.push(v), (c + k) as nat, flg_add(fa, f),
                         list_dec_rec((n - 1) as nat, d, b.skip(k as int))),
{
    lemma_list_dec_step(n, d, b, v, k, f);
    if let Some((rest, k2, f2)) = list_dec_rec((n - 1) as nat, d, b.skip(k as int)) {
        assert(acc + (seq![v] + rest) =~= acc.push(v) + rest);
    }
}

/// An element failed to decode, so the whole list does.
pub proof fn lemma_list_loop_fail<A>(total: nat, d: Dec<A>, b0: Seq<bool>, acc: Seq<A>, c: nat,
                                     fa: Flg, n: nat, b: Seq<bool>)
    requires
        n > 0,
        d(b).is_none(),
        list_dec_rec(total, d, b0) == list_cont(acc, c, fa, list_dec_rec(n, d, b)),
    ensures list_dec_rec(total, d, b0).is_none(),
{
    lemma_list_dec_fail(n, d, b);
}

/// Leaving the loop with every element consumed.
pub proof fn lemma_list_loop_done<A>(total: nat, d: Dec<A>, b0: Seq<bool>, acc: Seq<A>, c: nat,
                                     fa: Flg, b: Seq<bool>)
    requires list_dec_rec(total, d, b0) == list_cont(acc, c, fa, list_dec_rec(0nat, d, b)),
    ensures list_dec_rec(total, d, b0) == Some::<(Seq<A>, nat, Flg)>((acc, c, fa)),
{
    assert(acc + Seq::<A>::empty() =~= acc);
}

/// Appending one element's encoding, for the encoder loop.
pub proof fn lemma_list_enc_push<A>(l: Seq<A>, e: Enc<A>, v: A)
    ensures list_enc_rec(l.push(v), e) =~= list_enc_rec(l, e) + e(v),
    decreases l.len(),
{
    let p = l.push(v);
    assert(p.len() == l.len() + 1);
    if l.len() == 0 {
        assert(p[0] == v);
        assert(p.skip(1) =~= Seq::<A>::empty());
        assert(list_enc_rec(p.skip(1), e) =~= Seq::<bool>::empty());
        assert(list_enc_rec(p, e) =~= e(v) + Seq::<bool>::empty());
        assert(list_enc_rec(l, e) =~= Seq::<bool>::empty());
        assert(e(v) + Seq::<bool>::empty() =~= Seq::<bool>::empty() + e(v));
    } else {
        assert(p[0] == l[0]);
        assert(p.skip(1) =~= l.skip(1).push(v));
        lemma_list_enc_push(l.skip(1), e, v);
        assert(list_enc_rec(p, e) =~= e(l[0]) + list_enc_rec(l.skip(1).push(v), e));
        assert(list_enc_rec(l, e) =~= e(l[0]) + list_enc_rec(l.skip(1), e));
        assert(e(l[0]) + (list_enc_rec(l.skip(1), e) + e(v))
               =~= (e(l[0]) + list_enc_rec(l.skip(1), e)) + e(v));
    }
}

} // verus!
