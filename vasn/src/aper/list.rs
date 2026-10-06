//! Fixed-length lists, and a length followed by that many elements: `uper::list`
//! with each element starting where the one before it ended.
//!
//! What the ALIGNED variant adds is in the length and in where the elements
//! start (X.691 11.9.3.3, 16, 17, 20, 30.5):
//!
//!   * a constrained length (`SIZE (lb..ub)`, `ub` below 64K) is a constrained
//!     whole number (11.5.7): UPER's bit-field for a range up to 255, one or
//!     two octets, octet-aligned, above (`alen`, `a`);
//!   * the elements of a BIT STRING, an OCTET STRING, or a known-multiplier
//!     string wide enough are an octet-aligned field (16.10, 16.11, 17.7, 17.8,
//!     30.5.6, 30.5.7), but only when there is at least one: "if n is zero
//!     there shall be no further addition to the field-list" (11.9.3.3), so no
//!     padding either (`alist`, `al`). A SEQUENCE OF's are not (20.6).
use vstd::prelude::*;
use crate::aper::format::*;
use crate::bits::bitspec::*;
use crate::aper::term::*;
use crate::uper::list as ul;

verus! {

broadcast use {format_steps, map_steps};

/// Concatenated encodings of every element, the first starting at `pos`.
pub open spec fn list_enc_rec<A>(pos: nat, l: Seq<A>, e: Enc<A>) -> Seq<bool>
    decreases l.len(),
{
    if l.len() == 0 {
        Seq::<bool>::empty()
    } else {
        let h = e(pos, l[0]);
        h + list_enc_rec(pos + h.len(), l.skip(1), e)
    }
}

/// Decode exactly `n` elements, left to right.
pub open spec fn list_dec_rec<A>(n: nat, d: Dec<A>, b: In) -> Option<(Seq<A>, nat, Flg)>
    decreases n,
{
    if n == 0 {
        Some((Seq::<A>::empty(), 0nat, Flg::SameVer))
    } else {
        match d(b) {
            Some((v, k, f)) => match list_dec_rec((n - 1) as nat, d, adv(b, k)) {
                Some((rest, k2, f2)) => Some((seq![v] + rest, (k + k2) as nat, flg_add(f, f2))),
                None => None,
            },
            None => None,
        }
    }
}

/// A list of fixed-width elements is exactly as wide as the arithmetic says.
pub proof fn lemma_list_enc_rec_len<A>(pos: nat, l: Seq<A>, e: Enc<A>, m: nat)
    requires forall|p: nat, a: A| (#[trigger] e(p, a)).len() == m,
    ensures list_enc_rec(pos, l, e).len() == l.len() * m,
    decreases l.len(),
{
    if l.len() > 0 {
        lemma_list_enc_rec_len(pos + e(pos, l[0]).len(), l.skip(1), e, m);
        assert(l.len() * m == m + (l.len() - 1) * m) by (nonlinear_arith);
    }
}

#[verifier::opaque]
pub open spec fn list_wf<A>(n: nat, w: Wf<A>) -> Wf<Seq<A>> {
    |l: Seq<A>| l.len() == n && forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])
}

#[verifier::opaque]
pub open spec fn list_enc<A>(n: nat, e: Enc<A>) -> Enc<Seq<A>> {
    |pos: nat, l: Seq<A>| list_enc_rec(pos, l, e)
}

#[verifier::opaque]
pub open spec fn list_dec<A>(n: nat, d: Dec<A>) -> Dec<Seq<A>> {
    |b: In| list_dec_rec(n, d, b)
}

pub proof fn lemma_list_format<A>(n: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(list_wf(n, w), list_enc(n, e), list_dec(n, d)),
{
    reveal(list_wf); reveal(list_enc); reveal(list_dec);
    assert forall|pos: nat, l: Seq<A>, rest: Seq<bool>| list_wf(n, w)(l) implies
        #[trigger] list_dec(n, d)((pos, list_enc(n, e)(pos, l) + rest))
            == Some::<(Seq<A>, nat, Flg)>((l, list_enc(n, e)(pos, l).len(), Flg::SameVer))
    by {
        lemma_list_surj(n, w, e, d, pos, l, rest);
    }
    assert forall|b: In| (#[trigger] list_dec(n, d)(b)).is_some() implies {
        let l = list_dec(n, d)(b).unwrap().0;
        let k = list_dec(n, d)(b).unwrap().1;
        &&& list_wf(n, w)(l) && k <= b.1.len()
        &&& list_dec(n, d)(b).unwrap().2 is SameVer ==> b.1.take(k as int) == list_enc(n, e)(b.0, l)
    } by {
        lemma_list_inj(n, w, e, d, b);
    }
}

pub proof fn lemma_list_surj<A>(n: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>, pos: nat, l: Seq<A>, rest: Seq<bool>)
    requires
        is_format(w, e, d),
        l.len() == n,
        forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i]),
    ensures
        list_dec_rec(n, d, (pos, list_enc_rec(pos, l, e) + rest))
            == Some::<(Seq<A>, nat, Flg)>((l, list_enc_rec(pos, l, e).len(), Flg::SameVer)),
    decreases n,
{
    if n == 0 {
        assert(l =~= Seq::<A>::empty());
        assert(list_enc_rec(pos, l, e) =~= Seq::<bool>::empty());
    } else {
        let head = e(pos, l[0]);
        let p1 = pos + head.len();
        let tail = list_enc_rec(p1, l.skip(1), e);
        assert(list_enc_rec(pos, l, e) =~= head + tail);
        let b = list_enc_rec(pos, l, e) + rest;
        assert(b =~= head + (tail + rest));
        assert(d((pos, b)) == Some::<(A, nat, Flg)>((l[0], head.len(), Flg::SameVer)));
        lemma_take_add(head, tail + rest);
        assert(adv((pos, b), head.len()) =~= (p1, tail + rest));
        assert forall|i: int| 0 <= i < l.skip(1).len() implies w(#[trigger] l.skip(1)[i]) by {
            assert(l.skip(1)[i] == l[i + 1]);
        }
        lemma_list_surj((n - 1) as nat, w, e, d, p1, l.skip(1), rest);
        assert(seq![l[0]] + l.skip(1) =~= l);
    }
}

pub proof fn lemma_list_inj<A>(n: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>, b: In)
    requires is_format(w, e, d), list_dec_rec(n, d, b).is_some(),
    ensures
        ({
            let l = list_dec_rec(n, d, b).unwrap().0;
            let k = list_dec_rec(n, d, b).unwrap().1;
            &&& l.len() == n
            &&& forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])
            &&& k <= b.1.len()
            &&& list_dec_rec(n, d, b).unwrap().2 is SameVer ==> b.1.take(k as int) == list_enc_rec(b.0, l, e)
        }),
    decreases n,
{
    if n == 0 {
        assert(b.1.take(0) =~= Seq::<bool>::empty());
        assert(list_enc_rec(b.0, Seq::<A>::empty(), e) =~= Seq::<bool>::empty());
    } else {
        let v = d(b).unwrap().0;
        let k1 = d(b).unwrap().1;
        let f1 = d(b).unwrap().2;
        let tb = adv(b, k1);
        lemma_list_inj((n - 1) as nat, w, e, d, tb);
        let rest = list_dec_rec((n - 1) as nat, d, tb).unwrap().0;
        let k2 = list_dec_rec((n - 1) as nat, d, tb).unwrap().1;
        let f2 = list_dec_rec((n - 1) as nat, d, tb).unwrap().2;
        let l = seq![v] + rest;
        assert(l.len() == n);
        assert forall|i: int| 0 <= i < l.len() implies w(#[trigger] l[i]) by {
            if i > 0 {
                assert(l[i] == rest[i - 1]);
            }
        }
        lemma_take_split(b.1, k1, k2);
        assert(l.skip(1) =~= rest);
        assert(l[0] == v);
        if flg_add(f1, f2) is SameVer {
            assert(b.1.take(k1 as int) == e(b.0, v));
            assert(e(b.0, v).len() == k1);
            assert(tb.1.take(k2 as int) == list_enc_rec(tb.0, rest, e));
            assert(list_enc_rec(b.0, l, e) =~= e(b.0, v) + list_enc_rec(b.0 + k1, rest, e));
        }
    }
}

/// A list of an element format that never reports `DiffVer` never does
/// either.
pub proof fn lemma_list_dec_same<A>(n: nat, d: Dec<A>, b: In)
    requires forall|s: In| (#[trigger] d(s)) is Some ==> d(s).unwrap().2 is SameVer,
    ensures list_dec_rec(n, d, b) is Some ==> list_dec_rec(n, d, b).unwrap().2 is SameVer,
    decreases n,
{
    if n > 0 && d(b) is Some {
        lemma_list_dec_same((n - 1) as nat, d, adv(b, d(b).unwrap().1));
    }
}

// ------------------------------------------------------------- step lemmas

pub broadcast proof fn lemma_list_wf_val<A>(n: nat, w: Wf<A>, l: Seq<A>)
    ensures #[trigger] list_wf(n, w)(l)
        == (l.len() == n && forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])),
{
    reveal(list_wf);
}

pub broadcast proof fn lemma_list_enc_val<A>(n: nat, e: Enc<A>, pos: nat, l: Seq<A>)
    ensures #[trigger] list_enc(n, e)(pos, l) == list_enc_rec(pos, l, e),
{
    reveal(list_enc);
}

pub broadcast proof fn lemma_list_dec_val<A>(n: nat, d: Dec<A>, b: In)
    ensures #[trigger] list_dec(n, d)(b) == list_dec_rec(n, d, b),
{
    reveal(list_dec);
}

pub proof fn lemma_list_dec_step<A>(n: nat, d: Dec<A>, b: In, v: A, k: nat, f: Flg)
    requires n > 0, d(b) == Some::<(A, nat, Flg)>((v, k, f)),
    ensures
        list_dec_rec(n, d, b) == (match list_dec_rec((n - 1) as nat, d, adv(b, k)) {
            Some((rest, k2, f2)) => Some((seq![v] + rest, (k + k2) as nat, flg_add(f, f2))),
            None => None,
        }),
{
}

pub proof fn lemma_list_dec_fail<A>(n: nat, d: Dec<A>, b: In)
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

// --------------------------------------------- constrained length determinant
//
// 11.9.3.3: the constrained whole number of 11.5.7. UPER's bit-field for a
// range up to 255 (`a` false); one or two octets, octet-aligned, for 256 and
// for 257 to 64K (`a` true, `n` 8 or 16). The bit-field is UPER's `ulen`.

pub open spec fn ulen_wf(lb: nat, ub: nat, n: nat) -> Wf<u64> { ul::ulen_wf(lb, ub, n) }
pub open spec fn ulen_enc(lb: nat, ub: nat, n: nat) -> Enc<u64> { lift_enc(ul::ulen_enc(lb, ub, n)) }
pub open spec fn ulen_dec(lb: nat, ub: nat, n: nat) -> Dec<u64> { lift_dec(ul::ulen_dec(lb, ub, n)) }

pub open spec fn alen_wf(lb: nat, ub: nat, n: nat, a: bool) -> Wf<u64> {
    if a { aligned_wf(ulen_wf(lb, ub, n)) } else { ulen_wf(lb, ub, n) }
}
pub open spec fn alen_enc(lb: nat, ub: nat, n: nat, a: bool) -> Enc<u64> {
    if a { aligned_enc(ulen_enc(lb, ub, n)) } else { ulen_enc(lb, ub, n) }
}
pub open spec fn alen_dec(lb: nat, ub: nat, n: nat, a: bool) -> Dec<u64> {
    if a { aligned_dec(ulen_dec(lb, ub, n)) } else { ulen_dec(lb, ub, n) }
}

pub proof fn lemma_alen_format(lb: nat, ub: nat, n: nat, a: bool)
    requires 1 <= n <= 56, lb <= ub, ub - lb < p2(n), ub < p2(56),
    ensures is_format(alen_wf(lb, ub, n, a), alen_enc(lb, ub, n, a), alen_dec(lb, ub, n, a)),
{
    ul::lemma_ulen_format(lb, ub, n);
    lemma_lift_format(ul::ulen_wf(lb, ub, n), ul::ulen_enc(lb, ub, n), ul::ulen_dec(lb, ub, n));
    if a {
        lemma_aligned_format(ulen_wf(lb, ub, n), ulen_enc(lb, ub, n), ulen_dec(lb, ub, n));
    }
}

/// The decoded length is inside the SIZE constraint.
pub proof fn lemma_alen_wf_bound(lb: nat, ub: nat, n: nat, a: bool, x: u64)
    requires alen_wf(lb, ub, n, a)(x), ub < p2(56),
    ensures lb <= x as nat <= ub,
{
    if a { lemma_aligned_wf_val(ulen_wf(lb, ub, n), x); }
    ul::lemma_ulen_wf_bound(lb, ub, n, x);
}

pub proof fn lemma_alen_wf_iff(lb: nat, ub: nat, n: nat, a: bool, x: u64)
    requires 1 <= n <= 56, lb <= ub, ub - lb < p2(n), ub < p2(56),
    ensures alen_wf(lb, ub, n, a)(x) <==> lb <= x as nat <= ub,
{
    if a { lemma_aligned_wf_val(ulen_wf(lb, ub, n), x); }
    ul::lemma_ulen_wf_iff(lb, ub, n, x);
}

// --------------------------------- the elements, octet-aligned if there are any

pub open spec fn alist_wf<A>(al: bool, c: nat, w: Wf<A>) -> Wf<Seq<A>> {
    if al && c > 0 { aligned_wf(list_wf(c, w)) } else { list_wf(c, w) }
}
pub open spec fn alist_enc<A>(al: bool, c: nat, e: Enc<A>) -> Enc<Seq<A>> {
    if al && c > 0 { aligned_enc(list_enc(c, e)) } else { list_enc(c, e) }
}
pub open spec fn alist_dec<A>(al: bool, c: nat, d: Dec<A>) -> Dec<Seq<A>> {
    if al && c > 0 { aligned_dec(list_dec(c, d)) } else { list_dec(c, d) }
}

pub proof fn lemma_alist_format<A>(al: bool, c: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(alist_wf(al, c, w), alist_enc(al, c, e), alist_dec(al, c, d)),
{
    lemma_list_format(c, w, e, d);
    if al && c > 0 {
        lemma_aligned_format(list_wf(c, w), list_enc(c, e), list_dec(c, d));
    }
}

/// Named so that the same closure value can be referred to at a use site and
/// at a step-lemma application.
pub open spec fn list_wf_f<A>(al: bool, w: Wf<A>) -> spec_fn(u64) -> Wf<Seq<A>> {
    |c: u64| alist_wf(al, c as nat, w)
}
pub open spec fn list_enc_f<A>(al: bool, e: Enc<A>) -> spec_fn(u64) -> Enc<Seq<A>> {
    |c: u64| alist_enc(al, c as nat, e)
}
pub open spec fn list_dec_f<A>(al: bool, d: Dec<A>) -> spec_fn(u64) -> Dec<Seq<A>> {
    |c: u64| alist_dec(al, c as nat, d)
}

// ------------------------------------- SIZE (lb..ub) followed by the elements

pub open spec fn sized_wf<A>(lb: nat, ub: nat, n: nat, a: bool, al: bool, w: Wf<A>) -> Wf<(u64, Seq<A>)> {
    dep_wf(alen_wf(lb, ub, n, a), list_wf_f(al, w))
}
pub open spec fn sized_enc<A>(lb: nat, ub: nat, n: nat, a: bool, al: bool, e: Enc<A>) -> Enc<(u64, Seq<A>)> {
    dep_enc(alen_enc(lb, ub, n, a), list_enc_f(al, e))
}
pub open spec fn sized_dec<A>(lb: nat, ub: nat, n: nat, a: bool, al: bool, d: Dec<A>) -> Dec<(u64, Seq<A>)> {
    dep_dec(alen_dec(lb, ub, n, a), list_dec_f(al, d))
}

pub proof fn lemma_sized_format<A>(lb: nat, ub: nat, n: nat, a: bool, al: bool, w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d), 1 <= n <= 56, lb <= ub, ub - lb < p2(n), ub < p2(56),
    ensures is_format(sized_wf(lb, ub, n, a, al, w), sized_enc(lb, ub, n, a, al, e),
                      sized_dec(lb, ub, n, a, al, d)),
{
    lemma_alen_format(lb, ub, n, a);
    assert forall|c: u64| alen_wf(lb, ub, n, a)(c) implies
        is_format(#[trigger] list_wf_f(al, w)(c), list_enc_f(al, e)(c), list_dec_f(al, d)(c))
    by {
        lemma_alist_format(al, c as nat, w, e, d);
    }
    lemma_dep_format(alen_wf(lb, ub, n, a), alen_enc(lb, ub, n, a), alen_dec(lb, ub, n, a),
                     list_wf_f(al, w), list_enc_f(al, e), list_dec_f(al, d));
}

// ------------------------------------------------ what the elements' bits are

/// `alist_wf` is `list_wf`: the padding carries no value.
pub proof fn lemma_alist_wf_val<A>(al: bool, c: nat, w: Wf<A>, l: Seq<A>)
    ensures alist_wf(al, c, w)(l) == list_wf(c, w)(l),
{
    if al && c > 0 { lemma_aligned_wf_val(list_wf(c, w), l); }
}

/// The padding, if any, then the elements: what an encoder writes.
pub proof fn lemma_alist_enc_val<A>(al: bool, c: nat, e: Enc<A>, pos: nat, l: Seq<A>)
    ensures ({
        let p = if al && c > 0 { pad(pos) } else { 0 };
        &&& alist_enc(al, c, e)(pos, l) == zeros(p) + list_enc_rec(pos + p, l, e)
        &&& al && c > 0 ==> (pos + p) % 8 == 0
    }),
{
    reveal(list_enc);
    if al && c > 0 {
        lemma_aligned_enc_val(list_enc(c, e), pos, l);
    } else {
        assert(zeros(0) + list_enc_rec(pos, l, e) =~= list_enc_rec(pos, l, e));
    }
}

/// ... and a decoder: past the padding, the elements' recursion.
pub proof fn lemma_alist_dec_val<A>(al: bool, c: nat, d: Dec<A>, i: In, p: nat)
    requires
        al && c > 0 ==> align_dec()(i) == Some::<((), nat, Flg)>(((), p, Flg::SameVer)),
        !(al && c > 0) ==> p == 0,
    ensures alist_dec(al, c, d)(i) == (match list_dec_rec(c, d, adv(i, p)) {
        Some((l, k, f)) => Some((l, (p + k) as nat, f)),
        None => None,
    }),
{
    reveal(list_dec);
    if al && c > 0 {
        lemma_aligned_dec_val(list_dec(c, d), i);
    } else {
        assert(adv(i, 0) =~= i);
    }
}

pub proof fn lemma_alist_dec_misaligned<A>(al: bool, c: nat, d: Dec<A>, i: In)
    requires al && c > 0, align_dec()(i) is None,
    ensures alist_dec(al, c, d)(i) is None,
{
    lemma_aligned_dec_val(list_dec(c, d), i);
}

} // verus!

verus! {

// ------------------------------------------------- lemmas for the exec loop

pub open spec fn list_cont<A>(acc: Seq<A>, c: nat, fa: Flg,
                              o: Option<(Seq<A>, nat, Flg)>) -> Option<(Seq<A>, nat, Flg)> {
    match o {
        Some((rest, k, f)) => Some((acc + rest, (c + k) as nat, flg_add(fa, f))),
        None => None,
    }
}

pub proof fn lemma_list_loop_start<A>(n: nat, d: Dec<A>, b: In)
    ensures list_dec_rec(n, d, b)
        == list_cont(Seq::<A>::empty(), 0nat, Flg::SameVer, list_dec_rec(n, d, b)),
{
    if let Some((rest, k, f)) = list_dec_rec(n, d, b) {
        assert(Seq::<A>::empty() + rest =~= rest);
    }
}

pub proof fn lemma_list_loop_step<A>(total: nat, d: Dec<A>, b0: In, acc: Seq<A>, c: nat,
                                     fa: Flg, n: nat, b: In, v: A, k: nat, f: Flg)
    requires
        n > 0,
        d(b) == Some::<(A, nat, Flg)>((v, k, f)),
        list_dec_rec(total, d, b0) == list_cont(acc, c, fa, list_dec_rec(n, d, b)),
    ensures
        list_dec_rec(total, d, b0)
            == list_cont(acc.push(v), (c + k) as nat, flg_add(fa, f),
                         list_dec_rec((n - 1) as nat, d, adv(b, k))),
{
    lemma_list_dec_step(n, d, b, v, k, f);
    if let Some((rest, k2, f2)) = list_dec_rec((n - 1) as nat, d, adv(b, k)) {
        assert(acc + (seq![v] + rest) =~= acc.push(v) + rest);
    }
}

pub proof fn lemma_list_loop_fail<A>(total: nat, d: Dec<A>, b0: In, acc: Seq<A>, c: nat,
                                     fa: Flg, n: nat, b: In)
    requires
        n > 0,
        d(b).is_none(),
        list_dec_rec(total, d, b0) == list_cont(acc, c, fa, list_dec_rec(n, d, b)),
    ensures list_dec_rec(total, d, b0).is_none(),
{
    lemma_list_dec_fail(n, d, b);
}

pub proof fn lemma_list_loop_done<A>(total: nat, d: Dec<A>, b0: In, acc: Seq<A>, c: nat,
                                     fa: Flg, b: In)
    requires list_dec_rec(total, d, b0) == list_cont(acc, c, fa, list_dec_rec(0nat, d, b)),
    ensures list_dec_rec(total, d, b0) == Some::<(Seq<A>, nat, Flg)>((acc, c, fa)),
{
    assert(acc + Seq::<A>::empty() =~= acc);
}

/// Appending one element's encoding, for the encoder loop: it starts where
/// the others ended.
pub proof fn lemma_list_enc_push<A>(pos: nat, l: Seq<A>, e: Enc<A>, v: A)
    ensures list_enc_rec(pos, l.push(v), e)
        =~= list_enc_rec(pos, l, e) + e(pos + list_enc_rec(pos, l, e).len(), v),
    decreases l.len(),
{
    let p = l.push(v);
    assert(p.len() == l.len() + 1);
    if l.len() == 0 {
        assert(p[0] == v);
        assert(p.skip(1) =~= Seq::<A>::empty());
        assert(list_enc_rec(pos + e(pos, v).len(), p.skip(1), e) =~= Seq::<bool>::empty());
        assert(list_enc_rec(pos, l, e) =~= Seq::<bool>::empty());
    } else {
        let h = e(pos, l[0]);
        assert(p[0] == l[0]);
        assert(p.skip(1) =~= l.skip(1).push(v));
        lemma_list_enc_push(pos + h.len(), l.skip(1), e, v);
        let t = list_enc_rec(pos + h.len(), l.skip(1), e);
        assert(list_enc_rec(pos, p, e) =~= h + list_enc_rec(pos + h.len(), l.skip(1).push(v), e));
        assert(list_enc_rec(pos, l, e) =~= h + t);
        assert(h + (t + e(pos + h.len() + t.len(), v)) =~= (h + t) + e(pos + h.len() + t.len(), v));
    }
}

} // verus!

verus! {

use crate::aper::cursor::*;

impl<'a> BitReader<'a> {
    /// Refines `alen_dec(lb, ub, n, a)`: the padding first if `a`, then UPER's
    /// bit-field.
    pub fn read_alen(&mut self, lb: u64, ub: u64, n: usize, a: bool) -> (res: Option<u64>)
        requires
            old(self).wf(), 1 <= n <= 56, lb <= ub,
            (ub as nat) - (lb as nat) < p2(n as nat), (ub as nat) < p2(56),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& alen_dec(lb as nat, ub as nat, n as nat, a)(old(self).at())
                        == Some::<(u64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& lb <= v <= ub
                },
                None => alen_dec(lb as nat, ub as nat, n as nat, a)(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = ulen_dec(lb as nat, ub as nat, n as nat);
        let ghost p0 = self.pos;
        if a {
            if !self.read_align() {
                proof { lemma_aligned_dec_val(d, i); }
                return None;
            }
            proof {
                lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
                lemma_aligned_dec_val(d, i);
            }
        }
        self.read_ulen(lb, ub, n)
    }
}

impl BitWriter {
    /// Refines `alen_enc(lb, ub, n, a)`.
    pub fn write_alen(&mut self, lb: u64, ub: u64, n: usize, a: bool, v: u64) -> (ok: bool)
        requires
            old(self).wf(), 1 <= n <= 56, lb <= v <= ub,
            (ub as nat) - (lb as nat) < p2(n as nat), (ub as nat) < p2(56),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written()
                + alen_enc(lb as nat, ub as nat, n as nat, a)(old(self).pos as nat, v),
    {
        let ghost p0 = self.pos as nat;
        if a {
            proof { lemma_aligned_enc_val(ulen_enc(lb as nat, ub as nat, n as nat), p0, v); }
            if !self.write_align() { return false; }
        }
        self.write_ulen(lb, ub, n, v)
    }
}

/// The encoder loop's step, as an equality: with its invariant an `==`, a
/// step proves no `=~=` of its own, index by index, whose cost grew with the
/// queries before it (NGAP's containers went over an rlimit of 100)
pub proof fn lemma_list_enc_step<A>(mid: Seq<bool>, pos: nat, l: Seq<A>, e: Enc<A>, v: A,
                                    wo: Seq<bool>, wn: Seq<bool>)
    requires
        wo == mid + list_enc_rec(pos, l, e),
        wn =~= wo + e(pos + list_enc_rec(pos, l, e).len(), v),
    ensures wn == mid + list_enc_rec(pos, l.push(v), e),
{
    lemma_list_enc_push(pos, l, e, v);
    assert(wn =~= mid + list_enc_rec(pos, l.push(v), e));
}

} // verus!
