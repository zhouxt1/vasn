//! Lists with a fragmenting length (X.691 11.9.3.8, by way of 11.9.4.2).
//!
//! In UNALIGNED PER a SIZE (lb..ub) whose `ub` is 64K or more -- or a fixed
//! SIZE of 64K or more (11.9.1) -- is not a constrained whole number. 11.9.4.2
//! sends it to 11.9.3.4-11.9.3.8.4: the length is encoded "as if unconstrained",
//! holding `n` itself rather than `n - lb`, and from 16K units on it fragments.
//!
//! `frag.rs` does this for octets (11.9.3.8.2 a), over reassembled content.
//! This module does it over a list of elements of any format, which covers
//! the other units at once: a BIT STRING's elements are 1-bit booleans (b), an
//! OCTET STRING's 8-bit octets (a again), a SEQUENCE OF's components (c). A
//! fragment of `m` blocks is `m * 16K` whole elements, so it is `list` on a
//! prefix, and no element straddles a fragment boundary.
//!
//! The canonicity rule is `frag.rs`'s: `m` must be maximal (11.9.3.8.1), so a
//! fragment below the cap of 4 blocks must be followed by fewer than 16K
//! elements. The SIZE constraint is a `restrict` on the decoded length.
use vstd::prelude::*;
use crate::format::*;
use crate::list::*;
use crate::frag::*;

verus! {

broadcast use {format_steps, list_steps};

pub open spec fn flist_enc_rec<A>(l: Seq<A>, e: Enc<A>) -> Seq<bool>
    decreases l.len(),
{
    if l.len() < 16384 {
        lh_enc()(LenHead::Final(l.len() as u64)) + list_enc_rec(l, e)
    } else {
        let m = frag_blocks(l.len());
        let n = (m * 16384) as int;
        lh_enc()(LenHead::Frag(m as u64)) + list_enc_rec(l.take(n), e) + flist_enc_rec(l.skip(n), e)
    }
}

pub open spec fn flist_dec_rec<A>(d: Dec<A>, b: Seq<bool>) -> Option<(Seq<A>, nat, Flg)>
    decreases b.len(),
{
    match lh_dec()(b) {
        Some((h, k, _)) => {
            if k == 0 || k > b.len() {
                None
            } else {
                match h {
                    LenHead::Final(n) => match list_dec_rec(n as nat, d, b.skip(k as int)) {
                        Some((l1, k1, f1)) => if k + k1 > b.len() {
                            None
                        } else {
                            Some((l1, (k + k1) as nat, f1))
                        },
                        None => None,
                    },
                    LenHead::Frag(m) => match list_dec_rec((m as nat) * 16384, d, b.skip(k as int)) {
                        Some((l1, k1, f1)) => if k + k1 > b.len() {
                            None
                        } else {
                            match flist_dec_rec(d, b.skip((k + k1) as int)) {
                                // 11.9.3.8.1: `m` had to be maximal, so either
                                // it is capped or what follows is under a block
                                Some((l2, k2, f2)) => if m == 4 || l2.len() < 16384 {
                                    Some((l1 + l2, (k + k1 + k2) as nat, flg_add(f1, f2)))
                                } else {
                                    None
                                },
                                None => None,
                            }
                        },
                        None => None,
                    },
                }
            }
        },
        None => None,
    }
}

#[verifier::opaque]
pub open spec fn flist_wf<A>(w: Wf<A>) -> Wf<Seq<A>> {
    |l: Seq<A>| forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])
}

#[verifier::opaque]
pub open spec fn flist_enc<A>(e: Enc<A>) -> Enc<Seq<A>> {
    |l: Seq<A>| flist_enc_rec(l, e)
}

#[verifier::opaque]
pub open spec fn flist_dec<A>(d: Dec<A>) -> Dec<Seq<A>> {
    |b: Seq<bool>| flist_dec_rec(d, b)
}

pub broadcast proof fn lemma_flist_wf_val<A>(w: Wf<A>, l: Seq<A>)
    ensures #[trigger] flist_wf(w)(l) == (forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])),
{
    reveal(flist_wf);
}

pub broadcast proof fn lemma_flist_enc_val<A>(e: Enc<A>, l: Seq<A>)
    ensures #[trigger] flist_enc(e)(l) == flist_enc_rec(l, e),
{
    reveal(flist_enc);
}

pub broadcast proof fn lemma_flist_dec_val<A>(d: Dec<A>, b: Seq<bool>)
    ensures #[trigger] flist_dec(d)(b) == flist_dec_rec(d, b),
{
    reveal(flist_dec);
}

pub broadcast group flist_steps {
    lemma_flist_wf_val,
    lemma_flist_enc_val,
    lemma_flist_dec_val,
}

/// `list_dec_rec(n, ..)` yields exactly `n` elements, whatever the element
/// format -- the loops need this without an `is_format` to hand.
pub proof fn lemma_list_dec_len<A>(n: nat, d: Dec<A>, b: Seq<bool>)
    ensures list_dec_rec(n, d, b) is Some ==> list_dec_rec(n, d, b).unwrap().0.len() == n,
    decreases n,
{
    if n > 0 && d(b) is Some {
        lemma_list_dec_len((n - 1) as nat, d, b.skip(d(b).unwrap().1 as int));
    }
}

/// The head's decode, pinned down: well formed, 8 or 16 bits, and exactly the
/// bits of its own encoding.
pub proof fn lemma_lh_dec_facts(b: Seq<bool>)
    requires lh_dec()(b) is Some,
    ensures
        lh_wf()(lh_dec()(b).unwrap().0),
        8 <= lh_dec()(b).unwrap().1 <= b.len(),
        lh_dec()(b).unwrap().2 is SameVer,
        b.take(lh_dec()(b).unwrap().1 as int) == lh_enc()(lh_dec()(b).unwrap().0),
{
    lemma_lh_format();
    lemma_lh_dec_same(b);
    lemma_lh_dec_k(b);
}

/// A head followed by anything decodes to itself.
pub proof fn lemma_lh_dec_enc(h: LenHead, rest: Seq<bool>)
    requires lh_wf()(h),
    ensures
        lh_dec()(lh_enc()(h) + rest)
            == Some::<(LenHead, nat, Flg)>((h, lh_enc()(h).len(), Flg::SameVer)),
        8 <= lh_enc()(h).len() <= 16,
{
    lemma_lh_format();
    lemma_lh_enc_len_bounds(h);
}

} // verus!

verus! {


/// The unfragmented branch of `lemma_flist_surj`, on its own for the same
/// reason as `frag.rs`'s `lemma_frag_surj_final`: two small queries rather
/// than one near the rlimit.
pub proof fn lemma_flist_surj_final<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>, l: Seq<A>, rest: Seq<bool>)
    requires
        is_format(w, e, d),
        forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i]),
        l.len() < 16384,
    ensures
        flist_dec_rec(d, flist_enc_rec(l, e) + rest)
            == Some::<(Seq<A>, nat, Flg)>((l, flist_enc_rec(l, e).len(), Flg::SameVer)),
{
    let h = LenHead::Final(l.len() as u64);
    lemma_lh_wf_iff(h);
    let g = lh_enc()(h);
    let body = list_enc_rec(l, e);
    let b = flist_enc_rec(l, e) + rest;
    assert(b =~= g + (body + rest));
    lemma_lh_dec_enc(h, body + rest);
    lemma_take_add(g, body + rest);
    assert(b.skip(g.len() as int) =~= body + rest);
    lemma_list_surj(l.len(), w, e, d, l, rest);
}

pub proof fn lemma_flist_surj<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>, l: Seq<A>, rest: Seq<bool>)
    requires
        is_format(w, e, d),
        forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i]),
    ensures
        flist_dec_rec(d, flist_enc_rec(l, e) + rest)
            == Some::<(Seq<A>, nat, Flg)>((l, flist_enc_rec(l, e).len(), Flg::SameVer)),
    decreases l.len(),
{
    if l.len() < 16384 {
        lemma_flist_surj_final(w, e, d, l, rest);
    } else {
        lemma_frag_len_ge(l.len());
        let m = frag_blocks(l.len());
        let n = (m * 16384) as int;
        let h = LenHead::Frag(m as u64);
        lemma_lh_wf_iff(h);
        let g = lh_enc()(h);
        let head = l.take(n);
        let tail = l.skip(n);
        let hb = list_enc_rec(head, e);
        let tb = flist_enc_rec(tail, e);
        let b = flist_enc_rec(l, e) + rest;
        assert(b =~= g + (hb + (tb + rest)));
        lemma_lh_dec_enc(h, hb + (tb + rest));
        lemma_take_add(g, hb + (tb + rest));
        assert(b.skip(g.len() as int) =~= hb + (tb + rest));
        assert forall|i: int| 0 <= i < head.len() implies w(#[trigger] head[i]) by {
            assert(head[i] == l[i]);
        }
        assert forall|i: int| 0 <= i < tail.len() implies w(#[trigger] tail[i]) by {
            assert(tail[i] == l[i + n]);
        }
        lemma_list_surj((m * 16384) as nat, w, e, d, head, tb + rest);
        lemma_take_add(hb, tb + rest);
        assert(b.skip((g.len() + hb.len()) as int) =~= tb + rest);
        lemma_flist_surj(w, e, d, tail, rest);
        // `m` was chosen maximal, so the canonicity check passes
        if m < 4 {
            assert(l.len() / 16384 == m);
            assert(l.len() - m * 16384 < 16384) by (nonlinear_arith)
                requires l.len() / 16384 == m;
            {}
        }
        assert(head + tail =~= l);
    }
}

pub proof fn lemma_flist_inj<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>, b: Seq<bool>)
    requires is_format(w, e, d), flist_dec_rec(d, b) is Some,
    ensures ({
        let (l, k, f) = flist_dec_rec(d, b).unwrap();
        &&& forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])
        &&& k <= b.len()
        &&& f is SameVer ==> b.take(k as int) == flist_enc_rec(l, e)
    }),
    decreases b.len(),
{
    lemma_lh_dec_facts(b);
    let (h, k, _) = lh_dec()(b).unwrap();
    lemma_lh_wf_iff(h);
    let body = b.skip(k as int);
    match h {
        LenHead::Final(n) => {
            lemma_list_inj(n as nat, w, e, d, body);
            let (l1, k1, f1) = list_dec_rec(n as nat, d, body).unwrap();
            lemma_take_split(b, k, k1);
            assert(l1.len() as u64 == n);
        },
        LenHead::Frag(m) => {
            let cnt = (m as nat) * 16384;
            lemma_list_inj(cnt, w, e, d, body);
            let (l1, k1, f1) = list_dec_rec(cnt, d, body).unwrap();
            let tailb = b.skip((k + k1) as int);
            lemma_flist_inj(w, e, d, tailb);
            let (l2, k2, f2) = flist_dec_rec(d, tailb).unwrap();
            let l = l1 + l2;
            assert forall|i: int| 0 <= i < l.len() implies w(#[trigger] l[i]) by {
                if i < l1.len() { assert(l[i] == l1[i]); } else { assert(l[i] == l2[i - l1.len()]); }
            }
            lemma_frag_blocks(m as nat, l2.len());
            assert(l.len() == cnt + l2.len());
            assert(l.len() >= 16384);
            assert(frag_blocks(l.len()) == m as nat);
            assert(l.take(cnt as int) =~= l1);
            assert(l.skip(cnt as int) =~= l2);
            lemma_take_split(b, k, k1);
            lemma_take_split(b, (k + k1) as nat, k2);
            assert(b.skip(k as int).take(k1 as int) =~= body.take(k1 as int));
        },
    }
}

pub proof fn lemma_flist_format<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(flist_wf(w), flist_enc(e), flist_dec(d)),
{
    reveal(flist_wf); reveal(flist_enc); reveal(flist_dec);
    assert forall|l: Seq<A>, rest: Seq<bool>| flist_wf(w)(l) implies
        #[trigger] flist_dec(d)(flist_enc(e)(l) + rest)
            == Some::<(Seq<A>, nat, Flg)>((l, flist_enc(e)(l).len(), Flg::SameVer))
    by {
        lemma_flist_surj(w, e, d, l, rest);
    }
    assert forall|b: Seq<bool>| (#[trigger] flist_dec(d)(b)).is_some() implies {
        let l = flist_dec(d)(b).unwrap().0;
        let k = flist_dec(d)(b).unwrap().1;
        &&& flist_wf(w)(l) && k <= b.len()
        &&& flist_dec(d)(b).unwrap().2 is SameVer ==> b.take(k as int) == flist_enc(e)(l)
    } by {
        lemma_flist_inj(w, e, d, b);
    }
}

// ------------------------------------------------ SIZE (lb..ub), ub >= 64K

pub open spec fn flist_ok<A>(lb: nat, ub: nat) -> spec_fn(Seq<A>) -> bool {
    |l: Seq<A>| lb <= l.len() <= ub
}

pub open spec fn fsized_wf<A>(lb: nat, ub: nat, w: Wf<A>) -> Wf<Seq<A>> {
    restrict_wf(flist_wf(w), flist_ok(lb, ub))
}
pub open spec fn fsized_enc<A>(e: Enc<A>) -> Enc<Seq<A>> { flist_enc(e) }
pub open spec fn fsized_dec<A>(lb: nat, ub: nat, d: Dec<A>) -> Dec<Seq<A>> {
    restrict_dec(flist_dec(d), flist_ok(lb, ub))
}

pub proof fn lemma_fsized_format<A>(lb: nat, ub: nat, w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(fsized_wf(lb, ub, w), fsized_enc(e), fsized_dec(lb, ub, d)),
{
    lemma_flist_format(w, e, d);
    lemma_restrict_format(flist_wf(w), flist_enc(e), flist_dec(d), flist_ok(lb, ub));
}

} // verus!

verus! {


// ------------------------------------------------- lemmas for the exec loops
//
// The generated decoder reads a head, then that fragment's elements with the
// ordinary list loop, and repeats; `flist_cont` is what it still owes, as
// `frag_cont` is for octets. `pending` is set after a fragment below the cap,
// when 11.9.3.8.1 allows only a final head next.

pub open spec fn flist_cont<A>(acc: Seq<A>, consumed: nat, fa: Flg, pending: bool,
                               r: Option<(Seq<A>, nat, Flg)>) -> Option<(Seq<A>, nat, Flg)> {
    match r {
        Some((l2, k2, f2)) =>
            if pending && l2.len() >= 16384 {
                None
            } else {
                Some((acc + l2, (consumed + k2) as nat, flg_add(fa, f2)))
            },
        None => None,
    }
}

pub proof fn lemma_flist_loop_start<A>(d: Dec<A>, b: Seq<bool>)
    ensures flist_dec_rec(d, b)
        == flist_cont(Seq::<A>::empty(), 0nat, Flg::SameVer, false, flist_dec_rec(d, b)),
{
    if let Some((l, k, f)) = flist_dec_rec(d, b) {
        assert(Seq::<A>::empty() + l =~= l);
    }
}

/// The head, or the elements after it, failed to decode, or the elements ran
/// past the end: the whole list fails.
pub proof fn lemma_flist_loop_fail<A>(d: Dec<A>, start: Seq<bool>, cur: Seq<bool>, acc: Seq<A>,
                                      consumed: nat, fa: Flg, pending: bool)
    requires
        flist_dec_rec(d, start) == flist_cont(acc, consumed, fa, pending, flist_dec_rec(d, cur)),
        lh_dec()(cur) is None || ({
            let (h, k, _) = lh_dec()(cur).unwrap();
            let cnt: nat = match h { LenHead::Final(n) => n as nat, LenHead::Frag(m) => (m as nat) * 16384 };
            list_dec_rec(cnt, d, cur.skip(k as int)) is None
        }),
    ensures flist_dec_rec(d, start) is None,
{
    if lh_dec()(cur) is Some {
        lemma_lh_dec_facts(cur);
    }
}

/// A fragment below the cap was followed by another fragment, which brings
/// at least one more block: 11.9.3.8.1 is violated.
pub proof fn lemma_flist_loop_pending<A>(d: Dec<A>, start: Seq<bool>, cur: Seq<bool>, acc: Seq<A>,
                                         consumed: nat, fa: Flg, m: u64, k: nat)
    requires
        flist_dec_rec(d, start) == flist_cont(acc, consumed, fa, true, flist_dec_rec(d, cur)),
        lh_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Frag(m), k, Flg::SameVer)),
    ensures flist_dec_rec(d, start) is None,
{
    lemma_lh_dec_facts(cur);
    lemma_lh_wf_iff(LenHead::Frag(m));
    let cnt = (m as nat) * 16384;
    lemma_list_dec_len(cnt, d, cur.skip(k as int));
}

/// One `Frag(m)` head and its `m * 16K` elements consumed.
pub proof fn lemma_flist_loop_frag<A>(d: Dec<A>, start: Seq<bool>, cur: Seq<bool>, acc: Seq<A>,
                                      consumed: nat, fa: Flg,
                                      m: u64, k: nat, l1: Seq<A>, k1: nat, f1: Flg)
    requires
        cur == start.skip(consumed as int),
        consumed + cur.len() == start.len(),
        flist_dec_rec(d, start) == flist_cont(acc, consumed, fa, false, flist_dec_rec(d, cur)),
        lh_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Frag(m), k, Flg::SameVer)),
        list_dec_rec((m as nat) * 16384, d, cur.skip(k as int)) == Some::<(Seq<A>, nat, Flg)>((l1, k1, f1)),
        k + k1 <= cur.len(),
    ensures
        1 <= m <= 4,
        flist_dec_rec(d, start)
            == flist_cont(acc + l1, (consumed + k + k1) as nat, flg_add(fa, f1), m < 4,
                          flist_dec_rec(d, start.skip((consumed + k + k1) as int))),
{
    lemma_lh_dec_facts(cur);
    lemma_lh_wf_iff(LenHead::Frag(m));
    let cur2 = cur.skip((k + k1) as int);
    assert(cur2 =~= start.skip((consumed + k + k1) as int));
    if let Some((l2, k2, f2)) = flist_dec_rec(d, cur2) {
        assert((acc + l1) + l2 =~= acc + (l1 + l2));
    }
}

/// And a `Final(n)` head and its `n` elements, which end it.
pub proof fn lemma_flist_loop_final<A>(d: Dec<A>, start: Seq<bool>, cur: Seq<bool>, acc: Seq<A>,
                                       consumed: nat, fa: Flg, pending: bool,
                                       n: u64, k: nat, l1: Seq<A>, k1: nat, f1: Flg)
    requires
        flist_dec_rec(d, start) == flist_cont(acc, consumed, fa, pending, flist_dec_rec(d, cur)),
        lh_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Final(n), k, Flg::SameVer)),
        list_dec_rec(n as nat, d, cur.skip(k as int)) == Some::<(Seq<A>, nat, Flg)>((l1, k1, f1)),
        k + k1 <= cur.len(),
    ensures
        flist_dec_rec(d, start)
            == Some::<(Seq<A>, nat, Flg)>((acc + l1, (consumed + k + k1) as nat, flg_add(fa, f1))),
{
    lemma_lh_dec_facts(cur);
    lemma_lh_wf_iff(LenHead::Final(n));
    lemma_list_dec_len(n as nat, d, cur.skip(k as int));
}

// The encoder: the spec's recursion read forwards, as in `write_frag`.

pub proof fn lemma_flist_enc_step<A>(s: Seq<A>, e: Enc<A>, off: nat, m: nat)
    requires
        off <= s.len(),
        s.len() - off >= 16384,
        m == frag_blocks((s.len() - off) as nat),
    ensures
        1 <= m <= 4,
        off + m * 16384 <= s.len(),
        flist_enc_rec(s.skip(off as int), e)
            =~= lh_enc()(LenHead::Frag(m as u64))
                + list_enc_rec(s.subrange(off as int, (off + m * 16384) as int), e)
                + flist_enc_rec(s.skip((off + m * 16384) as int), e),
{
    let rest = s.skip(off as int);
    lemma_frag_len_ge(rest.len());
    let n = (m * 16384) as int;
    assert(rest.take(n) =~= s.subrange(off as int, off + n));
    assert(rest.skip(n) =~= s.skip(off + n));
}

pub proof fn lemma_flist_enc_last<A>(s: Seq<A>, e: Enc<A>, off: nat)
    requires off <= s.len(), s.len() - off < 16384,
    ensures
        flist_enc_rec(s.skip(off as int), e)
            =~= lh_enc()(LenHead::Final((s.len() - off) as u64))
                + list_enc_rec(s.subrange(off as int, s.len() as int), e),
{
    assert(s.skip(off as int) =~= s.subrange(off as int, s.len() as int));
}

} // verus!

verus! {

/// One turn of the encoder's loop as a single implication on `written()`, so
/// the generated loop's own query stays small (as `lemma_frag_loop_step`).
pub proof fn lemma_flist_enc_loop_step<A>(
    wbefore: Seq<bool>, wafter: Seq<bool>, w0: Seq<bool>, s: Seq<A>, e: Enc<A>, off: nat, m: nat,
)
    requires
        off <= s.len(),
        s.len() - off >= 16384,
        m == frag_blocks((s.len() - off) as nat),
        wafter =~= wbefore + lh_enc()(LenHead::Frag(m as u64))
            + list_enc_rec(s.subrange(off as int, (off + m * 16384) as int), e),
        wbefore + flist_enc_rec(s.skip(off as int), e) =~= w0 + flist_enc_rec(s, e),
    ensures
        off + m * 16384 <= s.len(),
        wafter + flist_enc_rec(s.skip((off + m * 16384) as int), e) =~= w0 + flist_enc_rec(s, e),
{
    lemma_flist_enc_step(s, e, off, m);
}

/// And the last turn: a `Final` head and what is left.
pub proof fn lemma_flist_enc_loop_last<A>(
    wbefore: Seq<bool>, wafter: Seq<bool>, w0: Seq<bool>, s: Seq<A>, e: Enc<A>, off: nat,
)
    requires
        off <= s.len(),
        s.len() - off < 16384,
        wafter =~= wbefore + lh_enc()(LenHead::Final((s.len() - off) as u64))
            + list_enc_rec(s.subrange(off as int, s.len() as int), e),
        wbefore + flist_enc_rec(s.skip(off as int), e) =~= w0 + flist_enc_rec(s, e),
    ensures
        wafter =~= w0 + flist_enc_rec(s, e),
{
    lemma_flist_enc_last(s, e, off);
}

} // verus!

verus! {

use crate::term::*;
use crate::prim::*;

// -------------------------------------------------- the extension bit, generally
//
// An extensible SIZE (X.691 16.6, 17.3, 20.4): one bit, 0 if the size is in the
// extension root and then the root's encoding, 1 if not and then the size as
// a semi-constrained whole number, which is `flist`. A size in the root is
// always encoded as one (10.4.3), so the extension's format admits only sizes
// outside it; the generated code restricts it to those before it gets here.

pub open spec fn xext_alt_wf<A>(rw: Wf<A>, ew: Wf<A>) -> spec_fn(bool) -> Wf<A> {
    |x: bool| if x { ew } else { rw }
}
pub open spec fn xext_alt_enc<A>(re: Enc<A>, ee: Enc<A>) -> spec_fn(bool) -> Enc<A> {
    |x: bool| if x { ee } else { re }
}
pub open spec fn xext_alt_dec<A>(rd: Dec<A>, ed: Dec<A>) -> spec_fn(bool) -> Dec<A> {
    |x: bool| if x { ed } else { rd }
}
pub open spec fn xext_to<A>() -> spec_fn((bool, A)) -> A { |t: (bool, A)| t.1 }
pub open spec fn xext_from<A>(inr: spec_fn(A) -> bool) -> spec_fn(A) -> (bool, A) {
    |a: A| (!inr(a), a)
}

pub open spec fn xext_wf<A>(rw: Wf<A>, ew: Wf<A>, inr: spec_fn(A) -> bool) -> Wf<A> {
    map_wf(dep_wf(bool_wf(), xext_alt_wf(rw, ew)), xext_to(), xext_from(inr))
}
pub open spec fn xext_enc<A>(re: Enc<A>, ee: Enc<A>, inr: spec_fn(A) -> bool) -> Enc<A> {
    map_enc(dep_enc(bool_enc(), xext_alt_enc(re, ee)), xext_from(inr))
}
pub open spec fn xext_dec<A>(rd: Dec<A>, ed: Dec<A>) -> Dec<A> {
    map_dec(dep_dec(bool_dec(), xext_alt_dec(rd, ed)), xext_to())
}

/// An extension bit over any root format and any extension format, so long
/// as each admits only values on its own side of `inr`.
pub proof fn lemma_xext_format<A>(rw: Wf<A>, re: Enc<A>, rd: Dec<A>, ew: Wf<A>, ee: Enc<A>, ed: Dec<A>,
                                  inr: spec_fn(A) -> bool)
    requires
        is_format(rw, re, rd),
        is_format(ew, ee, ed),
        forall|a: A| #[trigger] rw(a) ==> inr(a),
        forall|a: A| #[trigger] ew(a) ==> !inr(a),
    ensures is_format(xext_wf(rw, ew, inr), xext_enc(re, ee, inr), xext_dec(rd, ed)),
{
    lemma_bool_format();
    assert forall|x: bool| bool_wf()(x) implies
        is_format(#[trigger] xext_alt_wf(rw, ew)(x), xext_alt_enc(re, ee)(x), xext_alt_dec(rd, ed)(x))
    by {}
    lemma_dep_format(bool_wf(), bool_enc(), bool_dec(), xext_alt_wf(rw, ew), xext_alt_enc(re, ee),
                     xext_alt_dec(rd, ed));
    assert forall|t: (bool, A)| dep_wf(bool_wf(), xext_alt_wf(rw, ew))(t) implies
        #[trigger] xext_from(inr)(xext_to()(t)) == t
    by {
        lemma_dep_wf_val(bool_wf(), xext_alt_wf(rw, ew), t.0, t.1);
    }
    lemma_map_format(dep_wf(bool_wf(), xext_alt_wf(rw, ew)), dep_enc(bool_enc(), xext_alt_enc(re, ee)),
                     dep_dec(bool_dec(), xext_alt_dec(rd, ed)), xext_to(), xext_from(inr));
}

/// What a value's well-formedness says, and what its encoding is: the bit, then
/// its side's encoding. For the generated encoder.
pub proof fn lemma_xext_enc<A>(re: Enc<A>, ee: Enc<A>, rw: Wf<A>, ew: Wf<A>, inr: spec_fn(A) -> bool, a: A)
    requires xext_wf(rw, ew, inr)(a),
    ensures
        xext_enc(re, ee, inr)(a) == bool_enc()(!inr(a)) + (if inr(a) { re(a) } else { ee(a) }),
        if inr(a) { rw(a) } else { ew(a) },
{
    lemma_map_wf_val(dep_wf(bool_wf(), xext_alt_wf(rw, ew)), xext_to(), xext_from(inr), a);
    lemma_dep_wf_val(bool_wf(), xext_alt_wf(rw, ew), !inr(a), a);
    lemma_map_enc_val(dep_enc(bool_enc(), xext_alt_enc(re, ee)), xext_from(inr), a);
    lemma_dep_enc_val(bool_enc(), xext_alt_enc(re, ee), !inr(a), a);
}

} // verus!
