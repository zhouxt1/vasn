//! Lists with a fragmenting length (X.691 11.9.3.5 to 11.9.3.8) in the ALIGNED
//! variant: `uper::fraglist` with every length head octet-aligned.
//!
//! In APER the length determinant of 11.9.3.6 to 11.9.3.8 is an octet-aligned
//! field in all its forms, and a fragment's `m * 16K` elements may end at any
//! bit (20.6 NOTE 2), so the next head is aligned again. The head is UPER's
//! `LenHead`, octet-aligned (`lha`). For a list of octets, bits or characters
//! of a power-of-two width the padding before every head after the first is
//! empty; for a SEQUENCE OF it is not.
use vstd::prelude::*;
use crate::aper::format::*;
use crate::aper::list::*;
use crate::uper::frag as uf;
pub use crate::uper::frag::LenHead;
#[cfg(verus_keep_ghost)]
pub use crate::uper::frag::{frag_blocks, lemma_frag_len_ge, lemma_frag_blocks, lh_wf, lemma_lh_wf_iff};

verus! {

broadcast use {format_steps, map_steps, list_steps};

// ------------------------------------------------------------ the head, aligned

pub open spec fn lha_wf() -> Wf<LenHead> { uf::lh_wf() }
pub open spec fn lha_enc() -> Enc<LenHead> { aligned_enc(lift_enc(uf::lh_enc())) }
pub open spec fn lha_dec() -> Dec<LenHead> { aligned_dec(lift_dec(uf::lh_dec())) }

pub proof fn lemma_lha_format()
    ensures is_format(lha_wf(), lha_enc(), lha_dec()),
{
    uf::lemma_lh_format();
    lemma_lift_format(uf::lh_wf(), uf::lh_enc(), uf::lh_dec());
    lemma_aligned_format(uf::lh_wf(), lift_enc(uf::lh_enc()), lift_dec(uf::lh_dec()));
}

/// The head's decode, pinned down: well formed, at least 8 bits, and exactly
/// the bits of its own encoding.
pub proof fn lemma_lha_dec_facts(b: In)
    requires lha_dec()(b) is Some,
    ensures
        uf::lh_wf()(lha_dec()(b).unwrap().0),
        8 <= lha_dec()(b).unwrap().1 <= b.1.len(),
        lha_dec()(b).unwrap().2 is SameVer,
        b.1.take(lha_dec()(b).unwrap().1 as int) == lha_enc()(b.0, lha_dec()(b).unwrap().0),
{
    lemma_lha_format();
    lemma_aligned_dec_val(lift_dec(uf::lh_dec()), b);
    let p = pad(b.0);
    let b1 = adv(b, p);
    crate::uper::fraglist::lemma_lh_dec_facts(b1.1);
}

/// A head followed by anything decodes to itself.
pub proof fn lemma_lha_dec_enc(pos: nat, h: LenHead, rest: Seq<bool>)
    requires uf::lh_wf()(h),
    ensures
        lha_dec()((pos, lha_enc()(pos, h) + rest))
            == Some::<(LenHead, nat, Flg)>((h, lha_enc()(pos, h).len(), Flg::SameVer)),
        8 <= lha_enc()(pos, h).len(),
{
    lemma_lha_format();
    lemma_aligned_enc_val(lift_enc(uf::lh_enc()), pos, h);
    crate::uper::fraglist::lemma_lh_dec_enc(h, rest);
}

/// `list_dec_rec(n, ..)` yields exactly `n` elements.
pub proof fn lemma_list_dec_len<A>(n: nat, d: Dec<A>, b: In)
    ensures list_dec_rec(n, d, b) is Some ==> list_dec_rec(n, d, b).unwrap().0.len() == n,
    decreases n,
{
    if n > 0 && d(b) is Some {
        lemma_list_dec_len((n - 1) as nat, d, adv(b, d(b).unwrap().1));
    }
}

// ------------------------------------------------------------------ the list

pub open spec fn flist_enc_rec<A>(pos: nat, l: Seq<A>, e: Enc<A>) -> Seq<bool>
    decreases l.len(),
{
    if l.len() < 16384 {
        let h = lha_enc()(pos, LenHead::Final(l.len() as u64));
        h + list_enc_rec(pos + h.len(), l, e)
    } else {
        let m = frag_blocks(l.len());
        let n = (m * 16384) as int;
        let h = lha_enc()(pos, LenHead::Frag(m as u64));
        let body = list_enc_rec(pos + h.len(), l.take(n), e);
        h + body + flist_enc_rec(pos + h.len() + body.len(), l.skip(n), e)
    }
}

pub open spec fn flist_dec_rec<A>(d: Dec<A>, b: In) -> Option<(Seq<A>, nat, Flg)>
    decreases b.1.len(),
{
    match lha_dec()(b) {
        Some((h, k, _)) => {
            if k == 0 || k > b.1.len() {
                None
            } else {
                match h {
                    LenHead::Final(n) => match list_dec_rec(n as nat, d, adv(b, k)) {
                        Some((l1, k1, f1)) => if k + k1 > b.1.len() {
                            None
                        } else {
                            Some((l1, (k + k1) as nat, f1))
                        },
                        None => None,
                    },
                    LenHead::Frag(m) => match list_dec_rec((m as nat) * 16384, d, adv(b, k)) {
                        Some((l1, k1, f1)) => if k + k1 > b.1.len() {
                            None
                        } else {
                            match flist_dec_rec(d, adv(b, (k + k1) as nat)) {
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
    |pos: nat, l: Seq<A>| flist_enc_rec(pos, l, e)
}

#[verifier::opaque]
pub open spec fn flist_dec<A>(d: Dec<A>) -> Dec<Seq<A>> {
    |b: In| flist_dec_rec(d, b)
}

pub broadcast proof fn lemma_flist_wf_val<A>(w: Wf<A>, l: Seq<A>)
    ensures #[trigger] flist_wf(w)(l) == (forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])),
{
    reveal(flist_wf);
}

pub broadcast proof fn lemma_flist_enc_val<A>(e: Enc<A>, pos: nat, l: Seq<A>)
    ensures #[trigger] flist_enc(e)(pos, l) == flist_enc_rec(pos, l, e),
{
    reveal(flist_enc);
}

pub broadcast proof fn lemma_flist_dec_val<A>(d: Dec<A>, b: In)
    ensures #[trigger] flist_dec(d)(b) == flist_dec_rec(d, b),
{
    reveal(flist_dec);
}

pub broadcast group flist_steps {
    lemma_flist_wf_val,
    lemma_flist_enc_val,
    lemma_flist_dec_val,
}

} // verus!

verus! {

pub proof fn lemma_flist_surj_final<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>, pos: nat, l: Seq<A>, rest: Seq<bool>)
    requires
        is_format(w, e, d),
        forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i]),
        l.len() < 16384,
    ensures
        flist_dec_rec(d, (pos, flist_enc_rec(pos, l, e) + rest))
            == Some::<(Seq<A>, nat, Flg)>((l, flist_enc_rec(pos, l, e).len(), Flg::SameVer)),
{
    let h = LenHead::Final(l.len() as u64);
    lemma_lh_wf_iff(h);
    let g = lha_enc()(pos, h);
    let p1 = pos + g.len();
    let body = list_enc_rec(p1, l, e);
    let b = flist_enc_rec(pos, l, e) + rest;
    assert(b =~= g + (body + rest));
    lemma_lha_dec_enc(pos, h, body + rest);
    lemma_take_add(g, body + rest);
    assert(adv((pos, b), g.len()) =~= (p1, body + rest));
    lemma_list_surj(l.len(), w, e, d, p1, l, rest);
}

pub proof fn lemma_flist_surj<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>, pos: nat, l: Seq<A>, rest: Seq<bool>)
    requires
        is_format(w, e, d),
        forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i]),
    ensures
        flist_dec_rec(d, (pos, flist_enc_rec(pos, l, e) + rest))
            == Some::<(Seq<A>, nat, Flg)>((l, flist_enc_rec(pos, l, e).len(), Flg::SameVer)),
    decreases l.len(),
{
    if l.len() < 16384 {
        lemma_flist_surj_final(w, e, d, pos, l, rest);
    } else {
        lemma_frag_len_ge(l.len());
        let m = frag_blocks(l.len());
        let n = (m * 16384) as int;
        let h = LenHead::Frag(m as u64);
        lemma_lh_wf_iff(h);
        let g = lha_enc()(pos, h);
        let p1 = pos + g.len();
        let head = l.take(n);
        let tail = l.skip(n);
        let hb = list_enc_rec(p1, head, e);
        let p2 = p1 + hb.len();
        let tb = flist_enc_rec(p2, tail, e);
        let b = flist_enc_rec(pos, l, e) + rest;
        assert(b =~= g + (hb + (tb + rest)));
        lemma_lha_dec_enc(pos, h, hb + (tb + rest));
        lemma_take_add(g, hb + (tb + rest));
        assert(adv((pos, b), g.len()) =~= (p1, hb + (tb + rest)));
        assert forall|i: int| 0 <= i < head.len() implies w(#[trigger] head[i]) by {
            assert(head[i] == l[i]);
        }
        assert forall|i: int| 0 <= i < tail.len() implies w(#[trigger] tail[i]) by {
            assert(tail[i] == l[i + n]);
        }
        lemma_list_surj((m * 16384) as nat, w, e, d, p1, head, tb + rest);
        lemma_take_add(hb, tb + rest);
        assert(adv((pos, b), (g.len() + hb.len()) as nat) =~= (p2, tb + rest));
        lemma_flist_surj(w, e, d, p2, tail, rest);
        if m < 4 {
            assert(l.len() / 16384 == m);
            assert(l.len() - m * 16384 < 16384) by (nonlinear_arith)
                requires l.len() / 16384 == m;
            {}
        }
        assert(head + tail =~= l);
    }
}

pub proof fn lemma_flist_inj<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>, b: In)
    requires is_format(w, e, d), flist_dec_rec(d, b) is Some,
    ensures ({
        let (l, k, f) = flist_dec_rec(d, b).unwrap();
        &&& forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i])
        &&& k <= b.1.len()
        &&& f is SameVer ==> b.1.take(k as int) == flist_enc_rec(b.0, l, e)
    }),
    decreases b.1.len(),
{
    lemma_lha_dec_facts(b);
    let (h, k, _) = lha_dec()(b).unwrap();
    lemma_lh_wf_iff(h);
    let body = adv(b, k);
    assert(lha_enc()(b.0, h).len() == k);
    match h {
        LenHead::Final(n) => {
            lemma_list_inj(n as nat, w, e, d, body);
            let (l1, k1, f1) = list_dec_rec(n as nat, d, body).unwrap();
            lemma_take_split(b.1, k, k1);
            assert(l1.len() as u64 == n);
        },
        LenHead::Frag(m) => {
            let cnt = (m as nat) * 16384;
            lemma_list_inj(cnt, w, e, d, body);
            let (l1, k1, f1) = list_dec_rec(cnt, d, body).unwrap();
            let tailb = adv(b, (k + k1) as nat);
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
            lemma_take_split(b.1, k, k1);
            lemma_take_split(b.1, (k + k1) as nat, k2);
            if flg_add(f1, f2) is SameVer {
                assert(body.1.take(k1 as int) == list_enc_rec(b.0 + k, l1, e));
                assert(list_enc_rec(b.0 + k, l1, e).len() == k1);
            }
        },
    }
}

pub proof fn lemma_flist_format<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(flist_wf(w), flist_enc(e), flist_dec(d)),
{
    reveal(flist_wf); reveal(flist_enc); reveal(flist_dec);
    assert forall|pos: nat, l: Seq<A>, rest: Seq<bool>| flist_wf(w)(l) implies
        #[trigger] flist_dec(d)((pos, flist_enc(e)(pos, l) + rest))
            == Some::<(Seq<A>, nat, Flg)>((l, flist_enc(e)(pos, l).len(), Flg::SameVer))
    by {
        lemma_flist_surj(w, e, d, pos, l, rest);
    }
    assert forall|b: In| (#[trigger] flist_dec(d)(b)).is_some() implies {
        let l = flist_dec(d)(b).unwrap().0;
        let k = flist_dec(d)(b).unwrap().1;
        &&& flist_wf(w)(l) && k <= b.1.len()
        &&& flist_dec(d)(b).unwrap().2 is SameVer ==> b.1.take(k as int) == flist_enc(e)(b.0, l)
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

pub proof fn lemma_flist_loop_start<A>(d: Dec<A>, b: In)
    ensures flist_dec_rec(d, b)
        == flist_cont(Seq::<A>::empty(), 0nat, Flg::SameVer, false, flist_dec_rec(d, b)),
{
    if let Some((l, k, f)) = flist_dec_rec(d, b) {
        assert(Seq::<A>::empty() + l =~= l);
    }
}

pub proof fn lemma_flist_loop_fail<A>(d: Dec<A>, start: In, cur: In, acc: Seq<A>,
                                      consumed: nat, fa: Flg, pending: bool)
    requires
        flist_dec_rec(d, start) == flist_cont(acc, consumed, fa, pending, flist_dec_rec(d, cur)),
        lha_dec()(cur) is None || ({
            let (h, k, _) = lha_dec()(cur).unwrap();
            let cnt: nat = match h { LenHead::Final(n) => n as nat, LenHead::Frag(m) => (m as nat) * 16384 };
            list_dec_rec(cnt, d, adv(cur, k)) is None
        }),
    ensures flist_dec_rec(d, start) is None,
{
    if lha_dec()(cur) is Some {
        lemma_lha_dec_facts(cur);
    }
}

pub proof fn lemma_flist_loop_pending<A>(d: Dec<A>, start: In, cur: In, acc: Seq<A>,
                                         consumed: nat, fa: Flg, m: u64, k: nat)
    requires
        flist_dec_rec(d, start) == flist_cont(acc, consumed, fa, true, flist_dec_rec(d, cur)),
        lha_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Frag(m), k, Flg::SameVer)),
    ensures flist_dec_rec(d, start) is None,
{
    lemma_lha_dec_facts(cur);
    lemma_lh_wf_iff(LenHead::Frag(m));
    let cnt = (m as nat) * 16384;
    lemma_list_dec_len(cnt, d, adv(cur, k));
}

pub proof fn lemma_flist_loop_frag<A>(d: Dec<A>, start: In, cur: In, acc: Seq<A>,
                                      consumed: nat, fa: Flg,
                                      m: u64, k: nat, l1: Seq<A>, k1: nat, f1: Flg)
    requires
        cur == adv(start, consumed),
        consumed + cur.1.len() == start.1.len(),
        flist_dec_rec(d, start) == flist_cont(acc, consumed, fa, false, flist_dec_rec(d, cur)),
        lha_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Frag(m), k, Flg::SameVer)),
        list_dec_rec((m as nat) * 16384, d, adv(cur, k)) == Some::<(Seq<A>, nat, Flg)>((l1, k1, f1)),
        k + k1 <= cur.1.len(),
    ensures
        1 <= m <= 4,
        flist_dec_rec(d, start)
            == flist_cont(acc + l1, (consumed + k + k1) as nat, flg_add(fa, f1), m < 4,
                          flist_dec_rec(d, adv(start, (consumed + k + k1) as nat))),
{
    lemma_lha_dec_facts(cur);
    lemma_lh_wf_iff(LenHead::Frag(m));
    let cur2 = adv(cur, (k + k1) as nat);
    assert(cur2 =~= adv(start, (consumed + k + k1) as nat));
    if let Some((l2, k2, f2)) = flist_dec_rec(d, cur2) {
        assert((acc + l1) + l2 =~= acc + (l1 + l2));
    }
}

pub proof fn lemma_flist_loop_final<A>(d: Dec<A>, start: In, cur: In, acc: Seq<A>,
                                       consumed: nat, fa: Flg, pending: bool,
                                       n: u64, k: nat, l1: Seq<A>, k1: nat, f1: Flg)
    requires
        flist_dec_rec(d, start) == flist_cont(acc, consumed, fa, pending, flist_dec_rec(d, cur)),
        lha_dec()(cur) == Some::<(LenHead, nat, Flg)>((LenHead::Final(n), k, Flg::SameVer)),
        list_dec_rec(n as nat, d, adv(cur, k)) == Some::<(Seq<A>, nat, Flg)>((l1, k1, f1)),
        k + k1 <= cur.1.len(),
    ensures
        flist_dec_rec(d, start)
            == Some::<(Seq<A>, nat, Flg)>((acc + l1, (consumed + k + k1) as nat, flg_add(fa, f1))),
{
    lemma_lha_dec_facts(cur);
    lemma_lh_wf_iff(LenHead::Final(n));
    lemma_list_dec_len(n as nat, d, adv(cur, k));
}

// The encoder: the spec's recursion read forwards.

pub proof fn lemma_flist_enc_step<A>(pos: nat, s: Seq<A>, e: Enc<A>, off: nat, m: nat)
    requires
        off <= s.len(),
        s.len() - off >= 16384,
        m == frag_blocks((s.len() - off) as nat),
    ensures
        1 <= m <= 4,
        off + m * 16384 <= s.len(),
        ({
            let h = lha_enc()(pos, LenHead::Frag(m as u64));
            let body = list_enc_rec(pos + h.len(), s.subrange(off as int, (off + m * 16384) as int), e);
            flist_enc_rec(pos, s.skip(off as int), e)
                =~= h + body + flist_enc_rec(pos + h.len() + body.len(), s.skip((off + m * 16384) as int), e)
        }),
{
    let rest = s.skip(off as int);
    lemma_frag_len_ge(rest.len());
    let n = (m * 16384) as int;
    assert(rest.take(n) =~= s.subrange(off as int, off + n));
    assert(rest.skip(n) =~= s.skip(off + n));
}

pub proof fn lemma_flist_enc_last<A>(pos: nat, s: Seq<A>, e: Enc<A>, off: nat)
    requires off <= s.len(), s.len() - off < 16384,
    ensures ({
        let h = lha_enc()(pos, LenHead::Final((s.len() - off) as u64));
        flist_enc_rec(pos, s.skip(off as int), e)
            =~= h + list_enc_rec(pos + h.len(), s.subrange(off as int, s.len() as int), e)
    }),
{
    assert(s.skip(off as int) =~= s.subrange(off as int, s.len() as int));
}

/// One turn of the encoder's loop as a single implication on `written()`:
/// `pb` is where this turn's head starts, `pa` where the next one does.
#[verifier::rlimit(20)]
pub proof fn lemma_flist_enc_loop_step<A>(
    wbefore: Seq<bool>, wafter: Seq<bool>, w0: Seq<bool>, p0: nat, pb: nat, s: Seq<A>, e: Enc<A>,
    off: nat, m: nat,
)
    requires
        off <= s.len(),
        s.len() - off >= 16384,
        m == frag_blocks((s.len() - off) as nat),
        pb == p0 + (wbefore.len() - w0.len()),
        wbefore.len() >= w0.len(),
        ({
            let h = lha_enc()(pb, LenHead::Frag(m as u64));
            wafter =~= wbefore + h
                + list_enc_rec(pb + h.len(), s.subrange(off as int, (off + m * 16384) as int), e)
        }),
        wbefore + flist_enc_rec(pb, s.skip(off as int), e) =~= w0 + flist_enc_rec(p0, s, e),
    ensures
        off + m * 16384 <= s.len(),
        wafter + flist_enc_rec((p0 + (wafter.len() - w0.len())) as nat, s.skip((off + m * 16384) as int), e)
            =~= w0 + flist_enc_rec(p0, s, e),
{
    lemma_flist_enc_step(pb, s, e, off, m);
}

pub proof fn lemma_flist_enc_loop_last<A>(
    wbefore: Seq<bool>, wafter: Seq<bool>, w0: Seq<bool>, p0: nat, pb: nat, s: Seq<A>, e: Enc<A>,
    off: nat,
)
    requires
        off <= s.len(),
        s.len() - off < 16384,
        pb == p0 + (wbefore.len() - w0.len()),
        ({
            let h = lha_enc()(pb, LenHead::Final((s.len() - off) as u64));
            wafter =~= wbefore + h + list_enc_rec(pb + h.len(), s.subrange(off as int, s.len() as int), e)
        }),
        wbefore + flist_enc_rec(pb, s.skip(off as int), e) =~= w0 + flist_enc_rec(p0, s, e),
    ensures
        wafter =~= w0 + flist_enc_rec(p0, s, e),
{
    lemma_flist_enc_last(pb, s, e, off);
}

} // verus!

verus! {

use crate::aper::cursor::*;

impl<'a> BitReader<'a> {
    /// Refines `lha_dec()`: the padding, then UPER's head.
    pub fn read_alh(&mut self) -> (res: Option<LenHead>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(h) => lha_dec()(old(self).at())
                    == Some::<(LenHead, nat, Flg)>((h, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => lha_dec()(old(self).at()).is_none(),
            },
    {
        let ghost i = self.at();
        let ghost d = lift_dec(uf::lh_dec());
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_dec_val(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_dec_val(d, i);
        }
        self.read_lh()
    }
}

impl BitWriter {
    /// Refines `lha_enc()`.
    pub fn write_alh(&mut self, h: LenHead) -> (ok: bool)
        requires old(self).wf(), uf::lh_wf()(h),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + lha_enc()(old(self).pos as nat, h),
    {
        proof { lemma_aligned_enc_val(lift_enc(uf::lh_enc()), old(self).pos as nat, h); }
        if !self.write_align() { return false; }
        self.write_lh(h)
    }
}

} // verus!
