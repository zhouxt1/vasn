//! The extensible SEQUENCE (X.691 19) in the ALIGNED variant: `uper::seqext`
//! with every part placed at a position.
//!
//! The shape is UPER's: the extension bit, the root, and, if the bit is set,
//! the count of additions as a normally small length (11.9.3.4), a bitmap of
//! that many bits (19.7), and each present addition as an open type (19.9).
//! What the ALIGNED variant changes is inside those parts: the count's long
//! form and every open type are octet-aligned (`aper::xext::nsld`,
//! `aper::opentype`). So the combinator and its proofs are UPER's, with the
//! position each part starts at carried along, and an unknown addition is
//! stepped over by this module's (aligned) `frag_dec`.
//!
//! The decoder's three branches for a peer of another version, and why the
//! flag makes injection provable on only one of them, are as in UPER; see
//! there.
use vstd::prelude::*;
use crate::aper::format::*;
use crate::aper::term::*;
use crate::aper::list::*;
use crate::aper::xext::*;
use crate::aper::opentype::*;
pub use crate::uper::seqext::{all_absent_run, bm_fit};
#[cfg(verus_keep_ghost)]
pub use crate::uper::seqext::all_absent;

verus! {

broadcast use {format_steps, map_steps, list_steps};

pub open spec fn ext_adds_ok<E>(
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
) -> bool {
    &&& forall|bm: Seq<bool>| bm.len() == c ==> is_format(#[trigger] wa(bm), ea(bm), da(bm))
    &&& forall|bm: Seq<bool>, e: E| #![trigger wa(bm)(e)]
            bm.len() == c && wa(bm)(e) ==> bmof(e) == bm
    &&& forall|e: E| #![trigger wa(zeros(c))(e)] wa(zeros(c))(e) ==> e == e0
    &&& wa(zeros(c))(e0)
}

// ------------------------------------------------------------------- the bits

pub open spec fn ext_count_enc(pos: nat, c: nat) -> Seq<bool> {
    nsld_enc()(pos, c as u64)
}

pub open spec fn ext_bm_enc(c: nat) -> Enc<Seq<bool>> {
    list_enc(c, bool_enc())
}

pub open spec fn ext_bm_dec(n: nat) -> Dec<Seq<bool>> {
    list_dec(n, bool_dec())
}

/// Step over the additions this schema has never heard of, one open type per
/// set bit, and report how many bits that took.
pub open spec fn skip_adds(bmtail: Seq<bool>, b: In) -> Option<nat>
    decreases bmtail.len(),
{
    if bmtail.len() == 0 {
        Some(0nat)
    } else if !bmtail[0] {
        skip_adds(bmtail.skip(1), b)
    } else {
        match frag_dec()(b) {
            Some((_, k, _)) => match skip_adds(bmtail.skip(1), adv(b, k)) {
                Some(k2) => Some((k + k2) as nat),
                None => None,
            },
            None => None,
        }
    }
}

pub proof fn lemma_skip_adds_bound(bmtail: Seq<bool>, b: In)
    ensures skip_adds(bmtail, b) is Some ==> skip_adds(bmtail, b).unwrap() <= b.1.len(),
    decreases bmtail.len(),
{
    lemma_frag_format();
    if bmtail.len() == 0 {
    } else if !bmtail[0] {
        lemma_skip_adds_bound(bmtail.skip(1), b);
    } else if frag_dec()(b) is Some {
        let k = frag_dec()(b).unwrap().1;
        assert(k <= b.1.len());
        lemma_skip_adds_bound(bmtail.skip(1), adv(b, k));
    }
}

// ------------------------------------------------------------------ the format

pub open spec fn ext_wf<R, E>(
    wr: Wf<R>,
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    bmof: spec_fn(E) -> Seq<bool>,
) -> Wf<(R, E)> {
    |p: (R, E)| wr(p.0) && bmof(p.1).len() == c && wa(bmof(p.1))(p.1)
}

/// The parts, and the position each starts at: the bit at `pos`, the root at
/// `pos + 1`, then the count, the bitmap and the additions each where the
/// one before ended.
pub open spec fn ext_enc<R, E>(
    er: Enc<R>,
    c: nat,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    bmof: spec_fn(E) -> Seq<bool>,
) -> Enc<(R, E)> {
    |pos: nat, p: (R, E)| {
        let bm = bmof(p.1);
        let root = er(pos + 1, p.0);
        let p2 = pos + 1 + root.len();
        if all_absent(bm) {
            seq![false] + root
        } else {
            let cnt = ext_count_enc(p2, c);
            let p3 = p2 + cnt.len();
            let bmb = ext_bm_enc(c)(p3, bm);
            let p4 = p3 + bmb.len();
            seq![true] + root + cnt + bmb + ea(bm)(p4, p.1)
        }
    }
}

pub open spec fn ext_tail_dec<E>(
    c: nat,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    b: In,
) -> Option<(E, nat, Flg)> {
    match nsld_dec()(b) {
        None => None,
        Some((n, kn, _)) => {
            let b2 = adv(b, kn);
            match ext_bm_dec(n as nat)(b2) {
                None => None,
                Some((bm, kb, _)) => {
                    if all_absent(bm) {
                        None
                    } else {
                        let b3 = adv(b2, kb);
                        if n as nat == c {
                            match da(bm)(b3) {
                                Some((e, ke, fe)) => Some((e, (kn + kb + ke) as nat, fe)),
                                None => None,
                            }
                        } else if (n as nat) < c {
                            let bmp = bm + zeros((c - n as nat) as nat);
                            match da(bmp)(b3) {
                                Some((e, ke, _)) =>
                                    Some((e, (kn + kb + ke) as nat, Flg::DiffVer)),
                                None => None,
                            }
                        } else {
                            let bmt = bm.take(c as int);
                            match da(bmt)(b3) {
                                Some((e, ke, _)) => match skip_adds(bm.skip(c as int), adv(b3, ke)) {
                                    Some(ks) =>
                                        Some((e, (kn + kb + ke + ks) as nat, Flg::DiffVer)),
                                    None => None,
                                },
                                None => None,
                            }
                        }
                    }
                },
            }
        },
    }
}

pub open spec fn ext_dec<R, E>(
    dr: Dec<R>,
    c: nat,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    e0: E,
) -> Dec<(R, E)> {
    |b: In| {
        if b.1.len() == 0 {
            None
        } else {
            match dr(adv(b, 1)) {
                None => None,
                Some((r, kr, fr)) => {
                    if !b.1[0] {
                        Some(((r, e0), (1 + kr) as nat, fr))
                    } else {
                        match ext_tail_dec(c, da, adv(b, (1 + kr) as nat)) {
                            Some((e, kt, ft)) =>
                                Some(((r, e), (1 + kr + kt) as nat, flg_add(fr, ft))),
                            None => None,
                        }
                    }
                },
            }
        }
    }
}

} // verus!

verus! {

// --------------------------------------------------------------- surjection

/// The short branch: no addition present, so the bit and the root.
proof fn lemma_ext_surj_absent<R, E>(
    wr: Wf<R>, er: Enc<R>, dr: Dec<R>,
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
    pos: nat,
    p: (R, E),
    rest: Seq<bool>,
)
    requires
        is_format(wr, er, dr),
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        ext_wf(wr, c, wa, bmof)(p),
        all_absent(bmof(p.1)),
    ensures
        ({
            let e = ext_enc(er, c, ea, bmof)(pos, p);
            ext_dec(dr, c, da, e0)((pos, e + rest))
                == Some::<((R, E), nat, Flg)>((p, e.len(), Flg::SameVer))
        }),
{
    let (r, ev) = p;
    let bm = bmof(ev);
    let enc = ext_enc(er, c, ea, bmof)(pos, p);
    let b = enc + rest;
    let root = er(pos + 1, r);
    assert(bm =~= zeros(c));
    assert(wa(zeros(c))(ev));
    assert(ev == e0);
    assert(enc == seq![false] + root);
    assert(b =~= seq![false] + (root + rest));
    assert(b[0] == false);
    lemma_take_add(seq![false], root + rest);
    let b1: In = adv((pos, b), 1);
    assert(b1.1 =~= root + rest);
    assert(b1 == (pos + 1, root + rest));
    assert(dr(b1) == Some::<(R, nat, Flg)>((r, root.len(), Flg::SameVer)));
}

/// The long branch, from just past the root: the count, the bitmap, the
/// additions, decoded as they were written.
proof fn lemma_ext_surj_tail<E>(
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
    p2: nat,
    ev: E,
    rest: Seq<bool>,
)
    requires
        0 < c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        bmof(ev).len() == c,
        wa(bmof(ev))(ev),
        !all_absent(bmof(ev)),
    ensures
        ({
            let bm = bmof(ev);
            let cnt = ext_count_enc(p2, c);
            let p3 = p2 + cnt.len();
            let bmb = ext_bm_enc(c)(p3, bm);
            let adds = ea(bm)(p3 + bmb.len(), ev);
            ext_tail_dec(c, da, (p2, cnt + (bmb + (adds + rest))))
                == Some::<(E, nat, Flg)>((ev, (cnt.len() + bmb.len() + adds.len()) as nat, Flg::SameVer))
        }),
{
    let bm = bmof(ev);
    lemma_nsld_format();
    lemma_nsld_wf_iff(c as u64);
    lemma_bool_format();
    lemma_list_format(c, bool_wf(), bool_enc(), bool_dec());
    let cnt = ext_count_enc(p2, c);
    let p3 = p2 + cnt.len();
    let bmb = ext_bm_enc(c)(p3, bm);
    let p4 = p3 + bmb.len();
    let adds = ea(bm)(p4, ev);
    let b1: In = (p2, cnt + (bmb + (adds + rest)));

    assert(nsld_wf()(c as u64));
    assert(nsld_dec()(b1) == Some::<(u64, nat, Flg)>((c as u64, cnt.len(), Flg::SameVer)));
    lemma_take_add(cnt, bmb + (adds + rest));
    let b2: In = adv(b1, cnt.len());
    assert(b2.1 =~= bmb + (adds + rest));
    assert(b2 == (p3, bmb + (adds + rest)));

    assert forall|j: int| 0 <= j < bm.len() implies bool_wf()(#[trigger] bm[j]) by {
        lemma_bool_wf_all(bm[j]);
    }
    assert(list_wf(c, bool_wf())(bm));
    assert(ext_bm_dec(c)(b2) == Some::<(Seq<bool>, nat, Flg)>((bm, bmb.len(), Flg::SameVer)));
    lemma_take_add(bmb, adds + rest);
    let b3: In = adv(b2, bmb.len());
    assert(b3.1 =~= adds + rest);
    assert(b3 == (p4, adds + rest));

    assert(is_format(wa(bm), ea(bm), da(bm)));
    assert(da(bm)(b3) == Some::<(E, nat, Flg)>((ev, adds.len(), Flg::SameVer)));
}

#[verifier::rlimit(60)]
pub proof fn lemma_ext_surj<R, E>(
    wr: Wf<R>, er: Enc<R>, dr: Dec<R>,
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
    pos: nat,
    p: (R, E),
    rest: Seq<bool>,
)
    requires
        is_format(wr, er, dr),
        c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        ext_wf(wr, c, wa, bmof)(p),
    ensures
        ({
            let e = ext_enc(er, c, ea, bmof)(pos, p);
            ext_dec(dr, c, da, e0)((pos, e + rest))
                == Some::<((R, E), nat, Flg)>((p, e.len(), Flg::SameVer))
        }),
{
    let (r, ev) = p;
    let bm = bmof(ev);
    if all_absent(bm) {
        lemma_ext_surj_absent(wr, er, dr, c, wa, ea, da, bmof, e0, pos, p, rest);
    } else {
        assert(c > 0) by { if c == 0 { assert(bm =~= zeros(0)); } }
        let enc = ext_enc(er, c, ea, bmof)(pos, p);
        let b = enc + rest;
        let root = er(pos + 1, r);
        let kr = root.len();
        let p2 = pos + 1 + kr;
        let cnt = ext_count_enc(p2, c);
        let p3 = p2 + cnt.len();
        let bmb = ext_bm_enc(c)(p3, bm);
        let adds = ea(bm)(p3 + bmb.len(), ev);
        let tail = cnt + (bmb + (adds + rest));
        assert(enc == seq![true] + root + cnt + bmb + adds);
        assert(b =~= seq![true] + (root + tail));
        assert(b[0] == true);
        lemma_take_add(seq![true], root + tail);
        let b0: In = adv((pos, b), 1);
        assert(b0.1 =~= root + tail);
        assert(b0 == (pos + 1, root + tail));
        assert(dr(b0) == Some::<(R, nat, Flg)>((r, kr, Flg::SameVer)));
        lemma_take_add(root, tail);
        let b1: In = adv((pos, b), (1 + kr) as nat);
        assert(b1.1 =~= tail);
        assert(b1 == (p2, tail));
        lemma_ext_surj_tail(c, wa, ea, da, bmof, e0, p2, ev, rest);
        assert(enc.len() == 1 + kr + cnt.len() + bmb.len() + adds.len());
    }
}

} // verus!

verus! {

// ----------------------------------------------------------- weak injection

pub proof fn lemma_ext_tail_weak<E>(
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
    b: In,
)
    requires
        c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        ext_tail_dec(c, da, b) is Some,
    ensures
        bmof(ext_tail_dec(c, da, b).unwrap().0).len() == c,
        wa(bmof(ext_tail_dec(c, da, b).unwrap().0))(ext_tail_dec(c, da, b).unwrap().0),
        ext_tail_dec(c, da, b).unwrap().1 <= b.1.len(),
{
    lemma_nsld_format();
    let n = nsld_dec()(b).unwrap().0 as nat;
    let kn = nsld_dec()(b).unwrap().1;
    let b2 = adv(b, kn);

    lemma_bool_format();
    lemma_list_format(n, bool_wf(), bool_enc(), bool_dec());
    let bm = ext_bm_dec(n)(b2).unwrap().0;
    let kb = ext_bm_dec(n)(b2).unwrap().1;
    let b3 = adv(b2, kb);
    assert(list_wf(n, bool_wf())(bm));
    assert(bm.len() == n);
    assert(kn <= b.1.len());
    assert(kb <= b2.1.len());

    let bmu = if n == c {
        bm
    } else if n < c {
        bm + zeros((c - n) as nat)
    } else {
        bm.take(c as int)
    };
    assert(bmu.len() == c);
    assert(is_format(wa(bmu), ea(bmu), da(bmu)));
    let e = da(bmu)(b3).unwrap().0;
    let ke = da(bmu)(b3).unwrap().1;
    assert(wa(bmu)(e));
    assert(bmof(e) == bmu);
    assert(ke <= b3.1.len());
    if n > c {
        lemma_skip_adds_bound(bm.skip(c as int), adv(b3, ke));
    }
}

pub proof fn lemma_ext_weak_inj<R, E>(
    wr: Wf<R>, er: Enc<R>, dr: Dec<R>,
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
    b: In,
)
    requires
        is_format(wr, er, dr),
        c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        ext_dec(dr, c, da, e0)(b) is Some,
    ensures
        ext_wf(wr, c, wa, bmof)(ext_dec(dr, c, da, e0)(b).unwrap().0),
        ext_dec(dr, c, da, e0)(b).unwrap().1 <= b.1.len(),
{
    let r = dr(adv(b, 1)).unwrap().0;
    let kr = dr(adv(b, 1)).unwrap().1;
    assert(wr(r));
    assert(kr <= adv(b, 1).1.len());
    if !b.1[0] {
        assert(wa(zeros(c))(e0));
        assert(bmof(e0) == zeros(c));
    } else {
        lemma_ext_tail_weak(c, wa, ea, da, bmof, e0, adv(b, (1 + kr) as nat));
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------- injection

pub proof fn lemma_ext_inj<R, E>(
    wr: Wf<R>, er: Enc<R>, dr: Dec<R>,
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
    b: In,
)
    requires
        is_format(wr, er, dr),
        c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        ext_dec(dr, c, da, e0)(b) is Some,
        ext_dec(dr, c, da, e0)(b).unwrap().2 is SameVer,
    ensures
        b.1.take(ext_dec(dr, c, da, e0)(b).unwrap().1 as int)
            == ext_enc(er, c, ea, bmof)(b.0, ext_dec(dr, c, da, e0)(b).unwrap().0),
{
    lemma_ext_weak_inj(wr, er, dr, c, wa, ea, da, bmof, e0, b);
    let s = b.1;
    let pos = b.0;
    let k = ext_dec(dr, c, da, e0)(b).unwrap().1;
    let r = dr(adv(b, 1)).unwrap().0;
    let kr = dr(adv(b, 1)).unwrap().1;
    assert(s.take(1) =~= seq![s[0]]);
    assert(adv(b, 1).1.take(kr as int) == er(pos + 1, r));
    assert(er(pos + 1, r).len() == kr);

    if !s[0] {
        lemma_take_split(s, 1nat, kr);
        assert(s.take((1 + kr) as int) =~= seq![false] + er(pos + 1, r));
        assert(wa(zeros(c))(e0));
        assert(bmof(e0) == zeros(c));
        assert(zeros(c).len() == c);
        assert(all_absent(bmof(e0)));
    } else {
        let b1 = adv(b, (1 + kr) as nat);
        lemma_ext_tail_weak(c, wa, ea, da, bmof, e0, b1);
        let kt = ext_tail_dec(c, da, b1).unwrap().1;
        let ev = ext_tail_dec(c, da, b1).unwrap().0;

        lemma_nsld_format();
        lemma_nsld_dec_same(b1);
        let n = nsld_dec()(b1).unwrap().0 as nat;
        let kn = nsld_dec()(b1).unwrap().1;
        let b2 = adv(b1, kn);
        assert(b1.1.take(kn as int) == nsld_enc()(b1.0, n as u64));

        lemma_bool_format();
        lemma_list_format(n, bool_wf(), bool_enc(), bool_dec());
        assert forall|t: In| (#[trigger] bool_dec()(t)) is Some implies
            bool_dec()(t).unwrap().2 is SameVer by { lemma_bool_dec_same(t); }
        lemma_list_dec_same(n, bool_dec(), b2);
        let bm = ext_bm_dec(n)(b2).unwrap().0;
        let kb = ext_bm_dec(n)(b2).unwrap().1;
        let b3 = adv(b2, kb);
        assert(ext_bm_dec(n)(b2).unwrap().2 is SameVer);
        assert(b2.1.take(kb as int) == list_enc(n, bool_enc())(b2.0, bm));

        assert(n == c);
        assert(is_format(wa(bm), ea(bm), da(bm)));
        let ke = da(bm)(b3).unwrap().1;
        assert(b3.1.take(ke as int) == ea(bm)(b3.0, ev));
        assert(bmof(ev) == bm);
        assert(!all_absent(bm));

        assert(kt == kn + kb + ke);
        lemma_take_split(s, 1nat, kt + kr);
        assert(s.skip(1).skip(kr as int) =~= b1.1);
        lemma_take_split(s.skip(1), kr, kt);
        lemma_take_split(b1.1, kn, (kb + ke) as nat);
        lemma_take_split(b2.1, kb, ke);
        assert(nsld_enc()(b1.0, n as u64).len() == kn);
        assert(list_enc(n, bool_enc())(b2.0, bm).len() == kb);
        assert(s.take(k as int)
               =~= seq![true] + er(pos + 1, r) + nsld_enc()(b1.0, c as u64)
                   + list_enc(c, bool_enc())(b2.0, bm) + ea(bm)(b3.0, ev));
    }
}

} // verus!

verus! {

pub proof fn lemma_ext_format<R, E>(
    wr: Wf<R>, er: Enc<R>, dr: Dec<R>,
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
)
    requires
        is_format(wr, er, dr),
        c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
    ensures
        is_format(ext_wf(wr, c, wa, bmof), ext_enc(er, c, ea, bmof), ext_dec(dr, c, da, e0)),
{
    let w = ext_wf(wr, c, wa, bmof);
    let e = ext_enc(er, c, ea, bmof);
    let d = ext_dec(dr, c, da, e0);

    assert forall|pos: nat, p: (R, E), rest: Seq<bool>| w(p) implies
        #[trigger] d((pos, e(pos, p) + rest)) == Some::<((R, E), nat, Flg)>((p, e(pos, p).len(), Flg::SameVer))
    by {
        lemma_ext_surj(wr, er, dr, c, wa, ea, da, bmof, e0, pos, p, rest);
    }

    assert forall|b: In| (#[trigger] d(b)).is_some() implies {
        let a = d(b).unwrap().0;
        let k = d(b).unwrap().1;
        &&& w(a) && k <= b.1.len()
        &&& d(b).unwrap().2 is SameVer ==> b.1.take(k as int) == e(b.0, a)
    } by {
        lemma_ext_weak_inj(wr, er, dr, c, wa, ea, da, bmof, e0, b);
        if d(b).unwrap().2 is SameVer {
            lemma_ext_inj(wr, er, dr, c, wa, ea, da, bmof, e0, b);
        }
    }
}

} // verus!

verus! {

use crate::aper::cursor::*;

impl BitWriter {
    #[verifier::loop_isolation(false)]
    pub fn write_abitmap(&mut self, bm: &Vec<bool>) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written()
                =~= old(self).written() + ext_bm_enc(bm@.len())(old(self).pos as nat, bm@),
    {
        let ghost w0 = *self;
        let ghost p0 = self.pos as nat;
        let mut i: usize = 0;
        while i < bm.len()
            invariant
                self.wf(),
                self.buf@.len() == w0.buf@.len(),
                i <= bm@.len(),
                p0 == w0.pos, p0 == w0.written().len(),
                self.written() =~= w0.written() + list_enc_rec(p0, bm@.take(i as int), bool_enc()),
            decreases bm@.len() - i,
        {
            let ghost before = bm@.take(i as int);
            if !self.write_bool(bm[i]) { return false; }
            proof {
                lemma_list_enc_push(p0, before, bool_enc(), bm@[i as int]);
                assert(bm@.take((i + 1) as int) =~= before.push(bm@[i as int]));
            }
            i = i + 1;
        }
        assert(bm@.take(i as int) =~= bm@);
        true
    }
}

impl<'a> BitReader<'a> {
    /// Read the `n`-bit extension bitmap. Refines `ext_bm_dec(n)`.
    #[verifier::loop_isolation(false)]
    pub fn read_abitmap(&mut self, n: usize) -> (res: Option<Vec<bool>>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& ext_bm_dec(n as nat)(old(self).at())
                        == Some::<(Seq<bool>, nat, Flg)>(
                            (v@, (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& v@.len() == n
                },
                None => ext_bm_dec(n as nat)(old(self).at()).is_none(),
            },
    {
        let ghost r0 = *self;
        let ghost start = r0.at();
        let mut out: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        proof { lemma_list_loop_start(n as nat, bool_dec(), start); }
        while i < n
            invariant
                self.wf(),
                self.buf == r0.buf,
                r0.pos <= self.pos,
                out@.len() == i,
                i <= n,
                list_dec_rec(n as nat, bool_dec(), start)
                    == list_cont(out@, (self.pos - r0.pos) as nat, Flg::SameVer,
                                 list_dec_rec((n - i) as nat, bool_dec(), self.at())),
            decreases n - i,
        {
            let ghost bi = self.at();
            let ghost pi = self.pos;
            let b = match self.read_bool() {
                Some(b) => b,
                None => {
                    proof {
                        lemma_list_loop_fail(n as nat, bool_dec(), start, out@,
                                             (pi - r0.pos) as nat, Flg::SameVer,
                                             (n - i) as nat, bi);
                        lemma_list_dec_val(n as nat, bool_dec(), start);
                    }
                    return None;
                },
            };
            proof {
                lemma_rem_skip(self.buf@, pi as nat, (self.pos - pi) as nat);
                lemma_list_loop_step(n as nat, bool_dec(), start, out@, (pi - r0.pos) as nat,
                                     Flg::SameVer, (n - i) as nat, bi, b,
                                     (self.pos - pi) as nat, Flg::SameVer);
            }
            out.push(b);
            i = i + 1;
        }
        proof {
            lemma_list_loop_done(n as nat, bool_dec(), start, out@,
                                 (self.pos - r0.pos) as nat, Flg::SameVer, self.at());
            lemma_list_dec_val(n as nat, bool_dec(), start);
        }
        Some(out)
    }

    /// Step over the additions a newer peer sent that this schema has never
    /// heard of. Refines `skip_adds`.
    #[verifier::loop_isolation(false)]
    pub fn skip_adds_arun(&mut self, bm: &Vec<bool>, from: usize) -> (ok: bool)
        requires old(self).wf(), from <= bm@.len(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            ok ==> skip_adds(bm@.skip(from as int), old(self).at())
                == Some::<nat>((final(self).pos - old(self).pos) as nat),
            !ok ==> skip_adds(bm@.skip(from as int), old(self).at()) is None,
    {
        let ghost r0 = *self;
        let mut i: usize = from;
        while i < bm.len()
            invariant
                self.wf(),
                self.buf == r0.buf,
                r0.pos <= self.pos,
                from <= i <= bm@.len(),
                skip_adds(bm@.skip(from as int), r0.at())
                    == (match skip_adds(bm@.skip(i as int), self.at()) {
                        Some(k) => Some(((self.pos - r0.pos) + k) as nat),
                        None => None,
                    }),
            decreases bm@.len() - i,
        {
            let ghost tail = bm@.skip(i as int);
            let ghost pi = self.pos;
            assert(tail.len() > 0 && tail[0] == bm@[i as int]);
            assert(tail.skip(1) =~= bm@.skip((i + 1) as int));
            if bm[i] {
                match self.read_afrag() {
                    Some(_) => {
                        proof { lemma_rem_skip(self.buf@, pi as nat, (self.pos - pi) as nat); }
                    },
                    None => {
                        return false;
                    },
                }
            }
            i = i + 1;
        }
        assert(bm@.skip(i as int) =~= Seq::<bool>::empty());
        true
    }
}

} // verus!
