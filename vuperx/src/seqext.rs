//! Extensible SEQUENCE (X.691 19).
//!
//! This is the one combinator that cannot be built out of `pair`, `dep` and
//! `map`, and the reason is worth stating precisely. The encoder always writes
//! the count of extension additions *this schema* knows about; the decoder
//! branches on the count it *reads*. On two of its three branches the decoder
//! returns a value whose re-encoding differs from the bits it consumed. `dep`
//! cannot express that: `lemma_dep_format` demands `is_format` of the second
//! family for **every** value the first component can take, including counts
//! the encoder never writes, and surjection is false there. So this is one
//! hand-proved combinator, as it is in VUPER (`SeqExt.v` plus 1.4k lines of
//! `SeqExtProp.v`).
//!
//! # Shape
//!
//! ```text
//! enc(r, e) = if bmof(e) is all absent { [0] + enc_r(r) }
//!             else { [1] + enc_r(r) + nsld(c) + bitmap(c) + adds }
//! ```
//!
//! and the decoder reads the bit, the root, and then -- if the bit is set --
//! a normally small length determinant `n`, an `n`-bit bitmap, and the
//! additions, with three cases:
//!
//! | | | |
//! | --- | --- | --- |
//! | `n == c` | decode each addition per the bitmap | `SameVer` if every part was |
//! | `n < c`  | decode per `bm + zeros(c-n)`: additions we know of and the peer does not are absent | `DiffVer` |
//! | `n > c`  | decode per `bm.take(c)`, then step over additions `c..n-1` by their open-type lengths | `DiffVer` |
//!
//! # Why the flag has to be there
//!
//! The `n != c` branches are exactly why `is_format` conditions injection on
//! `SameVer`. A value decoded from a peer running a different version does not
//! re-encode to the bits it came from -- additions we skipped are gone, and
//! additions we padded with "absent" were never on the wire. Both branches
//! return `DiffVer`, which discharges injection immediately; it is the same
//! structure as VUPER's `seq_ext_inj_same`, which kills the `le` and `ge`
//! cases with `to_parse_le_Diff` and `to_parse_ge_Diff`.
//!
//! # The all-zero bitmap
//!
//! 19.8 NOTE: "*n* cannot be zero, as this procedure is only invoked if there
//! is at least one extension addition being encoded." The extension bit being
//! set therefore means at least one addition is present, and a decoder that
//! accepted an all-absent bitmap would accept two encodings of the same value
//! -- the short form and the long one -- breaking injectivity. So the bitmap
//! read off the wire is rejected when it is all zero.
//!
//! **This is a deliberate divergence from VUPER**, which checks
//! `check_all_none_dec` on the *decoded value* (`SeqExt.v`, `seq_ext_parse`).
//! In the `n > c` case that rejects a legal message: a newer peer that sets
//! only additions this schema has never heard of produces exactly that --
//! every addition we know about absent, several unknown ones present. Checking
//! the received bitmap instead is correct there, and identical when `n == c`,
//! which is the only case injectivity has to cover.
use vstd::prelude::*;
use crate::format::*;
use crate::term::*;
use crate::list::*;
use crate::lendet::*;
use crate::frag::*;
use crate::opentype::*;

verus! {

broadcast use {format_steps, crate::prim::map_steps, list_steps};

/// The bitmap of a value with no additions present.
pub open spec fn all_absent(bm: Seq<bool>) -> bool {
    bm =~= zeros(bm.len())
}

// ---------------------------------------------------------------- the family
//
// The additions are supplied as a *family* of formats indexed by the presence
// bitmap -- in practice an `opt(bm[i], open_type(F_i))` chain, which the
// compiler builds with the machinery that is already proved. Everything this
// combinator needs from that chain is collected here, and all four parts are
// structural for such a chain.

pub open spec fn ext_adds_ok<E>(
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
) -> bool {
    // 1. every bitmap of the right width indexes a format
    &&& forall|bm: Seq<bool>| bm.len() == c ==> is_format(#[trigger] wa(bm), ea(bm), da(bm))
    // 2. a well-formed value's own bitmap is the one that accepted it -- this
    //    is what gives `wa(bmof(e))(e)` back on the padded and truncated
    //    bitmaps of the two `DiffVer` branches
    &&& forall|bm: Seq<bool>, e: E| #![trigger wa(bm)(e)]
            bm.len() == c && wa(bm)(e) ==> bmof(e) == bm
    // 3. the all-absent bitmap admits exactly one value, the empty record
    &&& forall|e: E| #![trigger wa(zeros(c))(e)] wa(zeros(c))(e) ==> e == e0
    &&& wa(zeros(c))(e0)
}

// ------------------------------------------------------------------- the bits

/// The count `c` and the bitmap it announces: a normally small length
/// determinant (11.9.3.4), then exactly `c` bits (19.7 -- trailing absent
/// additions are **not** trimmed).
pub open spec fn ext_count_enc(c: nat) -> Seq<bool> {
    nsld_enc()(c as u64)
}

pub open spec fn ext_bm_enc(c: nat) -> Enc<Seq<bool>> {
    list_enc(c, bool_enc())
}

pub open spec fn ext_bm_dec(n: nat) -> Dec<Seq<bool>> {
    list_dec(n, bool_dec())
}

/// Step over the additions this schema has never heard of, one open type per
/// set bit, and report how many bits that took.
///
/// Not a format: its encoding is empty while it consumes bits, so it cannot
/// satisfy surjection. It lives inside the combinator and is only ever reached
/// on a `DiffVer` path, where nothing is claimed about re-encoding.
pub open spec fn skip_adds(bmtail: Seq<bool>, b: Seq<bool>) -> Option<nat>
    decreases bmtail.len(),
{
    if bmtail.len() == 0 {
        Some(0nat)
    } else if !bmtail[0] {
        skip_adds(bmtail.skip(1), b)
    } else {
        match frag_dec()(b) {
            Some((_, k, _)) => match skip_adds(bmtail.skip(1), b.skip(k as int)) {
                Some(k2) => Some((k + k2) as nat),
                None => None,
            },
            None => None,
        }
    }
}

/// Whatever `skip_adds` consumed was there to consume.
pub proof fn lemma_skip_adds_bound(bmtail: Seq<bool>, b: Seq<bool>)
    ensures skip_adds(bmtail, b) is Some ==> skip_adds(bmtail, b).unwrap() <= b.len(),
    decreases bmtail.len(),
{
    lemma_frag_format();
    if bmtail.len() == 0 {
    } else if !bmtail[0] {
        lemma_skip_adds_bound(bmtail.skip(1), b);
    } else if frag_dec()(b) is Some {
        let k = frag_dec()(b).unwrap().1;
        assert(k <= b.len());
        lemma_skip_adds_bound(bmtail.skip(1), b.skip(k as int));
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

pub open spec fn ext_enc<R, E>(
    er: Enc<R>,
    c: nat,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    bmof: spec_fn(E) -> Seq<bool>,
) -> Enc<(R, E)> {
    |p: (R, E)| {
        let bm = bmof(p.1);
        if all_absent(bm) {
            seq![false] + er(p.0)
        } else {
            seq![true] + er(p.0) + ext_count_enc(c) + ext_bm_enc(c)(bm) + ea(bm)(p.1)
        }
    }
}

/// The tail of the decode, from just past the root to the end: the count, the
/// bitmap, and the additions. Split out so the three branches read as three
/// branches rather than as one nest six deep.
pub open spec fn ext_tail_dec<E>(
    c: nat,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    b: Seq<bool>,
) -> Option<(E, nat, Flg)> {
    match nsld_dec()(b) {
        None => None,
        Some((n, kn, _)) => {
            let b2 = b.skip(kn as int);
            match ext_bm_dec(n as nat)(b2) {
                None => None,
                Some((bm, kb, _)) => {
                    // 19.8 NOTE: the extension bit being set means at least one
                    // addition is present, so an all-absent bitmap is not a
                    // legal encoding of anything.
                    if all_absent(bm) {
                        None
                    } else {
                        let b3 = b2.skip(kb as int);
                        if n as nat == c {
                            match da(bm)(b3) {
                                Some((e, ke, fe)) => Some((e, (kn + kb + ke) as nat, fe)),
                                None => None,
                            }
                        } else if (n as nat) < c {
                            // additions we know of that the peer does not: absent
                            let bmp = bm + zeros((c - n as nat) as nat);
                            match da(bmp)(b3) {
                                Some((e, ke, _)) =>
                                    Some((e, (kn + kb + ke) as nat, Flg::DiffVer)),
                                None => None,
                            }
                        } else {
                            // additions the peer has that we do not: stepped over
                            let bmt = bm.take(c as int);
                            match da(bmt)(b3) {
                                Some((e, ke, _)) => match skip_adds(bm.skip(c as int),
                                                                   b3.skip(ke as int)) {
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
    |b: Seq<bool>| {
        if b.len() == 0 {
            None
        } else {
            match dr(b.skip(1)) {
                None => None,
                Some((r, kr, fr)) => {
                    if !b[0] {
                        Some(((r, e0), (1 + kr) as nat, fr))
                    } else {
                        match ext_tail_dec(c, da, b.skip(1 + kr as int)) {
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
//
// Only two of the decoder's four paths are reachable from a well-formed value:
// "no additions present" and `n == c`. The `n < c` and `n > c` branches exist
// for messages from peers on other versions, and cost nothing here.

pub proof fn lemma_ext_surj<R, E>(
    wr: Wf<R>, er: Enc<R>, dr: Dec<R>,
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
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
            let e = ext_enc(er, c, ea, bmof)(p);
            ext_dec(dr, c, da, e0)(e + rest)
                == Some::<((R, E), nat, Flg)>((p, e.len(), Flg::SameVer))
        }),
{
    let (r, ev) = p;
    let bm = bmof(ev);
    let enc = ext_enc(er, c, ea, bmof)(p);
    let b = enc + rest;

    if all_absent(bm) {
        assert(bm =~= zeros(c));
        assert(wa(zeros(c))(ev));
        assert(ev == e0);
        assert(enc =~= seq![false] + er(r));
        assert(b =~= seq![false] + (er(r) + rest));
        assert(b.len() >= 1);
        assert(b[0] == false);
        lemma_take_add(seq![false], er(r) + rest);
        assert(b.skip(1) =~= er(r) + rest);
        assert(dr(b.skip(1)) == Some::<(R, nat, Flg)>((r, er(r).len(), Flg::SameVer)));
        assert(enc.len() == 1 + er(r).len());
    } else {
        // With no extension additions in this version the bitmap is empty, so
        // it is always all-absent and this branch is unreachable -- which is
        // what lets `c == 0` share the combinator. ETSI ITS marks six types
        // extensible without adding anything yet, and 3GPP does it constantly.
        assert(c > 0) by { if c == 0 { assert(bm =~= zeros(0)); } }
        lemma_nsld_format();
        lemma_nsld_wf_iff(c as u64);
        lemma_bool_format();
        lemma_list_format(c, bool_wf(), bool_enc(), bool_dec());

        let cnt = ext_count_enc(c);
        let bmb = ext_bm_enc(c)(bm);
        let adds = ea(bm)(ev);
        assert(enc =~= seq![true] + er(r) + cnt + bmb + adds);

        // peel the leading bit
        assert(b =~= seq![true] + (er(r) + (cnt + (bmb + (adds + rest)))));
        assert(b.len() >= 1);
        assert(b[0] == true);
        lemma_take_add(seq![true], er(r) + (cnt + (bmb + (adds + rest))));
        assert(b.skip(1) =~= er(r) + (cnt + (bmb + (adds + rest))));

        // the root
        let kr = er(r).len();
        assert(dr(b.skip(1)) == Some::<(R, nat, Flg)>((r, kr, Flg::SameVer)));
        lemma_take_add(er(r), cnt + (bmb + (adds + rest)));
        assert(b.skip(1).skip(kr as int) =~= cnt + (bmb + (adds + rest)));
        assert(b.skip(1 + kr as int) =~= b.skip(1).skip(kr as int));

        // the count
        let b1 = b.skip(1 + kr as int);
        assert(nsld_wf()(c as u64));
        assert(nsld_dec()(b1) == Some::<(u64, nat, Flg)>((c as u64, cnt.len(), Flg::SameVer)));
        lemma_take_add(cnt, bmb + (adds + rest));
        assert(b1.skip(cnt.len() as int) =~= bmb + (adds + rest));

        // the bitmap
        let b2 = b1.skip(cnt.len() as int);
        assert forall|i: int| 0 <= i < bm.len() implies bool_wf()(#[trigger] bm[i]) by {
            lemma_bool_wf_all(bm[i]);
        }
        assert(list_wf(c, bool_wf())(bm));
        assert(ext_bm_dec(c)(b2) == Some::<(Seq<bool>, nat, Flg)>((bm, bmb.len(), Flg::SameVer)));
        lemma_take_add(bmb, adds + rest);
        assert(b2.skip(bmb.len() as int) =~= adds + rest);

        // the additions
        let b3 = b2.skip(bmb.len() as int);
        assert(is_format(wa(bm), ea(bm), da(bm)));
        assert(da(bm)(b3) == Some::<(E, nat, Flg)>((ev, adds.len(), Flg::SameVer)));

        assert(ext_tail_dec(c, da, b1)
               == Some::<(E, nat, Flg)>((ev, (cnt.len() + bmb.len() + adds.len()) as nat,
                                         Flg::SameVer)));
        assert(enc.len() == 1 + kr + cnt.len() + bmb.len() + adds.len());
    }
}

} // verus!

verus! {

// ----------------------------------------------------------- weak injection
//
// What survives on every path, including the two that report `DiffVer`: the
// value is well formed, so it can be re-encoded, and the bits consumed were
// there to consume. Hypothesis 2 is what carries it -- on the `n < c` and
// `n > c` branches the bitmap that accepted the value is a padded or truncated
// one, and hypothesis 2 says that is exactly the value's own bitmap.

pub proof fn lemma_ext_tail_weak<E>(
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
    b: Seq<bool>,
)
    requires
        c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        ext_tail_dec(c, da, b) is Some,
    ensures
        bmof(ext_tail_dec(c, da, b).unwrap().0).len() == c,
        wa(bmof(ext_tail_dec(c, da, b).unwrap().0))(ext_tail_dec(c, da, b).unwrap().0),
        ext_tail_dec(c, da, b).unwrap().1 <= b.len(),
{
    lemma_nsld_format();
    let n = nsld_dec()(b).unwrap().0 as nat;
    let kn = nsld_dec()(b).unwrap().1;
    let b2 = b.skip(kn as int);

    lemma_bool_format();
    lemma_list_format(n, bool_wf(), bool_enc(), bool_dec());
    let bm = ext_bm_dec(n)(b2).unwrap().0;
    let kb = ext_bm_dec(n)(b2).unwrap().1;
    let b3 = b2.skip(kb as int);
    assert(list_wf(n, bool_wf())(bm));
    assert(bm.len() == n);
    assert(kn <= b.len());
    assert(kb <= b2.len());

    // the bitmap the additions are actually decoded against, per branch
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
    assert(ke <= b3.len());
    if n > c {
        lemma_skip_adds_bound(bm.skip(c as int), b3.skip(ke as int));
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
    b: Seq<bool>,
)
    requires
        is_format(wr, er, dr),
        c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        ext_dec(dr, c, da, e0)(b) is Some,
    ensures
        ext_wf(wr, c, wa, bmof)(ext_dec(dr, c, da, e0)(b).unwrap().0),
        ext_dec(dr, c, da, e0)(b).unwrap().1 <= b.len(),
{
    let r = dr(b.skip(1)).unwrap().0;
    let kr = dr(b.skip(1)).unwrap().1;
    assert(wr(r));
    assert(kr <= b.skip(1).len());
    if !b[0] {
        // the empty record is well formed, and hypothesis 2 says its bitmap is
        // the all-absent one
        assert(wa(zeros(c))(e0));
        assert(bmof(e0) == zeros(c));
    } else {
        lemma_ext_tail_weak(c, wa, ea, da, bmof, e0, b.skip(1 + kr as int));
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------- injection
//
// Conditioned on `SameVer`, and that is what makes it provable at all: the
// `n < c` and `n > c` branches hand back `DiffVer`, so they are discharged
// before any re-encoding has to be considered. Only two paths remain, and on
// both the bits are pinned component by component. This is the same structure
// as VUPER's `seq_ext_inj_same`, which kills its `le` and `ge` cases with
// `to_parse_le_Diff` and `to_parse_ge_Diff`.

pub proof fn lemma_ext_inj<R, E>(
    wr: Wf<R>, er: Enc<R>, dr: Dec<R>,
    c: nat,
    wa: spec_fn(Seq<bool>) -> Wf<E>,
    ea: spec_fn(Seq<bool>) -> Enc<E>,
    da: spec_fn(Seq<bool>) -> Dec<E>,
    bmof: spec_fn(E) -> Seq<bool>,
    e0: E,
    b: Seq<bool>,
)
    requires
        is_format(wr, er, dr),
        c < 16384,
        ext_adds_ok(c, wa, ea, da, bmof, e0),
        ext_dec(dr, c, da, e0)(b) is Some,
        ext_dec(dr, c, da, e0)(b).unwrap().2 is SameVer,
    ensures
        b.take(ext_dec(dr, c, da, e0)(b).unwrap().1 as int)
            == ext_enc(er, c, ea, bmof)(ext_dec(dr, c, da, e0)(b).unwrap().0),
{
    lemma_ext_weak_inj(wr, er, dr, c, wa, ea, da, bmof, e0, b);
    let k = ext_dec(dr, c, da, e0)(b).unwrap().1;
    let r = dr(b.skip(1)).unwrap().0;
    let kr = dr(b.skip(1)).unwrap().1;
    assert(b.take(1) =~= seq![b[0]]);

    if !b[0] {
        assert(b.skip(1).take(kr as int) == er(r));
        lemma_take_split(b, 1nat, kr);
        assert(b.take((1 + kr) as int) =~= seq![false] + er(r));
        // the empty record's bitmap is all-absent, so the encoder takes the
        // short branch -- which is the branch these bits came from
        assert(wa(zeros(c))(e0));
        assert(bmof(e0) == zeros(c));
        assert(zeros(c).len() == c);
        assert(all_absent(bmof(e0)));
    } else {
        let b1 = b.skip(1 + kr as int);
        lemma_ext_tail_weak(c, wa, ea, da, bmof, e0, b1);
        let kt = ext_tail_dec(c, da, b1).unwrap().1;
        let ev = ext_tail_dec(c, da, b1).unwrap().0;

        lemma_nsld_format();
        lemma_nsld_dec_same(b1);
        let n = nsld_dec()(b1).unwrap().0 as nat;
        let kn = nsld_dec()(b1).unwrap().1;
        let b2 = b1.skip(kn as int);
        assert(b1.take(kn as int) == nsld_enc()(n as u64));

        lemma_bool_format();
        lemma_list_format(n, bool_wf(), bool_enc(), bool_dec());
        assert forall|s: Seq<bool>| (#[trigger] bool_dec()(s)) is Some implies
            bool_dec()(s).unwrap().2 is SameVer by { lemma_bool_dec_same(s); }
        lemma_list_dec_same(n, bool_dec(), b2);
        let bm = ext_bm_dec(n)(b2).unwrap().0;
        let kb = ext_bm_dec(n)(b2).unwrap().1;
        let b3 = b2.skip(kb as int);
        assert(ext_bm_dec(n)(b2).unwrap().2 is SameVer);
        assert(b2.take(kb as int) == list_enc(n, bool_enc())(bm));

        // `SameVer` is only reachable on the `n == c` branch: the other two
        // hand back `DiffVer` unconditionally
        assert(n == c);
        assert(is_format(wa(bm), ea(bm), da(bm)));
        let ke = da(bm)(b3).unwrap().1;
        assert(b3.take(ke as int) == ea(bm)(ev));
        assert(bmof(ev) == bm);
        assert(!all_absent(bm));

        // reassemble: one `take` split per component
        assert(kt == kn + kb + ke);
        lemma_take_split(b, 1nat, kt + kr);
        assert(b.skip(1).skip(kr as int) =~= b1);
        lemma_take_split(b.skip(1), kr, kt);
        lemma_take_split(b1, kn, (kb + ke) as nat);
        lemma_take_split(b2, kb, ke);
        assert(b.take(k as int)
               =~= seq![true] + er(r) + nsld_enc()(c as u64) + list_enc(c, bool_enc())(bm)
                   + ea(bm)(ev));
    }
}

} // verus!

verus! {

/// The extensible SEQUENCE is a format.
///
/// Three hypotheses, all structural for the `opt(bm[i], open_type(F_i))` chain
/// the compiler builds, and one arithmetic side condition on `c` -- 19.7's
/// count goes through a normally small length determinant, which carries
/// 1..16383.
///
/// Note what is *not* a hypothesis: any bound on how large an addition
/// encodes. VUPER needs one, because its open type's length determinant stops
/// at 16K. `frag` fragments, so an addition of any size works.
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

    assert forall|p: (R, E), rest: Seq<bool>| w(p) implies
        #[trigger] d(e(p) + rest) == Some::<((R, E), nat, Flg)>((p, e(p).len(), Flg::SameVer))
    by {
        lemma_ext_surj(wr, er, dr, c, wa, ea, da, bmof, e0, p, rest);
    }

    assert forall|b: Seq<bool>| (#[trigger] d(b)).is_some() implies {
        let a = d(b).unwrap().0;
        let k = d(b).unwrap().1;
        &&& w(a) && k <= b.len()
        &&& d(b).unwrap().2 is SameVer ==> b.take(k as int) == e(a)
    } by {
        lemma_ext_weak_inj(wr, er, dr, c, wa, ea, da, bmof, e0, b);
        if d(b).unwrap().2 is SameVer {
            lemma_ext_inj(wr, er, dr, c, wa, ea, da, bmof, e0, b);
        }
    }
}

} // verus!

verus! {

use crate::cursor::*;

// ------------------------------------------------------- the bitmap, runnable
//
// The bitmap is `c` plain bits, so it is the fixed-length list format over
// `bool`. Both directions live here rather than in generated code: nothing
// about them depends on the type, only on the count.

impl BitWriter {
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn write_bitmap(&mut self, bm: &Vec<bool>) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written()
                =~= old(self).written() + ext_bm_enc(bm@.len())(bm@),
    {
        let ghost w0 = *self;
        let mut i: usize = 0;
        while i < bm.len()
            invariant
                self.wf(),
                self.buf@.len() == w0.buf@.len(),
                i <= bm@.len(),
                self.written() =~= w0.written() + list_enc_rec(bm@.take(i as int), bool_enc()),
            decreases bm@.len() - i,
        {
            let ghost before = bm@.take(i as int);
            if !self.write_bool(bm[i]) { return false; }
            proof {
                lemma_list_enc_push(before, bool_enc(), bm@[i as int]);
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
    #[inline]
    pub fn read_bitmap(&mut self, n: usize) -> (res: Option<Vec<bool>>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& ext_bm_dec(n as nat)(old(self).rem())
                        == Some::<(Seq<bool>, nat, Flg)>(
                            (v@, (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& v@.len() == n
                },
                None => ext_bm_dec(n as nat)(old(self).rem()).is_none(),
            },
    {
        let ghost r0 = *self;
        let ghost start = r0.rem();
        let mut out: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        proof { lemma_list_loop_start(n as nat, bool_dec(), start); }
        while i < n
            invariant
                self.wf(),
                self.buf == r0.buf,
                r0.pos <= self.pos,
                self.rem() == start.skip((self.pos - r0.pos) as int),
                out@.len() == i,
                i <= n,
                list_dec_rec(n as nat, bool_dec(), start)
                    == list_cont(out@, (self.pos - r0.pos) as nat, Flg::SameVer,
                                 list_dec_rec((n - i) as nat, bool_dec(), self.rem())),
            decreases n - i,
        {
            let ghost bi = self.rem();
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
                                 (self.pos - r0.pos) as nat, Flg::SameVer, self.rem());
            lemma_list_dec_val(n as nat, bool_dec(), start);
        }
        Some(out)
    }

    /// Step over the additions a newer peer sent that this schema has never
    /// heard of: one open type per set bit of `bmtail`. Refines `skip_adds`.
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn skip_adds_run(&mut self, bm: &Vec<bool>, from: usize) -> (ok: bool)
        requires old(self).wf(), from <= bm@.len(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            ok ==> skip_adds(bm@.skip(from as int), old(self).rem())
                == Some::<nat>((final(self).pos - old(self).pos) as nat),
            !ok ==> skip_adds(bm@.skip(from as int), old(self).rem()) is None,
    {
        let ghost r0 = *self;
        let mut i: usize = from;
        while i < bm.len()
            invariant
                self.wf(),
                self.buf == r0.buf,
                r0.pos <= self.pos,
                from <= i <= bm@.len(),
                self.rem() == r0.rem().skip((self.pos - r0.pos) as int),
                skip_adds(bm@.skip(from as int), r0.rem())
                    == (match skip_adds(bm@.skip(i as int), self.rem()) {
                        Some(k) => Some(((self.pos - r0.pos) + k) as nat),
                        None => None,
                    }),
            decreases bm@.len() - i,
        {
            let ghost tail = bm@.skip(i as int);
            let ghost cur = self.rem();
            let ghost pi = self.pos;
            assert(tail.len() > 0 && tail[0] == bm@[i as int]);
            assert(tail.skip(1) =~= bm@.skip((i + 1) as int));
            if bm[i] {
                match self.read_frag() {
                    Some(_) => {
                        proof { lemma_rem_skip(self.buf@, pi as nat, (self.pos - pi) as nat); }
                    },
                    None => {
                        reveal(frag_dec);
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

verus! {

/// Is every addition absent? 19.8's note says the extension bit is only set
/// when at least one is present, so an all-zero bitmap is not a legal
/// encoding of anything and the decoder rejects it.
#[verifier::loop_isolation(false)]
#[inline]
pub fn all_absent_run(bm: &Vec<bool>) -> (res: bool)
    ensures res == all_absent(bm@),
{
    let mut i: usize = 0;
    while i < bm.len()
        invariant i <= bm@.len(), forall|j: int| 0 <= j < i ==> !bm@[j],
        decreases bm@.len() - i,
    {
        if bm[i] {
            assert(zeros(bm@.len())[i as int] == false);
            return false;
        }
        i = i + 1;
    }
    assert(bm@ =~= zeros(bm@.len()));
    true
}

/// The bitmap this schema decodes against, from the one that arrived.
///
/// Three cases, and they are the decoder's three branches: the same width,
/// shorter (additions we know of that the peer does not, so absent), or longer
/// (additions the peer has that we do not, which are stepped over separately).
#[verifier::loop_isolation(false)]
#[inline]
pub fn bm_fit(bm: &Vec<bool>, c: usize) -> (out: Vec<bool>)
    ensures
        out@.len() == c,
        bm@.len() == c ==> out@ =~= bm@,
        bm@.len() < c ==> out@ =~= bm@ + zeros((c - bm@.len()) as nat),
        bm@.len() > c ==> out@ =~= bm@.take(c as int),
{
    let mut out: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < c
        invariant
            i <= c,
            out@.len() == i,
            forall|j: int| #![trigger out@[j]]
                0 <= j < i ==> out@[j] == (if j < bm@.len() { bm@[j] } else { false }),
        decreases c - i,
    {
        if i < bm.len() {
            out.push(bm[i]);
        } else {
            out.push(false);
        }
        i = i + 1;
    }
    out
}

} // verus!
