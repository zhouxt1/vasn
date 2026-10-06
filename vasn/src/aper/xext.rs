//! The extension bit, and the numbers and lengths that come with extensions,
//! in the ALIGNED variant.
//!
//! * `xext`: a bit, then the root's encoding or the extension's (13.1, 14.3,
//!   23.7, 23.8), as in `uper::fraglist`, with the position passed along.
//! * `gld`: the unconstrained length determinant (11.9.3.6, 11.9.3.7), an
//!   octet-aligned field in both its forms: UPER's, aligned.
//! * `nsld`: the normally small length (11.9.3.4) that counts extension
//!   additions. `0` and 6 bits up to 64, as in UPER; above, `1` and `gld`,
//!   which is octet-aligned here.
//! * `nsn`: the normally small non-negative whole number (11.6) that indexes
//!   an extension addition. `0` and 6 bits up to 63; above, `1` and a
//!   semi-constrained whole number, octet-aligned.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::aper::format::*;
use crate::aper::term::*;
use crate::aper::list::*;
use crate::aper::intx::*;
use crate::aper::cursor::*;
use crate::uper::lendet as ulen;

verus! {

broadcast use {format_steps, map_steps};

// ------------------------------------------------------------------ xext

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

/// What a value's well-formedness says, and what its encoding is: the bit,
/// then its side's encoding, starting one bit on.
pub proof fn lemma_xext_enc<A>(re: Enc<A>, ee: Enc<A>, rw: Wf<A>, ew: Wf<A>, inr: spec_fn(A) -> bool,
                               pos: nat, a: A)
    requires xext_wf(rw, ew, inr)(a),
    ensures
        xext_enc(re, ee, inr)(pos, a)
            == bool_enc()(pos, !inr(a)) + (if inr(a) { re(pos + 1, a) } else { ee(pos + 1, a) }),
        if inr(a) { rw(a) } else { ew(a) },
{
    lemma_map_wf_val(dep_wf(bool_wf(), xext_alt_wf(rw, ew)), xext_to(), xext_from(inr), a);
    lemma_dep_wf_val(bool_wf(), xext_alt_wf(rw, ew), !inr(a), a);
    lemma_map_enc_val(dep_enc(bool_enc(), xext_alt_enc(re, ee)), xext_from(inr), pos, a);
    lemma_dep_enc_val(bool_enc(), xext_alt_enc(re, ee), pos, !inr(a), a);
    lemma_bool_enc_len(pos, !inr(a));
}

// ------------------------------------------- the unconstrained length, aligned

pub open spec fn gld_wf() -> Wf<u64> { ulen::gld_wf() }
pub open spec fn gld_enc() -> Enc<u64> { aligned_enc(lift_enc(ulen::gld_enc())) }
pub open spec fn gld_dec() -> Dec<u64> { aligned_dec(lift_dec(ulen::gld_dec())) }

pub proof fn lemma_gld_format()
    ensures is_format(gld_wf(), gld_enc(), gld_dec()),
{
    ulen::lemma_gld_format();
    lemma_lift_format(ulen::gld_wf(), ulen::gld_enc(), ulen::gld_dec());
    lemma_aligned_format(ulen::gld_wf(), lift_enc(ulen::gld_enc()), lift_dec(ulen::gld_dec()));
}

pub proof fn lemma_gld_wf_iff(n: u64)
    ensures gld_wf()(n) <==> n < 16384,
{
    ulen::lemma_gld_wf_iff(n);
}

// ------------------------------------------ the normally small length, 11.9.3.4

pub open spec fn nsld_big() -> spec_fn(u64) -> bool { |v: u64| 65 <= v < 16384 }

pub open spec fn nsld_part_wf() -> spec_fn(bool) -> Wf<u64> {
    |b: bool| if b { restrict_wf(gld_wf(), nsld_big()) } else { ulen_wf(1, 64, 6) }
}
pub open spec fn nsld_part_enc() -> spec_fn(bool) -> Enc<u64> {
    |b: bool| if b { gld_enc() } else { ulen_enc(1, 64, 6) }
}
pub open spec fn nsld_part_dec() -> spec_fn(bool) -> Dec<u64> {
    |b: bool| if b { restrict_dec(gld_dec(), nsld_big()) } else { ulen_dec(1, 64, 6) }
}

pub open spec fn nsld_to() -> spec_fn((bool, u64)) -> u64 { |p: (bool, u64)| p.1 }
pub open spec fn nsld_from() -> spec_fn(u64) -> (bool, u64) { |n: u64| (n > 64, n) }

pub open spec fn nsld_full_wf() -> Wf<(bool, u64)> { dep_wf(bool_wf(), nsld_part_wf()) }
pub open spec fn nsld_full_enc() -> Enc<(bool, u64)> { dep_enc(bool_enc(), nsld_part_enc()) }
pub open spec fn nsld_full_dec() -> Dec<(bool, u64)> { dep_dec(bool_dec(), nsld_part_dec()) }

pub open spec fn nsld_wf() -> Wf<u64> { map_wf(nsld_full_wf(), nsld_to(), nsld_from()) }
pub open spec fn nsld_enc() -> Enc<u64> { map_enc(nsld_full_enc(), nsld_from()) }
pub open spec fn nsld_dec() -> Dec<u64> { map_dec(nsld_full_dec(), nsld_to()) }

pub proof fn lemma_nsld_format()
    ensures is_format(nsld_wf(), nsld_enc(), nsld_dec()),
{
    lemma_bool_format();
    ulen::lemma_len_p2();
    crate::bits::prim_read::lemma_p2_56();
    assert forall|b: bool| bool_wf()(b) implies
        is_format(#[trigger] nsld_part_wf()(b), nsld_part_enc()(b), nsld_part_dec()(b))
    by {
        if b {
            lemma_gld_format();
            lemma_restrict_format(gld_wf(), gld_enc(), gld_dec(), nsld_big());
        } else {
            crate::uper::list::lemma_ulen_format(1, 64, 6);
            lemma_lift_format(crate::uper::list::ulen_wf(1, 64, 6), crate::uper::list::ulen_enc(1, 64, 6),
                              crate::uper::list::ulen_dec(1, 64, 6));
        }
    }
    lemma_dep_format(bool_wf(), bool_enc(), bool_dec(), nsld_part_wf(), nsld_part_enc(), nsld_part_dec());
    assert forall|p: (bool, u64)| nsld_full_wf()(p) implies #[trigger] nsld_from()(nsld_to()(p)) == p by {
        lemma_dep_wf_val(bool_wf(), nsld_part_wf(), p.0, p.1);
        if p.0 {
            lemma_restrict_wf_val(gld_wf(), nsld_big(), p.1);
        } else {
            crate::uper::list::lemma_ulen_wf_bound(1, 64, 6, p.1);
        }
    }
    lemma_map_format(nsld_full_wf(), nsld_full_enc(), nsld_full_dec(), nsld_to(), nsld_from());
}

pub proof fn lemma_nsld_dec_same(b: In)
    ensures nsld_dec()(b) is Some ==> nsld_dec()(b).unwrap().2 is SameVer,
{
    reveal(map_dec); reveal(dep_dec); reveal(restrict_dec); reveal(lift_dec); reveal(pair_dec);
    reveal(crate::uper::prim::map_dec); reveal(crate::uper::format::restrict_dec);
    if nsld_full_dec()(b) is Some {
        let sel = bool_dec()(b).unwrap().0;
        let b1 = adv(b, bool_dec()(b).unwrap().1);
        assert(bool_dec()(b).unwrap().2 is SameVer);
        if sel {
            lemma_aligned_dec_val(lift_dec(ulen::gld_dec()), b1);
            if gld_dec()(b1) is Some {
                ulen::lemma_gld_dec_same(adv(b1, pad(b1.0)).1);
            }
        }
    }
}

/// The extension-addition count is at least one and below 16K.
pub proof fn lemma_nsld_wf_iff(n: u64)
    ensures nsld_wf()(n) <==> 1 <= n < 16384,
{
    ulen::lemma_nsld_wf_iff(n);
    lemma_bool_wf_all(n > 64);
    lemma_map_wf_val(nsld_full_wf(), nsld_to(), nsld_from(), n);
    lemma_dep_wf_val(bool_wf(), nsld_part_wf(), n > 64, n);
    lemma_restrict_wf_val(gld_wf(), nsld_big(), n);
    lemma_gld_wf_iff(n);
    ulen::lemma_len_p2();
    crate::bits::prim_read::lemma_p2_56();
    if !(n > 64) {
        crate::uper::list::lemma_ulen_wf_iff(1, 64, 6, n);
    }
}

// ------------------------------------------- the normally small number, 11.6

pub open spec fn nsn_small() -> spec_fn(u64) -> bool { |n: u64| n <= 63 }
pub open spec fn nsn_big() -> spec_fn(u64) -> bool { |n: u64| 64 <= n }

#[verifier::opaque]
pub open spec fn nsn_wf() -> Wf<u64> { xext_wf(uint_wf(6), restrict_wf(usemi_wf(), nsn_big()), nsn_small()) }
#[verifier::opaque]
pub open spec fn nsn_enc() -> Enc<u64> { xext_enc(uint_enc(6), usemi_enc(), nsn_small()) }
#[verifier::opaque]
pub open spec fn nsn_dec() -> Dec<u64> { xext_dec(uint_dec(6), restrict_dec(usemi_dec(), nsn_big())) }

pub proof fn lemma_nsn_format()
    ensures
        is_format(nsn_wf(), nsn_enc(), nsn_dec()),
        forall|n: u64| #[trigger] nsn_wf()(n),
{
    reveal(nsn_wf); reveal(nsn_enc); reveal(nsn_dec);
    assert(p2(6) == 64) by { reveal_with_fuel(p2, 7); }
    lemma_uint_format(6);
    lemma_usemi_format();
    lemma_restrict_format(usemi_wf(), usemi_enc(), usemi_dec(), nsn_big());
    assert forall|n: u64| #[trigger] restrict_wf(usemi_wf(), nsn_big())(n) implies !nsn_small()(n) by {
        lemma_restrict_wf_val(usemi_wf(), nsn_big(), n);
    }
    lemma_xext_format(uint_wf(6), uint_enc(6), uint_dec(6), restrict_wf(usemi_wf(), nsn_big()),
                      usemi_enc(), restrict_dec(usemi_dec(), nsn_big()), nsn_small());
    assert forall|n: u64| #[trigger] nsn_wf()(n) by {
        lemma_bool_wf_all(!nsn_small()(n));
        lemma_map_wf_val(dep_wf(bool_wf(), xext_alt_wf(uint_wf(6), restrict_wf(usemi_wf(), nsn_big()))),
                         xext_to(), xext_from(nsn_small()), n);
        lemma_dep_wf_val(bool_wf(), xext_alt_wf(uint_wf(6), restrict_wf(usemi_wf(), nsn_big())), !nsn_small()(n), n);
        lemma_restrict_wf_val(usemi_wf(), nsn_big(), n);
        lemma_aligned_wf_val(crate::uper::intx::usemi_wf(), n);
    }
}

} // verus!

verus! {

impl<'a> BitReader<'a> {
    /// Refines `gld_dec()`.
    pub fn read_agld(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => gld_dec()(old(self).at())
                    == Some::<(u64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => gld_dec()(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = lift_dec(ulen::gld_dec());
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_dec_val(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_dec_val(d, i);
        }
        self.read_gld()
    }

    /// Refines `nsld_dec()`: the count of extension additions.
    pub fn read_ansld(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& nsld_dec()(old(self).at()) == Some::<(u64, nat, Flg)>(
                            (v, (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& 1 <= v < 16384
                },
                None => nsld_dec()(old(self).at()).is_none(),
            },
    {
        proof { ulen::lemma_len_p2(); crate::bits::prim_read::lemma_p2_56(); }
        let ghost start = old(self).at();
        let ghost p0 = self.pos;
        let big = match self.read_bool() {
            Some(v) => v,
            None => {
                proof {
                    lemma_dep_dec_none_fst(bool_dec(), nsld_part_dec(), start);
                    lemma_map_dec_none(nsld_full_dec(), nsld_to(), start);
                }
                return None;
            }
        };
        proof { lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat); }
        let ghost kb = (self.pos - p0) as nat;
        let ghost mid = adv(start, kb);
        let ghost p1 = self.pos;
        let got: Option<u64> = if big {
            match self.read_agld() {
                Some(v) => if v >= 65 {
                    proof { lemma_gld_format(); lemma_gld_wf_iff(v); }
                    proof { lemma_restrict_dec_some(gld_dec(), nsld_big(), mid, v,
                                                    (self.pos - p1) as nat, Flg::SameVer); }
                    Some(v)
                } else {
                    proof { lemma_restrict_dec_none(gld_dec(), nsld_big(), mid); }
                    None
                },
                None => {
                    proof { lemma_restrict_dec_none(gld_dec(), nsld_big(), mid); }
                    None
                }
            }
        } else {
            self.read_ulen(1, 64, 6)
        };
        match got {
            Some(v) => {
                proof {
                    lemma_dep_dec_some(bool_dec(), nsld_part_dec(), start, big, kb, Flg::SameVer,
                                       v, (self.pos - p1) as nat, Flg::SameVer);
                    lemma_map_dec_some(nsld_full_dec(), nsld_to(), start, (big, v),
                                       (self.pos - p0) as nat, Flg::SameVer);
                    lemma_nsld_format();
                    lemma_nsld_wf_iff(v);
                }
                Some(v)
            }
            None => {
                proof {
                    lemma_dep_dec_none_snd(bool_dec(), nsld_part_dec(), start, big, kb, Flg::SameVer);
                    lemma_map_dec_none(nsld_full_dec(), nsld_to(), start);
                }
                None
            }
        }
    }

    /// Refines `nsn_dec()`: a normally small non-negative whole number (11.6).
    pub fn read_ansn(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(n) => nsn_dec()(old(self).at())
                    == Some::<(u64, nat, Flg)>((n, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => nsn_dec()(old(self).at()) is None,
            },
    {
        proof { assert(p2(6) == 64) by { reveal_with_fuel(p2, 7); } reveal(nsn_dec); }
        let ghost start = self.at();
        let ghost p0 = self.pos;
        let ghost d2 = xext_alt_dec(uint_dec(6), restrict_dec(usemi_dec(), nsn_big()));
        let ghost full = dep_dec(bool_dec(), d2);
        let long = match self.read_bool() {
            Some(b) => b,
            None => {
                proof {
                    lemma_dep_dec_none_fst(bool_dec(), d2, start);
                    lemma_map_dec_none(full, xext_to::<u64>(), start);
                }
                return None;
            }
        };
        proof { lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat); }
        let ghost kb = (self.pos - p0) as nat;
        let ghost mid = adv(start, kb);
        let ghost p1 = self.pos;
        let got: Option<u64> = if !long {
            self.read_uint(6)
        } else {
            match self.read_ausemi() {
                Some(n) => if n >= 64 {
                    proof { lemma_restrict_dec_some(usemi_dec(), nsn_big(), mid, n, (self.pos - p1) as nat, Flg::SameVer); }
                    Some(n)
                } else {
                    proof { lemma_restrict_dec_none(usemi_dec(), nsn_big(), mid); }
                    { self.fail("a normally small number below 64 in the long form (X.691 11.6.1)"); None }
                },
                None => {
                    proof { lemma_restrict_dec_none(usemi_dec(), nsn_big(), mid); }
                    None
                }
            }
        };
        match got {
            Some(n) => {
                proof {
                    lemma_dep_dec_some(bool_dec(), d2, start, long, kb, Flg::SameVer, n, (self.pos - p1) as nat, Flg::SameVer);
                    lemma_map_dec_some(full, xext_to::<u64>(), start, (long, n), (self.pos - p0) as nat, Flg::SameVer);
                }
                Some(n)
            }
            None => {
                proof {
                    lemma_dep_dec_none_snd(bool_dec(), d2, start, long, kb, Flg::SameVer);
                    lemma_map_dec_none(full, xext_to::<u64>(), start);
                }
                None
            }
        }
    }
}

impl BitWriter {
    /// Refines `gld_enc()`.
    pub fn write_agld(&mut self, n: u64) -> (ok: bool)
        requires old(self).wf(), n < 16384,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + gld_enc()(old(self).pos as nat, n),
    {
        proof { lemma_aligned_enc_val(lift_enc(ulen::gld_enc()), old(self).pos as nat, n); }
        if !self.write_align() { return false; }
        self.write_gld(n)
    }

    /// Refines `nsld_enc()`.
    pub fn write_ansld(&mut self, n: u64) -> (ok: bool)
        requires old(self).wf(), 1 <= n < 16384,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + nsld_enc()(old(self).pos as nat, n),
    {
        let ghost p0 = old(self).pos as nat;
        proof {
            ulen::lemma_len_p2();
            crate::bits::prim_read::lemma_p2_56();
            lemma_map_enc_val(nsld_full_enc(), nsld_from(), p0, n);
            lemma_dep_enc_val(bool_enc(), nsld_part_enc(), p0, n > 64, n);
            lemma_bool_enc_len(p0, n > 64);
        }
        let big = n > 64;
        let ghost w0 = old(self).written();
        if !self.write_bool(big) { return false; }
        let ok = if big { self.write_agld(n) } else { self.write_ulen(1, 64, 6, n) };
        proof {
            if ok {
                assert(self.written() =~= w0 + (bool_enc()(p0, big) + nsld_part_enc()(big)(p0 + 1, n)));
            }
        }
        ok
    }

    /// Refines `nsn_enc()`.
    pub fn write_ansn(&mut self, n: u64) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + nsn_enc()(old(self).pos as nat, n),
    {
        let ghost p0 = old(self).pos as nat;
        proof {
            assert(p2(6) == 64) by { reveal_with_fuel(p2, 7); }
            lemma_nsn_format();
            reveal(nsn_wf); reveal(nsn_enc);
            lemma_xext_enc(uint_enc(6), usemi_enc(), uint_wf(6), restrict_wf(usemi_wf(), nsn_big()), nsn_small(), p0, n);
        }
        let small = n <= 63;
        if !self.write_bool(!small) { return false; }
        if small { self.write_uint(6, n) } else { self.write_ausemi(n) }
    }
}

} // verus!
