//! Length determinants (X.691 §11.9).
//!
//! Two of them, and neither needs a new combinator -- each is a `bool` that
//! selects a width, which is exactly `dep`, re-typed by `map` so the value is
//! the length itself rather than the (selector, length) pair.
//!
//!   * **general** (§11.9.3.6-7, VUPER's `uncons_len_det_format`): `'0'` then
//!     7 bits for n < 128, else `'1'` then 15 bits holding n. The second form
//!     is X.691's `'10'` + 14 bits: requiring n < 2^14 forces the 15-bit
//!     field's top bit to zero, so the two readings coincide.
//!   * **normally small** (§11.9.3.4, VUPER's `normally_small_len_det_format`):
//!     `'0'` then 6 bits of n-1 for 1 <= n <= 64, else `'1'` then the general
//!     form. This is what counts the extension additions in a SEQUENCE.
//!
//! Both restrict the wide form to values the narrow form cannot express, which
//! is what makes the encoding canonical and the format injective -- an encoder
//! that used the long form for a short length would be rejected.
//!
//! Neither carries a length of 16K or more; that is fragmentation, and it
//! lives in `frag.rs`, whose `LenHead` generalises `gld` to announce a
//! fragment as well as a final length. `lemma_gld_lh_agree` proves the two
//! spellings agree bit-for-bit on the lengths both can express, so they
//! cannot drift apart.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::uper::format::*;
use crate::uper::prim::*;
use crate::uper::term::*;
use crate::uper::list::*;

verus! {

broadcast use {format_steps, map_steps};

/// One past the largest length either determinant can carry.
pub open spec fn len_max() -> nat { 16384 }

// ------------------------------------------------- general length determinant

pub open spec fn gld_lo() -> spec_fn(u64) -> bool { |v: u64| v < 128 }
pub open spec fn gld_hi() -> spec_fn(u64) -> bool { |v: u64| 128 <= v < 16384 }

pub open spec fn gld_part_wf() -> spec_fn(bool) -> Wf<u64> {
    |b: bool| if b { restrict_wf(uint_wf(15), gld_hi()) } else { restrict_wf(uint_wf(7), gld_lo()) }
}
pub open spec fn gld_part_enc() -> spec_fn(bool) -> Enc<u64> {
    |b: bool| if b { uint_enc(15) } else { uint_enc(7) }
}
pub open spec fn gld_part_dec() -> spec_fn(bool) -> Dec<u64> {
    |b: bool| if b { restrict_dec(uint_dec(15), gld_hi()) } else { restrict_dec(uint_dec(7), gld_lo()) }
}

pub open spec fn gld_to() -> spec_fn((bool, u64)) -> u64 { |p: (bool, u64)| p.1 }
pub open spec fn gld_from() -> spec_fn(u64) -> (bool, u64) { |n: u64| (n >= 128, n) }

pub open spec fn gld_full_wf() -> Wf<(bool, u64)> { dep_wf(bool_wf(), gld_part_wf()) }
pub open spec fn gld_full_enc() -> Enc<(bool, u64)> { dep_enc(bool_enc(), gld_part_enc()) }
pub open spec fn gld_full_dec() -> Dec<(bool, u64)> { dep_dec(bool_dec(), gld_part_dec()) }

pub open spec fn gld_wf() -> Wf<u64> { map_wf(gld_full_wf(), gld_to(), gld_from()) }
pub open spec fn gld_enc() -> Enc<u64> { map_enc(gld_full_enc(), gld_from()) }
pub open spec fn gld_dec() -> Dec<u64> { map_dec(gld_full_dec(), gld_to()) }

/// `p2` at the three widths this module uses.
pub proof fn lemma_len_p2()
    ensures p2(6) == 64, p2(7) == 128, p2(15) == 32768,
{
    reveal_with_fuel(p2, 17);
}

pub proof fn lemma_gld_part_format(b: bool)
    ensures is_format(gld_part_wf()(b), gld_part_enc()(b), gld_part_dec()(b)),
{
    if b {
        lemma_uint_format(15);
        lemma_restrict_format(uint_wf(15), uint_enc(15), uint_dec(15), gld_hi());
    } else {
        lemma_uint_format(7);
        lemma_restrict_format(uint_wf(7), uint_enc(7), uint_dec(7), gld_lo());
    }
}

pub proof fn lemma_gld_format()
    ensures is_format(gld_wf(), gld_enc(), gld_dec()),
{
    lemma_bool_format();
    assert forall|b: bool| bool_wf()(b) implies
        is_format(#[trigger] gld_part_wf()(b), gld_part_enc()(b), gld_part_dec()(b))
    by { lemma_gld_part_format(b); }
    lemma_dep_format(bool_wf(), bool_enc(), bool_dec(),
                     gld_part_wf(), gld_part_enc(), gld_part_dec());
    assert forall|p: (bool, u64)| gld_full_wf()(p) implies
        #[trigger] gld_from()(gld_to()(p)) == p
    by {
        lemma_dep_wf_val(bool_wf(), gld_part_wf(), p.0, p.1);
        if p.0 {
            lemma_restrict_wf_val(uint_wf(15), gld_hi(), p.1);
        } else {
            lemma_restrict_wf_val(uint_wf(7), gld_lo(), p.1);
        }
    }
    lemma_map_format(gld_full_wf(), gld_full_enc(), gld_full_dec(), gld_to(), gld_from());
}

/// The determinant carries exactly the lengths below 16K.
pub proof fn lemma_gld_wf_iff(n: u64)
    ensures gld_wf()(n) <==> n < 16384,
{
    lemma_len_p2();
    lemma_bool_wf_all(n >= 128);
    lemma_map_wf_val(gld_full_wf(), gld_to(), gld_from(), n);
    lemma_dep_wf_val(bool_wf(), gld_part_wf(), n >= 128, n);
    lemma_restrict_wf_val(uint_wf(15), gld_hi(), n);
    lemma_restrict_wf_val(uint_wf(7), gld_lo(), n);
}

/// One octet for a short length, two for a long one.
pub proof fn lemma_gld_enc_len(n: u64)
    requires gld_wf()(n),
    ensures gld_enc()(n).len() == (if n < 128 { 8int } else { 16int }),
{
    lemma_gld_wf_iff(n);
    lemma_map_enc_val(gld_full_enc(), gld_from(), n);
    lemma_dep_enc_val(bool_enc(), gld_part_enc(), n >= 128, n);
    lemma_bool_enc_len(n >= 128);
    lemma_uint_enc_len(if n >= 128 { 15nat } else { 7nat }, n);
}

/// The determinant is built only from `uint`, so it can never report
/// `DiffVer`. VUPER states the same thing as `parse_to_SameVer`
/// (`Formats/SameVerProp.v`, `det_SameVer`); here it is one unfolding.
pub proof fn lemma_gld_dec_same(b: Seq<bool>)
    ensures gld_dec()(b) is Some ==> gld_dec()(b).unwrap().2 is SameVer,
{
    reveal(map_dec);
    reveal(dep_dec);
    reveal(restrict_dec);
}

// ------------------------------------------ normally small length determinant

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

pub proof fn lemma_nsld_part_format(b: bool)
    ensures is_format(nsld_part_wf()(b), nsld_part_enc()(b), nsld_part_dec()(b)),
{
    lemma_len_p2();
    if b {
        lemma_gld_format();
        lemma_restrict_format(gld_wf(), gld_enc(), gld_dec(), nsld_big());
    } else {
        crate::bits::prim_read::lemma_p2_56();
        lemma_ulen_format(1, 64, 6);
    }
}

pub proof fn lemma_nsld_format()
    ensures is_format(nsld_wf(), nsld_enc(), nsld_dec()),
{
    lemma_bool_format();
    assert forall|b: bool| bool_wf()(b) implies
        is_format(#[trigger] nsld_part_wf()(b), nsld_part_enc()(b), nsld_part_dec()(b))
    by { lemma_nsld_part_format(b); }
    lemma_dep_format(bool_wf(), bool_enc(), bool_dec(),
                     nsld_part_wf(), nsld_part_enc(), nsld_part_dec());
    assert forall|p: (bool, u64)| nsld_full_wf()(p) implies
        #[trigger] nsld_from()(nsld_to()(p)) == p
    by {
        lemma_dep_wf_val(bool_wf(), nsld_part_wf(), p.0, p.1);
        if p.0 {
            lemma_restrict_wf_val(gld_wf(), nsld_big(), p.1);
        } else {
            crate::bits::prim_read::lemma_p2_56();
            lemma_len_p2();
            lemma_ulen_wf_bound(1, 64, 6, p.1);
        }
    }
    lemma_map_format(nsld_full_wf(), nsld_full_enc(), nsld_full_dec(), nsld_to(), nsld_from());
}

pub proof fn lemma_nsld_dec_same(b: Seq<bool>)
    ensures nsld_dec()(b) is Some ==> nsld_dec()(b).unwrap().2 is SameVer,
{
    reveal(map_dec);
    reveal(dep_dec);
    reveal(restrict_dec);
    if nsld_full_dec()(b) is Some {
        let sel = bool_dec()(b).unwrap().0;
        if sel {
            lemma_gld_dec_same(b.skip(bool_dec()(b).unwrap().1 as int));
        }
    }
}

/// The extension-addition count is at least one and below 16K.
pub proof fn lemma_nsld_wf_iff(n: u64)
    ensures nsld_wf()(n) <==> 1 <= n < 16384,
{
    lemma_len_p2();
    crate::bits::prim_read::lemma_p2_56();
    lemma_bool_wf_all(n > 64);
    lemma_map_wf_val(nsld_full_wf(), nsld_to(), nsld_from(), n);
    lemma_dep_wf_val(bool_wf(), nsld_part_wf(), n > 64, n);
    lemma_restrict_wf_val(gld_wf(), nsld_big(), n);
    lemma_gld_wf_iff(n);
    if !(n > 64) {
        lemma_ulen_wf_iff(1, 64, 6, n);
    }
}

} // verus!

verus! {

use crate::uper::cursor::*;

impl<'a> BitReader<'a> {
    /// Refines `gld_dec()`. The range check is what rejects a long form that
    /// should have been short, and with it the whole encoding is canonical.
    #[inline]
    pub fn read_gld(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& gld_dec()(old(self).rem()) == Some::<(u64, nat, Flg)>(
                            (v, (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& v < 16384
                },
                None => gld_dec()(old(self).rem()).is_none(),
            },
    {
        let ghost start = old(self).rem();
        let ghost p0 = self.pos;
        let long = match self.read_bool() {
            Some(v) => v,
            None => {
                proof {
                    lemma_dep_dec_none_fst(bool_dec(), gld_part_dec(), start);
                    lemma_map_dec_none(gld_full_dec(), gld_to(), start);
                }
                return None;
            }
        };
        proof { lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat); }
        let ghost kb = (self.pos - p0) as nat;
        let ghost mid = start.skip(kb as int);
        let ghost p1 = self.pos;
        let w: usize = if long { 15 } else { 7 };
        let lo: u64 = if long { 128 } else { 0 };
        let hi: u64 = if long { 16384 } else { 128 };
        match self.read_uint(w) {
            Some(v) => {
                if v >= lo && v < hi {
                    proof {
                        if long {
                            lemma_restrict_dec_some(uint_dec(15), gld_hi(), mid, v, 15, Flg::SameVer);
                        } else {
                            lemma_restrict_dec_some(uint_dec(7), gld_lo(), mid, v, 7, Flg::SameVer);
                        }
                        lemma_dep_dec_some(bool_dec(), gld_part_dec(), start, long, kb,
                                           Flg::SameVer, v, w as nat, Flg::SameVer);
                        lemma_map_dec_some(gld_full_dec(), gld_to(), start, (long, v),
                                           (self.pos - p0) as nat, Flg::SameVer);
                    }
                    Some(v)
                } else {
                    proof {
                        if long {
                            lemma_restrict_dec_none(uint_dec(15), gld_hi(), mid);
                        } else {
                            lemma_restrict_dec_none(uint_dec(7), gld_lo(), mid);
                        }
                        lemma_dep_dec_none_snd(bool_dec(), gld_part_dec(), start, long, kb,
                                               Flg::SameVer);
                        lemma_map_dec_none(gld_full_dec(), gld_to(), start);
                    }
                    None
                }
            }
            None => {
                proof {
                    if long {
                        lemma_restrict_dec_none(uint_dec(15), gld_hi(), mid);
                    } else {
                        lemma_restrict_dec_none(uint_dec(7), gld_lo(), mid);
                    }
                    lemma_dep_dec_none_snd(bool_dec(), gld_part_dec(), start, long, kb, Flg::SameVer);
                    lemma_map_dec_none(gld_full_dec(), gld_to(), start);
                }
                None
            }
        }
    }
}

impl BitWriter {
    /// Refines `gld_enc()`.
    #[inline]
    pub fn write_gld(&mut self, n: u64) -> (ok: bool)
        requires old(self).wf(), n < 16384,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + gld_enc()(n),
    {
        proof {
            lemma_len_p2();
            lemma_map_enc_val(gld_full_enc(), gld_from(), n);
            lemma_dep_enc_val(bool_enc(), gld_part_enc(), n >= 128, n);
        }
        let long = n >= 128;
        let ghost w0 = old(self).written();
        if !self.write_bool(long) { return false; }
        let ghost w1 = self.written();
        let ok = if long { self.write_uint(15, n) } else { self.write_uint(7, n) };
        proof {
            if ok {
                assert(self.written() =~= w0 + (bool_enc()(long) + gld_part_enc()(long)(n)));
            }
        }
        ok
    }
}

} // verus!

verus! {

impl<'a> BitReader<'a> {
    /// Refines `nsld_dec()` -- the count of extension additions.
    #[inline]
    pub fn read_nsld(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& nsld_dec()(old(self).rem()) == Some::<(u64, nat, Flg)>(
                            (v, (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& 1 <= v < 16384
                },
                None => nsld_dec()(old(self).rem()).is_none(),
            },
    {
        proof { lemma_len_p2(); crate::bits::prim_read::lemma_p2_56(); }
        let ghost start = old(self).rem();
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
        let ghost mid = start.skip(kb as int);
        let ghost p1 = self.pos;
        let got: Option<u64> = if big {
            match self.read_gld() {
                Some(v) => if v >= 65 {
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
                }
                Some(v)
            }
            None => {
                proof {
                    lemma_dep_dec_none_snd(bool_dec(), nsld_part_dec(), start, big, kb,
                                           Flg::SameVer);
                    lemma_map_dec_none(nsld_full_dec(), nsld_to(), start);
                }
                None
            }
        }
    }
}

impl BitWriter {
    /// Refines `nsld_enc()`.
    #[inline]
    pub fn write_nsld(&mut self, n: u64) -> (ok: bool)
        requires old(self).wf(), 1 <= n < 16384,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + nsld_enc()(n),
    {
        proof {
            lemma_len_p2();
            crate::bits::prim_read::lemma_p2_56();
            lemma_map_enc_val(nsld_full_enc(), nsld_from(), n);
            lemma_dep_enc_val(bool_enc(), nsld_part_enc(), n > 64, n);
        }
        let big = n > 64;
        let ghost w0 = old(self).written();
        if !self.write_bool(big) { return false; }
        let ok = if big { self.write_gld(n) } else { self.write_ulen(1, 64, 6, n) };
        proof {
            if ok {
                assert(self.written() =~= w0 + (bool_enc()(big) + nsld_part_enc()(big)(n)));
            }
        }
        ok
    }
}

} // verus!
