//! The extensible INTEGER (X.691 13.1) in the ALIGNED variant: a bit, 0 and
//! the root's encoding for a value in the root, 1 and the unconstrained
//! encoding (octet-aligned here) for one outside it.
//!
//! The root is `uper::intx::XRoot`'s. What differs is how a range is encoded:
//! by its size, as a constrained whole number is (11.5.7, `cwn`), and over 64K
//! with the constrained length of 13.2.6 a, since the value is in the root.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::aper::format::*;
use crate::aper::term::*;
use crate::aper::opt::*;
use crate::aper::intx::*;
use crate::aper::cursor::*;
pub use crate::uper::intx::XRoot;
#[cfg(verus_keep_ghost)]
use crate::uper::intx::xroot_ok;

verus! {

broadcast use {format_steps, map_steps};

// --------------------------------------------- a constrained whole number, 11.5.7

/// `lb..ub` (`lb < ub`, a range below 2^56, `n` the UPER width) by the size of
/// its range.
pub open spec fn cwn_wf(lb: int, ub: int, n: nat) -> Wf<i64> {
    if ub - lb + 1 <= 255 { int_range_wf(lb, ub, n) }
    else if ub - lb + 1 == 256 { aint_range_wf(lb, ub, 8) }
    else if ub - lb + 1 <= 65536 { aint_range_wf(lb, ub, 16) }
    else { cwn_big_wf(lb, ub) }
}
pub open spec fn cwn_enc(lb: int, ub: int, n: nat) -> Enc<i64> {
    if ub - lb + 1 <= 255 { int_range_enc(lb, ub, n) }
    else if ub - lb + 1 == 256 { aint_range_enc(lb, ub, 8) }
    else if ub - lb + 1 <= 65536 { aint_range_enc(lb, ub, 16) }
    else { cwn_big_enc(lb, ub) }
}
pub open spec fn cwn_dec(lb: int, ub: int, n: nat) -> Dec<i64> {
    if ub - lb + 1 <= 255 { int_range_dec(lb, ub, n) }
    else if ub - lb + 1 == 256 { aint_range_dec(lb, ub, 8) }
    else if ub - lb + 1 <= 65536 { aint_range_dec(lb, ub, 16) }
    else { cwn_big_dec(lb, ub) }
}

pub open spec fn cwn_ok(lb: int, ub: int, n: nat) -> bool {
    1 <= n <= 56 && lb < ub && ub - lb < p2(n) && i64::MIN <= lb && ub <= i64::MAX
}

pub proof fn lemma_cwn_format(lb: int, ub: int, n: nat)
    requires cwn_ok(lb, ub, n),
    ensures
        is_format(cwn_wf(lb, ub, n), cwn_enc(lb, ub, n), cwn_dec(lb, ub, n)),
        forall|x: i64| #[trigger] cwn_wf(lb, ub, n)(x) <==> (lb <= x as int <= ub),
{
    crate::bits::prim_read::lemma_p2_56();
    crate::bits::prim_read::lemma_p2_mono(n, 56);
    crate::uper::intx::lemma_p2_octets();
    if ub - lb + 1 <= 255 {
        lemma_int_range_format(lb, ub, n);
        assert forall|x: i64| #[trigger] cwn_wf(lb, ub, n)(x) <==> (lb <= x as int <= ub) by {
            lemma_int_range_wf_iff(lb, ub, n, x);
        }
    } else if ub - lb + 1 == 256 {
        lemma_aint_range_format(lb, ub, 8);
        lemma_aint_range_wf_all(lb, ub, 8);
    } else if ub - lb + 1 <= 65536 {
        lemma_aint_range_format(lb, ub, 16);
        lemma_aint_range_wf_all(lb, ub, 16);
    } else {
        lemma_cwn_big_format(lb, ub);
        lemma_cwn_big_wf_all(lb, ub);
    }
}

// ------------------------------------------------------------------- the roots

pub open spec fn xroot_wf(r: XRoot) -> Wf<i64> {
    match r {
        XRoot::Range(lb, ub, n) => cwn_wf(lb as int, ub as int, n as nat),
        XRoot::Const(c) => unit_wf(c),
        XRoot::Semi(lb) => semi_wf(lb as int),
        XRoot::All => uc_wf(),
    }
}
pub open spec fn xroot_enc(r: XRoot) -> Enc<i64> {
    match r {
        XRoot::Range(lb, ub, n) => cwn_enc(lb as int, ub as int, n as nat),
        XRoot::Const(c) => unit_enc(),
        XRoot::Semi(lb) => semi_enc(lb as int),
        XRoot::All => uc_enc(),
    }
}
pub open spec fn xroot_dec(r: XRoot) -> Dec<i64> {
    match r {
        XRoot::Range(lb, ub, n) => cwn_dec(lb as int, ub as int, n as nat),
        XRoot::Const(c) => unit_dec(c),
        XRoot::Semi(lb) => semi_dec(lb as int),
        XRoot::All => uc_dec(),
    }
}
pub open spec fn xroot_in(r: XRoot) -> spec_fn(i64) -> bool { crate::uper::intx::xroot_in(r) }

pub proof fn lemma_xroot(r: XRoot)
    requires xroot_ok(r),
    ensures
        is_format(xroot_wf(r), xroot_enc(r), xroot_dec(r)),
        forall|v: i64| #[trigger] xroot_wf(r)(v) == xroot_in(r)(v),
{
    match r {
        XRoot::Range(lb, ub, n) => {
            lemma_cwn_format(lb as int, ub as int, n as nat);
        }
        XRoot::Const(c) => {
            lemma_unit_format(c);
            reveal(unit_wf);
        }
        XRoot::Semi(lb) => {
            lemma_semi_format(lb as int);
            lemma_semi_wf_all(lb as int);
        }
        XRoot::All => {
            lemma_uc_format();
            lemma_uc_wf_every();
        }
    }
}

// ------------------------------------------------------------------ extensible

pub open spec fn xint_out(inr: spec_fn(i64) -> bool) -> spec_fn(i64) -> bool { |v: i64| !inr(v) }

pub open spec fn xint_alt_wf(rw: Wf<i64>, inr: spec_fn(i64) -> bool) -> spec_fn(bool) -> Wf<i64> {
    |x: bool| if x { restrict_wf(uc_wf(), xint_out(inr)) } else { rw }
}
pub open spec fn xint_alt_enc(re: Enc<i64>) -> spec_fn(bool) -> Enc<i64> {
    |x: bool| if x { uc_enc() } else { re }
}
pub open spec fn xint_alt_dec(rd: Dec<i64>, inr: spec_fn(i64) -> bool) -> spec_fn(bool) -> Dec<i64> {
    |x: bool| if x { restrict_dec(uc_dec(), xint_out(inr)) } else { rd }
}

pub open spec fn xint_to() -> spec_fn((bool, i64)) -> i64 { |t: (bool, i64)| t.1 }
pub open spec fn xint_from(inr: spec_fn(i64) -> bool) -> spec_fn(i64) -> (bool, i64) {
    |v: i64| (!inr(v), v)
}

pub open spec fn xint_wf(rw: Wf<i64>, inr: spec_fn(i64) -> bool) -> Wf<i64> {
    map_wf(dep_wf(bool_wf(), xint_alt_wf(rw, inr)), xint_to(), xint_from(inr))
}
pub open spec fn xint_enc(re: Enc<i64>, inr: spec_fn(i64) -> bool) -> Enc<i64> {
    map_enc(dep_enc(bool_enc(), xint_alt_enc(re)), xint_from(inr))
}
pub open spec fn xint_dec(rd: Dec<i64>, inr: spec_fn(i64) -> bool) -> Dec<i64> {
    map_dec(dep_dec(bool_dec(), xint_alt_dec(rd, inr)), xint_to())
}

pub proof fn lemma_xint_format(rw: Wf<i64>, re: Enc<i64>, rd: Dec<i64>, inr: spec_fn(i64) -> bool)
    requires is_format(rw, re, rd), forall|v: i64| #[trigger] rw(v) == inr(v),
    ensures is_format(xint_wf(rw, inr), xint_enc(re, inr), xint_dec(rd, inr)),
{
    lemma_bool_format();
    lemma_uc_format();
    lemma_restrict_format(uc_wf(), uc_enc(), uc_dec(), xint_out(inr));
    assert forall|x: bool| bool_wf()(x) implies
        is_format(#[trigger] xint_alt_wf(rw, inr)(x), xint_alt_enc(re)(x), xint_alt_dec(rd, inr)(x))
    by {}
    lemma_dep_format(bool_wf(), bool_enc(), bool_dec(), xint_alt_wf(rw, inr), xint_alt_enc(re),
                     xint_alt_dec(rd, inr));
    assert forall|t: (bool, i64)| dep_wf(bool_wf(), xint_alt_wf(rw, inr))(t) implies
        #[trigger] xint_from(inr)(xint_to()(t)) == t
    by {
        lemma_dep_wf_val(bool_wf(), xint_alt_wf(rw, inr), t.0, t.1);
        lemma_restrict_wf_val(uc_wf(), xint_out(inr), t.1);
    }
    lemma_map_format(dep_wf(bool_wf(), xint_alt_wf(rw, inr)), dep_enc(bool_enc(), xint_alt_enc(re)),
                     dep_dec(bool_dec(), xint_alt_dec(rd, inr)), xint_to(), xint_from(inr));
}

pub proof fn lemma_xint_wf_all(rw: Wf<i64>, inr: spec_fn(i64) -> bool, v: i64)
    requires forall|v: i64| #[trigger] rw(v) == inr(v),
    ensures xint_wf(rw, inr)(v),
{
    lemma_bool_wf_all(!inr(v));
    lemma_map_wf_val(dep_wf(bool_wf(), xint_alt_wf(rw, inr)), xint_to(), xint_from(inr), v);
    lemma_dep_wf_val(bool_wf(), xint_alt_wf(rw, inr), !inr(v), v);
    lemma_restrict_wf_val(uc_wf(), xint_out(inr), v);
    lemma_uc_wf_all(v);
}

pub open spec fn xint_r_wf(r: XRoot) -> Wf<i64> { xint_wf(xroot_wf(r), xroot_in(r)) }
pub open spec fn xint_r_enc(r: XRoot) -> Enc<i64> { xint_enc(xroot_enc(r), xroot_in(r)) }
pub open spec fn xint_r_dec(r: XRoot) -> Dec<i64> { xint_dec(xroot_dec(r), xroot_in(r)) }

pub proof fn lemma_xint_r_format(r: XRoot)
    requires xroot_ok(r),
    ensures
        is_format(xint_r_wf(r), xint_r_enc(r), xint_r_dec(r)),
        forall|v: i64| #[trigger] xint_r_wf(r)(v),
{
    lemma_xroot(r);
    lemma_xint_format(xroot_wf(r), xroot_enc(r), xroot_dec(r), xroot_in(r));
    assert forall|v: i64| #[trigger] xint_r_wf(r)(v) by {
        lemma_xint_wf_all(xroot_wf(r), xroot_in(r), v);
    }
}

} // verus!

verus! {

impl<'a> BitReader<'a> {
    /// Refines `cwn_dec(lb, ub, n)`.
    pub fn read_cwn(&mut self, lb: i64, ub: i64, n: usize) -> (res: Option<i64>)
        requires old(self).wf(), cwn_ok(lb as int, ub as int, n as nat),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => cwn_dec(lb as int, ub as int, n as nat)(old(self).at())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => cwn_dec(lb as int, ub as int, n as nat)(old(self).at()) is None,
            },
    {
        proof {
            crate::bits::prim_read::lemma_p2_56();
            crate::bits::prim_read::lemma_p2_mono(n as nat, 56);
            assert(p2(8) == 256 && p2(16) == 65536) by { crate::uper::intx::lemma_p2_octets(); }
        }
        let range: u64 = ((ub as i128) - (lb as i128) + 1) as u64;
        if range <= 255 {
            self.read_int_range(lb, ub, n)
        } else if range == 256 {
            self.read_aint_range(lb, ub, 8)
        } else if range <= 65536 {
            self.read_aint_range(lb, ub, 16)
        } else {
            self.read_cwn_big(lb, ub)
        }
    }

    /// Refines `xint_r_dec(r)`: an extensible INTEGER (X.691 13.1).
    pub fn read_axint(&mut self, r: XRoot) -> (res: Option<i64>)
        requires old(self).wf(), xroot_ok(r),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => xint_r_dec(r)(old(self).at())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => xint_r_dec(r)(old(self).at()) is None,
            },
    {
        let ghost start = self.at();
        let ghost p0 = self.pos;
        let ghost d2 = xint_alt_dec(xroot_dec(r), xroot_in(r));
        let ghost full = dep_dec(bool_dec(), d2);
        let out = match self.read_bool() {
            Some(o) => o,
            None => {
                proof {
                    lemma_dep_dec_none_fst(bool_dec(), d2, start);
                    lemma_map_dec_none(full, xint_to(), start);
                }
                return None;
            }
        };
        proof { lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat); }
        let ghost kb = (self.pos - p0) as nat;
        let ghost mid = adv(start, kb);
        let ghost p1 = self.pos;
        let got: Option<i64> = if !out {
            match r {
                XRoot::Range(lb, ub, n) => self.read_cwn(lb, ub, n),
                XRoot::Const(c) => {
                    proof { lemma_unit_dec_val(c, mid); }
                    Some(c)
                }
                XRoot::Semi(lb) => self.read_asemi(lb),
                XRoot::All => self.read_auc(),
            }
        } else {
            match self.read_auc() {
                Some(v) => {
                    let inr = match r {
                        XRoot::Range(lb, ub, _) => lb <= v && v <= ub,
                        XRoot::Const(c) => v == c,
                        XRoot::Semi(lb) => lb <= v,
                        XRoot::All => true,
                    };
                    if inr {
                        proof { lemma_restrict_dec_none(uc_dec(), xint_out(xroot_in(r)), mid); }
                        { self.fail("extensible INTEGER: a root value sent as an extension (X.691 10.4.3)"); None }
                    } else {
                        proof {
                            lemma_restrict_dec_some(uc_dec(), xint_out(xroot_in(r)), mid, v,
                                                    (self.pos - p1) as nat, Flg::SameVer);
                        }
                        Some(v)
                    }
                }
                None => {
                    proof { lemma_restrict_dec_none(uc_dec(), xint_out(xroot_in(r)), mid); }
                    None
                }
            }
        };
        match got {
            Some(v) => {
                proof {
                    lemma_dep_dec_some(bool_dec(), d2, start, out, kb, Flg::SameVer, v,
                                       (self.pos - p1) as nat, Flg::SameVer);
                    lemma_map_dec_some(full, xint_to(), start, (out, v), (self.pos - p0) as nat, Flg::SameVer);
                }
                Some(v)
            }
            None => {
                proof {
                    lemma_dep_dec_none_snd(bool_dec(), d2, start, out, kb, Flg::SameVer);
                    lemma_map_dec_none(full, xint_to(), start);
                }
                None
            }
        }
    }
}

impl BitWriter {
    /// Refines `cwn_enc(lb, ub, n)`.
    pub fn write_cwn(&mut self, lb: i64, ub: i64, n: usize, v: i64) -> (ok: bool)
        requires old(self).wf(), cwn_ok(lb as int, ub as int, n as nat), lb <= v <= ub,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written()
                + cwn_enc(lb as int, ub as int, n as nat)(old(self).pos as nat, v),
    {
        proof {
            crate::bits::prim_read::lemma_p2_56();
            crate::bits::prim_read::lemma_p2_mono(n as nat, 56);
            assert(p2(8) == 256 && p2(16) == 65536) by { crate::uper::intx::lemma_p2_octets(); }
        }
        let range: u64 = ((ub as i128) - (lb as i128) + 1) as u64;
        if range <= 255 {
            self.write_int_range(lb, ub, n, v)
        } else if range == 256 {
            self.write_aint_range(lb, ub, 8, v)
        } else if range <= 65536 {
            self.write_aint_range(lb, ub, 16, v)
        } else {
            self.write_cwn_big(lb, ub, v)
        }
    }

    /// Refines `xint_r_enc(r)`.
    pub fn write_axint(&mut self, r: XRoot, v: i64) -> (ok: bool)
        requires old(self).wf(), xroot_ok(r),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + xint_r_enc(r)(old(self).pos as nat, v),
    {
        let ghost p0 = old(self).pos as nat;
        let inr = match r {
            XRoot::Range(lb, ub, _) => lb <= v && v <= ub,
            XRoot::Const(c) => v == c,
            XRoot::Semi(lb) => lb <= v,
            XRoot::All => true,
        };
        proof {
            assert(inr == xroot_in(r)(v));
            lemma_map_enc_val(dep_enc(bool_enc(), xint_alt_enc(xroot_enc(r))), xint_from(xroot_in(r)), p0, v);
            lemma_dep_enc_val(bool_enc(), xint_alt_enc(xroot_enc(r)), p0, !inr, v);
            lemma_bool_enc_len(p0, !inr);
        }
        let ghost w0 = self.written();
        if !self.write_bool(!inr) { return false; }
        let ghost w1 = self.written();
        let ok = if inr {
            match r {
                XRoot::Range(lb, ub, n) => self.write_cwn(lb, ub, n, v),
                XRoot::Const(c) => {
                    proof { reveal(unit_enc); assert(w1 + unit_enc::<i64>()(p0 + 1, v) =~= w1); }
                    true
                }
                XRoot::Semi(lb) => self.write_asemi(lb, v),
                XRoot::All => self.write_auc(v),
            }
        } else {
            self.write_auc(v)
        };
        proof {
            if ok {
                assert(self.written() =~= w0 + (bool_enc()(p0, !inr) + xint_alt_enc(xroot_enc(r))(!inr)(p0 + 1, v)));
            }
        }
        ok
    }
}

} // verus!
