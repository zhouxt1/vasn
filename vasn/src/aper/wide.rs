//! `INTEGER (0..18446744073709551615)` in the ALIGNED variant, the 3GPP
//! application protocols' 64-bit counters (`usageCountUL`): the indefinite
//! length case of a constrained whole number (X.691 11.5.7.4, 13.2.6 a),
//! as `intx`'s `cwn_big` builds it for ranges up to 2^56, here with the
//! range 2^64 and the value a `u64`. The count of octets is 1..8, so 3 bits
//! (`cb_w(8)`), unaligned; then that many octets, octet-aligned, the fewest
//! that hold the value (11.3.6), the eighth read in two (`uper::wide`).
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::aper::format::*;
use crate::aper::term::*;
use crate::aper::cursor::*;
use crate::aper::intx::*;
use crate::uper::intx as ui;
#[cfg(verus_keep_ghost)]
use crate::uper::intx::{uoct, lemma_uoct, lemma_p2_octets};

verus! {

broadcast use {format_steps, map_steps};

pub open spec fn u64_max() -> int { 0xffff_ffff_ffff_ffffint }

pub open spec fn cwn_u64_wf() -> Wf<u64> { cbu_wf(0, u64_max()) }
pub open spec fn cwn_u64_enc() -> Enc<u64> { cbu_enc(0, u64_max()) }
pub open spec fn cwn_u64_dec() -> Dec<u64> { cbu_dec(0, u64_max()) }

/// The range needs eight octets, so their count is 3 bits.
pub proof fn lemma_cb_m8()
    ensures cb_d(0, u64_max()) == 0xffff_ffff_ffff_ffffnat, cb_m(0, u64_max()) == 8,
            cb_w(8) == 3, 8 <= p2(3),
{
    lemma_p2_octets();
    reveal_with_fuel(p2, 4);
}

proof fn lemma_cbl8_format()
    ensures is_format(cbl_wf(8), cbl_enc(8), cbl_dec(8)),
{
    let w = cb_w(8);
    reveal_with_fuel(p2, 4);
    lemma_uint_format(w);
    lemma_restrict_format(uint_wf(w), uint_enc(w), uint_dec(w), cbl_ok(8));
    assert forall|v: u64| cbl_base_wf(8)(v) implies #[trigger] cbl_from()(cbl_to()(v)) == v by {
        assert(cbl_ok(8)(v));
    }
    lemma_map_format(cbl_base_wf(8), uint_enc(w), cbl_base_dec(8), cbl_to(), cbl_from());
}

proof fn lemma_cbo8_format(l: u64)
    requires 1 <= l <= 8,
    ensures is_format(cbo_wf(l), cbo_enc(l), cbo_dec(l)),
{
    let n = 8 * l as nat;
    lemma_uint_format(n);
    lemma_restrict_format(uint_wf(n), uint_enc(n), uint_dec(n), cbo_ok(l));
    lemma_aligned_format(restrict_wf(uint_wf(n), cbo_ok(l)), uint_enc(n), restrict_dec(uint_dec(n), cbo_ok(l)));
}

proof fn lemma_cbf8_format()
    ensures is_format(cbf_wf(8), cbf_enc(8), cbf_dec(8)),
{
    lemma_cbl8_format();
    assert forall|l: u64| cbl_wf(8)(l) implies
        is_format(#[trigger] cbo_wf_f()(l), cbo_enc_f()(l), cbo_dec_f()(l))
    by {
        let v = cbl_from()(l);
        assert(cbl_base_wf(8)(v) && cbl_to()(v) == l);
        assert(cbl_ok(8)(v));
        lemma_cbo8_format(l);
    }
    lemma_dep_format(cbl_wf(8), cbl_enc(8), cbl_dec(8), cbo_wf_f(), cbo_enc_f(), cbo_dec_f());
}

pub proof fn lemma_cwn_u64_format()
    ensures is_format(cwn_u64_wf(), cwn_u64_enc(), cwn_u64_dec()),
{
    let d = cb_d(0, u64_max());
    lemma_cb_m8();
    lemma_cbf8_format();
    assert forall|t: (u64, u64)| cbf_wf(8)(t) implies #[trigger] cbu_from()(cbu_to()(t)) == t by {
        lemma_dep_wf_val(cbl_wf(8), cbo_wf_f(), t.0, t.1);
        lemma_aligned_wf_val(restrict_wf(uint_wf(8 * t.0 as nat), cbo_ok(t.0)), t.1);
        assert(cbo_ok(t.0)(t.1));
    }
    lemma_map_format(cbf_wf(8), cbf_enc(8), cbf_dec(8), cbu_to(), cbu_from());
    lemma_restrict_format(map_wf(cbf_wf(8), cbu_to(), cbu_from()), cbu_enc(0, u64_max()),
                          map_dec(cbf_dec(8), cbu_to()), cb_le(d));
}

/// Every `u64` is a value.
pub proof fn lemma_cwn_u64_wf_all(u: u64)
    ensures cwn_u64_wf()(u),
{
    let d = cb_d(0, u64_max());
    lemma_cb_m8();
    let l = uoct(u as nat);
    lemma_uoct(u as nat);
    // the count 1..8, as `l - 1` in 3 bits
    let v = (l - 1) as u64;
    reveal_with_fuel(p2, 4);
    assert(cbl_ok(8)(v));
    assert(cbl_base_wf(8)(v));
    assert(cbl_to()(v) == l as u64);
    assert(cbl_wf(8)(l as u64));
    lemma_aligned_wf_val(restrict_wf(uint_wf(8 * l), cbo_ok(l as u64)), u);
    lemma_dep_wf_val(cbl_wf(8), cbo_wf_f(), l as u64, u);
    assert(cbu_from()(u) == (l as u64, u));
    assert(cb_le(d)(u));
}

/// What it writes, flat: the count, the padding after it, the octets.
pub proof fn lemma_cwn_u64_enc_val(pos: nat, u: u64)
    ensures ({
        let l = uoct(u as nat);
        cwn_u64_enc()(pos, u)
            == crate::uper::prim::uint_enc(3)((l - 1) as u64) + zeros(pad(pos + 3))
               + crate::uper::prim::uint_enc(8 * l)(u)
    }),
{
    lemma_cb_m8();
    let l = uoct(u as nat) as u64;
    assert(cwn_u64_enc()(pos, u) == cbf_enc(8)(pos, (l, u)));
    let p1 = pos + cbl_enc(8)(pos, l).len();
    assert(cbf_enc(8)(pos, (l, u)) == cbl_enc(8)(pos, l) + cbo_enc(l)(p1, u));
    assert(cbl_enc(8)(pos, l) == crate::uper::prim::uint_enc(3)((l - 1) as u64));
    crate::uper::prim::lemma_uint_enc_len(3, (l - 1) as u64);
    lemma_aligned_enc_val(uint_enc(8 * l as nat), p1, u);
}

} // verus!

verus! {

impl<'a> BitReader<'a> {
    /// Refines `cwn_u64_dec()`.
    pub fn read_cwn_u64(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => cwn_u64_dec()(old(self).at())
                    == Some::<(u64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => cwn_u64_dec()(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost p0 = self.pos;
        let ghost d = cb_d(0, u64_max());
        proof { lemma_cb_m8(); lemma_p2_octets(); reveal_with_fuel(p2, 4); }
        let ghost fd = cbf_dec(8);
        let ghost ud = map_dec(fd, cbu_to());
        // the count
        let v = match self.read_uint(3) {
            Some(v) => v,
            None => {
                proof {
                    lemma_restrict_dec_none(uint_dec(3), cbl_ok(8), i);
                    lemma_map_dec_none(cbl_base_dec(8), cbl_to(), i);
                    lemma_dep_dec_none_fst(cbl_dec(8), cbo_dec_f(), i);
                    lemma_map_dec_none(fd, cbu_to(), i);
                    lemma_restrict_dec_none(ud, cb_le(d), i);
                }
                return None;
            }
        };
        if v >= 8 {
            proof {
                lemma_restrict_dec_none(uint_dec(3), cbl_ok(8), i);
                lemma_map_dec_none(cbl_base_dec(8), cbl_to(), i);
                lemma_dep_dec_none_fst(cbl_dec(8), cbo_dec_f(), i);
                lemma_map_dec_none(fd, cbu_to(), i);
                lemma_restrict_dec_none(ud, cb_le(d), i);
            }
            return None;
        }
        let l = v + 1;
        proof {
            lemma_restrict_dec_some(uint_dec(3), cbl_ok(8), i, v, 3, Flg::SameVer);
            lemma_map_dec_some(cbl_base_dec(8), cbl_to(), i, v, 3, Flg::SameVer);
            lemma_rem_skip(self.buf@, p0 as nat, 3);
        }
        let ghost i1 = self.at();
        let ghost p1 = self.pos;
        proof { assert(i1 == adv(i, 3)); }
        let ghost od = restrict_dec(uint_dec(8 * l as nat), cbo_ok(l));
        // the octets, aligned
        if !self.read_align() {
            proof {
                lemma_aligned_none(od, i1);
                lemma_dep_dec_none_snd(cbl_dec(8), cbo_dec_f(), i, l, 3, Flg::SameVer);
                lemma_map_dec_none(fd, cbu_to(), i);
                lemma_restrict_dec_none(ud, cb_le(d), i);
            }
            return None;
        }
        let ghost kp = (self.pos - p1) as nat;
        proof {
            lemma_rem_skip(self.buf@, p1 as nat, kp);
            lemma_aligned_step(od, i1, kp);
        }
        let ghost i2 = self.at();
        let nb: usize = (8 * l) as usize;
        let u = match self.read_uint_wide(nb) {
            Some(u) => u,
            None => {
                proof {
                    lemma_restrict_dec_none(uint_dec(nb as nat), cbo_ok(l), i2);
                    lemma_dep_dec_none_snd(cbl_dec(8), cbo_dec_f(), i, l, 3, Flg::SameVer);
                    lemma_map_dec_none(fd, cbu_to(), i);
                    lemma_restrict_dec_none(ud, cb_le(d), i);
                }
                return None;
            }
        };
        proof {
            crate::bits::prim_read::lemma_p2_mono(nb as nat, 64);
            crate::bits::prim_read::lemma_p2_64();
            crate::bits::bitspec::lemma_bits_val_bound(i2.1.take(nb as int));
        }
        if ui::uoct_x(u) != l {
            proof {
                lemma_restrict_dec_none(uint_dec(nb as nat), cbo_ok(l), i2);
                lemma_dep_dec_none_snd(cbl_dec(8), cbo_dec_f(), i, l, 3, Flg::SameVer);
                lemma_map_dec_none(fd, cbu_to(), i);
                lemma_restrict_dec_none(ud, cb_le(d), i);
            }
            { self.fail("constrained INTEGER: not in the fewest octets (X.691 11.5.7.4, 11.3.6)"); return None; }
        }
        let ghost k = (self.pos - p0) as nat;
        proof {
            lemma_restrict_dec_some(uint_dec(nb as nat), cbo_ok(l), i2, u, nb as nat, Flg::SameVer);
            lemma_dep_dec_some(cbl_dec(8), cbo_dec_f(), i, l, 3, Flg::SameVer, u,
                               (self.pos - p1) as nat, Flg::SameVer);
            lemma_map_dec_some(fd, cbu_to(), i, (l, u), k, Flg::SameVer);
            assert(cb_le(d)(u));
            lemma_restrict_dec_some(ud, cb_le(d), i, u, k, Flg::SameVer);
        }
        Some(u)
    }
}

impl BitWriter {
    /// Refines `cwn_u64_enc()`.
    pub fn write_cwn_u64(&mut self, u: u64) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + cwn_u64_enc()(old(self).pos as nat, u),
    {
        let ghost p0 = self.pos as nat;
        proof {
            lemma_cb_m8();
            lemma_p2_octets();
            reveal_with_fuel(p2, 4);
            lemma_cwn_u64_enc_val(p0, u);
        }
        let l = ui::uoct_x(u);
        proof {
            lemma_uoct(u as nat);
            assert((l - 1) < p2(3));
        }
        let ghost w0 = self.written();
        if !self.write_uint(3, l - 1) { return false; }
        if !self.write_align() { return false; }
        proof { crate::bits::prim_read::lemma_p2_mono(8 * l as nat, 64); }
        if !self.write_uint_wide((8 * l) as usize, u) { return false; }
        proof {
            assert(self.written() =~= w0 + crate::uper::prim::uint_enc(3)((l - 1) as u64)
                   + zeros(pad(p0 + 3)) + crate::uper::prim::uint_enc(8 * l as nat)(u));
        }
        true
    }
}

} // verus!
