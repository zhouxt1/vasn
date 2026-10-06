//! INTEGERs in the ALIGNED variant (X.691 11.5.7, 11.7, 11.8, 13).
//!
//! A constrained whole number (11.5.7) is encoded by the size of its range:
//!
//!   * up to 255: the bit-field UPER uses (`aper::term::int_range`);
//!   * exactly 256: one octet, octet-aligned (`aint_range`, n = 8);
//!   * 257 to 64K: two octets, octet-aligned (`aint_range`, n = 16);
//!   * over 64K, "the indefinite length case" (11.5.7.4, 13.2.6 a): the number
//!     of octets `L` as a constrained whole number of range 1 to the octets the
//!     range needs, then `L` octets, octet-aligned, holding `n - lb` in the
//!     fewest octets (`cwn_big`).
//!
//! A semi-constrained or unconstrained INTEGER (11.7, 11.8, 13.2.6 b) is
//! UPER's encoding octet-aligned: an unconstrained length determinant, which
//! is one octet here, and whole octets after it. Once the first bit is on an
//! octet boundary everything after it is, so `aligned(lift(uper))` is the
//! whole of it.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::aper::format::*;
use crate::aper::term::*;
use crate::aper::cursor::*;
use crate::uper::intx as ui;
use crate::uper::term as ut;
#[cfg(verus_keep_ghost)]
use crate::uper::intx::{uoct, lemma_uoct, lemma_p2_octets};

verus! {

broadcast use {format_steps, map_steps};

// ------------------------------------------------------------ gluing `aligned`

/// The padding read, the rest of an aligned decode is the inner decode from
/// where the padding ended.
pub proof fn lemma_aligned_step<A>(d: Dec<A>, i: In, p: nat)
    requires align_dec()(i) == Some::<((), nat, Flg)>(((), p, Flg::SameVer)),
    ensures aligned_dec(d)(i) == (match d(adv(i, p)) {
        Some((a, k, f)) => Some((a, (p + k) as nat, f)),
        None => None,
    }),
{
    lemma_aligned_dec_val(d, i);
}

pub proof fn lemma_aligned_none<A>(d: Dec<A>, i: In)
    requires align_dec()(i) is None,
    ensures aligned_dec(d)(i) is None,
{
    lemma_aligned_dec_val(d, i);
}

// ------------------------------------------- one or two octets, octet-aligned

/// 11.5.7.2 (n = 8, a range of exactly 256) and 11.5.7.3 (n = 16, a range of
/// 257 to 64K): `n - lb` in an octet-aligned field of `n` bits.
pub open spec fn aint_range_wf(lb: int, ub: int, n: nat) -> Wf<i64> { aligned_wf(int_range_wf(lb, ub, n)) }
pub open spec fn aint_range_enc(lb: int, ub: int, n: nat) -> Enc<i64> { aligned_enc(int_range_enc(lb, ub, n)) }
pub open spec fn aint_range_dec(lb: int, ub: int, n: nat) -> Dec<i64> { aligned_dec(int_range_dec(lb, ub, n)) }

pub proof fn lemma_aint_range_format(lb: int, ub: int, n: nat)
    requires 1 <= n <= 56, lb < ub, ub - lb < p2(n), i64::MIN <= lb, ub <= i64::MAX,
    ensures is_format(aint_range_wf(lb, ub, n), aint_range_enc(lb, ub, n), aint_range_dec(lb, ub, n)),
{
    lemma_int_range_format(lb, ub, n);
    lemma_aligned_format(int_range_wf(lb, ub, n), int_range_enc(lb, ub, n), int_range_dec(lb, ub, n));
}

pub proof fn lemma_aint_range_wf_iff(lb: int, ub: int, n: nat, x: i64)
    requires 1 <= n <= 56, lb < ub, ub - lb < p2(n), i64::MIN <= lb, ub <= i64::MAX,
    ensures aint_range_wf(lb, ub, n)(x) <==> (lb <= x as int <= ub),
{
    lemma_aligned_wf_val(int_range_wf(lb, ub, n), x);
    lemma_int_range_wf_iff(lb, ub, n, x);
}

// ------------------------------------- an index of 256 to 64K, octet-aligned

/// An ENUMERATED or CHOICE index whose range is 256 (n = 8) or 257 to 64K
/// (n = 16): a constrained whole number with lb 0 (X.691 14.2, 23.6), so
/// 11.5.7.2 and 11.5.7.3, the index in an octet-aligned field of `n` bits.
pub open spec fn auint_wf(n: nat) -> Wf<u64> { aligned_wf(uint_wf(n)) }
pub open spec fn auint_enc(n: nat) -> Enc<u64> { aligned_enc(uint_enc(n)) }
pub open spec fn auint_dec(n: nat) -> Dec<u64> { aligned_dec(uint_dec(n)) }

pub proof fn lemma_auint_format(n: nat)
    requires 1 <= n <= 56,
    ensures is_format(auint_wf(n), auint_enc(n), auint_dec(n)),
{
    lemma_uint_format(n);
    lemma_aligned_format(uint_wf(n), uint_enc(n), uint_dec(n));
}

pub proof fn lemma_auint_wf_val(n: nat, v: u64)
    ensures auint_wf(n)(v) == uint_wf(n)(v),
{
    lemma_aligned_wf_val(uint_wf(n), v);
}

// ------------------------------------------ semi-constrained, unconstrained

pub open spec fn semi_wf(lb: int) -> Wf<i64> { aligned_wf(ui::semi_wf(lb)) }
pub open spec fn semi_enc(lb: int) -> Enc<i64> { aligned_enc(lift_enc(ui::semi_enc(lb))) }
pub open spec fn semi_dec(lb: int) -> Dec<i64> { aligned_dec(lift_dec(ui::semi_dec(lb))) }

pub proof fn lemma_semi_format(lb: int)
    requires i64::MIN <= lb <= i64::MAX,
    ensures is_format(semi_wf(lb), semi_enc(lb), semi_dec(lb)),
{
    ui::lemma_semi_format(lb);
    lemma_lift_format(ui::semi_wf(lb), ui::semi_enc(lb), ui::semi_dec(lb));
    lemma_aligned_format(ui::semi_wf(lb), lift_enc(ui::semi_enc(lb)), lift_dec(ui::semi_dec(lb)));
}

pub proof fn lemma_semi_wf_iff(lb: int, x: i64)
    ensures semi_wf(lb)(x) <==> lb <= x as int,
{
    lemma_aligned_wf_val(ui::semi_wf(lb), x);
}

pub open spec fn uc_wf() -> Wf<i64> { aligned_wf(ui::uc_wf()) }
pub open spec fn uc_enc() -> Enc<i64> { aligned_enc(lift_enc(ui::uc_enc())) }
pub open spec fn uc_dec() -> Dec<i64> { aligned_dec(lift_dec(ui::uc_dec())) }

pub proof fn lemma_uc_format()
    ensures is_format(uc_wf(), uc_enc(), uc_dec()),
{
    ui::lemma_uc_format();
    lemma_lift_format(ui::uc_wf(), ui::uc_enc(), ui::uc_dec());
    lemma_aligned_format(ui::uc_wf(), lift_enc(ui::uc_enc()), lift_dec(ui::uc_dec()));
}

pub proof fn lemma_uc_wf_all(x: i64)
    ensures uc_wf()(x),
{
    lemma_aligned_wf_val(ui::uc_wf(), x);
}

/// A semi-constrained whole number with lb 0 over all of u64 (11.7): the
/// normally small number's long form, and a length's.
pub open spec fn usemi_wf() -> Wf<u64> { aligned_wf(ui::usemi_wf()) }
pub open spec fn usemi_enc() -> Enc<u64> { aligned_enc(lift_enc(ui::usemi_enc())) }
pub open spec fn usemi_dec() -> Dec<u64> { aligned_dec(lift_dec(ui::usemi_dec())) }

pub proof fn lemma_usemi_format()
    ensures is_format(usemi_wf(), usemi_enc(), usemi_dec()),
{
    ui::lemma_usemi_format();
    lemma_lift_format(ui::usemi_wf(), ui::usemi_enc(), ui::usemi_dec());
    lemma_aligned_format(ui::usemi_wf(), lift_enc(ui::usemi_enc()), lift_dec(ui::usemi_dec()));
}

// ------------------------------------------ the indefinite length case, 11.5.7.4
//
// `n - lb` in `L` octets, the fewest that hold it (11.3.6), after `L` itself
// as a constrained whole number of range 1..M, where M is the octets the
// range needs (13.2.6 a). That range is at most 8, so `L` is a bit-field of
// at most 3 bits and is not aligned; the octets are.
//
// Ranges up to 2^56 are built, as UPER's constrained INTEGER is: the octets
// are then at most 7, and one `uint` field holds them.

pub open spec fn cb_d(lb: int, ub: int) -> nat { (ub - lb) as nat }
pub open spec fn cb_m(lb: int, ub: int) -> nat { uoct(cb_d(lb, ub)) }
/// The bits of a constrained whole number of range 1..m (11.5.7.1).
pub open spec fn cb_w(m: nat) -> nat { if m <= 2 { 1 } else if m <= 4 { 2 } else { 3 } }

/// When the case applies, and what is built of it.
pub open spec fn cb_ok(lb: int, ub: int) -> bool {
    &&& i64::MIN <= lb < ub <= i64::MAX
    &&& 0x1_0000 <= ub - lb < 0x100_0000_0000_0000
}

// the length, 1..m, as `L - 1` in cb_w(m) bits
pub open spec fn cbl_ok(m: nat) -> spec_fn(u64) -> bool { |v: u64| (v as nat) + 1 <= m }
pub open spec fn cbl_to() -> spec_fn(u64) -> u64 { |v: u64| (v + 1) as u64 }
pub open spec fn cbl_from() -> spec_fn(u64) -> u64 { |l: u64| (l - 1) as u64 }
pub open spec fn cbl_base_wf(m: nat) -> Wf<u64> { restrict_wf(uint_wf(cb_w(m)), cbl_ok(m)) }
pub open spec fn cbl_base_dec(m: nat) -> Dec<u64> { restrict_dec(uint_dec(cb_w(m)), cbl_ok(m)) }
pub open spec fn cbl_wf(m: nat) -> Wf<u64> { map_wf(cbl_base_wf(m), cbl_to(), cbl_from()) }
pub open spec fn cbl_enc(m: nat) -> Enc<u64> { map_enc(uint_enc(cb_w(m)), cbl_from()) }
pub open spec fn cbl_dec(m: nat) -> Dec<u64> { map_dec(cbl_base_dec(m), cbl_to()) }

// the octets: `8 L` bits, octet-aligned, and exactly the fewest
pub open spec fn cbo_ok(l: u64) -> spec_fn(u64) -> bool { |u: u64| uoct(u as nat) == l as nat }
pub open spec fn cbo_wf(l: u64) -> Wf<u64> { aligned_wf(restrict_wf(uint_wf(8 * l as nat), cbo_ok(l))) }
pub open spec fn cbo_enc(l: u64) -> Enc<u64> { aligned_enc(uint_enc(8 * l as nat)) }
pub open spec fn cbo_dec(l: u64) -> Dec<u64> { aligned_dec(restrict_dec(uint_dec(8 * l as nat), cbo_ok(l))) }
pub open spec fn cbo_wf_f() -> spec_fn(u64) -> Wf<u64> { |l: u64| cbo_wf(l) }
pub open spec fn cbo_enc_f() -> spec_fn(u64) -> Enc<u64> { |l: u64| cbo_enc(l) }
pub open spec fn cbo_dec_f() -> spec_fn(u64) -> Dec<u64> { |l: u64| cbo_dec(l) }

pub open spec fn cbf_wf(m: nat) -> Wf<(u64, u64)> { dep_wf(cbl_wf(m), cbo_wf_f()) }
pub open spec fn cbf_enc(m: nat) -> Enc<(u64, u64)> { dep_enc(cbl_enc(m), cbo_enc_f()) }
pub open spec fn cbf_dec(m: nat) -> Dec<(u64, u64)> { dep_dec(cbl_dec(m), cbo_dec_f()) }

// `(L, u)` as `u`, and at most the range
pub open spec fn cbu_to() -> spec_fn((u64, u64)) -> u64 { |t: (u64, u64)| t.1 }
pub open spec fn cbu_from() -> spec_fn(u64) -> (u64, u64) { |u: u64| (uoct(u as nat) as u64, u) }
pub open spec fn cb_le(d: nat) -> spec_fn(u64) -> bool { |u: u64| u as nat <= d }
pub open spec fn cbu_wf(lb: int, ub: int) -> Wf<u64> {
    restrict_wf(map_wf(cbf_wf(cb_m(lb, ub)), cbu_to(), cbu_from()), cb_le(cb_d(lb, ub)))
}
pub open spec fn cbu_enc(lb: int, ub: int) -> Enc<u64> { map_enc(cbf_enc(cb_m(lb, ub)), cbu_from()) }
pub open spec fn cbu_dec(lb: int, ub: int) -> Dec<u64> {
    restrict_dec(map_dec(cbf_dec(cb_m(lb, ub)), cbu_to()), cb_le(cb_d(lb, ub)))
}

pub open spec fn cwn_big_wf(lb: int, ub: int) -> Wf<i64> { map_wf(cbu_wf(lb, ub), ut::ir_to(lb), ut::ir_from(lb)) }
pub open spec fn cwn_big_enc(lb: int, ub: int) -> Enc<i64> { map_enc(cbu_enc(lb, ub), ut::ir_from(lb)) }
pub open spec fn cwn_big_dec(lb: int, ub: int) -> Dec<i64> { map_dec(cbu_dec(lb, ub), ut::ir_to(lb)) }

/// The octets a range of more than 64K needs, and the width of their count.
pub proof fn lemma_cb_m(lb: int, ub: int)
    requires cb_ok(lb, ub),
    ensures
        3 <= cb_m(lb, ub) <= 7,
        cb_w(cb_m(lb, ub)) == 2 || cb_w(cb_m(lb, ub)) == 3,
        cb_m(lb, ub) <= p2(cb_w(cb_m(lb, ub))),
{
    lemma_p2_octets();
    reveal_with_fuel(p2, 4);
}

/// Fewer octets for a smaller value.
pub proof fn lemma_uoct_mono(u: nat, d: nat)
    requires u <= d,
    ensures uoct(u) <= uoct(d),
{
}

proof fn lemma_cbl_format(m: nat)
    requires 1 <= m <= p2(cb_w(m)), m <= 8,
    ensures is_format(cbl_wf(m), cbl_enc(m), cbl_dec(m)),
{
    let w = cb_w(m);
    lemma_uint_format(w);
    lemma_restrict_format(uint_wf(w), uint_enc(w), uint_dec(w), cbl_ok(m));
    assert forall|v: u64| cbl_base_wf(m)(v) implies #[trigger] cbl_from()(cbl_to()(v)) == v by {
        assert(cbl_ok(m)(v));
    }
    lemma_map_format(cbl_base_wf(m), uint_enc(w), cbl_base_dec(m), cbl_to(), cbl_from());
}

/// A length that is well formed is 1..m.
proof fn lemma_cbl_wf(m: nat, l: u64)
    requires cbl_wf(m)(l), m <= 8,
    ensures 1 <= l as nat <= m,
{
    let v = cbl_from()(l);
    assert(cbl_base_wf(m)(v) && cbl_to()(v) == l);
    assert(cbl_ok(m)(v));
}

proof fn lemma_cbl_wf_iff(m: nat, l: u64)
    requires 1 <= l as nat <= m, m <= p2(cb_w(m)),
    ensures cbl_wf(m)(l),
{
    let v = cbl_from()(l);
    assert(v as nat == l as nat - 1);
    assert(uint_wf(cb_w(m))(v));
    assert(cbl_base_wf(m)(v));
}

proof fn lemma_cbo_format(l: u64)
    requires 1 <= l <= 7,
    ensures is_format(cbo_wf(l), cbo_enc(l), cbo_dec(l)),
{
    let n = 8 * l as nat;
    lemma_uint_format(n);
    lemma_restrict_format(uint_wf(n), uint_enc(n), uint_dec(n), cbo_ok(l));
    lemma_aligned_format(restrict_wf(uint_wf(n), cbo_ok(l)), uint_enc(n), restrict_dec(uint_dec(n), cbo_ok(l)));
}

proof fn lemma_cbf_format(m: nat)
    requires 1 <= m <= 7, m <= p2(cb_w(m)),
    ensures is_format(cbf_wf(m), cbf_enc(m), cbf_dec(m)),
{
    lemma_cbl_format(m);
    assert forall|l: u64| cbl_wf(m)(l) implies
        is_format(#[trigger] cbo_wf_f()(l), cbo_enc_f()(l), cbo_dec_f()(l))
    by {
        lemma_cbl_wf(m, l);
        lemma_cbo_format(l);
    }
    lemma_dep_format(cbl_wf(m), cbl_enc(m), cbl_dec(m), cbo_wf_f(), cbo_enc_f(), cbo_dec_f());
}

pub proof fn lemma_cwn_big_format(lb: int, ub: int)
    requires cb_ok(lb, ub),
    ensures is_format(cwn_big_wf(lb, ub), cwn_big_enc(lb, ub), cwn_big_dec(lb, ub)),
{
    let m = cb_m(lb, ub);
    let d = cb_d(lb, ub);
    lemma_cb_m(lb, ub);
    lemma_cbf_format(m);
    assert forall|t: (u64, u64)| cbf_wf(m)(t) implies #[trigger] cbu_from()(cbu_to()(t)) == t by {
        lemma_dep_wf_val(cbl_wf(m), cbo_wf_f(), t.0, t.1);
        lemma_aligned_wf_val(restrict_wf(uint_wf(8 * t.0 as nat), cbo_ok(t.0)), t.1);
        assert(cbo_ok(t.0)(t.1));
    }
    lemma_map_format(cbf_wf(m), cbf_enc(m), cbf_dec(m), cbu_to(), cbu_from());
    lemma_restrict_format(map_wf(cbf_wf(m), cbu_to(), cbu_from()), cbu_enc(lb, ub),
                          map_dec(cbf_dec(m), cbu_to()), cb_le(d));
    assert forall|u: u64| cbu_wf(lb, ub)(u) implies #[trigger] ut::ir_from(lb)(ut::ir_to(lb)(u)) == u by {
        assert(cb_le(d)(u));
    }
    lemma_map_format(cbu_wf(lb, ub), cbu_enc(lb, ub), cbu_dec(lb, ub), ut::ir_to(lb), ut::ir_from(lb));
}

/// The well-formed values are exactly the ones in the range.
pub proof fn lemma_cwn_big_wf_iff(lb: int, ub: int, x: i64)
    requires cb_ok(lb, ub),
    ensures cwn_big_wf(lb, ub)(x) <==> (lb <= x as int <= ub),
{
    let m = cb_m(lb, ub);
    let d = cb_d(lb, ub);
    lemma_cb_m(lb, ub);
    let u = ut::ir_from(lb)(x);
    if lb <= x as int <= ub {
        assert(u as nat == x as int - lb);
        let l = uoct(u as nat);
        lemma_uoct(u as nat);
        lemma_uoct_mono(u as nat, d);
        lemma_cbl_wf_iff(m, l as u64);
        lemma_aligned_wf_val(restrict_wf(uint_wf(8 * l), cbo_ok(l as u64)), u);
        lemma_dep_wf_val(cbl_wf(m), cbo_wf_f(), l as u64, u);
        assert(cbu_from()(u) == (l as u64, u));
        assert(cbu_wf(lb, ub)(u));
    } else if cwn_big_wf(lb, ub)(x) {
        assert(cbu_wf(lb, ub)(u) && ut::ir_to(lb)(u) == x);
        assert(cb_le(d)(u));
    }
}

/// What `cwn_big` writes, flat: the count, the padding after it, the octets.
pub proof fn lemma_cwn_big_enc_val(lb: int, ub: int, pos: nat, x: i64)
    requires cb_ok(lb, ub), lb <= x as int <= ub,
    ensures ({
        let u = (x as int - lb) as nat;
        let l = uoct(u);
        let w = cb_w(cb_m(lb, ub));
        cwn_big_enc(lb, ub)(pos, x)
            == crate::uper::prim::uint_enc(w)((l - 1) as u64) + zeros(pad(pos + w))
               + crate::uper::prim::uint_enc(8 * l)(u as u64)
    }),
{
    let m = cb_m(lb, ub);
    let w = cb_w(m);
    let u = ut::ir_from(lb)(x);
    let l = uoct(u as nat) as u64;
    assert(cwn_big_enc(lb, ub)(pos, x) == cbu_enc(lb, ub)(pos, u));
    assert(cbu_enc(lb, ub)(pos, u) == cbf_enc(m)(pos, (l, u)));
    let p1 = pos + cbl_enc(m)(pos, l).len();
    assert(cbf_enc(m)(pos, (l, u)) == cbl_enc(m)(pos, l) + cbo_enc(l)(p1, u));
    assert(cbl_enc(m)(pos, l) == crate::uper::prim::uint_enc(w)((l - 1) as u64));
    crate::uper::prim::lemma_uint_enc_len(w, (l - 1) as u64);
    lemma_aligned_enc_val(uint_enc(8 * l as nat), p1, u);
}

} // verus!

verus! {

// ----------------------------------------------------------- exec: read

impl<'a> BitReader<'a> {
    /// Refines `auint_dec(n)`.
    pub fn read_auint(&mut self, n: usize) -> (res: Option<u64>)
        requires old(self).wf(), 1 <= n <= 56,
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => auint_dec(n as nat)(old(self).at())
                    == Some::<(u64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => auint_dec(n as nat)(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = uint_dec(n as nat);
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_none(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_step(d, i, (self.pos - p0) as nat);
        }
        self.read_uint(n)
    }

    /// Refines `aint_range_dec(lb, ub, n)`.
    pub fn read_aint_range(&mut self, lb: i64, ub: i64, n: usize) -> (res: Option<i64>)
        requires old(self).wf(), 1 <= n <= 56, lb < ub, (ub as int) - (lb as int) < p2(n as nat),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => aint_range_dec(lb as int, ub as int, n as nat)(old(self).at())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => aint_range_dec(lb as int, ub as int, n as nat)(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = int_range_dec(lb as int, ub as int, n as nat);
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_none(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_step(d, i, (self.pos - p0) as nat);
        }
        self.read_int_range(lb, ub, n)
    }

    /// Refines `semi_dec(lb)`.
    pub fn read_asemi(&mut self, lb: i64) -> (res: Option<i64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => semi_dec(lb as int)(old(self).at())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => semi_dec(lb as int)(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = lift_dec(ui::semi_dec(lb as int));
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_none(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_step(d, i, (self.pos - p0) as nat);
        }
        self.read_semi(lb)
    }

    /// Refines `uc_dec()`.
    pub fn read_auc(&mut self) -> (res: Option<i64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => uc_dec()(old(self).at())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => uc_dec()(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = lift_dec(ui::uc_dec());
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_none(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_step(d, i, (self.pos - p0) as nat);
        }
        self.read_uc()
    }

    /// Refines `usemi_dec()`.
    pub fn read_ausemi(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => usemi_dec()(old(self).at())
                    == Some::<(u64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => usemi_dec()(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = lift_dec(ui::usemi_dec());
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_none(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_step(d, i, (self.pos - p0) as nat);
        }
        self.read_usemi()
    }

    /// Refines `cwn_big_dec(lb, ub)`: a constrained INTEGER whose range is
    /// over 64K.
    pub fn read_cwn_big(&mut self, lb: i64, ub: i64) -> (res: Option<i64>)
        requires old(self).wf(), cb_ok(lb as int, ub as int),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => cwn_big_dec(lb as int, ub as int)(old(self).at())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => cwn_big_dec(lb as int, ub as int)(old(self).at()) is None,
            },
    {
        let ghost lbi = lb as int;
        let ghost ubi = ub as int;
        let ghost m = cb_m(lbi, ubi);
        let ghost i = self.at();
        let ghost p0 = self.pos;
        proof { lemma_cb_m(lbi, ubi); lemma_p2_octets(); }
        let d: u64 = ((ub as i128) - (lb as i128)) as u64;
        let mm = ui::uoct_x(d);
        let w: usize = if mm <= 2 { 1 } else if mm <= 4 { 2 } else { 3 };
        proof { assert(mm as nat == m); assert(w as nat == cb_w(m)); }
        let ghost fd = cbf_dec(m);
        let ghost ud = map_dec(fd, cbu_to());
        // the count
        let v = match self.read_uint(w) {
            Some(v) => v,
            None => {
                proof {
                    lemma_restrict_dec_none(uint_dec(w as nat), cbl_ok(m), i);
                    lemma_map_dec_none(cbl_base_dec(m), cbl_to(), i);
                    lemma_dep_dec_none_fst(cbl_dec(m), cbo_dec_f(), i);
                    lemma_map_dec_none(fd, cbu_to(), i);
                    lemma_restrict_dec_none(ud, cb_le(d as nat), i);
                    lemma_map_dec_none(cbu_dec(lbi, ubi), ut::ir_to(lbi), i);
                }
                return None;
            }
        };
        if v >= mm {
            proof {
                lemma_restrict_dec_none(uint_dec(w as nat), cbl_ok(m), i);
                lemma_map_dec_none(cbl_base_dec(m), cbl_to(), i);
                lemma_dep_dec_none_fst(cbl_dec(m), cbo_dec_f(), i);
                lemma_map_dec_none(fd, cbu_to(), i);
                lemma_restrict_dec_none(ud, cb_le(d as nat), i);
                lemma_map_dec_none(cbu_dec(lbi, ubi), ut::ir_to(lbi), i);
            }
            return None;
        }
        let l = v + 1;
        proof {
            lemma_restrict_dec_some(uint_dec(w as nat), cbl_ok(m), i, v, w as nat, Flg::SameVer);
            lemma_map_dec_some(cbl_base_dec(m), cbl_to(), i, v, w as nat, Flg::SameVer);
            lemma_rem_skip(self.buf@, p0 as nat, w as nat);
        }
        let ghost i1 = self.at();
        let ghost p1 = self.pos;
        proof { assert(i1 == adv(i, w as nat)); }
        let ghost od = restrict_dec(uint_dec(8 * l as nat), cbo_ok(l));
        // the octets, aligned
        let ghost got: Option<u64> = None;
        let ok_align = self.read_align();
        if !ok_align {
            proof {
                lemma_aligned_none(od, i1);
                lemma_dep_dec_none_snd(cbl_dec(m), cbo_dec_f(), i, l, w as nat, Flg::SameVer);
                lemma_map_dec_none(fd, cbu_to(), i);
                lemma_restrict_dec_none(ud, cb_le(d as nat), i);
                lemma_map_dec_none(cbu_dec(lbi, ubi), ut::ir_to(lbi), i);
            }
            return None;
        }
        let ghost kp = (self.pos - p1) as nat;
        proof {
            lemma_rem_skip(self.buf@, p1 as nat, kp);
            lemma_aligned_step(od, i1, kp);
        }
        let ghost i2 = self.at();
        let ghost p2 = self.pos;
        let nb: usize = (8 * l) as usize;
        let u = match self.read_uint(nb) {
            Some(u) => u,
            None => {
                proof {
                    lemma_restrict_dec_none(uint_dec(nb as nat), cbo_ok(l), i2);
                    lemma_dep_dec_none_snd(cbl_dec(m), cbo_dec_f(), i, l, w as nat, Flg::SameVer);
                    lemma_map_dec_none(fd, cbu_to(), i);
                    lemma_restrict_dec_none(ud, cb_le(d as nat), i);
                    lemma_map_dec_none(cbu_dec(lbi, ubi), ut::ir_to(lbi), i);
                }
                return None;
            }
        };
        proof {
            crate::bits::prim_read::lemma_p2_mono(nb as nat, 56);
            crate::bits::prim_read::lemma_p2_56();
            crate::bits::bitspec::lemma_bits_val_bound(i2.1.take(nb as int));
        }
        if ui::uoct_x(u) != l {
            proof {
                lemma_restrict_dec_none(uint_dec(nb as nat), cbo_ok(l), i2);
                lemma_dep_dec_none_snd(cbl_dec(m), cbo_dec_f(), i, l, w as nat, Flg::SameVer);
                lemma_map_dec_none(fd, cbu_to(), i);
                lemma_restrict_dec_none(ud, cb_le(d as nat), i);
                lemma_map_dec_none(cbu_dec(lbi, ubi), ut::ir_to(lbi), i);
            }
            { self.fail("constrained INTEGER: not in the fewest octets (X.691 11.5.7.4, 11.3.6)"); return None; }
        }
        let ghost k = (self.pos - p0) as nat;
        proof {
            lemma_restrict_dec_some(uint_dec(nb as nat), cbo_ok(l), i2, u, nb as nat, Flg::SameVer);
            lemma_dep_dec_some(cbl_dec(m), cbo_dec_f(), i, l, w as nat, Flg::SameVer, u,
                               (self.pos - p1) as nat, Flg::SameVer);
            lemma_map_dec_some(fd, cbu_to(), i, (l, u), k, Flg::SameVer);
        }
        if u > d {
            proof {
                lemma_restrict_dec_none(ud, cb_le(d as nat), i);
                lemma_map_dec_none(cbu_dec(lbi, ubi), ut::ir_to(lbi), i);
            }
            { self.fail("constrained INTEGER: above the upper bound"); return None; }
        }
        proof {
            lemma_restrict_dec_some(ud, cb_le(d as nat), i, u, k, Flg::SameVer);
            lemma_map_dec_some(cbu_dec(lbi, ubi), ut::ir_to(lbi), i, u, k, Flg::SameVer);
        }
        Some(((lb as i128) + (u as i128)) as i64)
    }
}

// ----------------------------------------------------------- exec: write

impl BitWriter {
    /// Refines `auint_enc(n)`.
    pub fn write_auint(&mut self, n: usize, v: u64) -> (ok: bool)
        requires old(self).wf(), 1 <= n <= 56, uint_wf(n as nat)(v),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + auint_enc(n as nat)(old(self).pos as nat, v),
    {
        proof { lemma_aligned_enc_val(uint_enc(n as nat), old(self).pos as nat, v); }
        if !self.write_align() { return false; }
        self.write_uint(n, v)
    }

    /// Refines `aint_range_enc(lb, ub, n)`.
    pub fn write_aint_range(&mut self, lb: i64, ub: i64, n: usize, v: i64) -> (ok: bool)
        requires old(self).wf(), 1 <= n <= 56, lb < ub, (ub as int) - (lb as int) < p2(n as nat),
                 lb <= v <= ub,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written()
                + aint_range_enc(lb as int, ub as int, n as nat)(old(self).pos as nat, v),
    {
        let ghost p0 = self.pos as nat;
        proof { lemma_aligned_enc_val(int_range_enc(lb as int, ub as int, n as nat), p0, v); }
        if !self.write_align() { return false; }
        self.write_int_range(lb, ub, n, v)
    }

    /// Refines `semi_enc(lb)`.
    pub fn write_asemi(&mut self, lb: i64, x: i64) -> (ok: bool)
        requires old(self).wf(), lb <= x,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + semi_enc(lb as int)(old(self).pos as nat, x),
    {
        proof { lemma_aligned_enc_val(lift_enc(ui::semi_enc(lb as int)), old(self).pos as nat, x); }
        if !self.write_align() { return false; }
        self.write_semi(lb, x)
    }

    /// Refines `uc_enc()`.
    pub fn write_auc(&mut self, v: i64) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + uc_enc()(old(self).pos as nat, v),
    {
        proof { lemma_aligned_enc_val(lift_enc(ui::uc_enc()), old(self).pos as nat, v); }
        if !self.write_align() { return false; }
        self.write_uc(v)
    }

    /// Refines `usemi_enc()`.
    pub fn write_ausemi(&mut self, n: u64) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + usemi_enc()(old(self).pos as nat, n),
    {
        proof { lemma_aligned_enc_val(lift_enc(ui::usemi_enc()), old(self).pos as nat, n); }
        if !self.write_align() { return false; }
        self.write_usemi(n)
    }

    /// Refines `cwn_big_enc(lb, ub)`.
    pub fn write_cwn_big(&mut self, lb: i64, ub: i64, x: i64) -> (ok: bool)
        requires old(self).wf(), cb_ok(lb as int, ub as int), lb <= x <= ub,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written()
                + cwn_big_enc(lb as int, ub as int)(old(self).pos as nat, x),
    {
        let ghost m = cb_m(lb as int, ub as int);
        let ghost p0 = self.pos as nat;
        proof {
            lemma_cb_m(lb as int, ub as int);
            lemma_p2_octets();
            lemma_cwn_big_enc_val(lb as int, ub as int, p0, x);
        }
        let d: u64 = ((ub as i128) - (lb as i128)) as u64;
        let u: u64 = ((x as i128) - (lb as i128)) as u64;
        let mm = ui::uoct_x(d);
        let l = ui::uoct_x(u);
        let w: usize = if mm <= 2 { 1 } else if mm <= 4 { 2 } else { 3 };
        proof {
            assert(mm as nat == m);
            lemma_uoct(u as nat);
            lemma_uoct_mono(u as nat, d as nat);
            assert(l <= mm);
            assert((l - 1) < p2(w as nat));
        }
        let ghost w0 = self.written();
        if !self.write_uint(w, l - 1) { return false; }
        let ghost w1 = self.written();
        if !self.write_align() { return false; }
        let ghost w2 = self.written();
        proof { assert(l <= 7); }
        if !self.write_uint((8 * l) as usize, u) { return false; }
        proof {
            assert(self.written() =~= w0 + crate::uper::prim::uint_enc(w as nat)((l - 1) as u64)
                   + zeros(pad(p0 + w as nat)) + crate::uper::prim::uint_enc(8 * l as nat)(u));
        }
        true
    }
}

} // verus!

verus! {

// ------------------------------------- well-formedness, for every value at once
//
// What a generated encoder's precondition needs from its field's `wf`: the
// value is in the range. Stated as one quantified fact so it can go in a
// function's preamble.

pub proof fn lemma_aint_range_wf_all(lb: int, ub: int, n: nat)
    requires 1 <= n <= 56, lb < ub, ub - lb < p2(n), i64::MIN <= lb, ub <= i64::MAX,
    ensures forall|x: i64| #[trigger] aint_range_wf(lb, ub, n)(x) <==> (lb <= x as int <= ub),
{
    assert forall|x: i64| #[trigger] aint_range_wf(lb, ub, n)(x) <==> (lb <= x as int <= ub) by {
        lemma_aint_range_wf_iff(lb, ub, n, x);
    }
}

pub proof fn lemma_cwn_big_wf_all(lb: int, ub: int)
    requires cb_ok(lb, ub),
    ensures forall|x: i64| #[trigger] cwn_big_wf(lb, ub)(x) <==> (lb <= x as int <= ub),
{
    assert forall|x: i64| #[trigger] cwn_big_wf(lb, ub)(x) <==> (lb <= x as int <= ub) by {
        lemma_cwn_big_wf_iff(lb, ub, x);
    }
}

pub proof fn lemma_semi_wf_all(lb: int)
    ensures forall|x: i64| #[trigger] semi_wf(lb)(x) <==> lb <= x as int,
{
    assert forall|x: i64| #[trigger] semi_wf(lb)(x) <==> lb <= x as int by {
        lemma_semi_wf_iff(lb, x);
    }
}

pub proof fn lemma_uc_wf_every()
    ensures forall|x: i64| #[trigger] uc_wf()(x),
{
    assert forall|x: i64| #[trigger] uc_wf()(x) by { lemma_uc_wf_all(x); }
}

} // verus!
