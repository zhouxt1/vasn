//! INTEGERs that carry a length: X.691 11.7, 11.8, 13.1, 13.2.3, 13.2.4.
//!
//! * **semi-constrained** (`INTEGER (lb..MAX)`, 13.2.3, 11.7): `n - lb` as a
//!   non-negative binary integer in the minimum number of octets (11.3.6).
//! * **unconstrained** (`INTEGER`, 13.2.4, 11.8): `n` as a 2's-complement
//!   binary integer in the minimum number of octets (11.4.6).
//!
//! Each is preceded by an unconstrained length determinant holding the octet
//! count (13.2.6 b). In UNALIGNED PER nothing is octet-aligned.
//!
//! * **extensible** (`INTEGER (lb..ub, ...)` and the like, 13.1): one bit, 0 if
//!   the value is in the root and then the root's own encoding, 1 if not and
//!   then the unconstrained encoding. A value in the root is always encoded as
//!   one (10.4.3), so the second branch only admits values outside it.
//!
//! Minimality is what makes the length canonical: a decoder that accepted a
//! value in more octets than needed would accept two encodings of it.
//!
//! The values are `i64`, so at most 8 octets are ever needed. X.691 itself
//! puts no bound on an unconstrained INTEGER: a valid encoding of a value
//! outside `i64` has more octets than 8, and is rejected rather than
//! truncated.
use vstd::prelude::*;
use crate::bitspec::*;
use crate::format::*;
use crate::prim::*;
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use crate::prim_write::{bits_seq, lemma_bits_seq_val, lemma_bits_val_inj};
use crate::lendet::*;
use crate::term::*;

verus! {

broadcast use {format_steps, map_steps};

// ------------------------------------------------------------------ p2 facts

/// The powers of two at octet boundaries, and one below each.
pub proof fn lemma_p2_octets()
    ensures
        p2(7) == 0x80, p2(8) == 0x100,
        p2(15) == 0x8000, p2(16) == 0x1_0000,
        p2(23) == 0x80_0000, p2(24) == 0x100_0000,
        p2(31) == 0x8000_0000, p2(32) == 0x1_0000_0000,
        p2(39) == 0x80_0000_0000, p2(40) == 0x100_0000_0000,
        p2(47) == 0x8000_0000_0000, p2(48) == 0x1_0000_0000_0000,
        p2(55) == 0x80_0000_0000_0000, p2(56) == 0x100_0000_0000_0000,
        p2(63) == 0x8000_0000_0000_0000, p2(64) == 0x1_0000_0000_0000_0000,
{
    reveal_with_fuel(p2, 9);
    assert(p2(7) == 0x80);
    assert(p2(8) == 0x100);
    lemma_p2_adds(8, 8);
    lemma_p2_adds(8, 7);
    lemma_p2_adds(16, 8);
    lemma_p2_adds(16, 7);
    lemma_p2_adds(24, 8);
    lemma_p2_adds(24, 7);
    lemma_p2_adds(32, 8);
    lemma_p2_adds(32, 7);
    lemma_p2_adds(40, 8);
    lemma_p2_adds(40, 7);
    lemma_p2_adds(48, 8);
    lemma_p2_adds(48, 7);
    lemma_p2_adds(56, 8);
    lemma_p2_adds(56, 7);
}

/// `p2(8k)` is twice `p2(8k - 1)`, and at most `2^64`, for `1 <= k <= 8`.
pub proof fn lemma_p2_oct(k: nat)
    requires 1 <= k <= 8,
    ensures
        p2(8 * k) == 2 * p2((8 * k - 1) as nat),
        p2(8 * k) <= 0x1_0000_0000_0000_0000nat,
        p2((8 * k - 1) as nat) <= 0x8000_0000_0000_0000nat,
{
    lemma_p2_octets();
    lemma_p2_adds((8 * k - 1) as nat, 1);
    assert(p2(1) == 2) by { reveal_with_fuel(p2, 2); }
}

// ------------------------------------------------ the octet-counted value

/// A length (1 to 8 octets, by the general determinant) and then that many
/// octets holding `u`: 11.7.4 and 11.8.3's field with 13.2.6 b's length.
pub open spec fn lo_enc(k: nat, u: nat) -> Seq<bool> {
    gld_enc()(k as u64) + bits_seq(u as u64, 8 * k)
}

/// The octet count, the value of the octets, and the bits consumed.
pub open spec fn lo_dec(b: Seq<bool>) -> Option<(nat, nat, nat)> {
    match gld_dec()(b) {
        Some((k, kl, _)) =>
            if 1 <= k <= 8 && kl + 8 * (k as nat) <= b.len() {
                Some((k as nat, bits_val(b.skip(kl as int).take(8 * k as int)), (kl + 8 * (k as nat)) as nat))
            } else {
                None
            },
        None => None,
    }
}

pub proof fn lemma_lo_surj(k: nat, u: nat, rest: Seq<bool>)
    requires 1 <= k <= 8, u < p2(8 * k),
    ensures lo_dec(lo_enc(k, u) + rest) == Some::<(nat, nat, nat)>((k, u, lo_enc(k, u).len())),
{
    lemma_gld_format();
    lemma_gld_wf_iff(k as u64);
    lemma_p2_oct(k);
    let g = gld_enc()(k as u64);
    let bs = bits_seq(u as u64, 8 * k);
    let b = lo_enc(k, u) + rest;
    assert(b =~= g + (bs + rest));
    assert(gld_dec()(g + (bs + rest)) == Some::<(u64, nat, Flg)>((k as u64, g.len(), Flg::SameVer)));
    lemma_take_add(g, bs + rest);
    lemma_take_add(bs, rest);
    assert(b.skip(g.len() as int) =~= bs + rest);
    assert(b.skip(g.len() as int).take(8 * k as int) =~= bs);
    lemma_bits_seq_val(u as u64, 8 * k);
}

pub proof fn lemma_lo_inj(b: Seq<bool>)
    requires lo_dec(b) is Some,
    ensures ({
        let (k, u, n) = lo_dec(b).unwrap();
        &&& 1 <= k <= 8
        &&& u < p2(8 * k)
        &&& n <= b.len()
        &&& b.take(n as int) == lo_enc(k, u)
    }),
{
    lemma_gld_format();
    lemma_gld_dec_same(b);
    let (k, kl, _) = gld_dec()(b).unwrap();
    assert(b.take(kl as int) == gld_enc()(k));
    let t = b.skip(kl as int).take(8 * k as int);
    let u = bits_val(t);
    lemma_bits_val_bound(t);
    lemma_p2_oct(k as nat);
    lemma_bits_seq_val(u as u64, 8 * (k as nat));
    lemma_bits_val_inj(bits_seq(u as u64, 8 * (k as nat)), t);
    lemma_take_split(b, kl, 8 * (k as nat));
}

// ----------------------------------------------- minimal octets (11.3, 11.4)

/// 11.3.6: the octets for `u >= 0`, at least one, no leading zero octet.
pub open spec fn uoct(u: nat) -> nat {
    if u < p2(8) { 1 } else if u < p2(16) { 2 } else if u < p2(24) { 3 } else if u < p2(32) { 4 }
    else if u < p2(40) { 5 } else if u < p2(48) { 6 } else if u < p2(56) { 7 } else { 8 }
}

/// `v` has a `k`-octet 2's-complement representation.
pub open spec fn sfits(v: int, k: nat) -> bool {
    -(p2((8 * k - 1) as nat) as int) <= v < p2((8 * k - 1) as nat) as int
}

/// 11.4.6: the octets for `v`, the leading nine bits not all equal.
pub open spec fn soct(v: int) -> nat {
    if sfits(v, 1) { 1 } else if sfits(v, 2) { 2 } else if sfits(v, 3) { 3 } else if sfits(v, 4) { 4 }
    else if sfits(v, 5) { 5 } else if sfits(v, 6) { 6 } else if sfits(v, 7) { 7 } else { 8 }
}

/// `v` as `k` octets of 2's complement, read as unsigned (11.4.4).
pub open spec fn tc(v: int, k: nat) -> nat {
    if v < 0 { (v + p2(8 * k)) as nat } else { v as nat }
}

/// `k` octets holding `u`, read as 2's complement (11.4.4).
pub open spec fn sgn(u: nat, k: nat) -> int {
    if u >= p2((8 * k - 1) as nat) { u - p2(8 * k) } else { u as int }
}

pub proof fn lemma_uoct(u: nat)
    requires u < 0x1_0000_0000_0000_0000nat,
    ensures 1 <= uoct(u) <= 8, u < p2(8 * uoct(u)),
{
    lemma_p2_octets();
}

pub proof fn lemma_soct(v: int)
    requires i64::MIN <= v <= i64::MAX,
    ensures 1 <= soct(v) <= 8, sfits(v, soct(v)),
{
    lemma_p2_octets();
}

/// The two readings are inverses: of each other on a value that fits, and on
/// any `k` octets.
pub proof fn lemma_tc_sgn(v: int, k: nat)
    requires 1 <= k <= 8, sfits(v, k),
    ensures tc(v, k) < p2(8 * k), sgn(tc(v, k), k) == v,
{
    lemma_p2_oct(k);
}

pub proof fn lemma_sgn_tc(u: nat, k: nat)
    requires 1 <= k <= 8, u < p2(8 * k),
    ensures sfits(sgn(u, k), k), tc(sgn(u, k), k) == u, i64::MIN <= sgn(u, k) <= i64::MAX,
{
    lemma_p2_oct(k);
}

// ------------------------------------------------------- semi-constrained

pub open spec fn semi_ok(lb: int) -> spec_fn(i64) -> bool { |x: i64| lb <= x as int }

pub open spec fn semi_wf(lb: int) -> Wf<i64> { |x: i64| lb <= x as int }

pub open spec fn semi_enc(lb: int) -> Enc<i64> {
    |x: i64| lo_enc(uoct((x as int - lb) as nat), (x as int - lb) as nat)
}

pub open spec fn semi_dec(lb: int) -> Dec<i64> {
    |b: Seq<bool>| match lo_dec(b) {
        Some((k, u, n)) =>
            if uoct(u) == k && lb + u <= i64::MAX {
                Some(((lb + u) as i64, n, Flg::SameVer))
            } else {
                None
            },
        None => None,
    }
}

pub proof fn lemma_semi_format(lb: int)
    requires i64::MIN <= lb <= i64::MAX,
    ensures is_format(semi_wf(lb), semi_enc(lb), semi_dec(lb)),
{
    assert forall|x: i64, rest: Seq<bool>| semi_wf(lb)(x) implies
        #[trigger] semi_dec(lb)(semi_enc(lb)(x) + rest)
            == Some::<(i64, nat, Flg)>((x, semi_enc(lb)(x).len(), Flg::SameVer))
    by {
        let u = (x as int - lb) as nat;
        lemma_uoct(u);
        lemma_lo_surj(uoct(u), u, rest);
    }
    assert forall|b: Seq<bool>| (#[trigger] semi_dec(lb)(b)).is_some() implies {
        let x = semi_dec(lb)(b).unwrap().0;
        let k = semi_dec(lb)(b).unwrap().1;
        &&& semi_wf(lb)(x) && k <= b.len()
        &&& semi_dec(lb)(b).unwrap().2 is SameVer ==> b.take(k as int) == semi_enc(lb)(x)
    } by {
        lemma_lo_inj(b);
    }
}

// ------------------------------------------------------------ unconstrained

pub open spec fn uc_wf() -> Wf<i64> { |v: i64| true }

pub open spec fn uc_enc() -> Enc<i64> {
    |v: i64| lo_enc(soct(v as int), tc(v as int, soct(v as int)))
}

pub open spec fn uc_dec() -> Dec<i64> {
    |b: Seq<bool>| match lo_dec(b) {
        Some((k, u, n)) =>
            if soct(sgn(u, k)) == k {
                Some((sgn(u, k) as i64, n, Flg::SameVer))
            } else {
                None
            },
        None => None,
    }
}

pub proof fn lemma_uc_format()
    ensures is_format(uc_wf(), uc_enc(), uc_dec()),
{
    assert forall|v: i64, rest: Seq<bool>| uc_wf()(v) implies
        #[trigger] uc_dec()(uc_enc()(v) + rest)
            == Some::<(i64, nat, Flg)>((v, uc_enc()(v).len(), Flg::SameVer))
    by {
        let k = soct(v as int);
        lemma_soct(v as int);
        lemma_tc_sgn(v as int, k);
        lemma_lo_surj(k, tc(v as int, k), rest);
    }
    assert forall|b: Seq<bool>| (#[trigger] uc_dec()(b)).is_some() implies {
        let v = uc_dec()(b).unwrap().0;
        let k = uc_dec()(b).unwrap().1;
        &&& uc_wf()(v) && k <= b.len()
        &&& uc_dec()(b).unwrap().2 is SameVer ==> b.take(k as int) == uc_enc()(v)
    } by {
        lemma_lo_inj(b);
        let (k, u, n) = lo_dec(b).unwrap();
        lemma_sgn_tc(u, k);
    }
}

// --------------------------------------------------------------- extensible

/// Outside the root: the only values the extension branch admits (10.4.3).
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

/// X.691 13.1 over any root format whose values are exactly `inr`'s.
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

/// Every value is well formed: in the root or out of it.
pub proof fn lemma_xint_wf_all(rw: Wf<i64>, inr: spec_fn(i64) -> bool, v: i64)
    requires forall|v: i64| #[trigger] rw(v) == inr(v),
    ensures xint_wf(rw, inr)(v),
{
    lemma_bool_wf_all(!inr(v));
    lemma_map_wf_val(dep_wf(bool_wf(), xint_alt_wf(rw, inr)), xint_to(), xint_from(inr), v);
    lemma_dep_wf_val(bool_wf(), xint_alt_wf(rw, inr), !inr(v), v);
    lemma_restrict_wf_val(uc_wf(), xint_out(inr), v);
}

} // verus!

verus! {

use crate::cursor::*;
use crate::opt::*;

// ------------------------------------------------------ the roots, named
//
// The extensible INTEGER's root, as the generated code names it: a range, a
// single value, a lower bound only, or everything.

#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum XRoot {
    /// `(lb..ub, ...)`, `lb < ub`, in `n` bits
    Range(i64, i64, usize),
    /// `(c, ...)`
    Const(i64),
    /// `(lb..MAX, ...)`
    Semi(i64),
    /// `(MIN..MAX, ...)`: every value is in the root
    All,
}

pub open spec fn xroot_ok(r: XRoot) -> bool {
    match r {
        XRoot::Range(lb, ub, n) => 1 <= n <= 56 && lb < ub && (ub as int) - (lb as int) < p2(n as nat),
        _ => true,
    }
}

pub open spec fn xroot_wf(r: XRoot) -> Wf<i64> {
    match r {
        XRoot::Range(lb, ub, n) => crate::term::int_range_wf(lb as int, ub as int, n as nat),
        XRoot::Const(c) => unit_wf(c),
        XRoot::Semi(lb) => semi_wf(lb as int),
        XRoot::All => uc_wf(),
    }
}
pub open spec fn xroot_enc(r: XRoot) -> Enc<i64> {
    match r {
        XRoot::Range(lb, ub, n) => crate::term::int_range_enc(lb as int, ub as int, n as nat),
        XRoot::Const(c) => unit_enc(),
        XRoot::Semi(lb) => semi_enc(lb as int),
        XRoot::All => uc_enc(),
    }
}
pub open spec fn xroot_dec(r: XRoot) -> Dec<i64> {
    match r {
        XRoot::Range(lb, ub, n) => crate::term::int_range_dec(lb as int, ub as int, n as nat),
        XRoot::Const(c) => unit_dec(c),
        XRoot::Semi(lb) => semi_dec(lb as int),
        XRoot::All => uc_dec(),
    }
}
pub open spec fn xroot_in(r: XRoot) -> spec_fn(i64) -> bool {
    |v: i64| match r {
        XRoot::Range(lb, ub, _) => lb <= v && v <= ub,
        XRoot::Const(c) => v == c,
        XRoot::Semi(lb) => lb <= v,
        XRoot::All => true,
    }
}

/// An extensible INTEGER (13.1) with root `r`.
pub open spec fn xint_r_wf(r: XRoot) -> Wf<i64> { xint_wf(xroot_wf(r), xroot_in(r)) }
pub open spec fn xint_r_enc(r: XRoot) -> Enc<i64> { xint_enc(xroot_enc(r), xroot_in(r)) }
pub open spec fn xint_r_dec(r: XRoot) -> Dec<i64> { xint_dec(xroot_dec(r), xroot_in(r)) }

pub proof fn lemma_xroot(r: XRoot)
    requires xroot_ok(r),
    ensures
        is_format(xroot_wf(r), xroot_enc(r), xroot_dec(r)),
        forall|v: i64| #[trigger] xroot_wf(r)(v) == xroot_in(r)(v),
{
    match r {
        XRoot::Range(lb, ub, n) => {
            crate::term::lemma_int_range_format(lb as int, ub as int, n as nat);
            assert forall|v: i64| #[trigger] xroot_wf(r)(v) == xroot_in(r)(v) by {
                crate::term::lemma_int_range_wf_iff(lb as int, ub as int, n as nat, v);
            }
        }
        XRoot::Const(c) => {
            lemma_unit_format(c);
            reveal(unit_wf);
        }
        XRoot::Semi(lb) => lemma_semi_format(lb as int),
        XRoot::All => lemma_uc_format(),
    }
}

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

// ------------------------------------------------------ exec counterparts

/// Refines `uoct`.
pub fn uoct_x(u: u64) -> (k: u64)
    ensures k as nat == uoct(u as nat), 1 <= k <= 8,
{
    proof { lemma_p2_octets(); }
    if u < 0x100 { 1 } else if u < 0x1_0000 { 2 } else if u < 0x100_0000 { 3 } else if u < 0x1_0000_0000 { 4 }
    else if u < 0x100_0000_0000 { 5 } else if u < 0x1_0000_0000_0000 { 6 } else if u < 0x100_0000_0000_0000 { 7 } else { 8 }
}

/// Refines `soct`.
pub fn soct_x(v: i64) -> (k: u64)
    ensures k as nat == soct(v as int), 1 <= k <= 8,
{
    proof { lemma_p2_octets(); }
    if -0x80 <= v && v < 0x80 { 1 }
    else if -0x8000 <= v && v < 0x8000 { 2 }
    else if -0x80_0000 <= v && v < 0x80_0000 { 3 }
    else if -0x8000_0000 <= v && v < 0x8000_0000 { 4 }
    else if -0x80_0000_0000 <= v && v < 0x80_0000_0000 { 5 }
    else if -0x8000_0000_0000 <= v && v < 0x8000_0000_0000 { 6 }
    else if -0x80_0000_0000_0000 <= v && v < 0x80_0000_0000_0000 { 7 }
    else { 8 }
}

/// `p2(8k)` and `p2(8k - 1)`, as `u128`.
fn p2_oct_x(k: u64) -> (r: (u128, u128))
    requires 1 <= k <= 8,
    ensures r.0 as nat == p2(8 * (k as nat)), r.1 as nat == p2((8 * (k as nat) - 1) as nat),
{
    proof { lemma_p2_octets(); }
    match k {
        1 => (0x100, 0x80),
        2 => (0x1_0000, 0x8000),
        3 => (0x100_0000, 0x80_0000),
        4 => (0x1_0000_0000, 0x8000_0000),
        5 => (0x100_0000_0000, 0x80_0000_0000),
        6 => (0x1_0000_0000_0000, 0x8000_0000_0000),
        7 => (0x100_0000_0000_0000, 0x80_0000_0000_0000),
        _ => (0x1_0000_0000_0000_0000, 0x8000_0000_0000_0000),
    }
}

/// Refines `tc`.
pub fn tc_x(v: i64, k: u64) -> (u: u64)
    requires 1 <= k <= 8, sfits(v as int, k as nat),
    ensures u as nat == tc(v as int, k as nat),
{
    proof { lemma_tc_sgn(v as int, k as nat); lemma_p2_oct(k as nat); }
    let (m, _) = p2_oct_x(k);
    if v < 0 { ((v as i128) + (m as i128)) as u64 } else { v as u64 }
}

/// Refines `sgn`.
pub fn sgn_x(u: u64, k: u64) -> (v: i64)
    requires 1 <= k <= 8, (u as nat) < p2(8 * (k as nat)),
    ensures v as int == sgn(u as nat, k as nat),
{
    proof { lemma_sgn_tc(u as nat, k as nat); }
    let (m, h) = p2_oct_x(k);
    if (u as u128) >= h { ((u as i128) - (m as i128)) as i64 } else { u as i64 }
}

pub proof fn lemma_bits_seq_64(u: u64)
    ensures bits_seq(u, 64) =~= bits_seq((u / 0x1_0000_0000) as u64, 32) + bits_seq((u % 0x1_0000_0000) as u64, 32),
{
    lemma_p2_octets();
    let hi = (u / 0x1_0000_0000) as u64;
    let lo = (u % 0x1_0000_0000) as u64;
    let a = bits_seq(u, 64);
    let b = bits_seq(hi, 32) + bits_seq(lo, 32);
    lemma_bits_seq_val(u, 64);
    lemma_bits_seq_val(hi, 32);
    lemma_bits_seq_val(lo, 32);
    lemma_bits_val_split(b, 32);
    assert(b.take(32) =~= bits_seq(hi, 32));
    assert(b.skip(32) =~= bits_seq(lo, 32));
    assert(bits_val(b) == (hi as nat) * p2(32) + lo as nat);
    assert((hi as nat) * 0x1_0000_0000 + lo as nat == u as nat) by (nonlinear_arith)
        requires hi == u / 0x1_0000_0000, lo == u % 0x1_0000_0000;
    lemma_bits_val_inj(a, b);
}

impl<'a> BitReader<'a> {
    /// Refines `lo_dec`.
    pub fn read_lo(&mut self) -> (res: Option<(u64, u64)>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some((k, u)) => lo_dec(old(self).rem())
                    == Some::<(nat, nat, nat)>((k as nat, u as nat, (final(self).pos - old(self).pos) as nat)),
                None => lo_dec(old(self).rem()) is None,
            },
    {
        proof { lemma_p2_octets(); }
        let ghost start = self.rem();
        let ghost p0 = self.pos;
        let k = match self.read_gld() {
            Some(k) => k,
            None => return None,
        };
        let ghost kl = (self.pos - p0) as nat;
        if k < 1 || k > 8 {
            return None;
        }
        let nb = (8 * k) as usize;
        if nb > self.buf.len() * 8 - self.pos {
            proof { assert(kl + 8 * (k as nat) > start.len()); }
            return None;
        }
        proof { lemma_rem_skip(self.buf@, p0 as nat, kl); }
        let ghost body = self.rem();
        proof { assert(body =~= start.skip(kl as int)); }
        let ghost p1 = self.pos;
        let u: u64 = if k <= 7 {
            match self.read_uint(nb) {
                Some(v) => {
                    proof {
                        lemma_bits_val_bound(body.take(nb as int));
                        crate::prim_read::lemma_p2_mono(nb as nat, 56);
                        assert(v as nat == bits_val(body.take(nb as int)));
                    }
                    v
                }
                None => return None,
            }
        } else {
            let hi = match self.read_uint(32) {
                Some(v) => v,
                None => return None,
            };
            proof {
                lemma_rem_skip(self.buf@, p1 as nat, 32);
                lemma_bits_val_bound(body.take(32));
                assert(hi as nat == bits_val(body.take(32)));
            }
            let ghost mid = self.rem();
            proof { assert(mid =~= body.skip(32)); }
            let lo = match self.read_uint(32) {
                Some(v) => v,
                None => return None,
            };
            proof {
                lemma_bits_val_bound(mid.take(32));
                assert(lo as nat == bits_val(mid.take(32)));
                let t = body.take(64);
                lemma_bits_val_split(t, 32);
                assert(t.take(32) =~= body.take(32));
                assert(t.skip(32) =~= mid.take(32));
                assert(bits_val(t) == (hi as nat) * p2(32) + lo as nat);
                lemma_bits_val_bound(t);
                assert(((hi as nat) * 0x1_0000_0000 + (lo as nat)) < 0x1_0000_0000_0000_0000nat);
            }
            hi * 0x1_0000_0000 + lo
        };
        proof {
            assert(start.skip(kl as int).take(8 * k as int) =~= body.take(nb as int));
        }
        Some((k, u))
    }

    /// Refines `semi_dec(lb)`.
    pub fn read_semi(&mut self, lb: i64) -> (res: Option<i64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(x) => semi_dec(lb as int)(old(self).rem())
                    == Some::<(i64, nat, Flg)>((x, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => semi_dec(lb as int)(old(self).rem()) is None,
            },
    {
        match self.read_lo() {
            Some((k, u)) => {
                if uoct_x(u) != k || (lb as i128) + (u as i128) > (i64::MAX as i128) {
                    { self.fail("semi-constrained INTEGER: not in the fewest octets, or out of range (X.691 11.3.6)"); None }
                } else {
                    Some(((lb as i128) + (u as i128)) as i64)
                }
            }
            None => None,
        }
    }

    /// Refines `uc_dec()`.
    pub fn read_uc(&mut self) -> (res: Option<i64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => uc_dec()(old(self).rem())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => uc_dec()(old(self).rem()) is None,
            },
    {
        let ghost start = self.rem();
        match self.read_lo() {
            Some((k, u)) => {
                proof { lemma_lo_inj(start); }
                let v = sgn_x(u, k);
                if soct_x(v) != k {
                    { self.fail("INTEGER: not in the fewest octets (X.691 11.4.6)"); None }
                } else {
                    Some(v)
                }
            }
            None => None,
        }
    }

    /// Refines `xint_r_dec(r)`: an extensible INTEGER (X.691 13.1).
    pub fn read_xint(&mut self, r: XRoot) -> (res: Option<i64>)
        requires old(self).wf(), xroot_ok(r),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => xint_r_dec(r)(old(self).rem())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => xint_r_dec(r)(old(self).rem()) is None,
            },
    {
        let ghost start = self.rem();
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
        let ghost mid = start.skip(kb as int);
        let ghost p1 = self.pos;
        let got: Option<i64> = if !out {
            // the root: the value encoded as if there were no extension marker
            match r {
                XRoot::Range(lb, ub, n) => self.read_int_range(lb, ub, n),
                XRoot::Const(c) => {
                    proof { lemma_unit_dec_val(c, mid); }
                    Some(c)
                }
                XRoot::Semi(lb) => self.read_semi(lb),
                XRoot::All => self.read_uc(),
            }
        } else {
            // outside the root: unconstrained, and only a value outside it
            match self.read_uc() {
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
    /// Refines `lo_enc`.
    pub fn write_lo(&mut self, k: u64, u: u64) -> (ok: bool)
        requires old(self).wf(), 1 <= k <= 8, (u as nat) < p2(8 * (k as nat)),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + lo_enc(k as nat, u as nat),
    {
        proof { lemma_p2_octets(); lemma_gld_wf_iff(k); }
        let ghost w0 = self.written();
        if !self.write_gld(k) { return false; }
        if k <= 7 {
            self.write_uint((8 * k) as usize, u)
        } else {
            let hi = u / 0x1_0000_0000;
            let lo = u % 0x1_0000_0000;
            if !self.write_uint(32, hi) { return false; }
            if !self.write_uint(32, lo) { return false; }
            proof { lemma_bits_seq_64(u); }
            true
        }
    }

    /// Refines `semi_enc(lb)`.
    pub fn write_semi(&mut self, lb: i64, x: i64) -> (ok: bool)
        requires old(self).wf(), lb <= x,
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + semi_enc(lb as int)(x),
    {
        let u = ((x as i128) - (lb as i128)) as u64;
        let k = uoct_x(u);
        proof { lemma_uoct(u as nat); }
        self.write_lo(k, u)
    }

    /// Refines `uc_enc()`.
    pub fn write_uc(&mut self, v: i64) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + uc_enc()(v),
    {
        let k = soct_x(v);
        proof { lemma_soct(v as int); lemma_tc_sgn(v as int, k as nat); }
        let u = tc_x(v, k);
        self.write_lo(k, u)
    }

    /// Refines `xint_r_enc(r)`.
    pub fn write_xint(&mut self, r: XRoot, v: i64) -> (ok: bool)
        requires old(self).wf(), xroot_ok(r),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + xint_r_enc(r)(v),
    {
        let inr = match r {
            XRoot::Range(lb, ub, _) => lb <= v && v <= ub,
            XRoot::Const(c) => v == c,
            XRoot::Semi(lb) => lb <= v,
            XRoot::All => true,
        };
        proof {
            assert(inr == xroot_in(r)(v));
            lemma_map_enc_val(dep_enc(bool_enc(), xint_alt_enc(xroot_enc(r))), xint_from(xroot_in(r)), v);
            lemma_dep_enc_val(bool_enc(), xint_alt_enc(xroot_enc(r)), !inr, v);
        }
        let ghost w0 = self.written();
        if !self.write_bool(!inr) { return false; }
        let ghost w1 = self.written();
        let ok = if inr {
            match r {
                XRoot::Range(lb, ub, n) => self.write_int_range(lb, ub, n, v),
                XRoot::Const(c) => {
                    proof { reveal(unit_enc); assert(w1 + unit_enc::<i64>()(v) =~= w1); }
                    true
                }
                XRoot::Semi(lb) => self.write_semi(lb, v),
                XRoot::All => self.write_uc(v),
            }
        } else {
            self.write_uc(v)
        };
        proof {
            if ok {
                assert(self.written() =~= w0 + (bool_enc()(!inr) + xint_alt_enc(xroot_enc(r))(!inr)(v)));
            }
        }
        ok
    }
}

} // verus!

verus! {

use crate::cursor::*;
use crate::fraglist::*;

// ------------------------------------------ normally small (11.6), in full
//
// `0` and 6 bits for n <= 63 (11.6.1), else `1` and n as a semi-constrained
// whole number with lb 0 (11.6.2), which is `usemi`. The short form is
// mandatory for n <= 63, so the long branch admits only n >= 64. It is the
// extension bit of `fraglist`'s `xext` over u64: bitwise, the short form is
// the 7-bit field restricted to <= 63 that CHOICE and ENUMERATED used before.

/// A semi-constrained whole number, lb 0, over all of u64 (11.7).
pub open spec fn usemi_wf() -> Wf<u64> { |n: u64| true }
pub open spec fn usemi_enc() -> Enc<u64> { |n: u64| lo_enc(uoct(n as nat), n as nat) }
pub open spec fn usemi_dec() -> Dec<u64> {
    |b: Seq<bool>| match lo_dec(b) {
        Some((k, u, len)) => if uoct(u) == k { Some((u as u64, len, Flg::SameVer)) } else { None },
        None => None,
    }
}

pub proof fn lemma_usemi_format()
    ensures is_format(usemi_wf(), usemi_enc(), usemi_dec()),
{
    assert forall|n: u64, rest: Seq<bool>| usemi_wf()(n) implies
        #[trigger] usemi_dec()(usemi_enc()(n) + rest)
            == Some::<(u64, nat, Flg)>((n, usemi_enc()(n).len(), Flg::SameVer))
    by {
        lemma_uoct(n as nat);
        lemma_lo_surj(uoct(n as nat), n as nat, rest);
    }
    assert forall|b: Seq<bool>| (#[trigger] usemi_dec()(b)).is_some() implies {
        let n = usemi_dec()(b).unwrap().0;
        let k = usemi_dec()(b).unwrap().1;
        &&& usemi_wf()(n) && k <= b.len()
        &&& usemi_dec()(b).unwrap().2 is SameVer ==> b.take(k as int) == usemi_enc()(n)
    } by {
        lemma_lo_inj(b);
        let (k, u, len) = lo_dec(b).unwrap();
        lemma_p2_oct(k);
    }
}

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
    // opaque, so that a CHOICE or ENUMERATED that uses it carries its
    // definition only where this lemma is called, not in every query
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
    }
}

impl<'a> BitReader<'a> {
    /// Refines `usemi_dec()`.
    pub fn read_usemi(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(n) => usemi_dec()(old(self).rem())
                    == Some::<(u64, nat, Flg)>((n, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => usemi_dec()(old(self).rem()) is None,
            },
    {
        match self.read_lo() {
            Some((k, u)) => if uoct_x(u) != k {
                { self.fail("a whole number not in the fewest octets (X.691 11.3.6)"); None }
            } else {
                Some(u)
            },
            None => None,
        }
    }

    /// Refines `nsn_dec()`: a normally small non-negative whole number (11.6).
    pub fn read_nsn(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(n) => nsn_dec()(old(self).rem())
                    == Some::<(u64, nat, Flg)>((n, (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
                None => nsn_dec()(old(self).rem()) is None,
            },
    {
        proof { assert(p2(6) == 64) by { reveal_with_fuel(p2, 7); } reveal(nsn_dec); }
        let ghost start = self.rem();
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
        let ghost mid = start.skip(kb as int);
        let ghost p1 = self.pos;
        let got: Option<u64> = if !long {
            self.read_uint(6)
        } else {
            match self.read_usemi() {
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
    /// Refines `usemi_enc()`.
    pub fn write_usemi(&mut self, n: u64) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + usemi_enc()(n),
    {
        let k = uoct_x(n);
        proof { lemma_uoct(n as nat); }
        self.write_lo(k, n)
    }

    /// Refines `nsn_enc()`.
    pub fn write_nsn(&mut self, n: u64) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + nsn_enc()(n),
    {
        proof {
            assert(p2(6) == 64) by { reveal_with_fuel(p2, 7); }
            lemma_nsn_format();
            reveal(nsn_wf); reveal(nsn_enc);
            lemma_xext_enc(uint_enc(6), usemi_enc(), uint_wf(6), restrict_wf(usemi_wf(), nsn_big()), nsn_small(), n);
        }
        let small = n <= 63;
        let ghost w0 = self.written();
        if !self.write_bool(!small) { return false; }
        if small { self.write_uint(6, n) } else { self.write_usemi(n) }
    }
}

} // verus!
