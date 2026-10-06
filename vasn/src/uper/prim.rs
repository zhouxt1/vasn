//! Primitive formats: the unsigned n-bit field, and the map combinator that
//! turns it into every other terminal ASN.1 type.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::bits::bytebits::*;
use crate::uper::format::*;
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use crate::bits::prim_write::{bits_seq, lemma_bits_seq_val, lemma_bits_val_inj};

verus! {

// ------------------------------------------------------- unsigned n-bit field

pub open spec fn uint_wf(n: nat) -> Wf<u64> { |v: u64| (v as nat) < p2(n) }

pub open spec fn uint_enc(n: nat) -> Enc<u64> { |v: u64| bits_seq(v, n) }

pub open spec fn uint_dec(n: nat) -> Dec<u64> {
    |b: Seq<bool>| if b.len() >= n {
        Some((bits_val(b.take(n as int)) as u64, n, Flg::SameVer))
    } else {
        None
    }
}

/// An n-bit sequence is the unique encoding of its own value.
pub proof fn lemma_bits_roundtrip(s: Seq<bool>)
    requires s.len() <= 64,
    ensures bits_seq(bits_val(s) as u64, s.len()) =~= s,
{
    lemma_bits_val_bound(s);
    crate::bits::prim_read::lemma_p2_mono(s.len(), 64);
    crate::bits::prim_read::lemma_p2_64();
    assert(bits_val(s) < 0x1_0000_0000_0000_0000nat);
    lemma_bits_seq_val(bits_val(s) as u64, s.len());
    lemma_bits_val_inj(bits_seq(bits_val(s) as u64, s.len()), s);
}

pub proof fn lemma_uint_format(n: nat)
    requires 1 <= n <= 64,
    ensures is_format(uint_wf(n), uint_enc(n), uint_dec(n)),
{
    let w = uint_wf(n);
    let e = uint_enc(n);
    let d = uint_dec(n);
    assert forall|v: u64, rest: Seq<bool>| w(v) implies
        #[trigger] d(e(v) + rest) == Some::<(u64, nat, Flg)>((v, e(v).len(), Flg::SameVer))
    by {
        lemma_take_add(bits_seq(v, n), rest);
        lemma_bits_seq_val(v, n);
        assert((bits_seq(v, n) + rest).take(n as int) =~= bits_seq(v, n));
    }
    assert forall|b: Seq<bool>| (#[trigger] d(b)).is_some() implies {
        let a = d(b).unwrap().0;
        let k = d(b).unwrap().1;
        &&& w(a) && k <= b.len()
        &&& d(b).unwrap().2 is SameVer ==> b.take(k as int) == e(a)
    } by {
        assert(b.len() >= n);
        let t = b.take(n as int);
        assert(t.len() == n);
        lemma_bits_val_bound(t);
        lemma_bits_roundtrip(t);
    }
}

/// Every field is exactly its declared width.
pub proof fn lemma_uint_enc_len(n: nat, v: u64)
    ensures uint_enc(n)(v).len() == n,
{
}

// -------------------------------------------------------------- map (project)

#[verifier::opaque]
pub open spec fn map_wf<A, B>(wa: Wf<A>, to: spec_fn(A) -> B, from: spec_fn(B) -> A) -> Wf<B> {
    |b: B| wa(from(b)) && to(from(b)) == b
}

#[verifier::opaque]
pub open spec fn map_enc<A, B>(ea: Enc<A>, from: spec_fn(B) -> A) -> Enc<B> {
    |b: B| ea(from(b))
}

#[verifier::opaque]
pub open spec fn map_dec<A, B>(da: Dec<A>, to: spec_fn(A) -> B) -> Dec<B> {
    |bits: Seq<bool>| match da(bits) {
        Some((a, k, f)) => Some((to(a), k, f)),
        None => None,
    }
}

/// Re-typing a format through a partial bijection yields a format. This is how
/// BOOLEAN, ENUMERATED and constrained INTEGER are built from `uint`.
pub proof fn lemma_map_format<A, B>(wa: Wf<A>, ea: Enc<A>, da: Dec<A>,
                                    to: spec_fn(A) -> B, from: spec_fn(B) -> A)
    requires
        is_format(wa, ea, da),
        forall|a: A| wa(a) ==> #[trigger] from(to(a)) == a,
    ensures
        is_format(map_wf(wa, to, from), map_enc(ea, from), map_dec(da, to)),
{
    reveal(map_wf); reveal(map_enc); reveal(map_dec);
    let w = map_wf(wa, to, from);
    let e = map_enc(ea, from);
    let d = map_dec(da, to);
    assert forall|b: B, rest: Seq<bool>| w(b) implies
        #[trigger] d(e(b) + rest) == Some::<(B, nat, Flg)>((b, e(b).len(), Flg::SameVer))
    by {
        assert(da(ea(from(b)) + rest)
               == Some::<(A, nat, Flg)>((from(b), ea(from(b)).len(), Flg::SameVer)));
    }
    assert forall|bits: Seq<bool>| (#[trigger] d(bits)).is_some() implies {
        let v = d(bits).unwrap().0;
        let k = d(bits).unwrap().1;
        &&& w(v) && k <= bits.len()
        &&& d(bits).unwrap().2 is SameVer ==> bits.take(k as int) == e(v)
    } by {
        assert(da(bits).is_some());
        let a = da(bits).unwrap().0;
        assert(wa(a));
        assert(from(to(a)) == a);
    }
}

} // verus!

verus! {

// --------------------------------------------------- map step lemmas
// See the note on step lemmas in `format.rs`: the combinator is opaque, and
// these are how callers walk one level of it.

pub broadcast proof fn lemma_map_wf_val<A, B>(wa: Wf<A>, to: spec_fn(A) -> B,
                                              from: spec_fn(B) -> A, b: B)
    ensures #[trigger] map_wf(wa, to, from)(b) == (wa(from(b)) && to(from(b)) == b),
{
    reveal(map_wf);
}

pub broadcast proof fn lemma_map_enc_val<A, B>(ea: Enc<A>, from: spec_fn(B) -> A, b: B)
    ensures #[trigger] map_enc(ea, from)(b) == ea(from(b)),
{
    reveal(map_enc);
}

pub proof fn lemma_map_dec_some<A, B>(da: Dec<A>, to: spec_fn(A) -> B, bits: Seq<bool>,
                                      a: A, k: nat, f: Flg)
    requires da(bits) == Some::<(A, nat, Flg)>((a, k, f)),
    ensures map_dec(da, to)(bits) == Some::<(B, nat, Flg)>((to(a), k, f)),
{
    reveal(map_dec);
}

pub proof fn lemma_map_dec_none<A, B>(da: Dec<A>, to: spec_fn(A) -> B, bits: Seq<bool>)
    requires da(bits).is_none(),
    ensures map_dec(da, to)(bits).is_none(),
{
    reveal(map_dec);
}

pub broadcast group map_steps {
    lemma_map_wf_val,
    lemma_map_enc_val,
}

} // verus!
