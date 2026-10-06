//! Octets with a fragmenting length, and open types, in the ALIGNED variant.
//!
//! An unconstrained OCTET STRING (17.8, 11.9.3.5 to 11.9.3.8) is UPER's
//! encoding octet-aligned. Its length determinant is an octet-aligned field in
//! both of its forms, and every fragment is whole octets, so once the first
//! length starts on a boundary everything after it does: `aligned(lift(frag))`.
//!
//! An open type (11.2) holds a *complete* encoding of its value (11.1): the
//! value encoded from bit 0 on, padded to whole octets, one octet if empty.
//! Those octets are then the octets above. So the content is the APER format
//! read at position 0 (`at0`), which is a UPER format, and the open type is
//! UPER's open type over it, octet-aligned.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::aper::format::*;
use crate::aper::cursor::*;
use crate::uper::format as u;
use crate::uper::frag as uf;
use crate::uper::opentype as uo;
pub use crate::uper::opentype::{ot_octets_eq};
pub use crate::uper::frag::Octets;
#[cfg(verus_keep_ghost)]
pub use crate::uper::opentype::{ot_octets, ot_body, lemma_ot_octets};

verus! {

broadcast use {format_steps, map_steps};

// ------------------------------------------------------------ fragmenting octets

pub open spec fn frag_wf() -> Wf<Seq<bool>> { uf::frag_wf() }
pub open spec fn frag_enc() -> Enc<Seq<bool>> { aligned_enc(lift_enc(uf::frag_enc())) }
pub open spec fn frag_dec() -> Dec<Seq<bool>> { aligned_dec(lift_dec(uf::frag_dec())) }

pub proof fn lemma_frag_format()
    ensures is_format(frag_wf(), frag_enc(), frag_dec()),
{
    uf::lemma_frag_format();
    lemma_lift_format(uf::frag_wf(), uf::frag_enc(), uf::frag_dec());
    lemma_aligned_format(uf::frag_wf(), lift_enc(uf::frag_enc()), lift_dec(uf::frag_dec()));
}

/// Never `DiffVer`: octets carry no extension.
pub proof fn lemma_frag_dec_same(i: In)
    ensures frag_dec()(i) is Some ==> frag_dec()(i).unwrap().2 is SameVer,
{
    lemma_aligned_dec_val(lift_dec(uf::frag_dec()), i);
    if frag_dec()(i) is Some {
        uf::lemma_frag_dec_same(adv(i, pad(i.0)).1);
    }
}

// ------------------------------------------------------ the format at position 0

/// An APER format read from position 0: the encoding of a value as the whole
/// of an outermost encoding (11.1). It no longer depends on a position, so it
/// is a UPER format.
pub open spec fn at0_enc<A>(e: Enc<A>) -> u::Enc<A> { |a: A| e(0, a) }
pub open spec fn at0_dec<A>(d: Dec<A>) -> u::Dec<A> { |b: Seq<bool>| d((0, b)) }

pub proof fn lemma_at0_format<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures u::is_format(w, at0_enc(e), at0_dec(d)),
{
    let e0 = at0_enc(e);
    let d0 = at0_dec(d);
    assert forall|a: A, rest: Seq<bool>| w(a) implies
        #[trigger] d0(e0(a) + rest) == Some::<(A, nat, Flg)>((a, e0(a).len(), Flg::SameVer))
    by {
        assert(d((0, e(0, a) + rest)) == Some::<(A, nat, Flg)>((a, e(0, a).len(), Flg::SameVer)));
    }
    assert forall|b: Seq<bool>| (#[trigger] d0(b)).is_some() implies {
        let a = d0(b).unwrap().0;
        let k = d0(b).unwrap().1;
        &&& w(a) && k <= b.len()
        &&& d0(b).unwrap().2 is SameVer ==> b.take(k as int) == e0(a)
    } by {
        let i: In = (0, b);
        assert(d(i).is_some());
    }
}

// ------------------------------------------------------------------ open types

#[verifier::opaque]
pub open spec fn open_enc<A>(e: Enc<A>) -> Enc<A> {
    aligned_enc(lift_enc(uo::open_enc(at0_enc(e))))
}

#[verifier::opaque]
pub open spec fn open_dec<A>(d: Dec<A>) -> Dec<A> {
    aligned_dec(lift_dec(uo::open_dec(at0_dec(d))))
}

pub proof fn lemma_open_format<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(w, open_enc(e), open_dec(d)),
{
    reveal(open_enc); reveal(open_dec);
    lemma_at0_format(w, e, d);
    uo::lemma_open_format(w, at0_enc(e), at0_dec(d));
    lemma_lift_format(w, uo::open_enc(at0_enc(e)), uo::open_dec(at0_dec(d)));
    lemma_aligned_format(w, lift_enc(uo::open_enc(at0_enc(e))), lift_dec(uo::open_dec(at0_dec(d))));
}

// ------------------------------------------------------------- step lemmas
//
// The shapes a generated open-type decode ends in, stated over this module's
// `frag_dec` (the aligned octets) and the content decoded from position 0.

proof fn lemma_open_dec_unfold<A>(d: Dec<A>, i: In)
    ensures open_dec(d)(i) == (match frag_dec()(i) {
        Some((c, k, _)) => match d((0, c)) {
            Some((a, k2, f)) => {
                if k2 <= c.len() && ot_octets(k2) == c.len() / 8
                    && c.skip(k2 as int) == zeros((c.len() - k2) as nat) {
                    Some((a, k, f))
                } else {
                    None
                }
            },
            None => None,
        },
        None => None,
    }),
{
    reveal(open_dec);
    reveal(uo::open_dec);
    lemma_aligned_dec_val(lift_dec(uo::open_dec(at0_dec(d))), i);
    lemma_aligned_dec_val(lift_dec(uf::frag_dec()), i);
}

pub proof fn lemma_open_dec_some<A>(d: Dec<A>, b: In, c: Seq<bool>, k: nat, a: A, k2: nat, f: Flg)
    requires
        frag_dec()(b) == Some::<(Seq<bool>, nat, Flg)>((c, k, Flg::SameVer)),
        d((0, c)) == Some::<(A, nat, Flg)>((a, k2, f)),
        k2 <= c.len(),
        ot_octets(k2) == c.len() / 8,
        c.skip(k2 as int) == zeros((c.len() - k2) as nat),
    ensures open_dec(d)(b) == Some::<(A, nat, Flg)>((a, k, f)),
{
    lemma_open_dec_unfold(d, b);
}

pub proof fn lemma_open_dec_none_len<A>(d: Dec<A>, b: In)
    requires frag_dec()(b) is None,
    ensures open_dec(d)(b) is None,
{
    lemma_open_dec_unfold(d, b);
}

pub proof fn lemma_open_dec_none_content<A>(d: Dec<A>, b: In, c: Seq<bool>, k: nat)
    requires
        frag_dec()(b) == Some::<(Seq<bool>, nat, Flg)>((c, k, Flg::SameVer)),
        d((0, c)) is None,
    ensures open_dec(d)(b) is None,
{
    lemma_open_dec_unfold(d, b);
}

pub proof fn lemma_open_dec_none_pad<A>(d: Dec<A>, b: In, c: Seq<bool>, k: nat)
    requires
        frag_dec()(b) == Some::<(Seq<bool>, nat, Flg)>((c, k, Flg::SameVer)),
        d((0, c)) is Some,
        ({
            let k2 = d((0, c)).unwrap().1;
            ||| k2 > c.len()
            ||| ot_octets(k2) != c.len() / 8
            ||| c.skip(k2 as int) != zeros((c.len() - k2) as nat)
        }),
    ensures open_dec(d)(b) is None,
{
    lemma_open_dec_unfold(d, b);
}

/// What an encoder puts in its scratch buffer: the value encoded from 0, then
/// zero padding to a whole octet.
pub proof fn lemma_ot_body_shape<A>(e: Enc<A>, a: A)
    ensures
        ot_body(at0_enc(e), a).len() == 8 * ot_octets(e(0, a).len()),
        ot_body(at0_enc(e), a).len() % 8 == 0,
        ot_body(at0_enc(e), a).take(e(0, a).len() as int) =~= e(0, a),
        ot_body(at0_enc(e), a).skip(e(0, a).len() as int)
            =~= zeros((8 * ot_octets(e(0, a).len()) - e(0, a).len()) as nat),
{
    uo::lemma_ot_body_shape(at0_enc(e), a);
}

} // verus!

verus! {

// ------------------------------------------------------------------- exec

impl<'a> BitReader<'a> {
    /// Refines `frag_dec()`: the padding, then UPER's fragmenting octets.
    pub fn read_afrag(&mut self) -> (res: Option<Vec<u8>>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& frag_dec()(old(self).at())
                        == Some::<(Seq<bool>, nat, Flg)>(
                            (bits_of(v@), (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& v@.len() <= old(self).buf@.len()
                },
                None => frag_dec()(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = lift_dec(uf::frag_dec());
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_dec_val(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_dec_val(d, i);
        }
        self.read_frag()
    }
}

impl<'a> BitReader<'a> {
    /// `read_afrag`, with the content borrowed from the buffer when it is
    /// one fragment, as every open type below 16K octets is: after the
    /// padding it starts on an octet boundary (`uper::frag::read_frag_ref`).
    pub fn read_afrag_ref(&mut self) -> (res: Option<Octets<'a>>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf, final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& frag_dec()(old(self).at())
                        == Some::<(Seq<bool>, nat, Flg)>(
                            (bits_of(v@), (final(self).pos - old(self).pos) as nat, Flg::SameVer))
                    &&& v@.len() <= old(self).buf@.len()
                },
                None => frag_dec()(old(self).at()) is None,
            },
    {
        let ghost i = self.at();
        let ghost d = lift_dec(uf::frag_dec());
        let ghost p0 = self.pos;
        if !self.read_align() {
            proof { lemma_aligned_dec_val(d, i); }
            return None;
        }
        proof {
            lemma_rem_skip(self.buf@, p0 as nat, (self.pos - p0) as nat);
            lemma_aligned_dec_val(d, i);
        }
        self.read_frag_ref()
    }
}

impl BitWriter {
    /// Refines `frag_enc()`.
    pub fn write_afrag(&mut self, src: &[u8], from: usize, nbits: usize) -> (ok: bool)
        requires
            old(self).wf(),
            nbits % 8 == 0,
            from + nbits <= 8 * src@.len(),
            8 * src@.len() <= usize::MAX,
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written()
                + frag_enc()(old(self).pos as nat, bits_of(src@).skip(from as int).take(nbits as int)),
    {
        let ghost p0 = self.pos as nat;
        let ghost c = bits_of(src@).skip(from as int).take(nbits as int);
        proof {
            lemma_aligned_enc_val(lift_enc(uf::frag_enc()), p0, c);
            reveal(uf::frag_enc);
        }
        if !self.write_align() { return false; }
        self.write_frag(src, from, nbits)
    }

    /// Write a value already encoded into `src` from bit 0 as an open type:
    /// the padding, the octet count, the content.
    pub fn write_aopen<A>(&mut self, src: &[u8], nbits: usize,
                          Ghost(e): Ghost<Enc<A>>, Ghost(a): Ghost<A>) -> (ok: bool)
        requires
            old(self).wf(),
            8 * src@.len() <= usize::MAX,
            nbits <= 8 * src@.len(),
            bits_of(src@).take(nbits as int) == ot_body(at0_enc(e), a),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + open_enc(e)(old(self).pos as nat, a),
    {
        let ghost p0 = self.pos as nat;
        proof {
            reveal(open_enc);
            lemma_aligned_enc_val(lift_enc(uo::open_enc(at0_enc(e))), p0, a);
        }
        if !self.write_align() { return false; }
        self.write_open(src, nbits, Ghost(at0_enc(e)), Ghost(a))
    }
}

} // verus!
