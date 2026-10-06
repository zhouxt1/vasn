//! Bulk reads, seen from APER: `uper::fast`'s, for the elements X.691 encodes
//! the same way in both variants.
//!
//! An element whose format is lifted from UPER ignores the position, so a
//! list of them reads the same bits as UPER's list (`lemma_list_lift`), and
//! UPER's bulk reads refine it as they stand. A preamble's bits are UPER's
//! too, and `lemma_bool_dec_at` is what its one-word read is proved with.
use vstd::prelude::*;
use crate::aper::format::*;
use crate::aper::list::*;
use crate::aper::term::*;
pub use crate::uper::cursor::{BitReader, BitWriter};
#[cfg(verus_keep_ghost)]
use crate::uper::format as u;
#[cfg(verus_keep_ghost)]
use crate::uper::list as ul;
#[cfg(verus_keep_ghost)]
use crate::uper::term as ut;

verus! {

/// A list of elements lifted from UPER decodes as UPER's list of them, from
/// the bits alone.
pub proof fn lemma_list_lift<A>(n: nat, d: u::Dec<A>, b: In)
    ensures list_dec_rec(n, lift_dec(d), b) == ul::list_dec_rec(n, d, b.1),
    decreases n,
{
    if n > 0 {
        reveal(lift_dec);
        if let Some((v, k, f)) = d(b.1) {
            lemma_list_lift((n - 1) as nat, d, adv(b, k));
            assert(adv(b, k).1 == b.1.skip(k as int));
        }
    }
}

/// Bit `o` from `i`, as a BOOLEAN: what a preamble read as one word splits
/// into (`vasnc`'s `{T}_bmfast`, as in UPER).
pub proof fn lemma_bool_dec_at(i: In, o: int)
    requires 0 <= o < i.1.len(),
    ensures bool_dec()(adv(i, o as nat)) == Some::<(bool, nat, Flg)>((i.1[o], 1nat, Flg::SameVer)),
{
    reveal(lift_dec);
    crate::uper::fast::lemma_bool_dec_at(i.1, o);
}

/// Two steps from `i` are one.
pub proof fn lemma_adv_adv(i: In, a: nat, b: nat)
    requires a + b <= i.1.len(),
    ensures adv(adv(i, a), b) == adv(i, a + b),
{
    assert(i.1.skip(a as int).skip(b as int) =~= i.1.skip((a + b) as int));
}

/// The same for encoding: a list of elements lifted from UPER encodes as
/// UPER's list of them, wherever it starts.
pub proof fn lemma_list_enc_lift<A>(pos: nat, l: Seq<A>, e: u::Enc<A>)
    ensures list_enc_rec(pos, l, lift_enc(e)) == ul::list_enc_rec(l, e),
    decreases l.len(),
{
    reveal(lift_enc);
    if l.len() > 0 {
        lemma_list_enc_lift(pos + e(l[0]).len(), l.skip(1), e);
    }
}

/// A BOOLEAN is its one bit, wherever it is.
pub proof fn lemma_abool_enc_bit(b: bool)
    ensures forall|pos: nat| #[trigger] bool_enc()(pos, b) == seq![b],
{
    reveal(lift_enc);
    crate::uper::fast::lemma_bool_enc_bit(b);
}

impl BitWriter {
    /// A BIT STRING's bits, as UPER's `write_bit_list` writes them.
    #[inline]
    pub fn write_abit_list(&mut self, l: &Vec<bool>) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written()
                =~= old(self).written() + list_enc_rec(old(self).pos as nat, l@, bool_enc()),
    {
        proof { lemma_list_enc_lift(self.pos as nat, l@, ut::bool_enc()); }
        self.write_bit_list(l)
    }

    /// An OCTET STRING's octets, as UPER's `write_octet_list` writes them.
    #[inline]
    pub fn write_aoctet_list(&mut self, l: &Vec<u8>) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written()
                =~= old(self).written() + list_enc_rec(old(self).pos as nat, l@, byte_enc()),
    {
        proof { lemma_list_enc_lift(self.pos as nat, l@, ut::byte_enc()); }
        self.write_octet_list(l)
    }
}

impl<'a> BitReader<'a> {
    /// `c` BOOLEANs, 56 bits a read: a BIT STRING's bits.
    #[inline]
    pub fn read_abit_list(&mut self, c: usize) -> (out: Vec<bool>)
        requires old(self).wf(), c <= 8 * old(self).buf@.len() - old(self).pos,
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos == old(self).pos + c,
            out@.len() == c,
            list_dec_rec(c as nat, bool_dec(), old(self).at())
                == Some::<(Seq<bool>, nat, Flg)>((out@, c as nat, Flg::SameVer)),
    {
        proof { lemma_list_lift(c as nat, ut::bool_dec(), self.at()); }
        self.read_bit_list(c)
    }

    /// `c` octets, as `read_octets` copies them: an OCTET STRING's.
    #[inline]
    pub fn read_aoctet_list(&mut self, c: usize) -> (out: Vec<u8>)
        requires old(self).wf(), 8 * c <= 8 * old(self).buf@.len() - old(self).pos,
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos == old(self).pos + 8 * c,
            out@.len() == c,
            list_dec_rec(c as nat, byte_dec(), old(self).at())
                == Some::<(Seq<u8>, nat, Flg)>((out@, (8 * c) as nat, Flg::SameVer)),
    {
        proof { lemma_list_lift(c as nat, ut::byte_dec(), self.at()); }
        self.read_octet_list(c)
    }
}

} // verus!
