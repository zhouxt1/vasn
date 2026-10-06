//! The cursors, seen from APER.
//!
//! APER uses UPER's `BitReader` and `BitWriter` unchanged. Their `pos` is
//! already the absolute bit position an APER format is indexed by, as long as
//! the reader or writer was started at the beginning of the outermost encoding
//! (`BitReader::new`, `BitWriter::with_capacity`), which is where X.691 counts
//! alignment from. So a decoder's input is `r.at()`, the position and the bits
//! from there on, and an encoder writes `e(w.pos, v)`.
//!
//! What UPER's cursors do not have is the padding itself: `read_align` and
//! `write_align` below.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::aper::format::*;
pub use crate::uper::cursor::{BitReader, BitWriter};
#[cfg(verus_keep_ghost)]
use crate::bits::prim_write::bits_seq;
#[cfg(verus_keep_ghost)]
use crate::uper::prim::{uint_dec, uint_wf, lemma_bits_roundtrip};

verus! {

impl<'a> BitReader<'a> {
    /// The input an APER decoder at this point reads.
    pub open spec fn at(self) -> In { (self.pos as nat, self.rem()) }
}

/// Advancing the cursor by `k` advances its input by `k`. Generated decoders
/// chain this to line their spec up with the spec-level composition; it is
/// UPER's `lemma_rem_skip` with the position carried along.
pub proof fn lemma_rem_skip(buf: Seq<u8>, p: nat, k: nat)
    requires p + k <= 8 * buf.len(),
    ensures
        bits_of(buf).skip((p + k) as int) =~= bits_of(buf).skip(p as int).skip(k as int),
        ((p + k) as nat, bits_of(buf).skip((p + k) as int))
            == adv((p, bits_of(buf).skip(p as int)), k),
{
    assert(bits_of(buf).skip((p + k) as int) =~= bits_of(buf).skip(p as int).skip(k as int));
}

/// The written bits are as long as the writer's position, so an encoder's
/// `pos` and the length of what it has written are one number.
pub proof fn lemma_written_len(w: BitWriter)
    requires w.wf(),
    ensures w.written().len() == w.pos,
{
}

proof fn lemma_bits_seq_zero(n: nat)
    ensures bits_seq(0, n) =~= zeros(n),
{
    assert forall|i: int| 0 <= i < n implies bits_seq(0, n)[i] == zeros(n)[i] by {
        crate::bits::bitspec::lemma_p2_pos((n - 1 - i) as nat);
        assert(0nat / p2((n - 1 - i) as nat) == 0);
    }
}

/// An `n`-bit field reads as 0 exactly when its bits are all zero.
proof fn lemma_zero_field(s: Seq<bool>, n: nat)
    requires 1 <= n <= 56, s.len() >= n,
    ensures (bits_val(s.take(n as int)) == 0) == (s.take(n as int) == zeros(n)),
{
    let t = s.take(n as int);
    lemma_bits_seq_zero(n);
    if bits_val(t) == 0 {
        lemma_bits_roundtrip(t);
        assert(bits_seq(0, n) =~= t);
    }
    if t == zeros(n) {
        crate::bits::bitspec::lemma_p2_pos(n);
        crate::bits::prim_write::lemma_bits_seq_val(0, n);
    }
}

/// Diagnostics, for a fuzzing harness: where `read_align` last found padding
/// that is not zero, as (first bit, number of bits) in the reader's `buf`,
/// or, with 0 bits, where the value ended that `check_complete` found
/// followed by more than its complete encoding's padding. Like
/// `BitReader::fail`, it is data about a rejection and nothing more; no spec
/// mentions it.
#[verifier::external_body]
#[inline(always)]
pub(crate) fn note_bad_padding(buf: &[u8], from: usize, n: usize) {
    let at = buf.as_ptr() as usize;
    BAD_PADDING.with(|p| p.set(Some((at, from, n))));
}

impl<'a> BitReader<'a> {
    /// Consume the padding to the next octet boundary, checking it is zero.
    /// Refines `align_dec()`.
    #[inline]
    pub fn read_align(&mut self) -> (res: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            res ==> align_dec()(old(self).at())
                == Some::<((), nat, Flg)>(((), (final(self).pos - old(self).pos) as nat, Flg::SameVer)),
            res ==> final(self).pos % 8 == 0,
            !res ==> align_dec()(old(self).at()).is_none(),
    {
        let n: usize = (8 - self.pos % 8) % 8;
        let ghost i = old(self).at();
        proof { lemma_pad(i.0); assert(n == pad(i.0)); }
        if n == 0 {
            assert(i.1.take(0) =~= zeros(0));
            return true;
        }
        if n > self.buf.len() * 8 - self.pos {
            return false;
        }
        let start = self.pos;
        match self.read_uint(n) {
            Some(v) => {
                proof {
                    let t = i.1.take(n as int);
                    lemma_zero_field(i.1, n as nat);
                    crate::bits::bitspec::lemma_bits_val_bound(t);
                    crate::bits::prim_read::lemma_p2_mono(n as nat, 56);
                    crate::bits::prim_read::lemma_p2_56();
                    assert(v as nat == bits_val(t));
                }
                if v != 0 {
                    note_bad_padding(self.buf, start, n);
                }
                v == 0
            }
            None => false,
        }
    }
}

impl BitWriter {
    /// Write the padding to the next octet boundary. Refines `align_enc()`.
    #[inline]
    pub fn write_align(&mut self) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + align_enc()(old(self).pos as nat, ()),
            ok ==> final(self).pos % 8 == 0,
    {
        proof { lemma_pad(old(self).pos as nat); }
        self.pad_to_octet()
    }
}

} // verus!

thread_local! {
    static BAD_PADDING: std::cell::Cell<Option<(usize, usize, usize)>> = const { std::cell::Cell::new(None) };
}

/// Where the last `read_align` on this thread found padding that is not
/// zero, as (first bit, number of bits), or (end of the value, 0) where
/// `check_complete` found more than the complete encoding's padding after
/// it (X.691 11.1.4); and forget it. The bits are counted in MSG, the
/// buffer the outermost reader was given; None if the padding was in
/// another (an open type's content that was copied out of MSG, being
/// fragmented). A decoder that rejects for its padding rejects there;
/// a fuzzing harness asks, to tell a rejection for padding (OVERVIEW.md §1) from
/// any other.
pub fn take_bad_padding(msg: &[u8]) -> Option<(usize, usize)> {
    let (at, from, n) = BAD_PADDING.with(|p| p.take())?;
    let base = msg.as_ptr() as usize;
    let off = at.checked_sub(base).filter(|&o| o <= msg.len())?;
    Some((8 * off + from, n))
}
