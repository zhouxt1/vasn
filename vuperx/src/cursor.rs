//! Executable cursors. Every generated decoder threads a `BitReader`; every
//! generated encoder threads a `BitWriter`. Their contracts are stated directly
//! against the spec-level `uint_dec` / `uint_enc`, so generated code never has
//! to reason about buffers or bit offsets again.
use vstd::prelude::*;
use crate::bitspec::*;
use crate::bytebits::*;
use crate::format::*;
use crate::prim::*;
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use crate::prim_write::bits_seq;
use crate::err::DecodeError;

verus! {

pub proof fn lemma_bview_in_range(s: Seq<u8>, i: int, j: int)
    requires 0 <= i <= j <= 8 * s.len(),
    ensures bview(s).subrange(i, j) =~= bits_of(s).subrange(i, j),
{
}

// ------------------------------------------------------------------- reader

pub struct BitReader<'a> {
    pub buf: &'a [u8],
    pub pos: usize,
    /// why the last decode failed (`err.rs`); no part of any contract
    pub err: DecodeError,
}

impl<'a> BitReader<'a> {
    pub open spec fn wf(self) -> bool {
        &&& self.pos <= 8 * self.buf@.len()
        &&& 8 * self.buf@.len() <= usize::MAX
    }

    /// The bits still to be consumed.
    pub open spec fn rem(self) -> Seq<bool> {
        bits_of(self.buf@).skip(self.pos as int)
    }

    #[inline]
    pub fn new(buf: &'a [u8]) -> (r: BitReader<'a>)
        requires 8 * buf@.len() <= usize::MAX,
        ensures r.wf(), r.buf == buf, r.pos == 0, r.rem() =~= bits_of(buf@),
    {
        BitReader { buf, pos: 0, err: DecodeError::empty() }
    }

    /// Consume an unsigned `n`-bit field. Refines `uint_dec(n)`.
    #[inline]
    pub fn read_uint(&mut self, n: usize) -> (res: Option<u64>)
        requires old(self).wf(), 1 <= n <= 56,
        ensures
            final(self).buf == old(self).buf,
            final(self).wf(),
            match res {
                Some(v) => {
                    &&& uint_dec(n as nat)(old(self).rem())
                        == Some::<(u64, nat, Flg)>((v, n as nat, Flg::SameVer))
                    &&& final(self).pos == old(self).pos + n
                },
                None => {
                    &&& uint_dec(n as nat)(old(self).rem()).is_none()
                    &&& final(self).pos == old(self).pos
                },
            },
    {
        if n > self.buf.len() * 8 - self.pos {
            assert(self.rem().len() < n);
            return None;
        }
        let v = crate::fastload::read_bits_fast(self.buf, self.pos, n);
        proof {
            lemma_bview_in_range(self.buf@, self.pos as int, self.pos as int + n as int);
            assert(self.rem().take(n as int)
                   =~= bits_of(self.buf@).subrange(self.pos as int, self.pos as int + n as int));
        }
        self.pos = self.pos + n;
        Some(v)
    }
}

// ------------------------------------------------------------------- writer

pub struct BitWriter {
    pub buf: Vec<u8>,
    pub pos: usize,
}

impl BitWriter {
    pub open spec fn wf(self) -> bool {
        &&& self.pos <= 8 * self.buf@.len()
        &&& 8 * self.buf@.len() <= usize::MAX
    }

    /// The bits written so far.
    pub open spec fn written(self) -> Seq<bool> {
        bits_of(self.buf@).take(self.pos as int)
    }

    #[inline]
    pub fn with_capacity(nbytes: usize) -> (w: BitWriter)
        requires 8 * nbytes <= usize::MAX,
        ensures w.wf(), w.pos == 0, w.buf@.len() == nbytes, w.written() =~= Seq::<bool>::empty(),
    {
        let mut buf: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < nbytes
            invariant i <= nbytes, buf@.len() == i,
            decreases nbytes - i,
        {
            buf.push(0u8);
            i = i + 1;
        }
        BitWriter { buf, pos: 0 }
    }

    /// Append an unsigned `n`-bit field. Refines `uint_enc(n)`.
    #[inline]
    pub fn write_uint(&mut self, n: usize, v: u64) -> (ok: bool)
        requires old(self).wf(), 1 <= n <= 56, uint_wf(n as nat)(v),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> {
                &&& final(self).pos == old(self).pos + n
                &&& final(self).written() =~= old(self).written() + uint_enc(n as nat)(v)
            },
            !ok ==> final(self).pos == old(self).pos,
    {
        if n > self.buf.len() * 8 - self.pos {
            return false;
        }
        let ghost before = bits_of(self.buf@);
        crate::prim_write::write_bits(&mut self.buf, self.pos, n, v);
        proof {
            let after = bits_of(self.buf@);
            assert(after =~= before.take(self.pos as int) + bits_seq(v, n as nat)
                             + before.skip(self.pos as int + n as int));
            assert(after.take(self.pos as int + n as int)
                   =~= before.take(self.pos as int) + bits_seq(v, n as nat));
        }
        self.pos = self.pos + n;
        true
    }
}

} // verus!

verus! {

use crate::term::*;

broadcast use {format_steps, map_steps};

/// Advancing the cursor drops a prefix of the remaining bits. Generated
/// decoders chain this to line their spec up with the spec-level composition.
pub proof fn lemma_rem_skip(buf: Seq<u8>, p: nat, k: nat)
    requires p + k <= 8 * buf.len(),
    ensures bits_of(buf).skip((p + k) as int) =~= bits_of(buf).skip(p as int).skip(k as int),
{
}

impl<'a> BitReader<'a> {
    /// Refines `bool_dec()`.
    #[inline]
    pub fn read_bool(&mut self) -> (res: Option<bool>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => bool_dec()(old(self).rem())
                    == Some::<(bool, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat,
                                                 Flg::SameVer)),
                None => bool_dec()(old(self).rem()).is_none(),
            },
    {
        let ghost start = old(self).rem();
        match self.read_uint(1) {
            Some(v) => {
                proof { lemma_map_dec_some(uint_dec(1), bool_to_f(), start, v, 1, Flg::SameVer); }
                Some(v == 1)
            }
            None => {
                proof { lemma_map_dec_none(uint_dec(1), bool_to_f(), start); }
                None
            }
        }
    }

    /// Refines `int_range_dec(lb, ub, n)`.
    #[inline]
    pub fn read_int_range(&mut self, lb: i64, ub: i64, n: usize) -> (res: Option<i64>)
        requires
            old(self).wf(),
            1 <= n <= 56,
            lb < ub,
            (ub as int) - (lb as int) < p2(n as nat),
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => int_range_dec(lb as int, ub as int, n as nat)(old(self).rem())
                    == Some::<(i64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat,
                                                Flg::SameVer)),
                None => int_range_dec(lb as int, ub as int, n as nat)(old(self).rem()).is_none(),
            },
    {
        proof {
            crate::prim_read::lemma_p2_mono(n as nat, 56);
            crate::prim_read::lemma_p2_56();
        }
        let range: i64 = ub - lb;
        let ghost start = old(self).rem();
        let ghost lbi = lb as int;
        let ghost ubi = ub as int;
        let ghost nn = n as nat;
        match self.read_uint(n) {
            Some(v) => {
                if v <= range as u64 {
                    let out = lb + (v as i64);
                    proof {
                        lemma_restrict_dec_some(uint_dec(nn), ir_ok(lbi, ubi), start, v, nn,
                                                Flg::SameVer);
                        lemma_map_dec_some(ir_base_dec(lbi, ubi, nn), ir_to(lbi), start, v, nn,
                                           Flg::SameVer);
                        assert(ir_to(lbi)(v) == out);
                    }
                    Some(out)
                } else {
                    proof {
                        lemma_restrict_dec_none(uint_dec(nn), ir_ok(lbi, ubi), start);
                        lemma_map_dec_none(ir_base_dec(lbi, ubi, nn), ir_to(lbi), start);
                    }
                    None
                }
            }
            None => {
                proof {
                    lemma_restrict_dec_none(uint_dec(nn), ir_ok(lbi, ubi), start);
                    lemma_map_dec_none(ir_base_dec(lbi, ubi, nn), ir_to(lbi), start);
                }
                None
            }
        }
    }
}

impl BitWriter {
    /// Refines `bool_enc()`.
    #[inline]
    pub fn write_bool(&mut self, v: bool) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + bool_enc()(v),
            !ok ==> final(self).pos == old(self).pos,
    {
        proof { reveal_with_fuel(p2, 3); }
        self.write_uint(1, if v { 1u64 } else { 0u64 })
    }

    /// Refines `int_range_enc(lb, ub, n)`.
    #[inline]
    pub fn write_int_range(&mut self, lb: i64, ub: i64, n: usize, v: i64) -> (ok: bool)
        requires
            old(self).wf(),
            1 <= n <= 56,
            lb < ub,
            (ub as int) - (lb as int) < p2(n as nat),
            lb <= v <= ub,
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written()
                   =~= old(self).written() + int_range_enc(lb as int, ub as int, n as nat)(v),
            !ok ==> final(self).pos == old(self).pos,
    {
        proof {
            crate::prim_read::lemma_p2_mono(n as nat, 56);
            crate::prim_read::lemma_p2_56();
        }
        let d: u64 = (v - lb) as u64;
        proof {
            assert(d == ir_from(lb as int)(v));
            assert((d as nat) < p2(n as nat));
        }
        self.write_uint(n, d)
    }
}

} // verus!

verus! {

use crate::list::*;

impl<'a> BitReader<'a> {
    /// Refines `ulen_dec(lb, ub, n)` -- the constrained length determinant.
    #[inline]
    pub fn read_ulen(&mut self, lb: u64, ub: u64, n: usize) -> (res: Option<u64>)
        requires
            old(self).wf(),
            1 <= n <= 56,
            lb <= ub,
            (ub as nat) - (lb as nat) < p2(n as nat),
            (ub as nat) < p2(56),
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => {
                    &&& ulen_dec(lb as nat, ub as nat, n as nat)(old(self).rem())
                        == Some::<(u64, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat,
                                                    Flg::SameVer))
                    &&& lb <= v <= ub
                },
                None => ulen_dec(lb as nat, ub as nat, n as nat)(old(self).rem()).is_none(),
            },
    {
        let ghost start = old(self).rem();
        let ghost lbn = lb as nat;
        let ghost ubn = ub as nat;
        let ghost nn = n as nat;
        let range: u64 = ub - lb;
        match self.read_uint(n) {
            Some(v) => {
                if v <= range {
                    let out = lb + v;
                    proof {
                        lemma_restrict_dec_some(uint_dec(nn), ulen_ok(lbn, ubn), start, v, nn,
                                                Flg::SameVer);
                        lemma_map_dec_some(ulen_base_dec(lbn, ubn, nn), ulen_to(lbn), start, v, nn,
                                           Flg::SameVer);
                        assert(ulen_to(lbn)(v) == out);
                    }
                    Some(out)
                } else {
                    proof {
                        lemma_restrict_dec_none(uint_dec(nn), ulen_ok(lbn, ubn), start);
                        lemma_map_dec_none(ulen_base_dec(lbn, ubn, nn), ulen_to(lbn), start);
                    }
                    None
                }
            }
            None => {
                proof {
                    lemma_restrict_dec_none(uint_dec(nn), ulen_ok(lbn, ubn), start);
                    lemma_map_dec_none(ulen_base_dec(lbn, ubn, nn), ulen_to(lbn), start);
                }
                None
            }
        }
    }
}

impl BitWriter {
    /// Refines `ulen_enc(lb, ub, n)`.
    #[inline]
    pub fn write_ulen(&mut self, lb: u64, ub: u64, n: usize, v: u64) -> (ok: bool)
        requires
            old(self).wf(),
            1 <= n <= 56,
            lb <= v <= ub,
            (ub as nat) - (lb as nat) < p2(n as nat),
            (ub as nat) < p2(56),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written()
                   =~= old(self).written() + ulen_enc(lb as nat, ub as nat, n as nat)(v),
            !ok ==> final(self).pos == old(self).pos,
    {
        let d: u64 = v - lb;
        proof {
            assert(d == ulen_from(lb as nat)(v));
            assert((d as nat) < p2(n as nat));
        }
        self.write_uint(n, d)
    }
}

} // verus!

verus! {

impl<'a> BitReader<'a> {
    /// Refines `byte_dec()`.
    #[inline]
    pub fn read_byte(&mut self) -> (res: Option<u8>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => byte_dec()(old(self).rem())
                    == Some::<(u8, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat,
                                               Flg::SameVer)),
                None => byte_dec()(old(self).rem()).is_none(),
            },
    {
        let ghost start = old(self).rem();
        match self.read_uint(8) {
            Some(v) => {
                proof { lemma_map_dec_some(uint_dec(8), byte_to(), start, v, 8, Flg::SameVer); }
                Some(v as u8)
            }
            None => {
                proof { lemma_map_dec_none(uint_dec(8), byte_to(), start); }
                None
            }
        }
    }
}

impl BitWriter {
    /// Refines `byte_enc()`.
    #[inline]
    pub fn write_byte(&mut self, v: u8) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + byte_enc()(v),
            !ok ==> final(self).pos == old(self).pos,
    {
        proof { reveal_with_fuel(p2, 10); }
        self.write_uint(8, v as u64)
    }
}

} // verus!

verus! {

use crate::opt::*;

impl<'a> BitReader<'a> {
    /// Refines `null_dec()`. Consumes nothing.
    #[inline]
    pub fn read_null(&mut self) -> (res: Option<Null>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            match res {
                Some(v) => null_dec()(old(self).rem())
                    == Some::<(Null, nat, Flg)>((v, (final(self).pos - old(self).pos) as nat,
                                                 Flg::SameVer)),
                None => null_dec()(old(self).rem()).is_none(),
            },
    {
        proof { lemma_unit_dec_val(Null, old(self).rem()); }
        Some(Null)
    }
}

impl BitWriter {
    /// Refines `null_enc()`. Writes nothing.
    #[inline]
    pub fn write_null(&mut self, v: Null) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + null_enc()(v),
            !ok ==> final(self).pos == old(self).pos,
    {
        proof {
            lemma_unit_enc_val(v);
            assert(old(self).written() + null_enc()(v) =~= old(self).written());
        }
        true
    }
}

} // verus!

verus! {

impl BitWriter {
    /// Append the first `nbits` bits of `src`.
    ///
    /// An open type has to state its content's length before the content, and
    /// the length is not known until the content has been encoded. So the
    /// content is encoded into a scratch buffer, measured, and then spliced in
    /// after the determinant -- which is what this does. Copying 56 bits at a
    /// time rather than one keeps it a shift-and-mask per word instead of per
    /// bit.
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn write_slice(&mut self, src: &[u8], from: usize, nbits: usize) -> (ok: bool)
        requires
            old(self).wf(),
            from + nbits <= 8 * src@.len(),
            8 * src@.len() <= usize::MAX,
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> {
                &&& final(self).pos == old(self).pos + nbits
                &&& final(self).written()
                    =~= old(self).written()
                        + bits_of(src@).skip(from as int).take(nbits as int)
            },
    {
        let ghost w0 = *self;
        let ghost sbits = bits_of(src@).skip(from as int);
        let mut r = BitReader::new(src);
        r.pos = from;
        let mut done: usize = 0;
        while done < nbits
            invariant
                self.wf(),
                r.wf(),
                r.buf == src,
                r.pos == from + done,
                done <= nbits,
                from + nbits <= 8 * src@.len(),
                sbits == bits_of(src@).skip(from as int),
                self.buf@.len() == w0.buf@.len(),
                self.pos == w0.pos + done,
                self.written() =~= w0.written() + sbits.take(done as int),
            decreases nbits - done,
        {
            let n: usize = if nbits - done > 56 { 56 } else { nbits - done };
            let ghost rem0 = r.rem();
            proof { lemma_uint_format(n as nat); }
            let v = match r.read_uint(n) {
                Some(v) => v,
                None => return false,
            };
            // `uint`'s two injection properties: the value is in range, so it
            // can be written back, and the bits it came from are exactly its
            // encoding
            assert(uint_wf(n as nat)(v));
            assert(rem0.take(n as int) == uint_enc(n as nat)(v));
            let ghost before = self.written();
            if !self.write_uint(n, v) {
                return false;
            }
            proof {
                assert(rem0 =~= sbits.skip(done as int));
                lemma_take_split(sbits, done as nat, n as nat);
                assert(self.written() =~= before + bits_seq(v, n as nat));
            }
            done = done + n;
        }
        assert(done == nbits);
        true
    }
}

} // verus!

verus! {

impl<'a> BitReader<'a> {
    /// Consume `n` octets and append them to `out`.
    ///
    /// The bits are copied rather than pointed at: the source is at an
    /// arbitrary bit offset, and a fragmented value's octets are not
    /// contiguous on the wire anyway, so there is nothing to borrow.
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn read_octets(&mut self, n: usize, out: &mut Vec<u8>) -> (ok: bool)
        requires old(self).wf(), 8 * n <= usize::MAX,
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos >= old(self).pos,
            ok ==> {
                &&& final(self).pos == old(self).pos + 8 * n
                &&& bits_of(final(out)@)
                    =~= bits_of(old(out)@) + old(self).rem().take((8 * n) as int)
            },
            // a caller that has already checked the bits are there can rely on
            // this succeeding, which is what makes the failure paths of a
            // fragmented read provably unreachable
            8 * n <= 8 * old(self).buf@.len() - old(self).pos ==> ok,
    {
        let ghost r0 = *self;
        let ghost o0 = old(out)@;
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(),
                self.buf == r0.buf,
                i <= n,
                8 * n <= usize::MAX,
                self.pos == r0.pos + 8 * i,
                bits_of(out@) =~= bits_of(o0) + r0.rem().take((8 * i) as int),
            decreases n - i,
        {
            proof { lemma_rem_skip(self.buf@, r0.pos as nat, (8 * i) as nat); }
            let ghost bi = self.rem();
            let v = match self.read_byte() {
                Some(v) => v,
                None => {
                    proof {
                        reveal(map_dec);
                        assert(self.rem().len() == 8 * self.buf@.len() - self.pos);
                        assert(self.rem().len() < 8);
                    }
                    return false;
                },
            };
            proof {
                lemma_byte_format();
                // the eight bits just consumed are exactly this byte's encoding
                assert(bi.take(8) == byte_enc()(v));
                assert(byte_enc()(v) =~= bits_seq(v as u64, 8));
                lemma_bits_of_push(out@, v);
                lemma_take_split(r0.rem(), (8 * i) as nat, 8nat);
                assert(bi =~= r0.rem().skip((8 * i) as int));
            }
            out.push(v);
            i = i + 1;
        }
        true
    }
}

} // verus!
