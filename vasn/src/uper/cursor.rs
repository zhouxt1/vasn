//! Executable cursors. Every generated decoder threads a `BitReader`; every
//! generated encoder threads a `BitWriter`. Their contracts are stated directly
//! against the spec-level `uint_dec` / `uint_enc`, so generated code never has
//! to reason about buffers or bit offsets again.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::bits::bytebits::*;
use crate::uper::format::*;
use crate::uper::prim::*;
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use crate::bits::prim_write::bits_seq;
use crate::uper::err::DecodeError;

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
        let v = crate::bits::fastload::read_bits_fast_ool(self.buf, self.pos, n);
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
    /// buffers for open types' contents, kept between them (`scratch`,
    /// `give_back`); no part of any contract
    pub spare: Vec<Vec<u8>>,
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
        // one zeroed allocation; nothing depends on the contents, since what
        // has been written is the bits before `pos`
        let buf: Vec<u8> = vec![0u8; nbytes];
        BitWriter { buf, pos: 0, spare: Vec::new() }
    }

    /// A writer for an open type's content, as large as this one: a spare
    /// buffer if there is one of that size, else a new one. It takes the
    /// other spares with it, for the open types inside; `give_back` returns
    /// them all.
    #[inline]
    pub fn scratch(&mut self) -> (sc: BitWriter)
        requires 8 * old(self).buf@.len() <= usize::MAX,
        ensures
            final(self).buf == old(self).buf, final(self).pos == old(self).pos,
            sc.wf(), sc.pos == 0, sc.buf@.len() == old(self).buf@.len(),
            sc.written() =~= Seq::<bool>::empty(),
    {
        let n = self.buf.len();
        let mut pool: Vec<Vec<u8>> = Vec::new();
        core::mem::swap(&mut pool, &mut self.spare);
        let buf = match pool.pop() {
            Some(b) if b.len() == n => b,
            _ => vec![0u8; n],
        };
        BitWriter { buf, pos: 0, spare: pool }
    }

    /// Take back what `scratch` gave out.
    #[inline]
    pub fn give_back(&mut self, sc: BitWriter)
        ensures final(self).buf == old(self).buf, final(self).pos == old(self).pos,
    {
        let BitWriter { buf, pos: _, spare } = sc;
        self.spare = spare;
        self.spare.push(buf);
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
        if self.pos / 8 + 8 <= self.buf.len() {
            // one store, leaving what follows the field as it may
            crate::bits::faststore::store_bits(&mut self.buf, self.pos, n, v);
        } else {
            // the last eight bytes, a bit at a time
            crate::bits::prim_write::write_bits(&mut self.buf, self.pos, n, v);
            proof {
                let after = bits_of(self.buf@);
                assert(after =~= before.take(self.pos as int) + bits_seq(v, n as nat)
                                 + before.skip(self.pos as int + n as int));
                assert(after.take(self.pos as int + n as int)
                       =~= before.take(self.pos as int) + bits_seq(v, n as nat));
            }
        }
        self.pos = self.pos + n;
        true
    }
}

} // verus!

verus! {

use crate::uper::term::*;

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
            crate::bits::prim_read::lemma_p2_mono(n as nat, 56);
            crate::bits::prim_read::lemma_p2_56();
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
            crate::bits::prim_read::lemma_p2_mono(n as nat, 56);
            crate::bits::prim_read::lemma_p2_56();
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

use crate::uper::list::*;

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

use crate::uper::opt::*;

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
    /// `src[i..i + n]` onto an octet boundary, as a slice copy.
    #[inline]
    fn write_octets_aligned(&mut self, src: &[u8], i: usize, n: usize)
        requires
            old(self).wf(), old(self).pos % 8 == 0,
            i + n <= src@.len(), 8 * src@.len() <= usize::MAX,
            old(self).pos / 8 + n <= old(self).buf@.len(),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            final(self).pos == old(self).pos + 8 * n,
            final(self).written() =~= old(self).written() + bits_of(src@.subrange(i as int, (i + n) as int)),
    {
        let ghost b0 = self.buf@;
        let j = self.pos / 8;
        let part = vstd::slice::slice_subrange(src, i, i + n);
        {
            let s = self.buf.as_mut_slice();
            let (_head, rest) = s.split_at_mut(j);
            let (mid, _tail) = rest.split_at_mut(n);
            mid.copy_from_slice(part);
        }
        proof {
            assert(self.buf@ =~= b0.take(j as int) + src@.subrange(i as int, (i + n) as int)
                                + b0.skip((j + n) as int));
            crate::bits::bytebits::lemma_bits_of_add(b0.take(j as int), b0.skip(j as int));
            assert(b0 =~= b0.take(j as int) + b0.skip(j as int));
            crate::bits::bytebits::lemma_bits_of_add(b0.take(j as int), src@.subrange(i as int, (i + n) as int));
            crate::bits::bytebits::lemma_bits_of_add(
                b0.take(j as int) + src@.subrange(i as int, (i + n) as int), b0.skip((j + n) as int));
            assert(8 * j == self.pos);
            assert(bits_of(b0).take(self.pos as int) =~= bits_of(b0.take(j as int)));
        }
        self.pos = self.pos + 8 * n;
    }

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
        // short: 56 bits at a time
        if nbits < 128 {
            return self.write_slice_bits(src, from, nbits);
        }
        let ghost w0 = self.written();
        let ghost sb = bits_of(src@).skip(from as int);
        // the bits that bring the output to an octet boundary
        let h: usize = (8 - self.pos % 8) % 8;
        if !self.write_slice_bits(src, from, h) {
            return false;
        }
        let f1 = from + h;
        let r = nbits - h;
        let n = r / 8;
        if n > self.buf.len() - self.pos / 8 {
            return false;
        }
        let ghost w1 = self.written();
        // then whole octets: copied if the input is on a boundary too, else
        // sixteen at a time in SSE2
        let m = self.write_octets_from(src, f1, n);
        let ghost w2 = self.written();
        // and what is left
        let ok = self.write_slice_bits(src, f1 + 8 * m, r - 8 * m);
        proof {
            let s1 = bits_of(src@).skip(f1 as int);
            assert(sb.take(h as int) =~= bits_of(src@).skip(from as int).take(h as int));
            assert(s1 =~= sb.skip(h as int));
            assert(bits_of(src@).skip((f1 + 8 * m) as int) =~= s1.skip((8 * m) as int));
            assert(sb.take(nbits as int) =~= sb.take(h as int) + s1.take((8 * m) as int)
                   + s1.skip((8 * m) as int).take((r - 8 * m) as int));
        }
        ok
    }

    /// Whole octets onto an octet boundary from bit `f` of `src`: copied when
    /// `f` is on one too, else sixteen at a time (`write_wide`); how many.
    #[inline]
    fn write_octets_from(&mut self, src: &[u8], f: usize, n: usize) -> (m: usize)
        requires
            old(self).wf(), old(self).pos % 8 == 0,
            f + 8 * n <= 8 * src@.len(), 8 * src@.len() <= usize::MAX,
            old(self).pos / 8 + n <= old(self).buf@.len(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(), m <= n,
            final(self).pos == old(self).pos + 8 * m,
            final(self).written() =~= old(self).written() + bits_of(src@).skip(f as int).take((8 * m) as int),
    {
        if f % 8 == 0 {
            self.write_octets_aligned(src, f / 8, n);
            proof {
                crate::uper::fast::lemma_bits_of_subrange(src@, (f / 8) as int, (f / 8 + n) as int);
                assert(bits_of(src@).skip(f as int).take((8 * n) as int)
                       =~= bits_of(src@).subrange(f as int, (f + 8 * n) as int));
            }
            n
        } else {
            self.write_wide(src, f, n)
        }
    }

    /// `write_octets_from` off an octet boundary, sixteen octets at a time in
    /// SSE2 (`uper::simd::shifted16`, as `read_octets` reads them); how many.
    #[cfg(target_arch = "x86_64")]
    #[verifier::loop_isolation(false)]
    #[inline]
    fn write_wide(&mut self, src: &[u8], f: usize, n: usize) -> (m: usize)
        requires
            old(self).wf(), old(self).pos % 8 == 0, f % 8 != 0,
            f + 8 * n <= 8 * src@.len(), 8 * src@.len() <= usize::MAX,
            old(self).pos / 8 + n <= old(self).buf@.len(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(), m <= n,
            final(self).pos == old(self).pos + 8 * m,
            final(self).written() =~= old(self).written() + bits_of(src@).skip(f as int).take((8 * m) as int),
    {
        let ghost w0 = self.written();
        let ghost p0 = self.pos;
        let ghost sb = bits_of(src@).skip(f as int);
        let b0 = f / 8;
        let k = (f % 8) as u32;
        let mut i: usize = 0;
        proof { assert(sb.take(0) =~= Seq::<bool>::empty()); }
        while i + 16 <= n && b0 + i + 17 <= src.len()
            invariant
                self.wf(), self.buf@.len() == old(self).buf@.len(),
                i <= n, self.pos == p0 + 8 * i, p0 == old(self).pos, p0 % 8 == 0,
                p0 / 8 + n <= self.buf@.len(),
                b0 == f / 8, k == f % 8, 1 <= k <= 7,
                f + 8 * n <= 8 * src@.len(), 8 * src@.len() <= usize::MAX,
                sb == bits_of(src@).skip(f as int),
                self.written() =~= w0 + sb.take((8 * i) as int),
            decreases n - i,
        {
            let a = crate::uper::simd::shifted16(src, b0 + i, k);
            proof {
                crate::uper::simd::lemma_shifted16_bits(src@, (b0 + i) as int, k as nat, a@);
                assert(8 * (b0 + i) + k == f + 8 * i);
                assert(a@.subrange(0, 16) =~= a@);
                assert(f + 8 * i + 128 <= 8 * src@.len());
                assert(sb.skip((8 * i) as int).take(128)
                       =~= bits_of(src@).subrange((f + 8 * i) as int, (f + 8 * i + 128) as int));
                assert(bits_of(a@.subrange(0, 16)) =~= sb.skip((8 * i) as int).take(128));
                assert(sb.take((8 * i + 128) as int) =~= sb.take((8 * i) as int) + sb.skip((8 * i) as int).take(128));
            }
            self.write_octets_aligned(a.as_slice(), 0, 16);
            i = i + 16;
        }
        i
    }

    /// Off x86-64, nothing written wide.
    #[cfg(not(target_arch = "x86_64"))]
    #[inline]
    fn write_wide(&mut self, src: &[u8], f: usize, n: usize) -> (m: usize)
        requires
            old(self).wf(), old(self).pos % 8 == 0, f % 8 != 0,
            f + 8 * n <= 8 * src@.len(), 8 * src@.len() <= usize::MAX,
            old(self).pos / 8 + n <= old(self).buf@.len(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(), m <= n,
            final(self).pos == old(self).pos + 8 * m,
            final(self).written() =~= old(self).written() + bits_of(src@).skip(f as int).take((8 * m) as int),
    {
        assert(bits_of(src@).skip(f as int).take(0) =~= Seq::<bool>::empty());
        assert(self.written() =~= old(self).written() + Seq::<bool>::empty());
        0
    }

    /// `write_slice` 56 bits at a time.
    #[verifier::loop_isolation(false)]
    #[inline]
    fn write_slice_bits(&mut self, src: &[u8], from: usize, nbits: usize) -> (ok: bool)
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
    /// contiguous on the wire anyway, so there is nothing to borrow. On an
    /// octet boundary the octets are copied as a slice; otherwise seven per
    /// 56-bit read straight from the buffer, the length checked once, and
    /// appended as one array (`fast::word_octets`); the last few one read
    /// each.
    #[verifier::rlimit(60)]
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
        if 8 * n > self.buf.len() * 8 - self.pos {
            return false;
        }
        if self.pos % 8 == 0 {
            self.octets_aligned(n, out);
            return true;
        }
        let ghost s0 = self.rem();
        let ghost p0 = self.pos;
        let ghost o0 = old(out)@;
        out.reserve(n);
        assert(out@ == o0);
        let k = self.octets_wide(n, out);
        proof { lemma_rem_skip(self.buf@, p0 as nat, (8 * k) as nat); }
        assert(self.rem() =~= s0.skip((8 * k) as int));
        let ghost s1 = self.rem();
        let ghost p1 = self.pos;
        let m = n - k;
        let w = m - m % 7;
        self.octets_words(w, out);
        proof { lemma_rem_skip(self.buf@, p1 as nat, (8 * w) as nat); }
        assert(self.rem() =~= s1.skip((8 * w) as int));
        self.octets_bytes(m - w, out);
        assert(s1.take((8 * w) as int) + s1.skip((8 * w) as int).take((8 * (m - w)) as int)
               =~= s1.take((8 * m) as int));
        assert(s0.take((8 * k) as int) + s0.skip((8 * k) as int).take((8 * m) as int)
               =~= s0.take((8 * n) as int));
        true
    }

    /// The first octets of an unaligned `read_octets`, sixteen at a time in
    /// SSE2 (`uper::simd`); how many it read, a multiple of 16.
    #[cfg(target_arch = "x86_64")]
    #[verifier::loop_isolation(false)]
    #[inline]
    fn octets_wide(&mut self, n: usize, out: &mut Vec<u8>) -> (k: usize)
        requires old(self).wf(), old(self).pos % 8 != 0,
            8 * n <= 8 * old(self).buf@.len() - old(self).pos,
        ensures
            final(self).wf(), final(self).buf == old(self).buf, k <= n,
            final(self).pos == old(self).pos + 8 * k,
            bits_of(final(out)@) =~= bits_of(old(out)@) + old(self).rem().take((8 * k) as int),
    {
        let ghost r0 = *self;
        let ghost o0 = old(out)@;
        let mut i: usize = 0;
        while i + 16 <= n
            invariant
                self.wf(), self.buf == r0.buf,
                i <= n,
                8 * n <= 8 * r0.buf@.len() - r0.pos,
                r0.pos % 8 != 0,
                self.pos == r0.pos + 8 * i,
                bits_of(out@) =~= bits_of(o0) + r0.rem().take((8 * i) as int),
            decreases n - i,
        {
            let p = self.pos;
            let b = p / 8;
            let k = (p % 8) as u32;
            assert(p % 8 == r0.pos % 8) by (nonlinear_arith)
                requires p == r0.pos + 8 * i;
            assert(b + 17 <= self.buf@.len()) by (nonlinear_arith)
                requires b == p / 8, p % 8 >= 1, p + 8 * (n - i) <= 8 * self.buf@.len(),
                         n - i >= 16;
            let ghost bi = self.rem();
            proof { lemma_rem_skip(self.buf@, r0.pos as nat, (8 * i) as nat); }
            assert(bi =~= r0.rem().skip((8 * i) as int));
            let a = crate::uper::simd::shifted16(self.buf, b, k);
            proof {
                crate::uper::simd::lemma_shifted16_bits(self.buf@, b as int, k as nat, a@);
                assert(8 * b + k == p);
                assert(bi.take(128) =~= bits_of(self.buf@).subrange(p as int, p + 128));
                crate::bits::bytebits::lemma_bits_of_add(out@, a@);
                assert(r0.rem().take((8 * i + 128) as int)
                       =~= r0.rem().take((8 * i) as int) + bi.take(128));
            }
            let ghost before = out@;
            out.extend_from_slice(a.as_slice());
            assert(out@ =~= before + a@);
            self.pos = p + 128;
            i = i + 16;
        }
        i
    }

    /// Off x86-64, nothing read wide.
    #[cfg(not(target_arch = "x86_64"))]
    #[inline]
    fn octets_wide(&mut self, n: usize, out: &mut Vec<u8>) -> (k: usize)
        requires old(self).wf(), old(self).pos % 8 != 0,
            8 * n <= 8 * old(self).buf@.len() - old(self).pos,
        ensures
            final(self).wf(), final(self).buf == old(self).buf, k <= n,
            final(self).pos == old(self).pos + 8 * k,
            bits_of(final(out)@) =~= bits_of(old(out)@) + old(self).rem().take((8 * k) as int),
    {
        assert(bits_of(old(out)@) + self.rem().take(0) =~= bits_of(out@));
        0
    }

    /// `read_octets` on an octet boundary: the octets themselves.
    #[inline]
    fn octets_aligned(&mut self, n: usize, out: &mut Vec<u8>)
        requires old(self).wf(), old(self).pos % 8 == 0,
            8 * n <= 8 * old(self).buf@.len() - old(self).pos,
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos == old(self).pos + 8 * n,
            bits_of(final(out)@) =~= bits_of(old(out)@) + old(self).rem().take((8 * n) as int),
    {
        let ghost s0 = self.rem();
        let ghost o0 = old(out)@;
        let j = self.pos / 8;
        assert(j + n <= self.buf.len()) by (nonlinear_arith)
            requires j == self.pos / 8, self.pos % 8 == 0,
                     8 * n <= 8 * self.buf@.len() - self.pos;
        out.extend_from_slice(vstd::slice::slice_subrange(self.buf, j, j + n));
        proof {
            crate::bits::bytebits::lemma_bits_of_add(o0, self.buf@.subrange(j as int, (j + n) as int));
            crate::uper::fast::lemma_bits_of_subrange(self.buf@, j as int, (j + n) as int);
            assert(8 * j == self.pos);
            assert(s0.take((8 * n) as int)
                   =~= bits_of(self.buf@).subrange(8 * j as int, 8 * (j + n) as int));
        }
        self.pos = self.pos + 8 * n;
    }

    /// `read_octets`, seven octets per 56-bit window read straight from the
    /// buffer: the caller checked the length, once.
    #[verifier::loop_isolation(false)]
    #[inline]
    fn octets_words(&mut self, n: usize, out: &mut Vec<u8>)
        requires old(self).wf(), 8 * n <= 8 * old(self).buf@.len() - old(self).pos, n % 7 == 0,
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos == old(self).pos + 8 * n,
            bits_of(final(out)@) =~= bits_of(old(out)@) + old(self).rem().take((8 * n) as int),
    {
        let ghost r0 = *self;
        let ghost o0 = old(out)@;
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(), self.buf == r0.buf,
                i <= n, i % 7 == 0, n % 7 == 0,
                8 * n <= 8 * r0.buf@.len() - r0.pos,
                self.pos == r0.pos + 8 * i,
                bits_of(out@) =~= bits_of(o0) + r0.rem().take((8 * i) as int),
            decreases n - i,
        {
            let p = self.pos;
            let ghost bi = self.rem();
            proof { lemma_rem_skip(self.buf@, r0.pos as nat, (8 * i) as nat); }
            assert(bi =~= r0.rem().skip((8 * i) as int));
            let w = crate::bits::fastload::read_bits_fast_ool(self.buf, p, 56);
            proof {
                lemma_bview_in_range(self.buf@, p as int, p + 56);
                assert(bi.take(56) =~= bits_of(self.buf@).subrange(p as int, p + 56));
            }
            let a = crate::uper::fast::word_octets(w, Ghost(bi));
            proof {
                crate::bits::bytebits::lemma_bits_of_add(out@, a@);
                assert(r0.rem().take((8 * i + 56) as int)
                       =~= r0.rem().take((8 * i) as int) + bi.take(56));
            }
            let ghost before = out@;
            out.extend_from_slice(a.as_slice());
            assert(out@ =~= before + a@);
            self.pos = p + 56;
            i = i + 7;
        }
    }

    /// `read_octets`, one octet a read: the last few.
    #[verifier::loop_isolation(false)]
    #[inline]
    fn octets_bytes(&mut self, n: usize, out: &mut Vec<u8>)
        requires old(self).wf(), 8 * n <= 8 * old(self).buf@.len() - old(self).pos,
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            final(self).pos == old(self).pos + 8 * n,
            bits_of(final(out)@) =~= bits_of(old(out)@) + old(self).rem().take((8 * n) as int),
    {
        let ghost r0 = *self;
        let ghost o0 = old(out)@;
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(), self.buf == r0.buf,
                i <= n,
                8 * n <= 8 * r0.buf@.len() - r0.pos,
                self.pos == r0.pos + 8 * i,
                bits_of(out@) =~= bits_of(o0) + r0.rem().take((8 * i) as int),
            decreases n - i,
        {
            proof { lemma_rem_skip(self.buf@, r0.pos as nat, (8 * i) as nat); }
            let ghost bi = self.rem();
            let v = match self.read_byte() {
                Some(v) => v,
                None => {
                    proof { reveal(map_dec); }
                    assert(false);
                    return;
                },
            };
            proof {
                reveal(map_dec);
                lemma_byte_format();
                assert(self.pos == r0.pos + 8 * i + 8);
                assert(bi.take(8) == byte_enc()(v));
                assert(byte_enc()(v) =~= bits_seq(v as u64, 8));
                lemma_bits_of_push(out@, v);
                lemma_take_split(r0.rem(), (8 * i) as nat, 8nat);
                assert(bi =~= r0.rem().skip((8 * i) as int));
            }
            out.push(v);
            i = i + 1;
        }
    }
}

} // verus!
