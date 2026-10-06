//! Unsigned fields of up to 64 bits: `read_uint` and `write_uint` take up to
//! 56 (one unaligned 64-bit load holds them at any bit offset), and a field
//! of 57 to 64 bits is two of those, the high `n - 32` bits then the low 32.
//! What the 3GPP protocols' 64-bit counters need, `INTEGER (0..2^64-1)`
//! (`usageCountUL`): 64 bits in UNALIGNED, up to eight octets in ALIGNED.
//! In a module of its own so that its proofs do not share a solver
//! process with the cursor's.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::uper::format::*;
use crate::uper::prim::*;
use crate::uper::cursor::*;
#[cfg(verus_keep_ghost)]
use crate::bits::prim_write::{bits_seq, lemma_bits_seq_val, lemma_bits_val_inj};

verus! {

/// `hi` and `lo` as one 64-bit value, high part first.
proof fn lemma_join(hi: u64, lo: u64)
    requires hi < 0x1_0000_0000u64, lo < 0x1_0000_0000u64,
    ensures
        (hi << 32u64) | lo == hi * 0x1_0000_0000u64 + lo,
        (hi as nat) * 0x1_0000_0000nat + (lo as nat) < 0x1_0000_0000_0000_0000nat,
{
    assert((hi << 32u64) | lo == hi * 0x1_0000_0000u64 + lo) by (bit_vector)
        requires hi < 0x1_0000_0000u64, lo < 0x1_0000_0000u64;
    assert((hi as nat) * 0x1_0000_0000nat + (lo as nat) < 0x1_0000_0000_0000_0000nat) by (nonlinear_arith)
        requires (hi as nat) < 0x1_0000_0000nat, (lo as nat) < 0x1_0000_0000nat;
}

/// A value's `n` bits are its high `n - 32` bits, then its low 32.
proof fn lemma_split_seq(v: u64, n: nat)
    requires 32 < n <= 64, (v as nat) < p2(n),
    ensures
        (v >> 32u64) as nat == (v as nat) / 0x1_0000_0000nat,
        (v & 0xffff_ffffu64) as nat == (v as nat) % 0x1_0000_0000nat,
        ((v >> 32u64) as nat) < p2((n - 32) as nat),
        bits_seq(v, n) =~= bits_seq(v >> 32u64, (n - 32) as nat) + bits_seq(v & 0xffff_ffffu64, 32),
{
    let hi = v >> 32u64;
    let lo = v & 0xffff_ffffu64;
    let h = (n - 32) as nat;
    assert((v >> 32u64) == v / 0x1_0000_0000u64 && (v & 0xffff_ffffu64) == v % 0x1_0000_0000u64)
        by (bit_vector);
    crate::bits::prim_read::lemma_p2_64();
    lemma_p2_adds(h, 32);
    assert(p2(32) == 0x1_0000_0000nat) by {
        crate::uper::intx::lemma_p2_octets();
    }
    assert((hi as nat) < p2(h)) by (nonlinear_arith)
        requires (v as nat) < p2(n), p2(n) == p2(h) * 0x1_0000_0000nat,
                 hi as nat == (v as nat) / 0x1_0000_0000nat;
    assert((lo as nat) < p2(32));
    let s = bits_seq(hi, h) + bits_seq(lo, 32);
    lemma_bits_seq_val(hi, h);
    lemma_bits_seq_val(lo, 32);
    lemma_bits_seq_val(v, n);
    lemma_bits_val_split(s, h as int);
    assert(s.take(h as int) =~= bits_seq(hi, h));
    assert(s.skip(h as int) =~= bits_seq(lo, 32));
    assert(bits_val(s) == (hi as nat) * 0x1_0000_0000nat + (lo as nat));
    assert((v as nat) == (hi as nat) * 0x1_0000_0000nat + (lo as nat)) by (nonlinear_arith)
        requires hi as nat == (v as nat) / 0x1_0000_0000nat, lo as nat == (v as nat) % 0x1_0000_0000nat;
    lemma_bits_val_inj(bits_seq(v, n), s);
}

impl<'a> BitReader<'a> {
    /// Consume an unsigned `n`-bit field, `n` up to 64. Refines `uint_dec(n)`.
    pub fn read_uint_wide(&mut self, n: usize) -> (res: Option<u64>)
        requires old(self).wf(), 1 <= n <= 64,
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
        if n <= 56 {
            return self.read_uint(n);
        }
        let ghost b = self.rem();
        let p0 = self.pos;
        let h: usize = n - 32;
        let hi = match self.read_uint(h) {
            Some(x) => x,
            None => return None,
        };
        proof { assert(self.rem() =~= b.skip(h as int)); }
        let lo = match self.read_uint(32) {
            Some(x) => x,
            None => {
                self.pos = p0;
                proof { assert(self.rem() =~= b); }
                return None;
            }
        };
        let ghost t = b.take(n as int);
        proof {
            crate::uper::intx::lemma_p2_octets();
            lemma_bits_val_bound(b.take(h as int));
            crate::bits::prim_read::lemma_p2_mono(h as nat, 32);
            lemma_bits_val_bound(b.skip(h as int).take(32));
            assert(hi as nat == bits_val(b.take(h as int)));
            assert(lo as nat == bits_val(b.skip(h as int).take(32)));
            lemma_join(hi, lo);
            lemma_bits_val_split(t, h as int);
            assert(t.take(h as int) =~= b.take(h as int));
            assert(t.skip(h as int) =~= b.skip(h as int).take(32));
            assert(p2((n - h) as nat) == 0x1_0000_0000nat);
            assert(bits_val(t) == (hi as nat) * 0x1_0000_0000nat + (lo as nat));
        }
        Some((hi << 32u64) | lo)
    }
}

impl BitWriter {
    /// Append an unsigned `n`-bit field, `n` up to 64. Refines `uint_enc(n)`.
    pub fn write_uint_wide(&mut self, n: usize, v: u64) -> (ok: bool)
        requires old(self).wf(), 1 <= n <= 64, uint_wf(n as nat)(v),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> {
                &&& final(self).pos == old(self).pos + n
                &&& final(self).written() =~= old(self).written() + uint_enc(n as nat)(v)
            },
            !ok ==> final(self).pos == old(self).pos,
    {
        if n <= 56 {
            return self.write_uint(n, v);
        }
        let p0 = self.pos;
        let ghost w0 = self.written();
        let h: usize = n - 32;
        let hi = v >> 32u64;
        let lo = v & 0xffff_ffffu64;
        proof {
            lemma_split_seq(v, n as nat);
            crate::uper::intx::lemma_p2_octets();
            assert((v & 0xffff_ffffu64) < 0x1_0000_0000u64) by (bit_vector);
        }
        if !self.write_uint(h, hi) {
            return false;
        }
        if !self.write_uint(32, lo) {
            self.pos = p0;
            return false;
        }
        true
    }
}

} // verus!
