// Fast path for the window load: eight in-bounds indexed reads, which LLVM
// merges into one unaligned 64-bit load. No unsafe, no trusted primitive.
use vstd::prelude::*;
use crate::bitspec::*;
use crate::bytebits::*;
use crate::prim_read::*;

verus! {

proof fn bv_assemble(b0: u64, b1: u64, b2: u64, b3: u64, b4: u64, b5: u64, b6: u64, b7: u64)
    by (bit_vector)
    requires
        b0 < 256, b1 < 256, b2 < 256, b3 < 256,
        b4 < 256, b5 < 256, b6 < 256, b7 < 256,
    ensures
        (b0 << 56u64) | (b1 << 48u64) | (b2 << 40u64) | (b3 << 32u64)
      | (b4 << 24u64) | (b5 << 16u64) | (b6 << 8u64) | b7
      == add(mul(add(mul(add(mul(add(mul(add(mul(add(mul(add(mul(b0, 256), b1), 256), b2), 256),
         b3), 256), b4), 256), b5), 256), b6), 256), b7),
{
}

/// One 64-bit big-endian window load, fast path (fully in bounds).
#[inline]
pub fn load_window_fast(s: &[u8], i: usize) -> (w: u64)
    requires i + 8 <= s.len(),
    ensures w as nat == bits_val(bview(s@).subrange(8 * i as int, 8 * i as int + 64)),
{
    let b0 = s[i] as u64;
    let b1 = s[i + 1] as u64;
    let b2 = s[i + 2] as u64;
    let b3 = s[i + 3] as u64;
    let b4 = s[i + 4] as u64;
    let b5 = s[i + 5] as u64;
    let b6 = s[i + 6] as u64;
    let b7 = s[i + 7] as u64;
    let w = (b0 << 56u64) | (b1 << 48u64) | (b2 << 40u64) | (b3 << 32u64)
          | (b4 << 24u64) | (b5 << 16u64) | (b6 << 8u64) | b7;
    proof {
        bv_assemble(b0, b1, b2, b3, b4, b5, b6, b7);
        let ghost win = bwin(s@, i as int, 8);
        // unfold the window byte by byte
        assert(bwin(s@, i as int, 0) =~= Seq::<u8>::empty());
        lemma_step(s@, i as int, 0, b0 as u8);
        lemma_step(s@, i as int, 1, b1 as u8);
        lemma_step(s@, i as int, 2, b2 as u8);
        lemma_step(s@, i as int, 3, b3 as u8);
        lemma_step(s@, i as int, 4, b4 as u8);
        lemma_step(s@, i as int, 5, b5 as u8);
        lemma_step(s@, i as int, 6, b6 as u8);
        lemma_step(s@, i as int, 7, b7 as u8);
        lemma_bview_window(s@, i as int, 8);
    }
    w
}

proof fn lemma_step(s: Seq<u8>, i: int, k: nat, b: u8)
    requires 0 <= i, i + k < s.len(), b == s[i + k],
    ensures
        bits_val(bits_of(bwin(s, i, (k + 1) as nat)))
            == bits_val(bits_of(bwin(s, i, k))) * 256 + b as nat,
{
    assert(bwin(s, i, (k + 1) as nat) =~= bwin(s, i, k).push(b));
    lemma_bits_val_push_byte(bwin(s, i, k), b);
}

/// `read_bits` with the fast path taken whenever the window is in bounds.
#[inline]
pub fn read_bits_fast(s: &[u8], pos: usize, n: usize) -> (v: u64)
    requires
        1 <= n <= 56,
        pos + n <= 8 * s.len(),
        pos + n <= usize::MAX,
    ensures
        v as nat == bits_val(bview(s@).subrange(pos as int, pos as int + n as int)),
{
    let i: usize = pos / 8;
    let off: usize = pos % 8;
    assert(i <= s.len()) by (nonlinear_arith)
        requires i == pos / 8, pos + n <= 8 * s.len(), n >= 0;
    let w = if i + 8 <= s.len() { load_window_fast(s, i) } else { load_window(s, i) };
    let sh: usize = 64 - off - n;
    let nn: u64 = n as u64;
    assert(1u64 << nn >= 1) by (bit_vector) requires nn <= 56;
    let mask: u64 = (1u64 << nn) - 1;
    assert(sh < 64);
    let v = (w >> (sh as u64)) & mask;
    proof {
        let t = bview(s@).subrange(8 * i as int, 8 * i as int + 64);
        assert(pos == 8 * i + off);
        assert(t.subrange(off as int, off as int + n as int)
               =~= bview(s@).subrange(pos as int, pos as int + n as int));
        lemma_bits_val_subrange(t, off as int, off as int + n as int);
        assert(t.len() == 64);
        lemma_p2_eq_pow2(sh as nat);
        lemma_p2_eq_pow2(n as nat);
        vstd::bits::lemma_u64_shr_is_div(w, sh as u64);
        vstd::bits::lemma_u64_pow2_no_overflow(n as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, nn);
        assert(mask == vstd::bits::low_bits_mask(n as nat) as u64);
        vstd::bits::lemma_u64_low_bits_mask_is_mod(w >> (sh as u64), n as nat);
    }
    v
}

} // verus!
