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

/// The `n` bits at offset `off` of the window `w` loaded at byte `i`.
#[inline]
fn window_bits(s: &[u8], i: usize, off: usize, n: usize, w: u64) -> (v: u64)
    requires
        1 <= n <= 56, off < 8, i <= s.len(),
        w as nat == bits_val(bview(s@).subrange(8 * i as int, 8 * i as int + 64)),
    ensures
        v as nat == bits_val(bview(s@).subrange(8 * i + off as int, 8 * i + off + n as int)),
{
    let sh: usize = 64 - off - n;
    let nn: u64 = n as u64;
    assert(1u64 << nn >= 1) by (bit_vector) requires nn <= 56;
    let mask: u64 = (1u64 << nn) - 1;
    assert(sh < 64);
    let v = (w >> (sh as u64)) & mask;
    proof {
        let t = bview(s@).subrange(8 * i as int, 8 * i as int + 64);
        assert(t.subrange(off as int, off as int + n as int)
               =~= bview(s@).subrange(8 * i + off as int, 8 * i + off + n as int));
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

proof fn lemma_bits_val_zeros(s: Seq<bool>)
    requires forall|m: int| 0 <= m < s.len() ==> !s[m],
    ensures bits_val(s) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        assert forall|m: int| 0 <= m < s.drop_last().len() implies !s.drop_last()[m] by { assert(s.drop_last()[m] == s[m]); }
        lemma_bits_val_zeros(s.drop_last());
        assert(!s.last());
        assert(bits_val(s) == 2nat * bits_val(s.drop_last()) + (if s.last() { 1nat } else { 0nat }));
    } else {
        assert(bits_val(s) == 0);
    }
}

/// The window at byte `i` of a buffer of eight bytes or more, past where a
/// whole window fits: its last eight bytes in one load, shifted up by what
/// runs past the end.
#[inline]
pub fn load_window_tail(s: &[u8], i: usize) -> (w: u64)
    requires 8 <= s.len(), s.len() - 8 < i <= s.len(),
    ensures w as nat == bits_val(bview(s@).subrange(8 * i as int, 8 * i as int + 64)),
{
    let b = s.len() - 8;
    let d = i - b;
    let ghost v = bview(s@);
    let ghost x = v.subrange(8 * i as int, 8 * i as int + 64);
    let ghost k = (8 * s.len() - 8 * i) as nat;
    proof {
        assert forall|m: int| 0 <= m < x.skip(k as int).len() implies !x.skip(k as int)[m] by {
            assert(x.skip(k as int)[m] == v[8 * i + k + m]);
            assert(8 * i + k + m >= 8 * s@.len());
        }
        lemma_bits_val_zeros(x.skip(k as int));
        lemma_bits_val_split(x, k as int);
    }
    if d == 8 {
        proof {
            assert(k == 0);
            assert(x.take(0) =~= Seq::<bool>::empty());
            assert(bits_val(x.take(0)) == 0);
            assert(bits_val(x.skip(0)) == 0);
            assert(bits_val(x.take(k as int)) * p2((x.len() - k) as nat) == 0) by (nonlinear_arith)
                requires bits_val(x.take(k as int)) == 0;
            assert(bits_val(x) == 0);
        }
        return 0;
    }
    let w0 = load_window_fast(s, b);
    let sh: u64 = (8 * d) as u64;
    let kk: u64 = 64 - sh;
    assert(1u64 << kk >= 1) by (bit_vector) requires 8 <= kk <= 56;
    let mask: u64 = (1u64 << kk) - 1;
    let lo = w0 & mask;
    proof {
        let t = v.subrange(8 * b as int, 8 * b as int + 64);
        assert(k == kk);
        assert(x.take(k as int) =~= t.subrange(sh as int, 64));
        lemma_bits_val_subrange(t, sh as int, 64);
        assert(t.len() == 64);
        assert(p2(0) == 1);
        assert(bits_val(t) / p2(0) == bits_val(t)) by (nonlinear_arith) requires p2(0) == 1;
        assert(k == 64 - sh);
        lemma_p2_eq_pow2(k);
        lemma_p2_eq_pow2(sh as nat);
        lemma_p2_adds(k, sh as nat);
        lemma_p2_64();
        vstd::bits::lemma_u64_pow2_no_overflow(k);
        vstd::bits::lemma_u64_shl_is_mul(1u64, kk);
        assert(mask == vstd::bits::low_bits_mask(k) as u64);
        vstd::bits::lemma_u64_low_bits_mask_is_mod(w0, k);
        assert(lo as nat == bits_val(t) % p2(k));
        assert((lo as nat) < p2(k)) by {
            lemma_p2_pos(k);
            vstd::arithmetic::div_mod::lemma_mod_bound(bits_val(t) as int, p2(k) as int);
        }
        lemma_p2_pos(sh as nat);
        assert(lo as nat * p2(sh as nat) < p2(64)) by (nonlinear_arith)
            requires (lo as nat) < p2(k), p2(64) == p2(k) * p2(sh as nat), p2(sh as nat) > 0;
        vstd::bits::lemma_u64_shl_is_mul(lo, sh);
        assert(bits_val(x.take(k as int)) == bits_val(t) % p2(k));
        assert(x.len() - k == sh);
        assert(bits_val(x) == bits_val(x.take(k as int)) * p2(sh as nat));
        assert((lo << sh) as nat == lo as nat * p2(sh as nat));
    }
    let w = lo << sh;
    w
}

/// The window in the last eight bytes, zero padded, out of line.
#[inline(never)]
pub fn load_window_end(s: &[u8], i: usize) -> (w: u64)
    requires i <= s.len(),
    ensures w as nat == bits_val(bview(s@).subrange(8 * i as int, 8 * i as int + 64)),
{
    if s.len() >= 8 && i > s.len() - 8 { load_window_tail(s, i) } else { load_window(s, i) }
}

/// `read_bits_fast` with the slow window out of line, so that the fast path
/// is all it brings to each caller it is inlined into. For a reader inlined
/// into very many places (vasn's generated decoders: 20-30% faster than with
/// the slow window inline), at the price of a call per read in the last
/// eight bytes.
#[inline]
pub fn read_bits_fast_ool(s: &[u8], pos: usize, n: usize) -> (v: u64)
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
    let w = if i + 8 <= s.len() { load_window_fast(s, i) } else { load_window_end(s, i) };
    window_bits(s, i, off, n, w)
}

} // verus!
