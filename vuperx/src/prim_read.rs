// Verified bit reader: one 64-bit window load per field, arbitrary bit offset.
use vstd::prelude::*;
use crate::bitspec::*;
use crate::bytebits::*;

verus! {

/// Byte `j` of the buffer, or 0 past the end (matches `bview`'s zero padding).
pub open spec fn byte_at(s: Seq<u8>, j: int) -> u8 {
    if 0 <= j < s.len() { s[j] } else { 0u8 }
}

/// The `k`-byte window of the buffer starting at byte `i`, zero padded.
pub open spec fn bwin(s: Seq<u8>, i: int, k: nat) -> Seq<u8> {
    Seq::new(k, |j: int| byte_at(s, i + j))
}

pub proof fn lemma_zero_bits(j: int)
    requires 0 <= j < 8,
    ensures !bit_of(0u8, j),
{
    let k = (7 - j) as u8;
    assert((0u8 >> k) & 1u8 != 1u8) by (bit_vector);
}

/// The padded byte window is exactly the corresponding slice of `bview`.
pub proof fn lemma_bview_window(s: Seq<u8>, i: int, k: nat)
    requires 0 <= i <= s.len(), k <= 8,
    ensures bits_of(bwin(s, i, k)) =~= bview(s).subrange(8 * i, 8 * i + 8 * k),
{
    let l = bits_of(bwin(s, i, k));
    let r = bview(s).subrange(8 * i, 8 * i + 8 * k);
    assert(l.len() == r.len());
    assert forall|m: int| 0 <= m < l.len() implies l[m] == r[m] by {
        assert(m / 8 < k) by (nonlinear_arith) requires 0 <= m < 8 * k;
        assert((8 * i + m) / 8 == i + m / 8) by (nonlinear_arith) requires 0 <= m;
        assert((8 * i + m) % 8 == m % 8) by (nonlinear_arith) requires 0 <= m;
        if i + m / 8 < s.len() {
        } else {
            assert(8 * i + m >= 8 * s.len()) by (nonlinear_arith)
                requires i + m / 8 >= s.len(), 0 <= m, (8 * i + m) / 8 == i + m / 8;
            lemma_zero_bits(m % 8);
        }
    }
}

pub proof fn lemma_p2_mono(a: nat, b: nat)
    requires a <= b,
    ensures p2(a) <= p2(b),
{
    lemma_p2_adds(a, (b - a) as nat);
    lemma_p2_pos((b - a) as nat);
    lemma_p2_pos(a);
    assert(p2(a) * 1 <= p2(a) * p2((b - a) as nat)) by (nonlinear_arith)
        requires p2((b - a) as nat) >= 1, p2(a) >= 1;
}

pub proof fn lemma_p2_64()
    ensures p2(64) == 0x1_0000_0000_0000_0000nat, p2(8) == 256,
{
    reveal_with_fuel(p2, 9);
    assert(p2(8) == 256);
    lemma_p2_adds(8, 8);
    assert(p2(16) == 256 * 256);
    lemma_p2_adds(16, 16);
    assert(p2(32) == 65536 * 65536);
    lemma_p2_adds(32, 32);
    assert(p2(64) == 4294967296 * 4294967296);
}

pub proof fn lemma_p2_56()
    ensures p2(56) == 0x100_0000_0000_0000nat,
{
    reveal_with_fuel(p2, 9);
    assert(p2(8) == 256);
    lemma_p2_adds(8, 8);
    assert(p2(16) == 65536);
    lemma_p2_adds(16, 16);
    assert(p2(32) == 4294967296);
    lemma_p2_adds(32, 16);
    assert(p2(48) == 281474976710656);
    lemma_p2_adds(48, 8);
}

/// Load the 64-bit big-endian window starting at byte `i`, zero padded.
#[inline]
pub fn load_window(s: &[u8], i: usize) -> (w: u64)
    requires i <= s.len(),
    ensures w as nat == bits_val(bview(s@).subrange(8 * i as int, 8 * i as int + 64)),
{
    let mut w: u64 = 0;
    let mut k: usize = 0;
    proof {
        lemma_p2_64();
        assert(bwin(s@, i as int, 0) =~= Seq::<u8>::empty());
    }
    while k < 8
        invariant
            k <= 8,
            i <= s.len(),
            p2(64) == 0x1_0000_0000_0000_0000nat,
            w as nat == bits_val(bits_of(bwin(s@, i as int, k as nat))),
        decreases 8 - k,
    {
        let b: u8 = if k < s.len() - i { s[i + k] } else { 0u8 };
        proof {
            let old_w = bits_val(bits_of(bwin(s@, i as int, k as nat)));
            lemma_bits_val_bound(bits_of(bwin(s@, i as int, k as nat)));
            lemma_p2_mono((8 * k + 8) as nat, 64);
            lemma_p2_adds((8 * k) as nat, 8);
            lemma_p2_64();
            assert(old_w * 256 + b < p2((8 * k + 8) as nat)) by (nonlinear_arith)
                requires old_w < p2((8 * k) as nat), b < 256,
                         p2((8 * k + 8) as nat) == p2((8 * k) as nat) * p2(8),
                         p2(8) == 256;
            lemma_bits_val_push_byte(bwin(s@, i as int, k as nat), b);
            assert(bwin(s@, i as int, (k + 1) as nat)
                   =~= bwin(s@, i as int, k as nat).push(b));
        }
        w = w * 256 + (b as u64);
        k = k + 1;
    }
    proof { lemma_bview_window(s@, i as int, 8); }
    w
}

} // verus!

verus! {

#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use vstd::arithmetic::power2::{pow2, lemma_pow2_adds};
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use vstd::arithmetic::power::pow;
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use vstd::bits::{low_bits_mask, lemma_u64_shr_is_div, lemma_u64_low_bits_mask_is_mod,
                 lemma_u64_shl_is_mul, lemma_u64_pow2_no_overflow};

/// Bridge between the self-contained `p2` and vstd's `pow2`.
pub proof fn lemma_p2_eq_pow2(n: nat)
    ensures p2(n) == pow2(n),
    decreases n,
{
    reveal(pow2);
    reveal_with_fuel(pow, 2);
    if n == 0 {
    } else {
        lemma_p2_eq_pow2((n - 1) as nat);
        lemma_pow2_adds((n - 1) as nat, 1);
        assert(pow2(1) == 2);
        assert(pow2(n) == pow2((n - 1) as nat) * 2);
    }
}

/// Read `n` bits (n <= 56) starting at bit position `pos`.
/// One unaligned 64-bit window load, one shift, one mask.
#[inline]
pub fn read_bits(s: &[u8], pos: usize, n: usize) -> (v: u64)
    requires
        1 <= n <= 56,
        pos + n <= 8 * s.len(),
    ensures
        v as nat == bits_val(bview(s@).subrange(pos as int, pos as int + n as int)),
{
    let i: usize = pos / 8;
    let off: usize = pos % 8;
    assert(i <= s.len()) by (nonlinear_arith)
        requires i == pos / 8, pos + n <= 8 * s.len(), n >= 0;
    let w = load_window(s, i);
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
        lemma_u64_shr_is_div(w, sh as u64);
        lemma_u64_pow2_no_overflow(n as nat);
        lemma_u64_shl_is_mul(1u64, n as u64);
        assert(mask == low_bits_mask(n as nat) as u64);
        lemma_u64_low_bits_mask_is_mod(w >> (sh as u64), n as nat);
    }
    v
}

} // verus!
