// The LSB-first view of a byte buffer, for formats that pack bits from the
// least significant end of each byte (DEFLATE, RFC 1951 3.1.1; Brotli, RFC
// 7932 2). `bitspec` is the MSB-first view the PER and EXI codecs use; the
// two share nothing but the byte window.
use vstd::prelude::*;
use crate::bitspec::*;
use crate::prim_read::*;

verus! {

#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use vstd::bits::{low_bits_mask, lemma_u64_shr_is_div, lemma_u64_low_bits_mask_is_mod,
                 lemma_u64_shl_is_mul, lemma_u64_pow2_no_overflow};

/// Bit `i` of byte `b`, LSB-first (i = 0 is the least significant bit).
pub open spec fn lbit(b: u8, i: int) -> bool {
    (b >> (i as u8)) & 1u8 == 1u8
}

/// The bit sequence of a byte sequence, LSB-first within each byte.
pub open spec fn lbits(s: Seq<u8>) -> Seq<bool> {
    Seq::new((s.len() * 8) as nat, |i: int| lbit(s[i / 8], i % 8))
}

/// `lbits` with 64 zero bits of virtual padding, so that a window load at
/// the end of the buffer stays inside the model.
pub open spec fn lview(s: Seq<u8>) -> Seq<bool> {
    lbits(s) + Seq::new(64, |_i: int| false)
}

/// Little-endian value of a bit sequence: its first bit is the least
/// significant. DEFLATE's data elements other than Huffman codes are read
/// this way.
pub open spec fn lval(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0nat
    } else {
        (if s[0] { 1nat } else { 0nat }) + 2nat * lval(s.subrange(1, s.len() as int))
    }
}

pub proof fn lemma_lval_bound(s: Seq<bool>)
    ensures lval(s) < p2(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_lval_bound(s.subrange(1, s.len() as int));
    }
}

/// Splitting a sequence splits its value into a low and a high part.
pub proof fn lemma_lval_split(s: Seq<bool>, k: int)
    requires 0 <= k <= s.len(),
    ensures lval(s) == lval(s.take(k)) + p2(k as nat) * lval(s.skip(k)),
    decreases k,
{
    if k == 0 {
        assert(s.take(0) =~= Seq::<bool>::empty());
        assert(s.skip(0) =~= s);
        assert(lval(s.take(0)) == 0);
        assert(p2(0) == 1);
        assert(lval(s.skip(k)) == lval(s));
        assert(p2(k as nat) == 1);
        assert(1 * lval(s) == lval(s)) by (nonlinear_arith);
        assert(lval(s) == lval(s.take(k)) + p2(k as nat) * lval(s.skip(k)));
    } else {
        let t = s.subrange(1, s.len() as int);
        lemma_lval_split(t, k - 1);
        assert(s.take(k).subrange(1, k) =~= t.take(k - 1));
        assert(s.skip(k) =~= t.skip(k - 1));
        let h = if s[0] { 1nat } else { 0nat };
        let a = lval(t.take(k - 1));
        let b = lval(t.skip(k - 1));
        let q = p2((k - 1) as nat);
        assert(s.take(k).len() > 0 && s.take(k)[0] == s[0]);
        assert(s.take(k).subrange(1, s.take(k).len() as int) =~= t.take(k - 1));
        assert(lval(s.take(k)) == h + 2 * a);
        assert(lval(t) == a + q * b);
        assert(lval(s) == h + 2 * lval(t));
        assert(lval(s) == h + 2 * (a + q * b));
        assert(p2(k as nat) == 2 * q);
        assert(h + 2 * (a + q * b) == (h + 2 * a) + (2 * q) * b) by (nonlinear_arith);
        assert(lval(s.skip(k)) == b);
        assert(p2(k as nat) == 2 * q);
        assert(lval(s) == lval(s.take(k)) + (2 * q) * b);
        assert(lval(s) == lval(s.take(k)) + p2(k as nat) * lval(s.skip(k)));
    }
}

/// A sub-range's value is a shift and a mask of the whole's.
pub proof fn lemma_lval_subrange(s: Seq<bool>, a: int, n: int)
    requires 0 <= a, 0 <= n, a + n <= s.len(),
    ensures lval(s.subrange(a, a + n)) == (lval(s) / p2(a as nat)) % p2(n as nat),
{
    let t = s.skip(a);
    lemma_lval_split(s, a);
    lemma_lval_split(t, n);
    assert(t.take(n) =~= s.subrange(a, a + n));
    let lo = lval(s.take(a)) as int;
    let m = lval(t.take(n)) as int;
    let hi = lval(t.skip(n)) as int;
    let pa = p2(a as nat) as int;
    let pn = p2(n as nat) as int;
    lemma_lval_bound(s.take(a));
    lemma_lval_bound(t.take(n));
    lemma_p2_pos(a as nat);
    lemma_p2_pos(n as nat);
    assert(lval(s) as int == (m + pn * hi) * pa + lo) by (nonlinear_arith)
        requires lval(s) as int == lo + pa * lval(t) as int, lval(t) as int == m + pn * hi;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(lval(s) as int, pa, m + pn * hi, lo);
    assert(m + pn * hi == pn * hi + m) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(hi, m, pn);
    vstd::arithmetic::div_mod::lemma_small_mod(m as nat, pn as nat);
}

/// One bit of a sequence, read off its value.
pub proof fn lemma_lval_bit(s: Seq<bool>, j: int)
    requires 0 <= j < s.len(),
    ensures s[j] == ((lval(s) / p2(j as nat)) % 2 == 1),
{
    lemma_lval_subrange(s, j, 1);
    let u = s.subrange(j, j + 1);
    assert(u.subrange(1, 1) =~= Seq::<bool>::empty());
    reveal_with_fuel(lval, 2);
    assert(u.len() == 1 && u[0] == s[j]);
    assert(lval(u) == if s[j] { 1nat } else { 0nat });
    assert(p2(1) == 2) by { reveal_with_fuel(p2, 2); }
}

/// `lbits` distributes over concatenation.
pub proof fn lemma_lbits_add(s1: Seq<u8>, s2: Seq<u8>)
    ensures lbits(s1 + s2) =~= lbits(s1) + lbits(s2),
{
    let l = lbits(s1 + s2);
    let r = lbits(s1) + lbits(s2);
    assert(l.len() == r.len());
    assert forall|i: int| 0 <= i < l.len() implies l[i] == r[i] by {
        if i < s1.len() * 8 {
            assert(i / 8 < s1.len()) by (nonlinear_arith) requires 0 <= i < s1.len() * 8;
            assert((s1 + s2)[i / 8] == s1[i / 8]);
        } else {
            let j = i - s1.len() * 8;
            assert(j / 8 == i / 8 - s1.len()) by (nonlinear_arith)
                requires i >= s1.len() * 8, j == i - s1.len() * 8;
            assert(j % 8 == i % 8) by (nonlinear_arith)
                requires i >= s1.len() * 8, j == i - s1.len() * 8;
            assert((s1 + s2)[i / 8] == s2[i / 8 - s1.len()]);
        }
    }
}

/// A byte's eight bits spell out its value.
pub proof fn lemma_lval_byte(x: u8)
    ensures lval(lbits(seq![x])) == x as nat,
{
    let s = lbits(seq![x]);
    assert(s.len() == 8);
    assert forall|i: int| 0 <= i < 8 implies s[i] == lbit(x, i) by {
        assert(seq![x][i / 8] == x);
    }
    let b = |i: int| if lbit(x, i) { 1nat } else { 0nat };
    reveal_with_fuel(lval, 9);
    assert(s.subrange(1, 8).subrange(1, 7) =~= s.subrange(2, 8));
    assert(s.subrange(2, 8).subrange(1, 6) =~= s.subrange(3, 8));
    assert(s.subrange(3, 8).subrange(1, 5) =~= s.subrange(4, 8));
    assert(s.subrange(4, 8).subrange(1, 4) =~= s.subrange(5, 8));
    assert(s.subrange(5, 8).subrange(1, 3) =~= s.subrange(6, 8));
    assert(s.subrange(6, 8).subrange(1, 2) =~= s.subrange(7, 8));
    assert(s.subrange(7, 8).subrange(1, 1) =~= Seq::<bool>::empty());
    assert(s.subrange(1, 8)[0] == s[1] && s.subrange(2, 8)[0] == s[2]
        && s.subrange(3, 8)[0] == s[3] && s.subrange(4, 8)[0] == s[4]
        && s.subrange(5, 8)[0] == s[5] && s.subrange(6, 8)[0] == s[6]
        && s.subrange(7, 8)[0] == s[7]);
    assert(lval(s) == b(0) + 2 * (b(1) + 2 * (b(2) + 2 * (b(3) + 2 * (b(4)
        + 2 * (b(5) + 2 * (b(6) + 2 * b(7))))))));
    let w = x as u64;
    assert(forall|i: u8| i < 8 ==> (((x >> i) & 1u8 == 1u8) == (((w >> (i as u64)) & 1u64) == 1u64)))
        by (bit_vector) requires w == x as u64;
    assert(forall|i: u64| i < 8 ==> ((w >> i) & 1u64) <= 1) by (bit_vector);
    assert(((w >> 0u64) & 1u64) + 2 * (((w >> 1u64) & 1u64) + 2 * (((w >> 2u64) & 1u64)
        + 2 * (((w >> 3u64) & 1u64) + 2 * (((w >> 4u64) & 1u64) + 2 * (((w >> 5u64) & 1u64)
        + 2 * (((w >> 6u64) & 1u64) + 2 * ((w >> 7u64) & 1u64))))))) == w)
        by (bit_vector) requires w < 256;
    assert(b(0) == ((w >> 0u64) & 1u64) as nat);
    assert(b(1) == ((w >> 1u64) & 1u64) as nat);
    assert(b(2) == ((w >> 2u64) & 1u64) as nat);
    assert(b(3) == ((w >> 3u64) & 1u64) as nat);
    assert(b(4) == ((w >> 4u64) & 1u64) as nat);
    assert(b(5) == ((w >> 5u64) & 1u64) as nat);
    assert(b(6) == ((w >> 6u64) & 1u64) as nat);
    assert(b(7) == ((w >> 7u64) & 1u64) as nat);
}

/// Prepending a byte: its value is the low eight bits.
pub proof fn lemma_lval_cons_byte(x: u8, s: Seq<u8>)
    ensures lval(lbits(seq![x] + s)) == x as nat + 256 * lval(lbits(s)),
{
    lemma_lbits_add(seq![x], s);
    let t = lbits(seq![x]) + lbits(s);
    assert(t.take(8) =~= lbits(seq![x]));
    assert(t.skip(8) =~= lbits(s));
    lemma_lval_split(t, 8);
    lemma_lval_byte(x);
    assert(p2(8) == 256) by { reveal_with_fuel(p2, 9); }
}

/// The zero-padded byte window is the corresponding slice of `lview`.
pub proof fn lemma_lview_window(s: Seq<u8>, i: int, k: nat)
    requires 0 <= i <= s.len(), k <= 8,
    ensures lbits(bwin(s, i, k)) =~= lview(s).subrange(8 * i, 8 * i + 8 * k),
{
    let l = lbits(bwin(s, i, k));
    let r = lview(s).subrange(8 * i, 8 * i + 8 * k);
    assert(l.len() == r.len());
    assert forall|m: int| 0 <= m < l.len() implies l[m] == r[m] by {
        assert(m / 8 < k) by (nonlinear_arith) requires 0 <= m < 8 * k;
        assert((8 * i + m) / 8 == i + m / 8) by (nonlinear_arith) requires 0 <= m;
        assert((8 * i + m) % 8 == m % 8) by (nonlinear_arith) requires 0 <= m;
        if i + m / 8 < s.len() {
            assert(8 * i + m < 8 * s.len()) by (nonlinear_arith)
                requires i + m / 8 < s.len(), 0 <= m, (8 * i + m) / 8 == i + m / 8;
        } else {
            assert(8 * i + m >= 8 * s.len()) by (nonlinear_arith)
                requires i + m / 8 >= s.len(), 0 <= m, (8 * i + m) / 8 == i + m / 8;
            let j = (m % 8) as u8;
            assert((0u8 >> j) & 1u8 != 1u8) by (bit_vector);
        }
    }
}

/// Inside the buffer, the padded view is the plain one.
pub proof fn lemma_lview_inside(s: Seq<u8>, a: int, b: int)
    requires 0 <= a <= b <= 8 * s.len(),
    ensures lview(s).subrange(a, b) =~= lbits(s).subrange(a, b),
{
}

proof fn bv_assemble_le(b0: u64, b1: u64, b2: u64, b3: u64, b4: u64, b5: u64, b6: u64, b7: u64)
    by (bit_vector)
    requires
        b0 < 256, b1 < 256, b2 < 256, b3 < 256,
        b4 < 256, b5 < 256, b6 < 256, b7 < 256,
    ensures
        b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)
      | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)
      == add(b0, mul(256, add(b1, mul(256, add(b2, mul(256, add(b3, mul(256, add(b4,
         mul(256, add(b5, mul(256, add(b6, mul(256, b7)))))))))))))),
{
}

proof fn lemma_win_cons(s: Seq<u8>, i: int, k: nat)
    requires 0 <= i, k >= 1,
    ensures bwin(s, i, k) =~= seq![byte_at(s, i)] + bwin(s, i + 1, (k - 1) as nat),
{
}

proof fn lemma_le_window(s: Seq<u8>, i: int, b0: u64, b1: u64, b2: u64, b3: u64,
                         b4: u64, b5: u64, b6: u64, b7: u64, w: u64)
    requires
        0 <= i <= s.len(),
        b0 == byte_at(s, i) as u64, b1 == byte_at(s, i + 1) as u64,
        b2 == byte_at(s, i + 2) as u64, b3 == byte_at(s, i + 3) as u64,
        b4 == byte_at(s, i + 4) as u64, b5 == byte_at(s, i + 5) as u64,
        b6 == byte_at(s, i + 6) as u64, b7 == byte_at(s, i + 7) as u64,
        w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)
           | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
    ensures w as nat == lval(lview(s).subrange(8 * i, 8 * i + 64)),
{
    bv_assemble_le(b0, b1, b2, b3, b4, b5, b6, b7);
    assert(bwin(s, i + 8, 0) =~= Seq::<u8>::empty());
    lemma_win_cons(s, i + 7, 1); lemma_lval_cons_byte(byte_at(s, i + 7), bwin(s, i + 8, 0));
    lemma_win_cons(s, i + 6, 2); lemma_lval_cons_byte(byte_at(s, i + 6), bwin(s, i + 7, 1));
    lemma_win_cons(s, i + 5, 3); lemma_lval_cons_byte(byte_at(s, i + 5), bwin(s, i + 6, 2));
    lemma_win_cons(s, i + 4, 4); lemma_lval_cons_byte(byte_at(s, i + 4), bwin(s, i + 5, 3));
    lemma_win_cons(s, i + 3, 5); lemma_lval_cons_byte(byte_at(s, i + 3), bwin(s, i + 4, 4));
    lemma_win_cons(s, i + 2, 6); lemma_lval_cons_byte(byte_at(s, i + 2), bwin(s, i + 3, 5));
    lemma_win_cons(s, i + 1, 7); lemma_lval_cons_byte(byte_at(s, i + 1), bwin(s, i + 2, 6));
    lemma_win_cons(s, i, 8);     lemma_lval_cons_byte(byte_at(s, i), bwin(s, i + 1, 7));
    assert(lval(lbits(Seq::<u8>::empty())) == 0) by {
        assert(lbits(Seq::<u8>::empty()) =~= Seq::<bool>::empty());
    }
    lemma_lview_window(s, i, 8);
}

/// The window load when all eight bytes are in the buffer: eight plain
/// indexed reads, which LLVM merges into one unaligned 64-bit load.
#[inline(always)]
pub fn load_le64_in(s: &[u8], i: usize) -> (w: u64)
    requires i + 8 <= s.len(),
    ensures w as nat == lval(lview(s@).subrange(8 * i as int, 8 * i as int + 64)),
{
    // the last byte first: once it is in bounds, so are the seven before
    // it, and the eight reads merge into one load
    let b7 = s[i + 7] as u64;
    let b0 = s[i] as u64;
    let b1 = s[i + 1] as u64;
    let b2 = s[i + 2] as u64;
    let b3 = s[i + 3] as u64;
    let b4 = s[i + 4] as u64;
    let b5 = s[i + 5] as u64;
    let b6 = s[i + 6] as u64;
    let w = b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)
          | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64);
    proof { lemma_le_window(s@, i as int, b0, b1, b2, b3, b4, b5, b6, b7, w); }
    w
}

/// The window load near the end of the buffer, zero padded.
fn load_le64_end(s: &[u8], i: usize) -> (w: u64)
    requires i <= s.len(),
    ensures w as nat == lval(lview(s@).subrange(8 * i as int, 8 * i as int + 64)),
{
    let r = s.len() - i;
    let b0 = if 0 < r { s[i] as u64 } else { 0 };
    let b1 = if 1 < r { s[i + 1] as u64 } else { 0 };
    let b2 = if 2 < r { s[i + 2] as u64 } else { 0 };
    let b3 = if 3 < r { s[i + 3] as u64 } else { 0 };
    let b4 = if 4 < r { s[i + 4] as u64 } else { 0 };
    let b5 = if 5 < r { s[i + 5] as u64 } else { 0 };
    let b6 = if 6 < r { s[i + 6] as u64 } else { 0 };
    let b7 = if 7 < r { s[i + 7] as u64 } else { 0 };
    let w = b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)
          | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64);
    proof { lemma_le_window(s@, i as int, b0, b1, b2, b3, b4, b5, b6, b7, w); }
    w
}

/// The 64-bit little-endian window starting at byte `i`, zero padded.
#[inline(always)]
pub fn load_le64(s: &[u8], i: usize) -> (w: u64)
    requires i <= s.len(),
    ensures w as nat == lval(lview(s@).subrange(8 * i as int, 8 * i as int + 64)),
{
    if s.len() - i >= 8 { load_le64_in(s, i) } else { load_le64_end(s, i) }
}

/// 56 bits at bit position `pos`, LSB-first, when the eight bytes from
/// `pos / 8` are all in the buffer: one 64-bit load.
#[inline(always)]
pub fn peek56_in(s: &[u8], pos: usize) -> (v: u64)
    requires pos / 8 + 8 <= s.len(),
    ensures
        v as nat == lval(lview(s@).subrange(pos as int, pos as int + 56)),
        v < (1u64 << 56),
{
    let i: usize = pos / 8;
    let off: u64 = (pos % 8) as u64;
    let w = load_le64_in(s, i);
    let n: u64 = 56;
    let mask: u64 = 0xFF_FFFF_FFFF_FFFF;
    assert(mask == (1u64 << n) - 1) by (bit_vector) requires n == 56, mask == 0xFF_FFFF_FFFF_FFFFu64;
    let v = (w >> off) & mask;
    proof {
        let t = lview(s@).subrange(8 * i as int, 8 * i as int + 64);
        assert(pos == 8 * i + off);
        assert(t.subrange(off as int, off as int + n as int)
               =~= lview(s@).subrange(pos as int, pos as int + n as int));
        lemma_lval_subrange(t, off as int, n as int);
        lemma_p2_eq_pow2(off as nat);
        lemma_p2_eq_pow2(n as nat);
        lemma_u64_shr_is_div(w, off);
        lemma_u64_pow2_no_overflow(n as nat);
        lemma_u64_shl_is_mul(1u64, n);
        assert(mask == low_bits_mask(n as nat) as u64);
        lemma_u64_low_bits_mask_is_mod(w >> off, n as nat);
        assert(v <= mask) by (bit_vector) requires v == (w >> off) & mask;
    }
    v
}

/// Read `n` bits (1 <= n <= 56) at bit position `pos`, LSB-first; past the
/// end of the buffer the bits read as zeros.
#[inline(always)]
pub fn peek_lsb(s: &[u8], pos: usize, n: u64) -> (v: u64)
    requires
        1 <= n <= 56,
        pos <= 8 * s.len(),
    ensures
        v as nat == lval(lview(s@).subrange(pos as int, pos as int + n as int)),
        v < (1u64 << n),
{
    let i: usize = pos / 8;
    let off: u64 = (pos % 8) as u64;
    assert(i <= s.len()) by (nonlinear_arith) requires i == pos / 8, pos <= 8 * s.len();
    let w = load_le64(s, i);
    assert(1u64 << n >= 1) by (bit_vector) requires 1 <= n <= 56;
    let mask: u64 = (1u64 << n) - 1;
    let v = (w >> off) & mask;
    proof {
        let t = lview(s@).subrange(8 * i as int, 8 * i as int + 64);
        assert(pos == 8 * i + off);
        assert(t.subrange(off as int, off as int + n as int)
               =~= lview(s@).subrange(pos as int, pos as int + n as int));
        lemma_lval_subrange(t, off as int, n as int);
        lemma_p2_eq_pow2(off as nat);
        lemma_p2_eq_pow2(n as nat);
        lemma_u64_shr_is_div(w, off);
        lemma_u64_pow2_no_overflow(n as nat);
        lemma_u64_shl_is_mul(1u64, n);
        assert(mask == low_bits_mask(n as nat) as u64);
        lemma_u64_low_bits_mask_is_mod(w >> off, n as nat);
        assert(v <= mask) by (bit_vector) requires v == (w >> off) & mask;
    }
    v
}

} // verus!
