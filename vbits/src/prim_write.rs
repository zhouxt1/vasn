// Verified bit writer. The postcondition is a single sequence equation, which
// subsumes VUPER's separately-proved `local_write` property.
use vstd::prelude::*;
use crate::bitspec::*;
use crate::bytebits::*;

verus! {

/// The `n`-bit big-endian representation of `v`.
pub open spec fn bits_seq(v: u64, n: nat) -> Seq<bool> {
    Seq::new(n, |i: int| (v as nat / p2((n - 1 - i) as nat)) % 2 == 1)
}

pub proof fn lemma_bits_seq_val(v: u64, n: nat)
    requires v < p2(n),
    ensures bits_val(bits_seq(v, n)) == v as nat,
    decreases n,
{
    if n == 0 {
    } else {
        let h = (v / 2) as u64;
        assert(h < p2((n - 1) as nat)) by (nonlinear_arith)
            requires v < p2(n), p2(n) == 2 * p2((n - 1) as nat), h == v / 2;
        lemma_bits_seq_val(h, (n - 1) as nat);
        assert(bits_seq(v, n).drop_last() =~= bits_seq(h, (n - 1) as nat)) by {
            assert forall|i: int| 0 <= i < n - 1 implies
                bits_seq(v, n)[i] == bits_seq(h, (n - 1) as nat)[i]
            by {
                assert(p2((n - 1 - i) as nat) == 2 * p2((n - 1 - 1 - i) as nat));
                lemma_p2_pos((n - 1 - 1 - i) as nat);
                vstd::arithmetic::div_mod::lemma_div_denominator(
                    v as int, 2, p2((n - 1 - 1 - i) as nat) as int);
            }
        }
        assert(p2(0) == 1);
        assert(bits_seq(v, n).last() == bits_seq(v, n)[n as int - 1]);
        assert((n - 1 - (n as int - 1)) == 0);
        assert(v as nat / 1 == v as nat);
    }
}

/// `bits_val` is injective on sequences of equal length.
pub proof fn lemma_bits_val_inj(a: Seq<bool>, b: Seq<bool>)
    requires a.len() == b.len(), bits_val(a) == bits_val(b),
    ensures a =~= b,
    decreases a.len(),
{
    if a.len() == 0 {
    } else {
        assert(a.last() == b.last());
        lemma_bits_val_inj(a.drop_last(), b.drop_last());
        assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
            if i < a.len() - 1 {
                assert(a.drop_last()[i] == b.drop_last()[i]);
            }
        }
    }
}

/// An n-bit sequence is the n-bit representation of its own value.
pub proof fn lemma_bits_seq_of_val(s: Seq<bool>)
    requires s.len() <= 64,
    ensures bits_val(s) < p2(s.len()), bits_seq(bits_val(s) as u64, s.len()) =~= s,
{
    lemma_bits_val_bound(s);
    crate::prim_read::lemma_p2_mono(s.len(), 64);
    crate::prim_read::lemma_p2_64();
    lemma_bits_seq_val(bits_val(s) as u64, s.len());
    lemma_bits_val_inj(bits_seq(bits_val(s) as u64, s.len()), s);
}

/// Bit-vector facts about setting one bit of a byte.
proof fn bv_set_same(ob: u8, sh: u8, bit: bool)
    by (bit_vector)
    requires sh < 8,
    ensures ((if bit { ob | (1u8 << sh) } else { ob & !(1u8 << sh) }) >> sh) & 1u8
            == (if bit { 1u8 } else { 0u8 }),
{
}

proof fn bv_set_other(ob: u8, sh: u8, sh2: u8, bit: bool)
    by (bit_vector)
    requires sh < 8, sh2 < 8, sh2 != sh,
    ensures ((if bit { ob | (1u8 << sh) } else { ob & !(1u8 << sh) }) >> sh2) & 1u8
            == (ob >> sh2) & 1u8,
{
}

/// Setting one bit of a byte.
pub proof fn lemma_set_bit_byte(ob: u8, nb: u8, off: u8, sh: u8, bit: bool)
    requires
        off < 8,
        sh == 7 - off,
        nb == if bit { ob | (1u8 << sh) } else { ob & !(1u8 << sh) },
    ensures
        bit_of(nb, off as int) == bit,
        forall|o: int| 0 <= o < 8 && o != off as int ==> bit_of(nb, o) == bit_of(ob, o),
{
    bv_set_same(ob, sh, bit);
    assert((7 - off as int) as u8 == sh);
    assert forall|o: int| 0 <= o < 8 && o != off as int implies bit_of(nb, o) == bit_of(ob, o) by {
        let sh2 = (7 - o) as u8;
        assert(sh2 < 8);
        assert(sh2 != sh);
        bv_set_other(ob, sh, sh2, bit);
    }
}

/// Updating one byte updates exactly its eight bits.
pub proof fn lemma_bits_of_update(s: Seq<u8>, j: int, nb: u8, off: int, bit: bool)
    requires
        0 <= j < s.len(),
        0 <= off < 8,
        bit_of(nb, off) == bit,
        forall|o: int| 0 <= o < 8 && o != off ==> bit_of(nb, o) == bit_of(s[j], o),
    ensures
        bits_of(s.update(j, nb)) =~= bits_of(s).update(8 * j + off, bit),
{
    let l = bits_of(s.update(j, nb));
    let r = bits_of(s).update(8 * j + off, bit);
    assert(l.len() == r.len());
    assert forall|m: int| 0 <= m < l.len() implies l[m] == r[m] by {
        if m / 8 == j {
            assert(s.update(j, nb)[m / 8] == nb);
            assert(m == 8 * (m / 8) + m % 8) by (nonlinear_arith) requires m >= 0;
            if m % 8 == off {
                assert(m == 8 * j + off);
            } else {
                assert(m != 8 * j + off);
            }
        } else {
            assert(s.update(j, nb)[m / 8] == s[m / 8]);
            assert(m != 8 * j + off) by (nonlinear_arith)
                requires m / 8 != j, 0 <= off < 8, m >= 0, m == 8 * (m / 8) + m % 8;
        }
    }
}

/// Set a single bit of the buffer.
#[inline]
pub fn set_bit(buf: &mut Vec<u8>, p: usize, bit: bool)
    requires p < 8 * old(buf).len(),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        bits_of(final(buf)@) =~= bits_of(old(buf)@).update(p as int, bit),
{
    let j: usize = p / 8;
    let off: usize = p % 8;
    assert(j < buf.len()) by (nonlinear_arith) requires j == p / 8, p < 8 * buf.len();
    let ob: u8 = buf[j];
    let sh: u8 = 7u8 - (off as u8);
    let m: u8 = 1u8 << sh;
    let nb: u8 = if bit { ob | m } else { ob & !m };
    proof {
        lemma_set_bit_byte(ob, nb, off as u8, sh, bit);
        lemma_bits_of_update(buf@, j as int, nb, off as int, bit);
        assert(8 * j + off == p) by (nonlinear_arith) requires j == p / 8, off == p % 8;
    }
    buf.set(j, nb);
}

/// Write `n` bits of `v` at bit position `pos`.
#[inline]
pub fn write_bits(buf: &mut Vec<u8>, pos: usize, n: usize, v: u64)
    requires
        1 <= n <= 56,
        pos + n <= 8 * old(buf).len(),
        pos + n <= usize::MAX,
        v < p2(n as nat),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        bits_of(final(buf)@) =~= bits_of(old(buf)@).take(pos as int)
                          + bits_seq(v, n as nat)
                          + bits_of(old(buf)@).skip(pos as int + n as int),
{
    let ghost orig = bits_of(old(buf)@);
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            pos + n <= 8 * buf@.len(),
            pos + n <= usize::MAX,
            n <= 56,
            buf@.len() == old(buf)@.len(),
            orig == bits_of(old(buf)@),
            bits_of(buf@) =~= orig.take(pos as int)
                              + bits_seq(v, n as nat).take(k as int)
                              + orig.skip(pos as int + k as int),
        decreases n - k,
    {
        assert(n - 1 - k < 64);
        let sh_k: u64 = (n - 1 - k) as u64;
        let bit: bool = ((v >> sh_k) & 1u64) == 1u64;
        proof {
            lemma_p2_eq_pow2_w((n - 1 - k) as nat);
            vstd::bits::lemma_u64_shr_is_div(v, sh_k);
            vstd::bits::lemma_u64_low_bits_mask_is_mod(v >> sh_k, 1);
            reveal(vstd::arithmetic::power2::pow2);
            reveal_with_fuel(vstd::arithmetic::power::pow, 2);
            assert(vstd::arithmetic::power2::pow2(1) == 2);
            assert(vstd::bits::low_bits_mask(1) == 1);
            assert(bits_seq(v, n as nat)[k as int] == bit);
        }
        set_bit(buf, pos + k, bit);
        proof {
            let s1 = orig.take(pos as int) + bits_seq(v, n as nat).take(k as int)
                     + orig.skip(pos as int + k as int);
            let s2 = orig.take(pos as int) + bits_seq(v, n as nat).take(k as int + 1)
                     + orig.skip(pos as int + k as int + 1);
            assert(s1.update(pos as int + k as int, bit) =~= s2);
        }
        k = k + 1;
    }
    assert(bits_seq(v, n as nat).take(n as int) =~= bits_seq(v, n as nat));
}

pub proof fn lemma_p2_eq_pow2_w(n: nat)
    ensures p2(n) == vstd::arithmetic::power2::pow2(n),
{
    crate::prim_read::lemma_p2_eq_pow2(n);
}

} // verus!
