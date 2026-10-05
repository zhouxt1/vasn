// Bridge between machine bytes and the ghost bit-sequence model.
use vstd::prelude::*;
use crate::bitspec::*;

verus! {

/// Value of bit `i` of byte `b` as a number (MSB-first).
pub open spec fn bitn(b: u8, i: int) -> nat {
    if bit_of(b, i) { 1nat } else { 0nat }
}

/// One bit of a byte, viewed through a u64 widening.
pub proof fn lemma_bit_u64(b: u8, k: u8)
    requires k < 8,
    ensures bitn(b, (7 - k) as int) == (((b as u64) >> (k as u64)) & 1u64) as nat,
{
    assert(((b >> k) & 1u8 == 1u8) == (((b as u64) >> (k as u64)) & 1u64 == 1u64))
        by (bit_vector) requires k < 8;
    assert(((b as u64) >> (k as u64)) & 1u64 <= 1) by (bit_vector);
    assert((7 - (7 - k) as int) == k as int);
}

/// A single byte's eight bits spell out its value.
pub proof fn lemma_byte_bits(b: u8)
    ensures bits_val(bits_of(seq![b])) == b as nat,
{
    let s = bits_of(seq![b]);
    assert(s.len() == 8);
    assert forall|i: int| 0 <= i < 8 implies s[i] == bit_of(b, i) by {
        assert(seq![b][i / 8] == b);
    }
    reveal_with_fuel(bits_val, 9);
    assert(s.drop_last().drop_last().drop_last().drop_last()
            .drop_last().drop_last().drop_last().drop_last()
           =~= Seq::<bool>::empty());
    assert(bits_val(s)
        == 128 * bitn(b, 0) + 64 * bitn(b, 1) + 32 * bitn(b, 2) + 16 * bitn(b, 3)
         +   8 * bitn(b, 4) +  4 * bitn(b, 5) +  2 * bitn(b, 6) +      bitn(b, 7));
    let x = b as u64;
    lemma_bit_u64(b, 0); lemma_bit_u64(b, 1); lemma_bit_u64(b, 2); lemma_bit_u64(b, 3);
    lemma_bit_u64(b, 4); lemma_bit_u64(b, 5); lemma_bit_u64(b, 6); lemma_bit_u64(b, 7);
    assert(
        128 * ((x >> 7u64) & 1u64) + 64 * ((x >> 6u64) & 1u64)
      +  32 * ((x >> 5u64) & 1u64) + 16 * ((x >> 4u64) & 1u64)
      +   8 * ((x >> 3u64) & 1u64) +  4 * ((x >> 2u64) & 1u64)
      +   2 * ((x >> 1u64) & 1u64) +      ((x >> 0u64) & 1u64) == x
    ) by (bit_vector) requires x < 256;
}

/// `bits_of` distributes over concatenation of byte sequences.
pub proof fn lemma_bits_of_add(s1: Seq<u8>, s2: Seq<u8>)
    ensures bits_of(s1 + s2) =~= bits_of(s1) + bits_of(s2),
{
    let l = bits_of(s1 + s2);
    let r = bits_of(s1) + bits_of(s2);
    assert(l.len() == r.len());
    assert forall|i: int| 0 <= i < l.len() implies l[i] == r[i] by {
        if i < s1.len() * 8 {
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

/// Appending a byte multiplies the running value by 256 and adds the byte.
pub proof fn lemma_bits_val_push_byte(s: Seq<u8>, b: u8)
    ensures bits_val(bits_of(s.push(b))) == bits_val(bits_of(s)) * 256 + b as nat,
{
    assert(s.push(b) =~= s + seq![b]);
    lemma_bits_of_add(s, seq![b]);
    let t = bits_of(s) + bits_of(seq![b]);
    assert(t.take((s.len() * 8) as int) =~= bits_of(s));
    assert(t.skip((s.len() * 8) as int) =~= bits_of(seq![b]));
    lemma_bits_val_split(t, (s.len() * 8) as int);
    lemma_byte_bits(b);
    reveal_with_fuel(p2, 9);
    assert(t.len() - s.len() * 8 == 8);
    assert(p2(8) == 256);
}

} // verus!
