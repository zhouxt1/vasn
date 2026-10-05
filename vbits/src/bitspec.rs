// Ghost-level model of a byte buffer as a big-endian bit sequence.
use vstd::prelude::*;

verus! {

/// Self-contained power of two (kept separate from vstd's opaque `pow2`
/// so that the sequence lemmas below need no reveal plumbing).
pub open spec fn p2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1nat } else { 2nat * p2((n - 1) as nat) }
}

pub proof fn lemma_p2_adds(a: nat, b: nat)
    ensures p2(a + b) == p2(a) * p2(b),
    decreases b,
{
    if b == 0 {
        assert(p2(a + 0) == p2(a) * 1);
    } else {
        let b1 = (b - 1) as nat;
        lemma_p2_adds(a, b1);
        assert(p2(a + b1) == p2(a) * p2(b1));
        assert(a + b == (a + b1) + 1);
        assert(p2((a + b1) + 1) == 2 * p2(a + b1));
        assert(p2(b1 + 1) == 2 * p2(b1));
        assert(b == b1 + 1);
        assert(p2(a + b) == 2 * (p2(a) * p2(b1)));
        assert(2 * (p2(a) * p2(b1)) == p2(a) * (2 * p2(b1))) by (nonlinear_arith);
        assert(p2(a) * p2(b) == p2(a) * (2 * p2(b1)));
    }
}

pub proof fn lemma_p2_pos(n: nat)
    ensures p2(n) > 0,
    decreases n,
{
    if n > 0 { lemma_p2_pos((n - 1) as nat); }
}

/// Bit `i` of byte `b`, MSB-first (i = 0 is the most significant bit).
pub open spec fn bit_of(b: u8, i: int) -> bool {
    (b >> ((7 - i) as u8)) & 1u8 == 1u8
}

/// The bit sequence of a byte sequence, MSB-first within each byte.
pub open spec fn bits_of(s: Seq<u8>) -> Seq<bool> {
    Seq::new((s.len() * 8) as nat, |i: int| bit_of(s[i / 8], i % 8))
}

/// Buffer view with 64 zero bits of virtual padding, so a fixed-width window
/// load is always inside the model even at the very end of the buffer.
pub open spec fn bview(s: Seq<u8>) -> Seq<bool> {
    bits_of(s) + Seq::new(64, |_i: int| false)
}

/// Big-endian numeric value of a bit sequence.
pub open spec fn bits_val(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0nat
    } else {
        2nat * bits_val(s.drop_last()) + (if s.last() { 1nat } else { 0nat })
    }
}

// ---------------------------------------------------------------- basic facts

pub proof fn lemma_bits_val_bound(s: Seq<bool>)
    ensures bits_val(s) < p2(s.len()),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        lemma_bits_val_bound(s.drop_last());
    }
}

/// Splitting a bit sequence splits its value into a high and a low part.
pub proof fn lemma_bits_val_split(s: Seq<bool>, k: int)
    requires 0 <= k <= s.len(),
    ensures bits_val(s) == bits_val(s.take(k)) * p2((s.len() - k) as nat) + bits_val(s.skip(k)),
    decreases s.len(),
{
    if k == s.len() {
        assert(s.take(k) =~= s);
        assert(s.skip(k) =~= Seq::<bool>::empty());
        assert(p2((s.len() - k) as nat) == 1);
        assert(bits_val(s.skip(k)) == 0);
        assert(bits_val(s.take(k)) * 1 == bits_val(s)) by (nonlinear_arith)
            requires bits_val(s.take(k)) == bits_val(s);
    } else {
        let s0 = s.drop_last();
        lemma_bits_val_split(s0, k);
        assert(s.take(k) =~= s0.take(k));
        assert(s.skip(k).drop_last() =~= s0.skip(k));
        assert(s.skip(k).last() == s.last());
        assert(p2((s.len() - k) as nat) == 2 * p2((s0.len() - k) as nat));
        assert(bits_val(s.skip(k)) == 2 * bits_val(s0.skip(k))
               + (if s.last() { 1nat } else { 0nat }));
        let ta = bits_val(s0.take(k));
        let pa = p2((s0.len() - k) as nat);
        assert(2 * (ta * pa) == ta * (2 * pa)) by (nonlinear_arith);
        assert(bits_val(s) == 2 * (ta * pa + bits_val(s0.skip(k)))
                              + (if s.last() { 1nat } else { 0nat }));
        assert(bits_val(s) == ta * (2 * pa)
                              + (2 * bits_val(s0.skip(k))
                                 + (if s.last() { 1nat } else { 0nat })));
        assert(bits_val(s.take(k)) == ta);
        assert(bits_val(s.take(k)) * p2((s.len() - k) as nat) == ta * (2 * pa));
    }
}

/// A sub-range's value is a shift-and-mask of the whole sequence's value.
pub proof fn lemma_bits_val_subrange(s: Seq<bool>, i: int, j: int)
    requires 0 <= i <= j <= s.len(),
    ensures
        bits_val(s.subrange(i, j))
            == (bits_val(s) / p2((s.len() - j) as nat)) % p2((j - i) as nat),
{
    let n = s.len() as int;
    let v = bits_val(s) as int;
    let hi = bits_val(s.take(i)) as int;
    let lo = bits_val(s.skip(i)) as int;
    let m = bits_val(s.subrange(i, j)) as int;
    let lj = bits_val(s.skip(i).skip(j - i)) as int;
    let a = p2((n - i) as nat) as int;
    let b = p2((n - j) as nat) as int;
    let c = p2((j - i) as nat) as int;

    lemma_p2_pos((n - i) as nat);
    lemma_p2_pos((n - j) as nat);
    lemma_p2_pos((j - i) as nat);
    lemma_p2_adds((j - i) as nat, (n - j) as nat);
    assert(a == c * b);

    lemma_bits_val_split(s, i);
    assert(s.skip(i).len() == n - i);
    assert(v == hi * a + lo);

    let t = s.skip(i);
    assert(t.take(j - i) =~= s.subrange(i, j));
    lemma_bits_val_split(t, j - i);
    assert(t.skip(j - i).len() == n - j);
    assert(lo == m * b + lj);
    lemma_bits_val_bound(t.skip(j - i));
    lemma_bits_val_bound(t.take(j - i));
    assert(lj < b);
    assert(m < c);

    assert(v == (hi * c + m) * b + lj) by (nonlinear_arith)
        requires v == hi * a + lo, lo == m * b + lj, a == c * b;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v, b, hi * c + m, lj);
    assert(v / b == hi * c + m);
    assert(hi * c + m == c * hi + m) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(hi, m, c);
    vstd::arithmetic::div_mod::lemma_small_mod(m as nat, c as nat);
}

} // verus!

verus! {

/// `1 << sh` and `p2(sh)`, for the eight shifts a byte has.
pub proof fn lemma_p2_u8(sh: u8)
    requires sh < 8,
    ensures p2(sh as nat) == (1u8 << sh) as nat,
{
    reveal_with_fuel(p2, 9);
    assert((1u8 << 0u8) == 1u8 && (1u8 << 1u8) == 2u8 && (1u8 << 2u8) == 4u8
           && (1u8 << 3u8) == 8u8 && (1u8 << 4u8) == 16u8 && (1u8 << 5u8) == 32u8
           && (1u8 << 6u8) == 64u8 && (1u8 << 7u8) == 128u8) by (bit_vector);
    assert(sh == 0 || sh == 1 || sh == 2 || sh == 3
           || sh == 4 || sh == 5 || sh == 6 || sh == 7);
}

/// Testing bit `sh` and dividing by `2^sh` then halving are the same question.
pub proof fn lemma_bit_div8(v: u8, sh: u8)
    requires sh < 8,
    ensures ((v >> sh) & 1u8 == 1u8) == ((v as nat) / p2(sh as nat) % 2 == 1),
{
    let d: u8 = 1u8 << sh;
    lemma_p2_u8(sh);
    assert(d > 0) by (bit_vector) requires sh < 8, d == 1u8 << sh;
    assert(((v >> sh) & 1u8 == 1u8) == ((v / d) % 2u8 == 1u8)) by (bit_vector)
        requires sh < 8, d == 1u8 << sh;
    assert((v as nat) / (d as nat) == (v / d) as nat);
}

/// A byte's bits, as `bit_of` sees them and as `bits_seq` writes them, are the
/// same eight bits. The two spellings exist because the buffer model is
/// byte-indexed and the format algebra is bit-indexed; appending a byte to an
/// output buffer is where they have to meet.
pub proof fn lemma_bit_of_is_bits_seq(v: u8, j: int)
    requires 0 <= j < 8,
    ensures bit_of(v, j) == crate::prim_write::bits_seq(v as u64, 8)[j],
{
    lemma_bit_div8(v, (7 - j) as u8);
    assert((v as nat) / p2((7 - j) as nat) % 2 == (v as u64 as nat) / p2((7 - j) as nat) % 2);
}

/// Appending a byte appends its eight bits.
pub proof fn lemma_bits_of_push(s: Seq<u8>, v: u8)
    ensures bits_of(s.push(v)) =~= bits_of(s) + crate::prim_write::bits_seq(v as u64, 8),
{
    let lhs = bits_of(s.push(v));
    let rhs = bits_of(s) + crate::prim_write::bits_seq(v as u64, 8);
    assert(lhs.len() == rhs.len());
    assert forall|i: int| 0 <= i < lhs.len() implies lhs[i] == rhs[i] by {
        if i < 8 * s.len() {
            assert(i / 8 < s.len()) by (nonlinear_arith) requires 0 <= i < 8 * s.len();
        } else {
            assert(i / 8 == s.len() && i % 8 == i - 8 * s.len()) by (nonlinear_arith)
                requires 8 * s.len() <= i < 8 * s.len() + 8;
            lemma_bit_of_is_bits_seq(v, i - 8 * s.len());
        }
    }
}

} // verus!
