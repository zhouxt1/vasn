// The store side of `fastload`: a field of up to 56 bits written with one
// byte load and one 64-bit store (eight in-bounds byte writes, which LLVM
// merges), rather than a read-modify-write per bit (`prim_write::write_bits`).
//
// It is for a writer whose contract is what it has written so far, the bits
// before its position: the store keeps the first `pos % 8` bits of the byte it
// starts in and leaves zeros after the field, overwriting whatever was there,
// so it promises nothing about the bits after `pos + n`.
use vstd::prelude::*;
use crate::bitspec::*;
use crate::bytebits::*;
use crate::prim_write::*;
#[cfg(verus_keep_ghost)]
use crate::prim_read::{lemma_p2_mono, lemma_p2_64, lemma_p2_eq_pow2};

verus! {

/// The eight big-endian bytes of `w`.
pub open spec fn be8(w: u64) -> Seq<u8> {
    seq![(w >> 56u64) as u8, (w >> 48u64) as u8, (w >> 40u64) as u8, (w >> 32u64) as u8,
         (w >> 24u64) as u8, (w >> 16u64) as u8, (w >> 8u64) as u8, w as u8]
}

proof fn bv_disassemble(w: u64)
    by (bit_vector)
    ensures
        w == add(mul(add(mul(add(mul(add(mul(add(mul(add(mul(add(mul(
            ((w >> 56u64) & 0xffu64), 256), ((w >> 48u64) & 0xffu64)), 256),
            ((w >> 40u64) & 0xffu64)), 256), ((w >> 32u64) & 0xffu64)), 256),
            ((w >> 24u64) & 0xffu64)), 256), ((w >> 16u64) & 0xffu64)), 256),
            ((w >> 8u64) & 0xffu64)), 256), (w & 0xffu64)),
{
}

/// The bits of `w`'s eight bytes are `w`'s 64 bits.
proof fn lemma_be8_bits(w: u64)
    ensures bits_of(be8(w)) =~= bits_seq(w, 64),
{
    let s = be8(w);
    let e = Seq::<u8>::empty();
    assert(bits_of(e) =~= Seq::<bool>::empty());
    assert(s =~= e.push(s[0]).push(s[1]).push(s[2]).push(s[3]).push(s[4]).push(s[5]).push(s[6]).push(s[7]));
    lemma_bits_val_push_byte(e, s[0]);
    lemma_bits_val_push_byte(e.push(s[0]), s[1]);
    lemma_bits_val_push_byte(e.push(s[0]).push(s[1]), s[2]);
    lemma_bits_val_push_byte(e.push(s[0]).push(s[1]).push(s[2]), s[3]);
    lemma_bits_val_push_byte(e.push(s[0]).push(s[1]).push(s[2]).push(s[3]), s[4]);
    lemma_bits_val_push_byte(e.push(s[0]).push(s[1]).push(s[2]).push(s[3]).push(s[4]), s[5]);
    lemma_bits_val_push_byte(e.push(s[0]).push(s[1]).push(s[2]).push(s[3]).push(s[4]).push(s[5]), s[6]);
    lemma_bits_val_push_byte(e.push(s[0]).push(s[1]).push(s[2]).push(s[3]).push(s[4]).push(s[5]).push(s[6]), s[7]);
    assert((w >> 56u64) as u8 as u64 == (w >> 56u64) & 0xffu64) by (bit_vector);
    assert((w >> 48u64) as u8 as u64 == (w >> 48u64) & 0xffu64) by (bit_vector);
    assert((w >> 40u64) as u8 as u64 == (w >> 40u64) & 0xffu64) by (bit_vector);
    assert((w >> 32u64) as u8 as u64 == (w >> 32u64) & 0xffu64) by (bit_vector);
    assert((w >> 24u64) as u8 as u64 == (w >> 24u64) & 0xffu64) by (bit_vector);
    assert((w >> 16u64) as u8 as u64 == (w >> 16u64) & 0xffu64) by (bit_vector);
    assert((w >> 8u64) as u8 as u64 == (w >> 8u64) & 0xffu64) by (bit_vector);
    assert(w as u8 as u64 == w & 0xffu64) by (bit_vector);
    bv_disassemble(w);
    assert(bits_val(bits_of(s)) == w as nat);
    lemma_p2_64();
    lemma_bits_seq_val(w, 64);
    lemma_bits_val_inj(bits_of(s), bits_seq(w, 64));
}

/// `a * m + r == p * m` with `r < m` pins `a` to `p`.
proof fn lemma_mul_unique(a: nat, r: nat, p: nat, m: nat)
    requires a * m + r == p * m, r < m,
    ensures a == p,
{
    if a < p {
        assert(a * m + r < p * m) by (nonlinear_arith) requires a < p, r < m;
    } else if a > p {
        assert(a * m >= p * m + m) by (nonlinear_arith) requires a >= p + 1;
    }
}

/// The first `off + n` bits of the stored word: the byte's first `off`, then
/// `v`'s `n`.
proof fn lemma_word_prefix(b: u8, off: nat, n: nat, v: nat, p: nat, w: u64)
    requires
        off < 8, 1 <= n <= 56, v < p2(n),
        p == (b as nat / p2((8 - off) as nat)) * p2(n) + v,
        w as nat == p * p2((64 - off - n) as nat),
    ensures
        bits_seq(w, 64).take((off + n) as int)
            =~= bits_of(seq![b]).take(off as int) + bits_seq(v as u64, n),
{
    let t = bits_seq(w, 64);
    let k = (off + n) as int;
    let m = p2((64 - off - n) as nat);
    lemma_p2_64();
    lemma_bits_seq_val(w, 64);
    lemma_bits_val_split(t, k);
    lemma_bits_val_bound(t.skip(k));
    lemma_mul_unique(bits_val(t.take(k)), bits_val(t.skip(k)), p, m);
    // the right-hand side's value
    let bb = bits_of(seq![b]);
    let a = bb.take(off as int);
    let bs = bits_seq(v as u64, n);
    let r = a + bs;
    lemma_byte_bits(b);
    lemma_bits_val_split(bb, off as int);
    lemma_bits_val_bound(bb.skip(off as int));
    lemma_p2_pos((8 - off) as nat);
    assert(bits_val(a) == b as nat / p2((8 - off) as nat)) by (nonlinear_arith)
        requires b as nat == bits_val(a) * p2((8 - off) as nat) + bits_val(bb.skip(off as int)),
                 bits_val(bb.skip(off as int)) < p2((8 - off) as nat), p2((8 - off) as nat) > 0;
    lemma_p2_mono(n, 64);
    lemma_bits_seq_val(v as u64, n);
    assert(r.take(off as int) =~= a);
    assert(r.skip(off as int) =~= bs);
    lemma_bits_val_split(r, off as int);
    lemma_bits_val_inj(t.take(k), r);
}

/// The arithmetic of `store_bits`: the byte's first `off` bits, then `v`,
/// fit in `off + n` bits, and shifted to the top of a word they fit in it.
proof fn lemma_store_vals(b: u8, off: nat, n: nat, v: u64)
    requires off < 8, 1 <= n <= 56, v < p2(n),
    ensures
        ((b as u64) >> ((8 - off) as u64)) as nat == b as nat / p2((8 - off) as nat),
        (1u64 << (n as u64)) as nat == p2(n),
        ((b as u64) >> ((8 - off) as u64)) as nat * p2(n) + v < p2(off + n),
        p2(off + n) * p2((64 - off - n) as nat) == p2(64),
        p2(64) == 0x1_0000_0000_0000_0000nat,
        p2((64 - off - n) as nat) > 0,
        p2(off + n) <= 0x8000_0000_0000_0000nat,
{
    let sh = (8 - off) as nat;
    let hi = (b as u64) >> (sh as u64);
    lemma_p2_eq_pow2(sh);
    lemma_p2_eq_pow2(n);
    vstd::bits::lemma_u64_shr_is_div(b as u64, sh as u64);
    lemma_p2_pos(sh);
    lemma_p2_pos((64 - off - n) as nat);
    assert(hi as nat * p2(sh) <= b as nat) by (nonlinear_arith)
        requires hi as nat == b as nat / p2(sh), p2(sh) > 0;
    lemma_p2_adds(off, sh);
    lemma_p2_64();
    assert(hi < p2(off)) by (nonlinear_arith)
        requires hi as nat * p2(sh) <= b as nat, b < 256, p2(off) * p2(sh) == 256, p2(sh) > 0;
    vstd::bits::lemma_u64_pow2_no_overflow(n);
    vstd::bits::lemma_u64_shl_is_mul(1u64, n as u64);
    lemma_p2_adds(off, n);
    assert(hi * p2(n) + v < p2(off + n)) by (nonlinear_arith)
        requires hi < p2(off), v < p2(n), p2(off + n) == p2(off) * p2(n);
    lemma_p2_adds(off + n, (64 - off - n) as nat);
    lemma_p2_mono(off + n, 63);
    assert(p2(63) == 0x8000_0000_0000_0000nat) by { reveal_with_fuel(p2, 64); }
}

/// Eight bytes from byte `i` replaced by `w`'s: the bits before `8 i + off + n`
/// are the old ones before `8 i + off`, then what `w` starts with after its
/// first `off`.
proof fn lemma_store_splice(old: Seq<u8>, new: Seq<u8>, i: int, off: int, n: int, w: u64, x: Seq<bool>)
    requires
        0 <= i, i + 8 <= old.len(), 0 <= off < 8, 1 <= n, off + n <= 64,
        new =~= old.take(i) + be8(w) + old.skip(i + 8),
        bits_seq(w, 64).take(off + n) =~= bits_of(seq![old[i]]).take(off) + x,
    ensures
        bits_of(new).take(8 * i + off + n) =~= bits_of(old).take(8 * i + off) + x,
{
    lemma_be8_bits(w);
    lemma_bits_of_add(old.take(i), old.skip(i));
    assert(old =~= old.take(i) + old.skip(i));
    assert(old.skip(i) =~= seq![old[i]] + old.skip(i + 1));
    lemma_bits_of_add(seq![old[i]], old.skip(i + 1));
    lemma_bits_of_add(old.take(i), be8(w));
    lemma_bits_of_add(old.take(i) + be8(w), old.skip(i + 8));
    let pre = bits_of(old.take(i));
    assert(pre.len() == 8 * i);
    assert(bits_of(old).take(8 * i + off) =~= pre + bits_of(seq![old[i]]).take(off));
    assert(bits_of(new).take(8 * i + off + n) =~= pre + bits_seq(w, 64).take(off + n));
}

/// The low byte of `x`, as `as u8` truncates (plain Rust rejects
/// `#[verifier::truncate]` on an expression).
#[inline(always)]
fn lo8(x: u64) -> (r: u8)
    ensures r == x as u8,
{
    proof {
        assert(x & 0xffu64 < 256) by (bit_vector);
        assert((x & 0xffu64) as u8 == x as u8) by (bit_vector);
    }
    (x & 0xff) as u8
}

/// Write `v` as an `n`-bit field at bit `pos`: what was before `pos` is kept,
/// and what is after `pos + n` is not.
#[inline]
pub fn store_bits(buf: &mut Vec<u8>, pos: usize, n: usize, v: u64)
    requires
        1 <= n <= 56,
        pos / 8 + 8 <= old(buf).len(),
        v < p2(n as nat),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        bits_of(final(buf)@).take(pos + n) =~= bits_of(old(buf)@).take(pos as int) + bits_seq(v, n as nat),
{
    let ghost old_buf = buf@;
    let i: usize = pos / 8;
    let off: usize = pos % 8;
    let b: u8 = buf[i];
    let sl: u64 = (64 - off - n) as u64;
    proof { lemma_store_vals(b, off as nat, n as nat, v); }
    let hi: u64 = (b as u64) >> ((8 - off) as u64);
    let m: u64 = 1u64 << (n as u64);
    assert(hi * m + v < p2((off + n) as nat));
    let p: u64 = hi * m + v;
    proof {
        assert(p as nat * p2(sl as nat) < p2(64)) by (nonlinear_arith)
            requires p < p2((off + n) as nat), p2(64) == p2((off + n) as nat) * p2(sl as nat),
                     p2(sl as nat) > 0;
        lemma_p2_eq_pow2(sl as nat);
        vstd::bits::lemma_u64_shl_is_mul(p, sl);
    }
    let w: u64 = p << sl;
    // the eight bytes as one copy into one sub-slice: LLVM makes it a byte
    // swap and one store (eight `set`s each reload the Vec, which a byte
    // store may alias)
    let a: [u8; 8] = [lo8(w >> 56u64), lo8(w >> 48u64), lo8(w >> 40u64), lo8(w >> 32u64),
                      lo8(w >> 24u64), lo8(w >> 16u64), lo8(w >> 8u64), lo8(w)];
    proof { assert(a@ =~= be8(w)); }
    {
        let s = buf.as_mut_slice();
        let (_head, rest) = s.split_at_mut(i);
        let (mid, _tail) = rest.split_at_mut(8);
        mid.copy_from_slice(vstd::array::array_as_slice(&a));
    }
    proof {
        assert(buf@ =~= old_buf.take(i as int) + be8(w) + old_buf.skip(i as int + 8));
        lemma_word_prefix(b, off as nat, n as nat, v as nat, p as nat, w);
        lemma_store_splice(old_buf, buf@, i as int, off as int, n as int, w, bits_seq(v, n as nat));
    }
}

} // verus!
