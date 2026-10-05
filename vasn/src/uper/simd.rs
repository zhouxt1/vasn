//! Sixteen octets at a time, for `read_octets` off an octet boundary, in
//! SSE2 (`vsimd`). Octet `j` of a string `k` bits into byte `i` is the
//! middle eight bits of the pair `s[i + j], s[i + j + 1]`: interleaved, each
//! pair is a 16-bit lane, shifted down by `8 - k` and masked to its low byte,
//! and the lanes packed back into octets. `vsimd::x86`'s intrinsics are the
//! only trusted code here, each checked against the CPU by its tests.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use vstd::arithmetic::power2::pow2;
use crate::bits::bitspec::*;
use vsimd::spec;
use vsimd::x86::*;

verus! {

broadcast use lemma_byte;

/// The octet `k` bits into the pair `x, y`.
pub open spec fn shifted(x: u8, y: u8, k: nat) -> u8 {
    (((x as int) * 256 + y as int) / pow2((8 - k) as nat) as int % 256) as u8
}

proof fn lemma_and_ff(a: u8) ensures a & 0xffu8 == a, a & 0u8 == 0u8, {
    assert(a & 0xffu8 == a) by (bit_vector);
    assert(a & 0u8 == 0u8) by (bit_vector);
}

/// What the lane arithmetic leaves in one lane: the octet, below 256.
proof fn lemma_lane(x: u8, y: u8, k: nat)
    requires 1 <= k <= 7,
    ensures
        ({
            let v = (y as int + 256 * x as int) / pow2((8 - k) as nat) as int;
            &&& 0 <= v < 32768
            &&& spec::put16(v, 0) == shifted(x, y, k)
        }),
{
    vstd::arithmetic::power2::lemma_pow2_pos((8 - k) as nat);
    vstd::arithmetic::power2::lemma_pow2_adds((8 - k) as nat, (k + 7) as nat);
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma_pow2_strictly_increases((k + 7) as nat, 15);
    let p = pow2((8 - k) as nat) as int;
    let q = pow2((k + 7) as nat) as int;
    let w = y as int + 256 * x as int;
    assert(w < 65536);
    assert(p * q == 32768) by { assert((8 - k) + (k + 7) == 15); }
    assert(w / p < 32768) by (nonlinear_arith)
        requires w < 65536, p * q == 32768, p >= 2, q >= 1, w >= 0,
                 q <= 16384, p >= 1;
    assert(w / p >= 0) by (nonlinear_arith) requires w >= 0, p >= 1;
}

/// The sixteen octets `k` bits into `s[i..i + 17]`.
#[inline(always)]
pub fn shifted16(s: &[u8], i: usize, k: u32) -> (a: [u8; 16])
    requires i + 17 <= s@.len(), s@.len() <= usize::MAX, 1 <= k <= 7,
    ensures forall|j: int| 0 <= j < 16 ==> #[trigger] a@[j] == shifted(s@[i + j], s@[i + j + 1], k as nat),
{
    let x = loadu(s, i);
    let y = loadu(s, i + 1);
    let m = set1_epi16(0xff);
    let lo = and_si128(srl_epi16(unpacklo_epi8(y, x), 8 - k), m);
    let hi = and_si128(srl_epi16(unpackhi_epi8(y, x), 8 - k), m);
    let r = packus_epi16(lo, hi);
    let a = to_bytes(r);
    proof {
        let n = (8 - k) as nat;
        assert forall|j: int| 0 <= j < 16 implies #[trigger] a@[j] == shifted(s@[i + j], s@[i + j + 1], k as nat) by {
            let jj = if j < 8 { j } else { j - 8 };
            let u = if j < 8 { spec::unpacklo_epi8(v8(y), v8(x)) } else { spec::unpackhi_epi8(v8(y), v8(x)) };
            let l = if j < 8 { lo } else { hi };
            let sh = spec::srli_epi16(u, n);
            assert(u[2 * jj] == s@[i + j + 1]);
            assert(u[2 * jj + 1] == s@[i + j]);
            assert(spec::w16(u, jj) == s@[i + j + 1] as int + 256 * s@[i + j] as int);
            lemma_lane(s@[i + j], s@[i + j + 1], k as nat);
            let v = spec::w16(u, jj) / pow2(n) as int;
            assert(sh[2 * jj] == spec::put16(v, 2 * jj));
            assert(sh[2 * jj + 1] == spec::put16(v, 2 * jj + 1));
            assert(spec::put16(v, 2 * jj) == shifted(s@[i + j], s@[i + j + 1], k as nat));
            lemma_and_ff(sh[2 * jj]);
            lemma_and_ff(sh[2 * jj + 1]);
            assert(spec::set1_epi16(0xff)[2 * jj] == 0xffu8);
            assert(spec::set1_epi16(0xff)[2 * jj + 1] == 0u8);
            assert(v8(l)[2 * jj] == shifted(s@[i + j], s@[i + j + 1], k as nat));
            assert(v8(l)[2 * jj + 1] == 0u8);
            assert(spec::sw16(v8(l), jj) == shifted(s@[i + j], s@[i + j + 1], k as nat) as int);
        }
    }
    a
}

/// The octet `k` bits into the pair at byte `m` is those eight bits.
pub proof fn lemma_shifted_bits(s: Seq<u8>, m: int, k: nat)
    requires 0 <= m, m + 2 <= s.len(), 1 <= k <= 7,
    ensures
        crate::bits::prim_write::bits_seq(shifted(s[m], s[m + 1], k) as u64, 8)
            =~= bits_of(s).subrange(8 * m + k, 8 * m + k + 8),
{
    let t = bits_of(s).subrange(8 * m, 8 * m + 16);
    crate::uper::fast::lemma_bits_of_subrange(s, m, m + 2);
    assert(s.subrange(m, m + 2) =~= seq![s[m]].push(s[m + 1]));
    crate::bits::bytebits::lemma_bits_val_push_byte(seq![s[m]], s[m + 1]);
    crate::bits::bytebits::lemma_byte_bits(s[m]);
    assert(bits_val(t) == s[m] as nat * 256 + s[m + 1] as nat);
    lemma_bits_val_subrange(t, k as int, (k + 8) as int);
    let u = t.subrange(k as int, (k + 8) as int);
    assert(u =~= bits_of(s).subrange(8 * m + k, 8 * m + k + 8));
    crate::bits::prim_read::lemma_p2_eq_pow2((8 - k) as nat);
    assert(p2(8) == 256) by { reveal_with_fuel(p2, 10); }
    assert((16 - (k + 8)) as nat == (8 - k) as nat);
    assert(bits_val(u) == shifted(s[m], s[m + 1], k) as nat);
    crate::uper::prim::lemma_bits_roundtrip(u);
}

/// Sixteen shifted octets are those 128 bits.
pub proof fn lemma_shifted16_bits(s: Seq<u8>, i: int, k: nat, a: Seq<u8>)
    requires
        0 <= i, i + 17 <= s.len(), 1 <= k <= 7, a.len() == 16,
        forall|j: int| 0 <= j < 16 ==> #[trigger] a[j] == shifted(s[i + j], s[i + j + 1], k),
    ensures bits_of(a) =~= bits_of(s).subrange(8 * i + k, 8 * i + k + 128),
{
    let l = bits_of(a);
    let r = bits_of(s).subrange(8 * i + k, 8 * i + k + 128);
    assert forall|q: int| 0 <= q < 128 implies l[q] == r[q] by {
        let j = q / 8;
        let b = q % 8;
        assert(0 <= j < 16 && 0 <= b < 8 && q == 8 * j + b);
        lemma_shifted_bits(s, i + j, k);
        lemma_bit_of_is_bits_seq(a[j], b);
        assert(l[q] == bit_of(a[j], b));
        let bs = crate::bits::prim_write::bits_seq(shifted(s[i + j], s[i + j + 1], k) as u64, 8);
        assert(bs[b] == bits_of(s)[8 * (i + j) + k + b]);
        assert(8 * (i + j) + k + b == 8 * i + k + q);
    }
}

} // verus!
