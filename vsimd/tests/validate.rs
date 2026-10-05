//! Validation of the trusted base: each intrinsic in `vsimd::x86`, run on
//! this CPU, against the proved model of its contract in `vsimd::model`.
//!
//! * Bytewise ops of two operands: every pair of byte values, in every lane.
//! * Ops on 16-bit lanes of one operand (shifts, packs): every 16-bit value,
//!   in every lane.
//! * Everything: random vectors, which also covers mixing across lanes.
//! * `cargo test --release -- --ignored`: every pair of 16-bit values for
//!   the two-operand 16-bit ops (2^32 pairs each, a few minutes).
//!
//! The byte order the contracts use (byte 0 lowest, first in memory) is
//! checked against `_mm_set_epi8`, which names lanes independently of this
//! crate.
#![cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;
use vsimd::{model as m, x86 as x};

type B = [u8; 16];

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn bytes(&mut self) -> B { let (a, b) = (self.next(), self.next()); let mut r = [0u8; 16]; r[..8].copy_from_slice(&a.to_le_bytes()); r[8..].copy_from_slice(&b.to_le_bytes()); r }
    /// Random bytes biased towards the edges of the signed and unsigned ranges.
    fn edgy(&mut self) -> B {
        const E: [u8; 12] = [0, 1, 2, 126, 127, 128, 129, 130, 253, 254, 255, 64];
        let mut r = self.bytes();
        for b in r.iter_mut() { if self.next() % 3 == 0 { *b = E[(self.next() % 12) as usize]; } }
        r
    }
}

fn hw2(f: fn(__m128i, __m128i) -> __m128i, a: B, b: B) -> B { x::to_bytes(f(x::from_bytes(a), x::from_bytes(b))) }
fn hw1(f: &dyn Fn(__m128i) -> __m128i, a: B) -> B { x::to_bytes(f(x::from_bytes(a))) }

const RANDOM: usize = 1 << 20;

#[test]
fn byte_order() {
    // _mm_set_epi8 takes lanes from 15 down to 0.
    let v = unsafe { _mm_set_epi8(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0) };
    let want: B = core::array::from_fn(|k| k as u8);
    assert_eq!(x::to_bytes(v), want);
    assert_eq!(x::to_bytes(x::from_bytes(want)), want);
    let mut r = Rng(1);
    for _ in 0..RANDOM / 16 {
        let a = r.bytes();
        assert_eq!(x::to_bytes(x::from_bytes(a)), a);
    }
}

#[test]
fn load_store() {
    let mut r = Rng(2);
    for _ in 0..20000 {
        let n = 16 + (r.next() % 64) as usize;
        let s: Vec<u8> = (0..n).map(|_| r.next() as u8).collect();
        let i = (r.next() as usize) % (n - 15);
        assert_eq!(x::to_bytes(x::loadu(&s, i)), <B>::try_from(&s[i..i + 16]).unwrap());
        let v = r.bytes();
        let mut t = s.clone();
        x::storeu(&mut t, i, x::from_bytes(v));
        let mut want = s.clone();
        want[i..i + 16].copy_from_slice(&v);
        assert_eq!(t, want);
    }
}

#[test]
fn constants() {
    assert_eq!(x::to_bytes(x::setzero()), [0u8; 16]);
    for v in 0..=255u8 { assert_eq!(x::to_bytes(x::set1_epi8(v)), m::set1_epi8(v)); }
    for v in 0..=65535u16 { assert_eq!(x::to_bytes(x::set1_epi16(v)), m::set1_epi16(v)); }
}

/// Every (a, b) byte pair in every lane, then random vectors.
fn check_bytewise(name: &str, hw: fn(__m128i, __m128i) -> __m128i, model: fn(B, B) -> B) {
    for rot in 0..16usize {
        for chunk in 0..4096usize {
            let mut a = [0u8; 16];
            let mut b = [0u8; 16];
            for lane in 0..16 {
                let p = chunk * 16 + (lane + rot) % 16;
                a[lane] = (p >> 8) as u8;
                b[lane] = p as u8;
            }
            assert_eq!(hw2(hw, a, b), model(a, b), "{name} on {a:?} {b:?}");
        }
    }
    check_random2(name, hw, model);
}

fn check_random2(name: &str, hw: fn(__m128i, __m128i) -> __m128i, model: fn(B, B) -> B) {
    let mut r = Rng(0x9e3779b97f4a7c15 ^ name.len() as u64);
    for i in 0..RANDOM {
        let (a, b) = if i % 2 == 0 { (r.bytes(), r.bytes()) } else { (r.edgy(), r.edgy()) };
        assert_eq!(hw2(hw, a, b), model(a, b), "{name} on {a:?} {b:?}");
    }
}

/// Every 16-bit value in every 16-bit lane, for an op of one operand.
fn check_lanes16(name: &str, hw: &dyn Fn(__m128i) -> __m128i, model: &dyn Fn(B) -> B) {
    for rot in 0..8usize {
        for chunk in 0..8192usize {
            let mut a = [0u8; 16];
            for lane in 0..8 {
                let v = (chunk * 8 + (lane + rot) % 8) as u16;
                a[2 * lane..2 * lane + 2].copy_from_slice(&v.to_le_bytes());
            }
            assert_eq!(hw1(hw, a), model(a), "{name} on {a:?}");
        }
    }
    let mut r = Rng(77 + name.len() as u64);
    for _ in 0..RANDOM {
        let a = r.bytes();
        assert_eq!(hw1(hw, a), model(a), "{name} on {a:?}");
    }
}

macro_rules! bytewise {
    ($($t:ident),*) => { $( #[test] fn $t() { check_bytewise(stringify!($t), x::$t, m::$t); } )* };
}
bytewise!(subs_epu8, adds_epu8, max_epu8, cmpeq_epi8, and_si128, or_si128, xor_si128, andnot_si128,
          adds_epi8, subs_epi8, add_epi8, sub_epi8, avg_epu8);

#[test]
fn shifts() {
    check_lanes16("srai_epi16_7", &x::srai_epi16_7, &|a| m::srai_epi16(a, 7));
    check_lanes16("srai_epi16_11", &x::srai_epi16_11, &|a| m::srai_epi16(a, 11));
    check_lanes16("srli_epi16_1", &x::srli_epi16_1, &|a| m::srli_epi16(a, 1));
    check_lanes16("srai_epi16_6", &x::srai_epi16_6, &|a| m::srai_epi16(a, 6));
    check_lanes16("srli_epi16_6", &x::srli_epi16_6, &|a| m::srli_epi16(a, 6));
    check_lanes16("srli_epi16_4", &x::srli_epi16_4, &|a| m::srli_epi16(a, 4));
    check_lanes16("srli_epi16_8", &x::srli_epi16_8, &|a| m::srli_epi16(a, 8));
    check_lanes16("slli_epi16_8", &x::slli_epi16_8, &|a| m::slli_epi16(a, 8));
    for n in 0..16u32 {
        check_lanes16(&format!("srl_epi16 by {n}"), &|a| x::srl_epi16(a, n), &|a| m::srli_epi16(a, n));
    }
}

#[test]
fn packs() {
    // Every 16-bit value through each lane of either operand.
    check_lanes16("packs_epi16 (a)", &|a| x::packs_epi16(a, x::setzero()), &|a| m::packs_epi16(a, [0; 16]));
    check_lanes16("packs_epi16 (b)", &|b| x::packs_epi16(x::setzero(), b), &|b| m::packs_epi16([0; 16], b));
    check_random2("packs_epi16", x::packs_epi16, m::packs_epi16);
}

#[test]
fn unpack() {
    // A permutation: distinct bytes show where each one goes.
    let a: B = core::array::from_fn(|k| k as u8);
    let b: B = core::array::from_fn(|k| 16 + k as u8);
    assert_eq!(hw2(x::unpacklo_epi8, a, b), m::unpacklo_epi8(a, b));
    assert_eq!(hw2(x::unpackhi_epi8, a, b), m::unpackhi_epi8(a, b));
    check_random2("unpacklo_epi8", x::unpacklo_epi8, m::unpacklo_epi8);
    check_random2("unpackhi_epi8", x::unpackhi_epi8, m::unpackhi_epi8);
    type Op = (&'static str, fn(__m128i, __m128i) -> __m128i, fn(B, B) -> B);
    let ops: [Op; 6] = [("unpacklo_epi16", x::unpacklo_epi16, m::unpacklo_epi16), ("unpackhi_epi16", x::unpackhi_epi16, m::unpackhi_epi16),
        ("unpacklo_epi32", x::unpacklo_epi32, m::unpacklo_epi32), ("unpackhi_epi32", x::unpackhi_epi32, m::unpackhi_epi32),
        ("unpacklo_epi64", x::unpacklo_epi64, m::unpacklo_epi64), ("unpackhi_epi64", x::unpackhi_epi64, m::unpackhi_epi64)];
    for (name, hw, model) in ops {
        assert_eq!(hw2(hw, a, b), model(a, b), "{name}");
        check_random2(name, hw, model);
    }
}

#[test]
fn half_load_store() {
    let mut r = Rng(3);
    for _ in 0..20000 {
        let n = 8 + (r.next() % 64) as usize;
        let s: Vec<u8> = (0..n).map(|_| r.next() as u8).collect();
        let i = (r.next() as usize) % (n - 7);
        let mut want = [0u8; 16];
        want[..8].copy_from_slice(&s[i..i + 8]);
        assert_eq!(x::to_bytes(x::loadl(&s, i)), want);
        let v = r.bytes();
        let (mut t, mut u) = (s.clone(), s.clone());
        x::storel(&mut t, i, x::from_bytes(v));
        x::storeh(&mut u, i, x::from_bytes(v));
        let (mut wl, mut wh) = (s.clone(), s.clone());
        wl[i..i + 8].copy_from_slice(&v[..8]);
        wh[i..i + 8].copy_from_slice(&v[8..]);
        assert_eq!(t, wl);
        assert_eq!(u, wh);
    }
}

#[test]
fn arith16() {
    check_random2("add_epi16", x::add_epi16, m::add_epi16);
    check_random2("mulhi_epi16", x::mulhi_epi16, m::mulhi_epi16);
    check_random2("mulhi_epu16", x::mulhi_epu16, m::mulhi_epu16);
    check_random2("adds_epu16", x::adds_epu16, m::adds_epu16);
    check_random2("subs_epu16", x::subs_epu16, m::subs_epu16);
    // The YUV->RGB constants (vwebp::rgb), against every 16-bit value.
    for c in [19077u16, 26149, 6419, 13320, 33050, 14234, 8708, 17685] {
        let cb = m::set1_epi16(c);
        check_lanes16("mulhi_epu16 (constant)", &|a| x::mulhi_epu16(a, x::from_bytes(cb)), &|a| m::mulhi_epu16(a, cb));
        check_lanes16("adds_epu16 (constant)", &|a| x::adds_epu16(a, x::from_bytes(cb)), &|a| m::adds_epu16(a, cb));
        check_lanes16("subs_epu16 (constant)", &|a| x::subs_epu16(a, x::from_bytes(cb)), &|a| m::subs_epu16(a, cb));
    }
    // One operand every 16-bit value, the other the constants used.
    for c in [0x0900u16, 63, 1, 0x7fff, 0x8000, 0xffff] {
        let cb = m::set1_epi16(c);
        check_lanes16("mulhi_epi16 (constant)", &|a| x::mulhi_epi16(a, x::from_bytes(cb)), &|a| m::mulhi_epi16(a, cb));
        check_lanes16("add_epi16 (constant)", &|a| x::add_epi16(a, x::from_bytes(cb)), &|a| m::add_epi16(a, cb));
    }
}

/// Every pair of 16-bit values, each lane position covered in turn.
fn check_pairs16(name: &str, hw: fn(__m128i, __m128i) -> __m128i, model: fn(B, B) -> B) {
    for hi in 0..65536u32 {
        for lo in (0..65536u32).step_by(8) {
            let mut a = [0u8; 16];
            let mut b = [0u8; 16];
            for lane in 0..8 {
                let bv = (lo + ((lane as u32 + hi) % 8)) as u16;
                a[2 * lane..2 * lane + 2].copy_from_slice(&(hi as u16).to_le_bytes());
                b[2 * lane..2 * lane + 2].copy_from_slice(&bv.to_le_bytes());
            }
            assert_eq!(hw2(hw, a, b), model(a, b), "{name} on {a:?} {b:?}");
        }
    }
}

#[test]
#[ignore]
fn exhaustive_add_epi16() { check_pairs16("add_epi16", x::add_epi16, m::add_epi16); }

#[test]
#[ignore]
fn exhaustive_mulhi_epi16() { check_pairs16("mulhi_epi16", x::mulhi_epi16, m::mulhi_epi16); }

#[test]
#[ignore]
fn exhaustive_mulhi_epu16() { check_pairs16("mulhi_epu16", x::mulhi_epu16, m::mulhi_epu16); }

#[test]
#[ignore]
fn exhaustive_adds_subs_epu16() {
    check_pairs16("adds_epu16", x::adds_epu16, m::adds_epu16);
    check_pairs16("subs_epu16", x::subs_epu16, m::subs_epu16);
}

#[test]
fn slice_store() {
    let mut r = Rng(5);
    for _ in 0..20000 {
        let n = 16 + (r.next() % 64) as usize;
        let s: Vec<u8> = (0..n).map(|_| r.next() as u8).collect();
        let i = (r.next() as usize) % (n - 15);
        let v = r.bytes();
        let mut t = s.clone();
        x::storeu_s(&mut t[..], i, x::from_bytes(v));
        let mut want = s.clone();
        want[i..i + 16].copy_from_slice(&v);
        assert_eq!(t, want);
    }
}

#[test]
fn ops32() {
    for (name, hw, model) in [("sub_epi16", x::sub_epi16 as fn(__m128i, __m128i) -> __m128i, m::sub_epi16 as fn(B, B) -> B),
        ("packus_epi16", x::packus_epi16, m::packus_epi16), ("add_epi32", x::add_epi32, m::add_epi32),
        ("sub_epi32", x::sub_epi32, m::sub_epi32), ("packs_epi32", x::packs_epi32, m::packs_epi32)] {
        check_random2(name, hw, model);
    }
    check_lanes16("packus_epi16 (a)", &|a| x::packus_epi16(a, x::setzero()), &|a| m::packus_epi16(a, [0; 16]));
    check_lanes16("packus_epi16 (b)", &|b| x::packus_epi16(x::setzero(), b), &|b| m::packus_epi16([0; 16], b));
    check_lanes16("sub_epi16 (a - 0x1234)", &|a| x::sub_epi16(a, x::set1_epi16(0x1234)), &|a| m::sub_epi16(a, m::set1_epi16(0x1234)));
    // 32-bit lanes: values near every power of two and its negation, in every lane, and random.
    let mut edge: Vec<u32> = vec![0, 1, 2, 3, 4, 7, 8, 0x7fff_ffff, 0x8000_0000, 0xffff_ffff];
    for b in 0..32 { for d in [-2i64, -1, 0, 1, 2] { edge.push(((1i64 << b) + d) as u32); edge.push((-(1i64 << b) + d) as u32); } }
    let mut r = Rng(9);
    let lanes = |v: [u32; 4]| -> B { let mut o = [0u8; 16]; for j in 0..4 { o[4 * j..4 * j + 4].copy_from_slice(&v[j].to_le_bytes()); } o };
    for _ in 0..RANDOM {
        let pick = |r: &mut Rng| -> u32 { if r.next() % 2 == 0 { edge[(r.next() as usize) % edge.len()] } else { r.next() as u32 } };
        let a = lanes([pick(&mut r), pick(&mut r), pick(&mut r), pick(&mut r)]);
        let b = lanes([pick(&mut r), pick(&mut r), pick(&mut r), pick(&mut r)]);
        for (name, hw, model) in [("add_epi32", x::add_epi32 as fn(__m128i, __m128i) -> __m128i, m::add_epi32 as fn(B, B) -> B),
            ("sub_epi32", x::sub_epi32, m::sub_epi32), ("packs_epi32", x::packs_epi32, m::packs_epi32)] {
            assert_eq!(hw2(hw, a, b), model(a, b), "{name} on {a:?} {b:?}");
        }
        assert_eq!(hw1(&x::srai_epi32_3, a), m::srai_epi32(a, 3), "srai_epi32_3 on {a:?}");
        assert_eq!(hw1(&x::srai_epi32_16, a), m::srai_epi32(a, 16), "srai_epi32_16 on {a:?}");
        assert_eq!(hw1(&x::srli_epi32_8, a), m::srli_epi32(a, 8), "srli_epi32_8 on {a:?}");
        assert_eq!(hw1(&x::slli_epi32_16, a), m::slli_epi32(a, 16), "slli_epi32_16 on {a:?}");
        let c = pick(&mut r);
        assert_eq!(x::to_bytes(x::set1_epi32(c)), m::set1_epi32(c), "set1_epi32 {c}");
    }
}

#[test]
fn load4_store4() {
    let mut r = Rng(4);
    for _ in 0..20000 {
        let n = 4 + (r.next() % 64) as usize;
        let s: Vec<u8> = (0..n).map(|_| r.next() as u8).collect();
        let i = (r.next() as usize) % (n - 3);
        let mut want = [0u8; 16];
        want[..4].copy_from_slice(&s[i..i + 4]);
        assert_eq!(x::to_bytes(x::load4(&s, i)), want);
        let v = r.bytes();
        for lane in 0..4 {
            let mut t = s.clone();
            let base = t.clone();
            x::store4(&mut t, i, x::from_bytes(v), lane);
            let mut w = base.clone();
            w[i..i + 4].copy_from_slice(&v[4 * lane..4 * lane + 4]);
            assert_eq!(t, w);
        }
    }
}

/// Every 32-bit value in every lane, for the 32-bit shifts (2^32 values).
#[test]
#[ignore]
fn exhaustive_shifts_epi32() {
    for hi in 0..(1u64 << 30) {
        let mut a = [0u8; 16];
        for lane in 0..4 { a[4 * lane..4 * lane + 4].copy_from_slice(&((hi * 4 + lane as u64) as u32).to_le_bytes()); }
        assert_eq!(hw1(&x::srai_epi32_3, a), m::srai_epi32(a, 3));
        assert_eq!(hw1(&x::srai_epi32_16, a), m::srai_epi32(a, 16));
        assert_eq!(hw1(&x::srli_epi32_8, a), m::srli_epi32(a, 8));
        assert_eq!(hw1(&x::slli_epi32_16, a), m::slli_epi32(a, 16));
    }
}

#[test]
fn load_store_u32() {
    let mut r = Rng(6);
    for _ in 0..20000 {
        let n = 4 + (r.next() % 32) as usize;
        let s: Vec<u32> = (0..n).map(|_| r.next() as u32).collect();
        let i = (r.next() as usize) % (n - 3);
        let want: B = core::array::from_fn(|k| s[i + k / 4].to_le_bytes()[k % 4]);
        assert_eq!(x::to_bytes(x::loadu_u32(&s, i)), want);
        let v = r.bytes();
        let mut t = s.clone();
        x::storeu_u32(&mut t, i, x::from_bytes(v));
        let mut w = s.clone();
        for j in 0..4 { w[i + j] = u32::from_le_bytes([v[4 * j], v[4 * j + 1], v[4 * j + 2], v[4 * j + 3]]); }
        assert_eq!(t, w);
    }
    // u32s is put32 of each element: byte k is byte k % 4 of element k / 4
    let s: Vec<u32> = vec![0x04030201, 0x08070605, 0x0c0b0a09, 0x100f0e0d];
    let want: B = core::array::from_fn(|k| k as u8 + 1);
    assert_eq!(x::to_bytes(x::loadu_u32(&s, 0)), want);
}

#[test]
fn load_i32() {
    let mut r = Rng(5);
    for _ in 0..200000 {
        let c: [i32; 16] = core::array::from_fn(|_| match r.next() % 4 { 0 => r.next() as i32, 1 => (r.next() % 65536) as i32 - 32768, 2 => i32::MIN, _ => i32::MAX });
        for k in 0..4 { assert_eq!(x::to_bytes(x::load_i32x4(&c, k)), m::load_i32x4(&c, k)); }
    }
}

#[test]
fn mem_scalar() {
    // vsimd::mem's unchecked accesses give what the checked ones do.
    let v: Vec<u32> = (0..100u32).map(|k| k.wrapping_mul(0x9e3779b9)).collect();
    for i in 0..v.len() {
        assert_eq!(vsimd::mem::get(&v, i), v[i]);
        assert!(core::ptr::eq(vsimd::mem::get_ref(&v, i), &v[i]));
        let mut w = v.clone();
        vsimd::mem::vset(&mut w, i, 7);
        let mut want = v.clone();
        want[i] = 7;
        assert_eq!(w, want);
    }
    // sset_u32le: the four little-endian bytes at i, the rest as they were.
    for i in 0..=36usize {
        let mut s: Vec<u8> = (0..40u8).collect();
        let x = 0x1234_5678u32.wrapping_mul(i as u32 + 1);
        vsimd::mem::sset_u32le(&mut s, i, x);
        let mut want: Vec<u8> = (0..40u8).collect();
        want[i..i + 4].copy_from_slice(&x.to_le_bytes());
        assert_eq!(s, want);
    }
}
