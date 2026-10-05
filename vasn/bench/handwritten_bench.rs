use std::convert::TryInto;
// Plain-Rust mirror of the verified exec code, for codegen/perf inspection.
use std::time::Instant;

#[inline(always)]
fn load_window(s: &[u8], i: usize) -> u64 {
    let mut w: u64 = 0;
    let mut k: usize = 0;
    while k < 8 {
        let b: u8 = if k < s.len() - i { s[i + k] } else { 0u8 };
        w = w * 256 + (b as u64);
        k += 1;
    }
    w
}

#[inline(always)]
fn read_bits(s: &[u8], pos: usize, n: usize) -> u64 {
    let i = pos / 8;
    let off = pos % 8;
    let w = load_window(s, i);
    let sh = 64 - off - n;
    let mask = (1u64 << (n as u64)) - 1;
    (w >> (sh as u64)) & mask
}

// What a byte-at-a-time, read-k-bytes-then-mask decoder does (VUPER's shape).
#[inline(always)]
fn read_bits_bytewise(s: &[u8], pos: usize, n: usize) -> u64 {
    let i = pos / 8;
    let off = pos % 8;
    let nbytes = (off + n + 7) / 8;
    let mut a: u64 = 0;
    let mut k = 0;
    while k < nbytes {
        let b = if i + k < s.len() { s[i + k] } else { 0 };
        a = (a << 8) | (b as u64);
        k += 1;
    }
    let total = nbytes * 8;
    (a >> (total - off - n)) & ((1u64 << n) - 1)
}

// Fully safe, no trusted primitive: unrolled byte reads on the fast path.
#[inline(always)]
fn read_bits_unrolled(s: &[u8], pos: usize, n: usize) -> u64 {
    let i = pos / 8;
    let off = pos % 8;
    let w = if i + 8 <= s.len() {
        ((s[i] as u64) << 56) | ((s[i+1] as u64) << 48) | ((s[i+2] as u64) << 40)
      | ((s[i+3] as u64) << 32) | ((s[i+4] as u64) << 24) | ((s[i+5] as u64) << 16)
      | ((s[i+6] as u64) << 8)  |  (s[i+7] as u64)
    } else {
        load_window(s, i)
    };
    (w >> ((64 - off - n) as u64)) & ((1u64 << (n as u64)) - 1)
}

// Single unaligned 64-bit load; padded slow path only near the end.
#[inline(always)]
fn read_bits_fast(s: &[u8], pos: usize, n: usize) -> u64 {
    let i = pos / 8;
    let off = pos % 8;
    let w = if i + 8 <= s.len() {
        u64::from_be_bytes(s[i..i + 8].try_into().unwrap())
    } else {
        load_window(s, i)
    };
    (w >> ((64 - off - n) as u64)) & ((1u64 << (n as u64)) - 1)
}

// Refill-based bit accumulator: one load per ~57 bits consumed.
struct Acc<'a> { s: &'a [u8], byte: usize, bits: u32, acc: u64 }
impl<'a> Acc<'a> {
    #[inline(always)]
    fn new(s: &'a [u8]) -> Self { Acc { s, byte: 0, bits: 0, acc: 0 } }
    #[inline(always)]
    fn refill(&mut self) {
        while self.bits <= 56 && self.byte < self.s.len() {
            self.acc = (self.acc << 8) | self.s[self.byte] as u64;
            self.byte += 1;
            self.bits += 8;
        }
    }
    #[inline(always)]
    fn take(&mut self, n: usize) -> u64 {
        if (self.bits as usize) < n { self.refill(); }
        self.bits -= n as u32;
        (self.acc >> self.bits) & ((1u64 << n) - 1)
    }
}

fn main() {
    let buf: Vec<u8> = (0..4096u32).map(|x| (x * 37 + 11) as u8).collect();
    // A field-width mix roughly like 5G NR-RRC: lots of 1-bit presence flags,
    // small enums, occasional wider integers.
    let widths: Vec<usize> = vec![1,1,1,4,1,3,8,1,1,2,16,1,5,1,1,12,1,6,1,1,24,1,2,1];
    let iters = 3000;

    for (name, f) in [
        ("window64  ", read_bits as fn(&[u8], usize, usize) -> u64),
        ("bytewise  ", read_bits_bytewise as fn(&[u8], usize, usize) -> u64),
        ("fastload  ", read_bits_fast as fn(&[u8], usize, usize) -> u64),
        ("unrolled  ", read_bits_unrolled as fn(&[u8], usize, usize) -> u64),
    ] {
        let mut acc: u64 = 0;
        let mut nreads: u64 = 0;
        let t = Instant::now();
        for _ in 0..iters {
            let mut pos = 0usize;
            let mut wi = 0usize;
            while pos + 56 < buf.len() * 8 {
                let n = widths[wi % widths.len()];
                acc = acc.wrapping_add(f(&buf, pos, n));
                pos += n;
                wi += 1;
                nreads += 1;
            }
        }
        let el = t.elapsed();
        println!("{} {:>10} reads  {:>8.2} ns/read  (checksum {})",
                 name, nreads, el.as_nanos() as f64 / nreads as f64, acc);
    }

    // accumulator variant
    let mut acc_sum: u64 = 0;
    let mut nreads: u64 = 0;
    let t = Instant::now();
    for _ in 0..iters {
        let mut a = Acc::new(&buf);
        let mut consumed = 0usize;
        let mut wi = 0usize;
        while consumed + 56 < buf.len() * 8 {
            let n = widths[wi % widths.len()];
            acc_sum = acc_sum.wrapping_add(a.take(n));
            consumed += n;
            wi += 1;
            nreads += 1;
        }
    }
    let el = t.elapsed();
    println!("accum      {:>10} reads  {:>8.2} ns/read  (checksum {})",
             nreads, el.as_nanos() as f64 / nreads as f64, acc_sum);
}
