//! Values from entropy, for structure-aware fuzzing.
//!
//! Generated code builds a value of each type out of a `Gen`, following the
//! type's constraints -- sizes, ranges, only alternatives and values the
//! schema has -- so that, encoded by the (verified) encoder, it is a valid
//! message of the schema. A fuzzer mutating the entropy then mutates the
//! message's structure, not its bits.
//!
//! Unverified, and outside `verus!`, like `jer`. When the entropy runs out
//! every read returns zeros, which pick the smallest choice everywhere (no
//! optional component, the first alternative, the shortest list); the type
//! graph is acyclic, so generation always ends.
pub struct Gen<'a> {
    data: &'a [u8],
    bit: usize,
    /// how many more list elements a boundary length may add: a value has at
    /// most one list at a fragment boundary, so lists of such lists stay small
    budget: usize,
}

/// The lengths where the length determinant changes form (X.691 11.9.3.6 to
/// 11.9.3.8): one octet to 127, two below 16K, then fragments of 16K, 32K,
/// 48K and 64K.
const LEN_EDGES: [usize; 17] = [0, 1, 127, 128, 255, 256, 16383, 16384, 16385, 32767, 32768,
                                49151, 49152, 65535, 65536, 65537, 81920];

impl<'a> Gen<'a> {
    #[inline]
    pub fn new(data: &'a [u8]) -> Self {
        Gen { data, bit: 0, budget: 1 << 17 }
    }

    /// `n <= 64` bits, most significant first; zeros past the end.
    #[inline]
    pub fn bits(&mut self, n: u32) -> u64 {
        let mut v = 0u64;
        for _ in 0..n {
            let byte = self.data.get(self.bit / 8).copied().unwrap_or(0);
            v = (v << 1) | ((byte >> (7 - self.bit % 8)) & 1) as u64;
            self.bit += 1;
        }
        v
    }

    #[inline]
    pub fn bool(&mut self) -> bool {
        self.bits(1) == 1
    }

    /// An `i64` whose 2's-complement length is random too, 1 to 8 octets, so
    /// that every length of an unconstrained INTEGER (X.691 11.8) is reached.
    #[inline]
    pub fn wide(&mut self) -> i64 {
        if self.edge() {
            const E: [i64; 16] = [0, -1, 1, 127, 128, -128, -129, 255, 256, 32767, 32768, -32768,
                                  -32769, i64::MAX, i64::MIN, i64::MIN + 1];
            return E[self.bits(4) as usize];
        }
        let k = 1 + self.bits(3) as u32;
        let raw = self.bits(8 * k);
        let shift = 64 - 8 * k;
        ((raw << shift) as i64) >> shift
    }

    /// A `u64` whose octet length is random too, 1 to 8, so that every
    /// length of `INTEGER (0..18446744073709551615)` in ALIGNED is reached.
    #[inline]
    pub fn uwide(&mut self) -> u64 {
        if self.edge() {
            const E: [u64; 8] = [0, 1, 255, 256, 0xffff_ffff, 0x1_0000_0000, u64::MAX - 1, u64::MAX];
            return E[self.bits(3) as usize];
        }
        let k = 1 + self.bits(3) as u32;
        self.bits(8 * k)
    }

    /// A value `>= lb` whose offset from `lb` has a random octet length
    /// (X.691 11.7).
    #[inline]
    pub fn above(&mut self, lb: i64) -> i64 {
        if self.edge() {
            const E: [i64; 8] = [0, 1, 127, 128, 255, 256, 65535, i64::MAX];
            return lb.saturating_add(E[self.bits(3) as usize]);
        }
        let k = 1 + self.bits(3) as u32;
        let raw = self.bits(8 * k);
        lb.saturating_add((raw >> 1) as i64 | (raw & 1) as i64)
    }

    /// Uniform-ish in `lo..=hi`.
    #[inline]
    pub fn range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128) as u128;
        if span == 0 {
            return lo;
        }
        if self.edge() {
            // the bounds, their neighbours, and where an ALIGNED constrained
            // whole number changes width (X.691 11.5.7): offsets 255, 256,
            // 65535, 65536
            let e: [i128; 8] = [0, 1, span as i128 - 1, span as i128, 255, 256, 65535, 65536];
            let off = e[self.bits(3) as usize].clamp(0, span as i128);
            return (lo as i128 + off) as i64;
        }
        let n = 128 - span.leading_zeros();
        let raw = self.bits(n.min(64)) as u128;
        (lo as i128 + (raw % (span + 1)) as i128) as i64
    }

    /// An index in `0..n`, `n >= 1`.
    #[inline]
    pub fn pick(&mut self, n: usize) -> usize {
        self.range(0, n as i64 - 1) as usize
    }

    /// A length in `lb..=ub`, biased short: the extra over `lb` is at most 15,
    /// so that nested lists with large bounds stay a sensible size.
    #[inline]
    ///
    /// One draw in eight is a boundary instead: `lb`, `ub`, `ub - 1`, or a
    /// length where the determinant changes form (`LEN_EDGES`), within the
    /// bounds and the budget.
    pub fn len(&mut self, lb: usize, ub: usize) -> usize {
        if self.edge() {
            let k = self.bits(5) as usize;
            let n = match k {
                0..=16 => LEN_EDGES[k],
                17..=23 => lb,
                24..=27 => ub,
                _ => ub.saturating_sub(1),
            }
            .clamp(lb, ub);
            if n - lb <= 15 || n - lb <= self.budget {
                if n - lb > 15 {
                    self.budget = 0;
                }
                return n;
            }
        }
        let extra = self.bits(4) as usize;
        lb + extra.min(ub - lb)
    }

    /// Whether to draw a boundary value: one time in eight.
    #[inline]
    fn edge(&mut self) -> bool {
        self.bits(3) == 0
    }

    /// A subidentifier: small, or at a base-128 digit boundary, or wide.
    fn subid(&mut self) -> u128 {
        match self.bits(2) {
            0 => self.bits(7) as u128,
            1 => {
                const E: [u128; 8] = [127, 128, 16383, 16384, 2097151, 2097152, u32::MAX as u128, u64::MAX as u128];
                E[self.bits(3) as usize]
            }
            2 => self.bits(32) as u128,
            _ => self.bits(64) as u128,
        }
    }

    /// The contents octets (X.690 8.19, 8.20) of an OBJECT IDENTIFIER, or
    /// with `relative` a RELATIVE-OID, of a few random arcs.
    pub fn oid(&mut self, relative: bool) -> Vec<u8> {
        let mut ids: Vec<u128> = Vec::new();
        let n = 1 + self.bits(3) as usize;
        if !relative {
            // the first two arcs, as 40 X + Y
            let x = self.range(0, 2) as u128;
            let y = if x < 2 { self.range(0, 39) as u128 } else { self.subid() };
            ids.push(40 * x + y);
        }
        for _ in ids.len()..n {
            ids.push(self.subid());
        }
        let mut out = Vec::new();
        for mut v in ids {
            let mut d = vec![(v & 0x7f) as u8];
            v >>= 7;
            while v > 0 {
                d.push(0x80 | (v & 0x7f) as u8);
                v >>= 7;
            }
            out.extend(d.iter().rev());
        }
        out
    }

    /// The CER/DER contents octets (X.690 8.5, 11.3) of a REAL: zero, a
    /// special value, a base-2 value, or now and then a base-10 one.
    pub fn real(&mut self) -> Vec<u8> {
        match self.bits(4) {
            0 => Vec::new(),
            1 => vec![0x40 + self.bits(2) as u8],
            2 => {
                // NR3: [-]M.E[-]X, M without a 0 at either end
                let neg = self.bool();
                let mut m = self.range(1, 999_999_999) as u64;
                while m % 10 == 0 {
                    m /= 10;
                }
                let x = self.range(-40, 40);
                let e = if x == 0 { "+0".to_string() } else { x.to_string() };
                let mut out = vec![3u8];
                out.extend(format!("{}{m}.E{e}", if neg { "-" } else { "" }).into_bytes());
                out
            }
            _ => {
                // a value a binary64 holds exactly and not as a subnormal,
                // which is what the references decode a REAL to: N at most
                // 53 bits, N 2^E between 2^-1022 and 2^1024. (Wider mantissas
                // and exponents are in the hand-derived vectors.)
                let neg = self.bool();
                let mut n: u64 = match self.bits(2) {
                    0 => 1,
                    1 => self.bits(8),
                    _ => self.bits(53),
                };
                if n == 0 {
                    n = 1;
                }
                // M odd (11.3.1): the trailing zeros go into the exponent
                let tz = n.trailing_zeros() as i64;
                n >>= tz;
                let w = 64 - n.leading_zeros() as i64;
                let e: i64 = if self.edge() {
                    const E: [i64; 8] = [0, -1, 127, 128, -128, -129, 255, 256];
                    E[self.bits(3) as usize]
                } else {
                    self.range(-1000, 960)
                };
                let e = (e + tz).clamp(-1022, 1024 - w);
                let eo = min_twos(e);
                let no: Vec<u8> = n.to_be_bytes().iter().copied().skip_while(|&b| b == 0).collect();
                let mut out = vec![0x80 | if neg { 0x40 } else { 0 } | (eo.len() as u8 - 1)];
                out.extend(eo);
                out.extend(no);
                out
            }
        }
    }
}

/// `e` in two's complement in the fewest octets.
fn min_twos(e: i64) -> Vec<u8> {
    let b = e.to_be_bytes();
    let mut i = 0;
    while i < 7 && ((b[i] == 0 && b[i + 1] < 0x80) || (b[i] == 0xff && b[i + 1] >= 0x80)) {
        i += 1;
    }
    b[i..].to_vec()
}
