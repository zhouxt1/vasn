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
}

impl<'a> Gen<'a> {
    #[inline]
    pub fn new(data: &'a [u8]) -> Self {
        Gen { data, bit: 0 }
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
        let k = 1 + self.bits(3) as u32;
        let raw = self.bits(8 * k);
        let shift = 64 - 8 * k;
        ((raw << shift) as i64) >> shift
    }

    /// A value `>= lb` whose offset from `lb` has a random octet length
    /// (X.691 11.7).
    #[inline]
    pub fn above(&mut self, lb: i64) -> i64 {
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
    pub fn len(&mut self, lb: usize, ub: usize) -> usize {
        let extra = self.bits(4) as usize;
        lb + extra.min(ub - lb)
    }
}
