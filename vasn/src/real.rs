//! REAL contents in the form CER and DER allow (X.690 8.5, 11.3).
//!
//! X.691 15.2 encodes a REAL as "the contents octets of the CER/DER encoding"
//! behind a length, and 15.1 keeps the base: a base-2 value is sent in binary,
//! a base-10 one in decimal. The octets are the value's, as for an OBJECT
//! IDENTIFIER (`oid`): in the CER/DER form every value has one encoding, so
//! the octets in that form stand for the value, and `real_ok` says which
//! octets are in it:
//!
//!   * none: plus zero (8.5.2);
//!   * one, 40 to 43: PLUS-INFINITY, MINUS-INFINITY, NOT-A-NUMBER, minus zero
//!     (8.5.9);
//!   * binary (8.5.7, 11.3.1): a first octet `1 S 00 00 FF`, base 2 and the
//!     scaling factor 0; the exponent in two's complement in the fewest
//!     octets, one to three of them in the short forms (FF = 0, 1, 2), and the
//!     long form (FF = 3, a count octet first) only for four or more; then N,
//!     unsigned, in the fewest octets, and odd, so that the mantissa is (11.3.1:
//!     "M is either 0 or is odd");
//!   * decimal (8.5.8, 11.3.2): a first octet 03 (NR3), then `[-]M.E` and the
//!     exponent: `M` digits neither beginning nor ending with 0 (11.3.2.4),
//!     and the exponent `+0` or a `-` or nothing and digits not beginning with
//!     0 (11.3.2.6).
//!
//! The long form for an exponent of one to three octets would represent E in
//! as few octets as the short form does, and 11.3.1 does not rule it out in
//! words; it is rejected here so that the form is unique, as the rest of 11.3
//! intends.
use vstd::prelude::*;

verus! {

pub open spec fn dig(c: u8) -> bool { 48 <= c <= 57 }

/// Where the exponent's octets begin and how many there are, for a binary
/// encoding's first octet `s[0]` (8.5.7.4).
pub open spec fn exp_at(s: Seq<u8>) -> (int, int) {
    if s[0] % 4 < 3 { (1, (s[0] % 4) + 1) } else { (2, s[1] as int) }
}

pub open spec fn binary_ok(s: Seq<u8>) -> bool {
    &&& s.len() >= 1
    // bit 8 set, bits 6 to 3 clear: base 2 (8.5.7.2), F = 0 (11.3.1)
    &&& (s[0] == 0x80 || s[0] == 0x81 || s[0] == 0x82 || s[0] == 0x83
         || s[0] == 0xc0 || s[0] == 0xc1 || s[0] == 0xc2 || s[0] == 0xc3)
    &&& (s[0] % 4 == 3 ==> s.len() >= 2 && s[1] >= 4)
    &&& {
        let (e, ne) = exp_at(s);
        &&& e + ne < s.len()
        // the exponent in the fewest octets: the first nine bits not all
        // equal (8.5.7.4 d, 11.3.1)
        &&& (ne >= 2 ==> !(s[e] == 0 && s[e + 1] < 128) && !(s[e] == 255 && s[e + 1] >= 128))
        // N: no leading zero octet, and odd
        &&& s[e + ne] != 0
        &&& s[s.len() - 1] % 2 == 1
    }
}

/// `t`, the octets after the first, from `m` (past a sign) on: digits from
/// `m` to `p` with no 0 at either end, then `.E`, then the exponent.
pub open spec fn nr3_at(t: Seq<u8>, m: int, p: int) -> bool {
    &&& m < p && p + 2 <= t.len()
    &&& forall|j: int| m <= j < p ==> #[trigger] dig(t[j])
    &&& t[m] != 48 && t[p - 1] != 48
    &&& t[p] == 46 && t[p + 1] == 69  // '.', 'E'
    &&& {
        let r = t.subrange(p + 2, t.len() as int);
        ||| r == seq![43u8, 48u8]  // "+0"
        ||| {
            let k: int = if r.len() >= 1 && r[0] == 45 { 1 } else { 0 };  // '-'
            &&& r.len() > k
            &&& r[k] != 48
            &&& forall|j: int| k <= j < r.len() ==> #[trigger] dig(r[j])
        }
    }
}

/// The octets after the first, and where the mantissa's digits begin.
pub open spec fn nr3_t(s: Seq<u8>) -> Seq<u8> { s.subrange(1, s.len() as int) }
pub open spec fn nr3_m(t: Seq<u8>) -> int { if t.len() >= 1 && t[0] == 45 { 1 } else { 0 } }

pub open spec fn decimal_ok(s: Seq<u8>) -> bool {
    &&& s.len() >= 1 && s[0] == 3
    &&& exists|p: int| nr3_at(nr3_t(s), nr3_m(nr3_t(s)), p)
}

pub open spec fn real_ok(s: Seq<u8>) -> bool {
    ||| s.len() == 0
    ||| (s.len() == 1 && 0x40 <= s[0] <= 0x43)
    ||| binary_ok(s)
    ||| decimal_ok(s)
}

fn all_digits(s: &[u8], lo: usize, hi: usize) -> (ok: bool)
    requires lo <= hi <= s@.len(),
    ensures ok == (forall|j: int| lo <= j < hi ==> #[trigger] dig(s@[j])),
{
    let mut i = lo;
    while i < hi
        invariant lo <= i <= hi <= s@.len(), forall|j: int| lo <= j < i ==> #[trigger] dig(s@[j]),
        decreases hi - i,
    {
        if !(48 <= s[i] && s[i] <= 57) {
            assert(!dig(s@[i as int]));
            return false;
        }
        i += 1;
    }
    true
}

fn binary_check(s: &[u8]) -> (ok: bool)
    requires s@.len() >= 1,
    ensures ok == binary_ok(s@),
{
    let n = s.len();
    let b = s[0];
    if !(b == 0x80 || b == 0x81 || b == 0x82 || b == 0x83 || b == 0xc0 || b == 0xc1 || b == 0xc2 || b == 0xc3) {
        return false;
    }
    let (e, ne): (usize, usize) = if b % 4 < 3 {
        (1, (b % 4) as usize + 1)
    } else {
        if n < 2 || s[1] < 4 {
            return false;
        }
        (2, s[1] as usize)
    };
    assert(exp_at(s@) == (e as int, ne as int));
    if e + ne >= n {
        return false;
    }
    if ne >= 2 && ((s[e] == 0 && s[e + 1] < 128) || (s[e] == 255 && s[e + 1] >= 128)) {
        return false;
    }
    s[e + ne] != 0 && s[n - 1] % 2 == 1
}

fn decimal_check(s: &[u8]) -> (ok: bool)
    requires s@.len() >= 1,
    ensures ok == decimal_ok(s@),
{
    let n = s.len();
    if s[0] != 3 {
        return false;
    }
    // `t` is the octets after the first: t[j] is s[j + 1], and the
    // positions below (m, p) are t's
    let ghost t = nr3_t(s@);
    assert(forall|j: int| 0 <= j < t.len() ==> t[j] == s@[j + 1]);
    let m: usize = if n >= 2 && s[1] == 45 { 1 } else { 0 };
    assert(m == nr3_m(t));
    // the mantissa's digits, up to the first octet that is not one
    let mut i: usize = m;
    while i + 1 < n && 48 <= s[i + 1] && s[i + 1] <= 57
        invariant m <= i, i + 1 <= n, n >= 1, n == s@.len(), t == nr3_t(s@), m == nr3_m(t),
            forall|j: int| m <= j < i ==> #[trigger] dig(t[j]),
        decreases n - i,
    {
        assert(dig(t[i as int]));
        i += 1;
    }
    let p = i;
    // no other position can be the '.': every octet before `p` is a digit,
    // and the one at `p` is not
    assert forall|q: int| nr3_at(t, m as int, q) implies q == p by {
        if q < p { assert(dig(t[q])); assert(t[q] != 46); }
        if q > p { assert(dig(t[p as int])); }
    }
    if !(m < p && n - p >= 3) {
        return false;
    }
    if s[m + 1] == 48 || s[p] == 48 || s[p + 1] != 46 || s[p + 2] != 69 {
        return false;
    }
    let ghost r = t.subrange(p + 2, t.len() as int);
    let rs = p + 3;  // where r begins in s
    assert(forall|j: int| 0 <= j < r.len() ==> r[j] == s@[rs + j]);
    let rl = n - rs;
    assert(r.len() == rl);
    if rl == 2 && s[rs] == 43 && s[rs + 1] == 48 {
        assert(r =~= seq![43u8, 48u8]);
        assert(nr3_at(t, m as int, p as int));
        assert(decimal_ok(s@));
        return true;
    }
    assert(r != seq![43u8, 48u8]) by {
        if r == seq![43u8, 48u8] { assert(r[0] == 43 && r[1] == 48); }
    }
    let k: usize = if rl >= 1 && s[rs] == 45 { 1 } else { 0 };
    assert(k == (if r.len() >= 1 && r[0] == 45 { 1int } else { 0int }));
    if !(rl > k) || s[rs + k] == 48 {
        return false;
    }
    let ok = all_digits(s, rs + k, n);
    proof {
        if ok {
            assert forall|j: int| k <= j < r.len() implies #[trigger] dig(r[j]) by { assert(dig(s@[rs + j])); }
            assert(nr3_at(t, m as int, p as int));
            assert(decimal_ok(s@));
        } else {
            assert(exists|j: int| rs + k <= j < n && !#[trigger] dig(s@[j]));
            let j0 = choose|j: int| rs + k <= j < n && !#[trigger] dig(s@[j]);
            assert(!dig(r[j0 - rs]));
            assert(!nr3_at(t, m as int, p as int));
        }
    }
    ok
}

/// Refines `real_ok`.
pub fn real_check(s: &[u8]) -> (ok: bool)
    ensures ok == real_ok(s@),
{
    let n = s.len();
    if n == 0 {
        return true;
    }
    if n == 1 && 0x40 <= s[0] && s[0] <= 0x43 {
        return true;
    }
    let b = binary_check(s);
    let d = decimal_check(s);
    proof {
        // a binary first octet is 80 or above, a decimal one 03, a special
        // 40 to 43: at most one reading applies
    }
    b || d
}

} // verus!
