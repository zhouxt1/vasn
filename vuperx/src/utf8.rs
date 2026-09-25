//! Well-formed UTF-8 (RFC 3629; Unicode 15, Table 3-7), for UTF8String.
//!
//! X.691 30.6 encodes a UTF8String as its octets, from X.690 8.23.5, with a
//! length in octets. Octets that are not UTF-8 are the encoding of no string at
//! all, so an injective decoder has to reject them: the UTF8String format is an
//! OCTET STRING restricted to `utf8_ok`. Overlong forms, surrogates and code
//! points above U+10FFFF are all ill-formed, which is what keeps one string to
//! one octet sequence. `utf8_ok` itself is checked against Rust's
//! `std::str::from_utf8` on every sequence of 1 to 4 octets
//! (`vuperx/tests/utf8_exhaustive.rs`).
use vstd::prelude::*;

verus! {

pub open spec fn in_range(b: u8, lo: u8, hi: u8) -> bool { lo <= b && b <= hi }

/// The octets of one well-formed character starting at `i`, or 0 if none.
pub open spec fn utf8_char_len(s: Seq<u8>, i: int) -> nat {
    let n = s.len() as int;
    let b0 = s[i];
    let cont = |j: int| i + j < n && in_range(s[i + j], 0x80, 0xBF);
    if b0 <= 0x7F {
        1
    } else if in_range(b0, 0xC2, 0xDF) {
        if cont(1) { 2 } else { 0 }
    } else if b0 == 0xE0 {
        if i + 1 < n && in_range(s[i + 1], 0xA0, 0xBF) && cont(2) { 3 } else { 0 }
    } else if in_range(b0, 0xE1, 0xEC) || in_range(b0, 0xEE, 0xEF) {
        if cont(1) && cont(2) { 3 } else { 0 }
    } else if b0 == 0xED {
        if i + 1 < n && in_range(s[i + 1], 0x80, 0x9F) && cont(2) { 3 } else { 0 }
    } else if b0 == 0xF0 {
        if i + 1 < n && in_range(s[i + 1], 0x90, 0xBF) && cont(2) && cont(3) { 4 } else { 0 }
    } else if in_range(b0, 0xF1, 0xF3) {
        if cont(1) && cont(2) && cont(3) { 4 } else { 0 }
    } else if b0 == 0xF4 {
        if i + 1 < n && in_range(s[i + 1], 0x80, 0x8F) && cont(2) && cont(3) { 4 } else { 0 }
    } else {
        0
    }
}

/// `s[i..]` is a sequence of well-formed characters.
pub open spec fn utf8_from(s: Seq<u8>, i: int) -> bool
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        i == s.len()
    } else {
        let k = utf8_char_len(s, i);
        k > 0 && utf8_from(s, i + k)
    }
}

pub open spec fn utf8_ok(s: Seq<u8>) -> bool { utf8_from(s, 0) }

/// Refines `utf8_char_len`.
pub fn utf8_char_len_x(s: &[u8], i: usize) -> (k: usize)
    requires i < s@.len(),
    ensures k as nat == utf8_char_len(s@, i as int),
{
    let n = s.len();
    let b0 = s[i];
    let cont = |j: usize| -> (r: bool)
        requires j <= 3,
        ensures r == (i + j < n && in_range(s@[i + j], 0x80, 0xBF)),
        { j < n - i && 0x80 <= s[i + j] && s[i + j] <= 0xBF };
    if b0 <= 0x7F {
        1
    } else if 0xC2 <= b0 && b0 <= 0xDF {
        if cont(1) { 2 } else { 0 }
    } else if b0 == 0xE0 {
        if 1 < n - i && 0xA0 <= s[i + 1] && s[i + 1] <= 0xBF && cont(2) { 3 } else { 0 }
    } else if (0xE1 <= b0 && b0 <= 0xEC) || (0xEE <= b0 && b0 <= 0xEF) {
        if cont(1) && cont(2) { 3 } else { 0 }
    } else if b0 == 0xED {
        if 1 < n - i && 0x80 <= s[i + 1] && s[i + 1] <= 0x9F && cont(2) { 3 } else { 0 }
    } else if b0 == 0xF0 {
        if 1 < n - i && 0x90 <= s[i + 1] && s[i + 1] <= 0xBF && cont(2) && cont(3) { 4 } else { 0 }
    } else if 0xF1 <= b0 && b0 <= 0xF3 {
        if cont(1) && cont(2) && cont(3) { 4 } else { 0 }
    } else if b0 == 0xF4 {
        if 1 < n - i && 0x80 <= s[i + 1] && s[i + 1] <= 0x8F && cont(2) && cont(3) { 4 } else { 0 }
    } else {
        0
    }
}

/// Refines `utf8_ok`.
pub fn utf8_check(s: &[u8]) -> (ok: bool)
    ensures ok == utf8_ok(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            utf8_ok(s@) == utf8_from(s@, i as int),
        decreases s@.len() - i,
    {
        let k = utf8_char_len_x(s, i);
        if k == 0 {
            return false;
        }
        assert(utf8_char_len(s@, i as int) <= 4);
        if i + k > s.len() {
            // a character's octets are all inside `s`, so this cannot happen
            assert(false);
            return false;
        }
        i = i + k;
    }
    true
}

} // verus!
