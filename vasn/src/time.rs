//! The forms of GeneralizedTime and UTCTime that PER sends.
//!
//! Both are VisibleStrings (X.680 46.3, 47.3), and X.691 10.6.5 encodes them
//! as such, with "the restrictions imposed on the encoding of the generalized
//! time and universal time types by Rec. ITU-T X.690 | ISO/IEC 8825-1, 11.7
//! and 11.8". Those are DER's forms:
//!
//!   * GeneralizedTime (X.690 11.7): `YYYYMMDDHHMMSS`, then optionally a `.`
//!     and a fraction of a second with no trailing zero, then `Z`: the seconds
//!     always present (11.7.2), no trailing zero and no empty fraction
//!     (11.7.3), a full stop (11.7.4), UTC (11.7.1);
//!   * UTCTime (X.690 11.8): `YYMMDDHHMMSSZ`.
//!
//! So a decoder rejects any other VisibleString in their place. The fields are
//! checked against X.680 46.2's ISO 8601 ranges -- month 01 to 12, day 01 to 31,
//! hour 00 to 23, minute 00 to 59, second 00 to 60 (a leap second) -- but not
//! against the calendar: 20240231 passes.
use vstd::prelude::*;

verus! {

pub open spec fn is_digit(c: u8) -> bool { 48 <= c <= 57 }

/// The two digits at `i`, as a number.
pub open spec fn two(s: Seq<u8>, i: int) -> int { (s[i] - 48) * 10 + (s[i + 1] - 48) }

/// Ten digits from `i`: month, day, hour, minute, second, each in range.
pub open spec fn mdhms_ok(s: Seq<u8>, i: int) -> bool {
    &&& forall|j: int| i <= j < i + 10 ==> #[trigger] is_digit(s[j])
    &&& 1 <= two(s, i) <= 12
    &&& 1 <= two(s, i + 2) <= 31
    &&& two(s, i + 4) <= 23
    &&& two(s, i + 6) <= 59
    &&& two(s, i + 8) <= 60
}

/// X.690 11.8: `YYMMDDHHMMSSZ`.
pub open spec fn utctime_ok(s: Seq<u8>) -> bool {
    &&& s.len() == 13
    &&& is_digit(s[0]) && is_digit(s[1])
    &&& mdhms_ok(s, 2)
    &&& s[12] == 90  // 'Z'
}

/// X.690 11.7: `YYYYMMDDHHMMSS[.F]Z`, `F` digits not ending in 0.
pub open spec fn gtime_ok(s: Seq<u8>) -> bool {
    &&& s.len() >= 15
    &&& forall|j: int| 0 <= j < 4 ==> #[trigger] is_digit(s[j])
    &&& mdhms_ok(s, 4)
    &&& s[s.len() - 1] == 90  // 'Z'
    &&& (s.len() == 15 || {
        &&& s.len() >= 17
        &&& s[14] == 46  // '.'
        &&& (forall|j: int| 15 <= j < s.len() - 1 ==> #[trigger] is_digit(s[j]))
        &&& s[s.len() - 2] != 48  // no trailing '0'
    })
}

/// Whether `s[lo..hi]` is all digits.
fn digits(s: &[u8], lo: usize, hi: usize) -> (ok: bool)
    requires lo <= hi <= s@.len(),
    ensures ok == (forall|j: int| lo <= j < hi ==> #[trigger] is_digit(s@[j])),
{
    let mut i = lo;
    while i < hi
        invariant lo <= i <= hi <= s@.len(), forall|j: int| lo <= j < i ==> #[trigger] is_digit(s@[j]),
        decreases hi - i,
    {
        if !(48 <= s[i] && s[i] <= 57) {
            assert(!is_digit(s@[i as int]));
            return false;
        }
        i += 1;
    }
    true
}

fn mdhms(s: &[u8], i: usize) -> (ok: bool)
    requires i + 10 <= s@.len(),
    ensures ok == mdhms_ok(s@, i as int),
{
    if !digits(s, i, i + 10) {
        return false;
    }
    let t = |k: usize| -> (r: u32)
        requires k + 1 < s@.len(), is_digit(s@[k as int]), is_digit(s@[k as int + 1]),
        ensures r == two(s@, k as int),
    { (s[k] - 48) as u32 * 10 + (s[k + 1] - 48) as u32 };
    proof {
        assert(is_digit(s@[i as int])); assert(is_digit(s@[i as int + 1]));
        assert(is_digit(s@[i as int + 2])); assert(is_digit(s@[i as int + 3]));
        assert(is_digit(s@[i as int + 4])); assert(is_digit(s@[i as int + 5]));
        assert(is_digit(s@[i as int + 6])); assert(is_digit(s@[i as int + 7]));
        assert(is_digit(s@[i as int + 8])); assert(is_digit(s@[i as int + 9]));
    }
    let mo = t(i);
    let d = t(i + 2);
    let h = t(i + 4);
    let mi = t(i + 6);
    let se = t(i + 8);
    1 <= mo && mo <= 12 && 1 <= d && d <= 31 && h <= 23 && mi <= 59 && se <= 60
}

/// Refines `utctime_ok`.
pub fn utctime_check(s: &[u8]) -> (ok: bool)
    ensures ok == utctime_ok(s@),
{
    s.len() == 13 && 48 <= s[0] && s[0] <= 57 && 48 <= s[1] && s[1] <= 57 && mdhms(s, 2) && s[12] == 90
}

/// Refines `gtime_ok`.
pub fn gtime_check(s: &[u8]) -> (ok: bool)
    ensures ok == gtime_ok(s@),
{
    let n = s.len();
    if n < 15 || !digits(s, 0, 4) || !mdhms(s, 4) || s[n - 1] != 90 {
        return false;
    }
    if n == 15 {
        return true;
    }
    n >= 17 && s[14] == 46 && digits(s, 15, n - 1) && s[n - 2] != 48
}

} // verus!
