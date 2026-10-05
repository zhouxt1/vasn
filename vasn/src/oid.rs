//! OBJECT IDENTIFIER and RELATIVE-OID contents (X.690 8.19, 8.20).
//!
//! X.691 24 and 25 encode either as the contents octets of its BER encoding,
//! behind a length. Those octets are a series of subidentifiers, each a number
//! in base 128, most significant digit first, every octet but a
//! subidentifier's last with bit 8 set (X.690 8.19.2). The digits are the
//! fewest: "the leading octet of the subidentifier shall not have the value
//! 80 (hexadecimal)". So a sequence of octets is the contents of exactly one
//! value when
//!
//!   * it is not empty (an OBJECT IDENTIFIER has at least two arcs, one
//!     subidentifier, X.690 8.19.4; a RELATIVE-OID at least one arc, X.680
//!     33.3),
//!   * its last octet ends a subidentifier (bit 8 clear), and
//!   * no subidentifier begins with 80.
//!
//! That is `oid_ok`, and the decoded value is those octets: between them and
//! the arcs is a bijection, so the octets stand for the value, as a
//! UTF8String's octets do for its characters. The JER printer turns them into
//! arcs (`jer::jer_oid`). For an OBJECT IDENTIFIER any first subidentifier is
//! some pair of first arcs (X.690 8.19.4: X is 0, 1 or 2, Y below 40 unless X
//! is 2), so nothing further is checked.
use vstd::prelude::*;

verus! {

pub open spec fn oid_ok(s: Seq<u8>) -> bool {
    &&& s.len() >= 1
    &&& s[s.len() - 1] < 128
    &&& forall|i: int| 0 <= i < s.len() && (i == 0 || s[i - 1] < 128) ==> #[trigger] s[i] != 128
}

/// Refines `oid_ok`.
pub fn oid_check(s: &[u8]) -> (ok: bool)
    ensures ok == oid_ok(s@),
{
    let n = s.len();
    if n == 0 || s[n - 1] >= 128 {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == s@.len(), i <= n,
            forall|j: int| 0 <= j < i && (j == 0 || s@[j - 1] < 128) ==> #[trigger] s@[j] != 128,
        decreases n - i,
    {
        if (i == 0 || s[i - 1] < 128) && s[i] == 128 {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
