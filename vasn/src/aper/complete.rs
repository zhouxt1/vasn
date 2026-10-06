//! The complete encoding of an outermost value (X.691 11.1).
//!
//! A format's decoder reads a value off the front of its input and leaves the
//! rest, which is what nesting needs. A message is more than that: 11.1.4
//! makes its complete encoding the field-list from bit 0, then "(zero to seven)
//! zero bits ... to produce a multiple of eight bits", and an empty field-list
//! "a single octet with all bits set to 0"; 11.1.5 says that bit string is the
//! complete encoding. It is exactly what an open type carries (11.2.1), so the
//! shape is `ot_body`'s, read at position 0.
//!
//! `complete_dec` accepts a buffer only if it is one value's complete encoding:
//! the value, then zero bits and nothing else, in the fewest octets. A non-zero
//! padding bit, or an octet more, is not an encoding of any value, and
//! accepting it would give one value several.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::aper::format::*;
use crate::aper::opentype::*;
use crate::uper::format as u;
use crate::uper::opentype as uo;

verus! {

/// 11.1.4: the field-list from position 0, padded with zero bits to whole
/// octets, one zero octet if it is empty.
pub open spec fn complete_enc<A>(e: Enc<A>, a: A) -> Seq<bool> {
    uo::ot_body(at0_enc(e), a)
}

/// `b` is exactly the complete encoding of the value decoded.
pub open spec fn complete_dec<A>(d: Dec<A>, b: Seq<bool>) -> Option<(A, Flg)> {
    match d((0, b)) {
        Some((a, k, f)) => {
            if k <= b.len() && b.len() % 8 == 0 && uo::ot_octets(k) == b.len() / 8
                && b.skip(k as int) == zeros((b.len() - k) as nat) {
                Some((a, f))
            } else {
                None
            }
        },
        None => None,
    }
}

/// The two are inverse: every value's complete encoding decodes to it, and a
/// buffer that decodes (to a value of this version) is that value's complete
/// encoding and nothing else.
pub proof fn lemma_complete<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures
        forall|a: A| w(a) ==> #[trigger] complete_dec(d, complete_enc(e, a))
            == Some::<(A, Flg)>((a, Flg::SameVer)),
        forall|b: Seq<bool>| (#[trigger] complete_dec(d, b)) is Some ==> {
            &&& w(complete_dec(d, b).unwrap().0)
            &&& complete_dec(d, b).unwrap().1 is SameVer
                ==> b == complete_enc(e, complete_dec(d, b).unwrap().0)
        },
{
    lemma_at0_format(w, e, d);
    let e0 = at0_enc(e);
    let d0 = at0_dec(d);
    assert forall|a: A| w(a) implies #[trigger] complete_dec(d, complete_enc(e, a))
        == Some::<(A, Flg)>((a, Flg::SameVer))
    by {
        let c = e0(a);
        let q = uo::ot_octets(c.len());
        let pad = (8 * q - c.len()) as nat;
        let body = complete_enc(e, a);
        uo::lemma_ot_octets(c.len());
        assert(body =~= c + zeros(pad));
        assert(body.len() == 8 * q);
        assert(body.len() % 8 == 0 && body.len() / 8 == q) by (nonlinear_arith)
            requires body.len() == 8 * q;
        assert(d0(c + zeros(pad)) == Some::<(A, nat, Flg)>((a, c.len(), Flg::SameVer)));
        assert(d((0, body)) == Some::<(A, nat, Flg)>((a, c.len(), Flg::SameVer)));
        lemma_take_add(c, zeros(pad));
        assert(body.skip(c.len() as int) =~= zeros(pad));
    }
    assert forall|b: Seq<bool>| (#[trigger] complete_dec(d, b)) is Some implies {
        &&& w(complete_dec(d, b).unwrap().0)
        &&& complete_dec(d, b).unwrap().1 is SameVer
            ==> b == complete_enc(e, complete_dec(d, b).unwrap().0)
    } by {
        assert(d0(b) == d((0, b)));
        let a = d0(b).unwrap().0;
        let k = d0(b).unwrap().1;
        assert(w(a) && k <= b.len());
        if d0(b).unwrap().2 is SameVer {
            assert(b.take(k as int) == e0(a));
            assert(b.len() == 8 * (b.len() / 8)) by (nonlinear_arith)
                requires b.len() % 8 == 0;
            assert(b =~= e0(a) + zeros((b.len() - k) as nat));
            assert(complete_enc(e, a) =~= b);
        }
    }
}

} // verus!

verus! {

use crate::aper::cursor::*;

impl<'a> BitReader<'a> {
    /// After a decoder that started at bit 0 has read a value: whether the
    /// rest of the buffer is its complete encoding's padding (11.1.4), zero
    /// bits up to the fewest octets that hold what was read, one octet if
    /// nothing was. On `true` the reader is at the end.
    #[inline]
    pub fn check_complete(&mut self) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            ok == (ot_octets(old(self).pos as nat) == old(self).buf@.len()
                && old(self).rem() == zeros(old(self).rem().len())),
    {
        // `ot_octets_eq` without its bound on the position: an octet count
        // is the whole octets plus one for a partial or an empty one
        let q = self.pos / 8;
        let octets = if self.pos == 0 || self.pos % 8 != 0 { q + 1 } else { q };
        let end = self.pos;
        if octets != self.buf.len() {
            note_bad_padding(self.buf, end, 0);
            return false;
        }
        let ok = self.check_zero_tail();
        if !ok {
            note_bad_padding(self.buf, end, 0);
        }
        ok
    }
}

} // verus!
