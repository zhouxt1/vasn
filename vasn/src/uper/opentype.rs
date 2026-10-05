//! Open types (X.691 11.2).
//!
//! An extension addition is carried as an *open type*: its encoding is padded
//! with zero bits up to a whole number of octets, and that octet count is
//! written in front of it as an unconstrained length determinant (11.2.2). A
//! decoder that does not know the addition can therefore step over it knowing
//! only its length.
//!
//! Note what UPER does **not** do here: there is no octet *alignment*. The
//! padding is relative to the start of the content, not to an absolute
//! position in the message, so an open type nested at bit 123 is padded from
//! bit 123. That is why this needs no notion of absolute position and stays a
//! function of the remaining bits alone. (Aligned PER is where real alignment
//! enters, and it is out of scope here.)
//!
//! The length goes through `frag`, so content of any size works -- 11.2.2's
//! note is explicit that a large open type fragments. That is what removes the
//! size hypothesis this lemma used to carry, and it is the one place this
//! library covers more than VUPER, whose `Term/LengthDet.v` stops at 16K.
//!
//! Two checks make it canonical, and both come from VUPER's `open_typ_parse`:
//! the content must occupy exactly the octets the determinant claims -- not
//! fewer, so a padded-out encoding is rejected -- and the padding bits must be
//! zero.
use vstd::prelude::*;
use crate::uper::format::*;
use crate::uper::bound::*;
use crate::uper::frag::*;

verus! {

/// Octets needed to hold `k` bits.
pub open spec fn byte_len(k: nat) -> nat { (k + 7) / 8 }

/// Octets an open type's *content* occupies -- which is not `byte_len`.
///
/// X.691 11.1.3.1: "If the result of encoding the outermost value is an empty
/// bit string, the bit string shall be replaced with a single octet with all
/// bits set to 0." An open type's content is an outermost value (11.1.1 c), so
/// a type that encodes to no bits at all -- NULL, `ENUMERATED { x }`, an empty
/// SEQUENCE, all common in 3GPP -- still occupies one octet and the length
/// determinant reads 1, never 0.
///
/// VUPER gets this wrong: `open_typ_serialize` writes `get_byte_len n`, and
/// `get_byte_len 0` is 0. Checked against pycrate, which writes the octet.
pub open spec fn ot_octets(k: nat) -> nat { if k == 0 { 1 } else { (k + 7) / 8 } }

pub open spec fn zeros(n: nat) -> Seq<bool> { Seq::new(n, |i: int| false) }

/// The content as it goes on the wire: the value's encoding, zero-padded out
/// to a whole number of octets.
pub open spec fn ot_body<A>(e: Enc<A>, a: A) -> Seq<bool> {
    e(a) + zeros((8 * ot_octets(e(a).len()) - e(a).len()) as nat)
}

#[verifier::opaque]
pub open spec fn open_enc<A>(e: Enc<A>) -> Enc<A> {
    |a: A| frag_enc()(ot_body(e, a))
}

#[verifier::opaque]
pub open spec fn open_dec<A>(d: Dec<A>) -> Dec<A> {
    |b: Seq<bool>|
        match frag_dec()(b) {
            Some((c, k, _)) => match d(c) {
                Some((a, k2, f)) => {
                    if k2 <= c.len() && ot_octets(k2) == c.len() / 8
                        && c.skip(k2 as int) == zeros((c.len() - k2) as nat) {
                        Some((a, k, f))
                    } else {
                        None
                    }
                },
                None => None,
            },
            None => None,
        }
}

pub proof fn lemma_ot_octets(k: nat)
    ensures 8 * ot_octets(k) >= k, ot_octets(k) >= 1, ot_octets(k) <= byte_len(k) + 1,
{
}

/// Monotone, which is what turns a bound on the content into a bound on the
/// open type.
pub proof fn lemma_ot_octets_mono(k: nat, m: nat)
    requires k <= m,
    ensures ot_octets(k) <= ot_octets(m),
{
}

/// Padding a value out to whole octets and prefixing its length yields a
/// format over the *same* values -- the open type changes the bits, not the
/// value type or its well-formedness.
///
/// There is no size hypothesis. `frag` fragments a long determinant per
/// 11.9.3.8, so the content may be any length; VUPER needs
/// `get_byte_len a' < 2^14` here and has nothing to discharge it with.
pub proof fn lemma_open_format<A>(w: Wf<A>, e: Enc<A>, d: Dec<A>)
    requires is_format(w, e, d),
    ensures is_format(w, open_enc(e), open_dec(d)),
{
    reveal(open_enc); reveal(open_dec);
    reveal(frag_wf);
    lemma_frag_format();
    let oe = open_enc(e);
    let od = open_dec(d);

    assert forall|a: A, rest: Seq<bool>| w(a) implies
        #[trigger] od(oe(a) + rest) == Some::<(A, nat, Flg)>((a, oe(a).len(), Flg::SameVer))
    by {
        let c = e(a);
        let q = ot_octets(c.len());
        let pad = (8 * q - c.len()) as nat;
        let body = ot_body(e, a);
        lemma_ot_octets(c.len());
        assert(body.len() == 8 * q);
        assert(body.len() % 8 == 0) by (nonlinear_arith)
            requires body.len() == 8 * q;
        {}
        assert(frag_wf()(body));
        assert(frag_dec()(frag_enc()(body) + rest)
               == Some::<(Seq<bool>, nat, Flg)>((body, frag_enc()(body).len(), Flg::SameVer)));
        // the inner value decodes out of the padded content, with the padding
        // standing in for the usual arbitrary tail
        assert(body =~= c + zeros(pad));
        assert(d(body) == Some::<(A, nat, Flg)>((a, c.len(), Flg::SameVer)));
        assert(body.len() / 8 == q) by (nonlinear_arith)
            requires body.len() == 8 * q;
        {}
        lemma_take_add(c, zeros(pad));
        assert(body.skip(c.len() as int) =~= zeros(pad));
        assert(body.len() - c.len() == pad);
    }

    assert forall|b: Seq<bool>| (#[trigger] od(b)).is_some() implies {
        let a = od(b).unwrap().0;
        let k = od(b).unwrap().1;
        &&& w(a) && k <= b.len()
        &&& od(b).unwrap().2 is SameVer ==> b.take(k as int) == oe(a)
    } by {
        let c = frag_dec()(b).unwrap().0;
        let k = frag_dec()(b).unwrap().1;
        let a = d(c).unwrap().0;
        let k2 = d(c).unwrap().1;
        assert(w(a));
        if od(b).unwrap().2 is SameVer {
            // `frag` is never anything but SameVer, so the flag came from the
            // content, and both halves are pinned
            lemma_frag_dec_same(b);
            assert(b.take(k as int) == frag_enc()(c));
            assert(c.take(k2 as int) == e(a));
            assert(k2 == e(a).len());
            assert(c.len() % 8 == 0);
            assert(c.len() == 8 * (c.len() / 8)) by (nonlinear_arith)
                requires c.len() % 8 == 0;
            {}
            assert(c.len() == 8 * ot_octets(k2));
            assert(c =~= e(a) + zeros((c.len() - k2) as nat));
            assert(ot_body(e, a) =~= c);
        }
    }
}

/// Content under 16K octets is one fragment: the determinant plus the padded
/// body. Larger content fragments, so it has no bound of this shape -- which is
/// the point.
pub proof fn lemma_open_bound<A>(w: Wf<A>, e: Enc<A>, m: nat)
    requires enc_bound(w, e, m), ot_octets(m) < 16384,
    ensures enc_bound(w, open_enc(e), (16 + 8 * ot_octets(m)) as nat),
{
    reveal(open_enc);
    assert forall|a: A| w(a) implies #[trigger] open_enc(e)(a).len() <= 16 + 8 * ot_octets(m) by {
        let c = e(a);
        let q = ot_octets(c.len());
        let body = ot_body(e, a);
        lemma_ot_octets(c.len());
        lemma_ot_octets_mono(c.len(), m);
        assert(body.len() == 8 * q);
        assert(body.len() / 8 == q) by (nonlinear_arith)
            requires body.len() == 8 * q;
        {}
        let h = LenHead::Final(q as u64);
        lemma_lh_wf_iff(h);
        lemma_lh_enc_len_bounds(h);
        reveal(frag_enc);
        assert(frag_enc()(body) =~= lh_enc()(h) + body);
    }
}

} // verus!

verus! {

use crate::uper::cursor::*;
use crate::uper::term::*;
use crate::uper::prim::*;
use crate::bits::bitspec::*;

broadcast use {crate::uper::format::format_steps, crate::uper::prim::map_steps};

pub proof fn lemma_bool_enc_false()
    ensures bool_enc()(false) =~= zeros(1),
{
    reveal(map_enc);
    lemma_bool_enc_len(false);
    assert(bool_enc()(false)[0] == false) by {
        reveal_with_fuel(crate::bits::bitspec::p2, 3);
    }
}

pub proof fn lemma_zeros_add(a: nat, b: nat)
    ensures zeros(a) + zeros(b) =~= zeros((a + b) as nat),
{
}

impl BitWriter {
    /// Pad out to the next octet boundary with zero bits.
    ///
    /// 11.1.3.1 and 11.2: an open type's content occupies a whole number of
    /// octets, padded at the end. The padding is relative to where the content
    /// started, not to an absolute position in the message -- UPER has no
    /// alignment -- which is why this is stated on the writer's own `pos`.
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn pad_to_octet(&mut self) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> {
                &&& final(self).pos % 8 == 0
                &&& final(self).pos == old(self).pos + (8 - old(self).pos % 8) % 8
                &&& final(self).written()
                    =~= old(self).written() + zeros(((8 - old(self).pos % 8) % 8) as nat)
            },
    {
        proof { lemma_bool_enc_false(); }
        let ghost w0 = *self;
        let i0: usize = self.pos % 8;
        if i0 == 0 {
            assert(w0.written() + zeros(0) =~= w0.written());
            return true;
        }
        let mut i: usize = i0;
        while i < 8
            invariant
                self.wf(),
                self.buf@.len() == w0.buf@.len(),
                i0 == w0.pos % 8,
                1 <= i0 < 8,
                i0 <= i <= 8,
                self.pos == w0.pos + (i - i0),
                self.written() =~= w0.written() + zeros((i - i0) as nat),
            decreases 8 - i,
        {
            let ghost before = self.written();
            if !self.write_bool(false) { return false; }
            proof { lemma_zeros_add((i - i0) as nat, 1); }
            i = i + 1;
        }
        assert(self.pos % 8 == 0) by (nonlinear_arith)
            requires self.pos == w0.pos + (8 - i0), i0 == w0.pos % 8, 1 <= i0 < 8;
        true
    }

    /// Pad a freshly written open-type body out to `ot_body`'s shape: whole
    /// octets, and -- 11.1.3.1 -- one zero octet when nothing was written at
    /// all, where `pad_to_octet` would add nothing. A caller whose proof can
    /// see that the content is non-empty never notices the difference; one
    /// that cannot -- a `[[ ]]` group holding a list, whose length is hidden
    /// behind the list's determinant -- needs this.
    #[inline]
    pub fn pad_open(&mut self) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written()
                + zeros((8 * ot_octets(old(self).pos as nat) - old(self).pos) as nat),
    {
        let ghost w0 = *self;
        if self.pos == 0 {
            proof { lemma_bool_enc_false(); }
            if !self.write_bool(false) { return false; }
            proof { assert(self.written().len() == 1); }
            if !self.pad_to_octet() { return false; }
            proof { lemma_zeros_add(1, 7); }
            return true;
        }
        if !self.pad_to_octet() { return false; }
        proof {
            let p = w0.pos as nat;
            assert(8 * ((p + 7) / 8) - p == (8 - p % 8) % 8) by (nonlinear_arith)
                requires p > 0;
        }
        true
    }

    /// Write a value already encoded into `src` as an open type: the octet
    /// count as a fragmenting length determinant, then the padded content.
    ///
    /// The caller encodes into a scratch writer and pads it, which is what
    /// `bits_of(src@).take(nbits) == ot_body(e, a)` says. Encoding first and
    /// measuring after is forced by the format: the length comes before the
    /// content on the wire but is not known until the content exists.
    #[inline]
    pub fn write_open<A>(&mut self, src: &[u8], nbits: usize,
                         Ghost(e): Ghost<Enc<A>>, Ghost(a): Ghost<A>) -> (ok: bool)
        requires
            old(self).wf(),
            8 * src@.len() <= usize::MAX,
            nbits <= 8 * src@.len(),
            bits_of(src@).take(nbits as int) == ot_body(e, a),
        ensures
            final(self).wf(),
            final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + open_enc(e)(a),
    {
        proof {
            reveal(open_enc);
            lemma_ot_octets(e(a).len());
            assert(ot_body(e, a).len() == 8 * ot_octets(e(a).len()));
            assert(nbits % 8 == 0) by (nonlinear_arith)
                requires nbits == 8 * ot_octets(e(a).len());
            assert(bits_of(src@).skip(0).take(nbits as int) =~= bits_of(src@).take(nbits as int));
            reveal(frag_enc);
        }
        self.write_frag(src, 0, nbits)
    }
}

/// `ot_octets(k) == octets`, as a runtime check. The odd case is `k == 0`:
/// 11.1.3.1 makes an empty encoding one zero octet, not none.
#[inline]
pub fn ot_octets_eq(k: usize, octets: usize) -> (res: bool)
    requires k <= usize::MAX - 7,
    ensures res == (ot_octets(k as nat) == octets as nat),
{
    if k == 0 { octets == 1 } else { (k + 7) / 8 == octets }
}

impl<'a> BitReader<'a> {
    /// Check that everything left is zero, and consume it.
    ///
    /// The open type's padding has to be zero for the encoding to be
    /// canonical: without the check a decoder would accept any bits there and
    /// two encodings would decode to one value.
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn check_zero_tail(&mut self) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf == old(self).buf,
            ok ==> old(self).rem() =~= zeros(old(self).rem().len()),
            // the negative direction is the one a decoder needs: rejecting
            // non-zero padding is what makes the encoding canonical, so the
            // caller has to be able to say *why* it rejected
            !ok ==> old(self).rem() != zeros(old(self).rem().len()),
    {
        let ghost r0 = *self;
        loop
            invariant
                self.wf(),
                self.buf == r0.buf,
                r0.pos <= self.pos,
                self.rem() == r0.rem().skip((self.pos - r0.pos) as int),
                forall|i: int| 0 <= i < self.pos - r0.pos ==> !r0.rem()[i],
            decreases 8 * self.buf@.len() - self.pos,
        {
            if self.pos == self.buf.len() * 8 {
                assert(self.rem().len() == 0);
                assert(r0.rem().len() == self.pos - r0.pos);
                return true;
            }
            let ghost p = self.pos;
            let ghost remp = self.rem();
            proof { lemma_bool_dec_bit(remp); }
            match self.read_bool() {
                Some(b) => {
                    proof { assert(r0.rem()[(p - r0.pos) as int] == remp[0]); }
                    if b {
                        assert(zeros(r0.rem().len())[(p - r0.pos) as int] == false);
                        return false;
                    }
                },
                None => {
                    // unreachable: the bit was there, we just checked
                    proof {
                        reveal(crate::uper::prim::map_dec);
                        assert(self.rem().len() >= 1);
                    }
                    return false;
                },
            }
        }
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------- step lemmas
//
// `open_enc`/`open_dec` are opaque, so generated code cannot see through them
// by unfolding -- the same discipline as the composition combinators. These
// are the four shapes a generated open-type decode can end in, each one
// reveal, so an addition costs the solver O(1) however many additions the
// SEQUENCE has.

pub proof fn lemma_open_dec_some<A>(d: Dec<A>, b: Seq<bool>, c: Seq<bool>, k: nat,
                                    a: A, k2: nat, f: Flg)
    requires
        frag_dec()(b) == Some::<(Seq<bool>, nat, Flg)>((c, k, Flg::SameVer)),
        d(c) == Some::<(A, nat, Flg)>((a, k2, f)),
        k2 <= c.len(),
        ot_octets(k2) == c.len() / 8,
        c.skip(k2 as int) == zeros((c.len() - k2) as nat),
    ensures open_dec(d)(b) == Some::<(A, nat, Flg)>((a, k, f)),
{
    reveal(open_dec);
}

/// The length determinant itself did not parse.
pub proof fn lemma_open_dec_none_len<A>(d: Dec<A>, b: Seq<bool>)
    requires frag_dec()(b) is None,
    ensures open_dec(d)(b) is None,
{
    reveal(open_dec);
}

/// The content did not parse.
pub proof fn lemma_open_dec_none_content<A>(d: Dec<A>, b: Seq<bool>, c: Seq<bool>, k: nat)
    requires
        frag_dec()(b) == Some::<(Seq<bool>, nat, Flg)>((c, k, Flg::SameVer)),
        d(c) is None,
    ensures open_dec(d)(b) is None,
{
    reveal(open_dec);
}

/// The content parsed but did not fill the octets the determinant claimed, or
/// the padding was not zero. Either way the encoding was not canonical.
pub proof fn lemma_open_dec_none_pad<A>(d: Dec<A>, b: Seq<bool>, c: Seq<bool>, k: nat)
    requires
        frag_dec()(b) == Some::<(Seq<bool>, nat, Flg)>((c, k, Flg::SameVer)),
        d(c) is Some,
        ({
            let k2 = d(c).unwrap().1;
            ||| k2 > c.len()
            ||| ot_octets(k2) != c.len() / 8
            ||| c.skip(k2 as int) != zeros((c.len() - k2) as nat)
        }),
    ensures open_dec(d)(b) is None,
{
    reveal(open_dec);
}

/// What an encoder has to produce in its scratch buffer: the value's bits,
/// then zero padding out to a whole octet.
pub proof fn lemma_ot_body_shape<A>(e: Enc<A>, a: A)
    ensures
        ot_body(e, a).len() == 8 * ot_octets(e(a).len()),
        ot_body(e, a).len() % 8 == 0,
        ot_body(e, a).take(e(a).len() as int) =~= e(a),
        ot_body(e, a).skip(e(a).len() as int)
            =~= zeros((8 * ot_octets(e(a).len()) - e(a).len()) as nat),
{
    lemma_ot_octets(e(a).len());
    let pad = (8 * ot_octets(e(a).len()) - e(a).len()) as nat;
    crate::uper::format::lemma_take_add(e(a), zeros(pad));
    assert(ot_body(e, a).len() % 8 == 0) by (nonlinear_arith)
        requires ot_body(e, a).len() == 8 * ot_octets(e(a).len());
}

} // verus!
