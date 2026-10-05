//! Reading several fields with one read. A SEQUENCE's preamble is a run of
//! single bits, and is read as one word of up to 56 bits and split, rather
//! than one checked `read_bool` per bit. These are the facts the generated
//! split needs: what a BOOLEAN read at bit `o` gives, and which bit of a word
//! is bit `j` of the input.
use vstd::prelude::*;
use crate::bits::bitspec::*;
use crate::uper::format::*;
use crate::uper::prim::*;
use crate::uper::term::*;
use crate::uper::list::*;
use crate::uper::cursor::*;

verus! {

broadcast use {format_steps, map_steps};

/// A BOOLEAN read at bit `o` of `s` is that bit.
pub proof fn lemma_bool_dec_at(s: Seq<bool>, o: int)
    requires 0 <= o < s.len(),
    ensures bool_dec()(s.skip(o)) == Some::<(bool, nat, Flg)>((s[o], 1nat, Flg::SameVer)),
{
    let t = s.skip(o);
    let u = t.take(1);
    reveal_with_fuel(bits_val, 2);
    assert(u.drop_last() =~= Seq::<bool>::empty());
    assert(u.last() == s[o]);
    lemma_map_dec_some(uint_dec(1), bool_to_f(), t, bits_val(u) as u64, 1, Flg::SameVer);
}

/// Bit `j` of the `k`-bit word that starts `s` is the word shifted down by
/// `sh = k - 1 - j`, its lowest bit.
pub proof fn lemma_word_bit(s: Seq<bool>, k: nat, j: nat, sh: u64)
    requires 1 <= k <= 56, s.len() >= k, j < k, sh + j + 1 == k,
    ensures ((((bits_val(s.take(k as int)) as u64) >> sh) & 1u64) == 1u64) == s[j as int],
{
    let t = s.take(k as int);
    let v = bits_val(t);
    lemma_bits_val_bound(t);
    crate::bits::prim_read::lemma_p2_mono(k, 56);
    crate::bits::prim_read::lemma_p2_56();
    assert(v < 0x1_0000_0000_0000_0000nat);
    let w = v as u64;
    assert(w as nat == v);
    lemma_bits_val_subrange(t, j as int, j as int + 1);
    let u = t.subrange(j as int, j as int + 1);
    reveal_with_fuel(bits_val, 2);
    assert(u.drop_last() =~= Seq::<bool>::empty());
    assert(u.last() == s[j as int]);
    reveal_with_fuel(p2, 2);
    assert(t.len() - (j + 1) == sh);
    crate::bits::prim_read::lemma_p2_eq_pow2(sh as nat);
    vstd::bits::lemma_u64_shr_is_div(w, sh);
    let x = w >> sh;
    assert(x as nat == v / p2(sh as nat));
    assert(((x & 1u64) == 1u64) == (x % 2 == 1)) by (bit_vector);
}

/// The octet at bit `j` of the `k`-bit word that starts `s`: the word
/// shifted down by `sh = k - j - 8`, its low eight bits.
pub proof fn lemma_word_byte(s: Seq<bool>, k: nat, j: nat, sh: u64)
    requires 8 <= k <= 56, s.len() >= k, j + 8 <= k, sh + j + 8 == k,
    ensures
        crate::bits::prim_write::bits_seq(
            (((bits_val(s.take(k as int)) as u64) >> sh) & 0xffu64) as u8 as u64, 8)
            =~= s.subrange(j as int, (j + 8) as int),
{
    let t = s.take(k as int);
    let v = bits_val(t);
    lemma_bits_val_bound(t);
    crate::bits::prim_read::lemma_p2_mono(k, 56);
    crate::bits::prim_read::lemma_p2_56();
    assert(v < 0x1_0000_0000_0000_0000nat);
    let w = v as u64;
    assert(w as nat == v);
    lemma_bits_val_subrange(t, j as int, (j + 8) as int);
    let u = t.subrange(j as int, (j + 8) as int);
    assert(u =~= s.subrange(j as int, (j + 8) as int));
    assert(t.len() - (j + 8) == sh);
    crate::bits::prim_read::lemma_p2_eq_pow2(sh as nat);
    vstd::bits::lemma_u64_shr_is_div(w, sh);
    let x = w >> sh;
    assert(x as nat == v / p2(sh as nat));
    assert(p2(8) == 256) by { reveal_with_fuel(p2, 10); }
    assert((x & 0xffu64) == x % 256) by (bit_vector);
    assert(((x & 0xffu64) as u8 as u64) == (x & 0xffu64)) by (bit_vector);
    assert(bits_val(u) == (x & 0xffu64) as nat);
    crate::uper::prim::lemma_bits_roundtrip(u);
}

/// The bits of a run of octets are that run of the bits.
pub proof fn lemma_bits_of_subrange(s: Seq<u8>, i: int, j: int)
    requires 0 <= i <= j <= s.len(),
    ensures bits_of(s.subrange(i, j)) =~= bits_of(s).subrange(8 * i, 8 * j),
{
    let l = bits_of(s.subrange(i, j));
    let r = bits_of(s).subrange(8 * i, 8 * j);
    assert(l.len() == r.len());
    assert forall|k: int| 0 <= k < l.len() implies l[k] == r[k] by {
        assert((8 * i + k) / 8 == i + k / 8) by (nonlinear_arith) requires 0 <= k;
        assert((8 * i + k) % 8 == k % 8) by (nonlinear_arith) requires 0 <= k;
        assert(k / 8 < j - i) by (nonlinear_arith) requires 0 <= k < 8 * (j - i);
    }
}

/// Seven octets as bits, one after another.
pub proof fn lemma_bits_of_seven(a: Seq<u8>)
    requires a.len() == 7,
    ensures bits_of(a) =~= crate::bits::prim_write::bits_seq(a[0] as u64, 8)
        + crate::bits::prim_write::bits_seq(a[1] as u64, 8)
        + crate::bits::prim_write::bits_seq(a[2] as u64, 8)
        + crate::bits::prim_write::bits_seq(a[3] as u64, 8)
        + crate::bits::prim_write::bits_seq(a[4] as u64, 8)
        + crate::bits::prim_write::bits_seq(a[5] as u64, 8)
        + crate::bits::prim_write::bits_seq(a[6] as u64, 8),
{
    let e = Seq::<u8>::empty();
    assert(bits_of(e) =~= Seq::<bool>::empty());
    assert(a =~= e.push(a[0]).push(a[1]).push(a[2]).push(a[3]).push(a[4]).push(a[5]).push(a[6]));
    lemma_bits_of_push(e, a[0]);
    lemma_bits_of_push(e.push(a[0]), a[1]);
    lemma_bits_of_push(e.push(a[0]).push(a[1]), a[2]);
    lemma_bits_of_push(e.push(a[0]).push(a[1]).push(a[2]), a[3]);
    lemma_bits_of_push(e.push(a[0]).push(a[1]).push(a[2]).push(a[3]), a[4]);
    lemma_bits_of_push(e.push(a[0]).push(a[1]).push(a[2]).push(a[3]).push(a[4]), a[5]);
    lemma_bits_of_push(e.push(a[0]).push(a[1]).push(a[2]).push(a[3]).push(a[4]).push(a[5]), a[6]);
}

/// Octets whose bits are the input's are what a list of `byte`s decodes to.
pub proof fn lemma_octets_list(v: Seq<u8>, s: Seq<bool>)
    requires s.len() >= 8 * v.len(), bits_of(v) =~= s.take((8 * v.len()) as int),
    ensures list_dec_rec(v.len(), byte_dec(), s)
        == Some::<(Seq<u8>, nat, Flg)>((v, 8 * v.len(), Flg::SameVer)),
    decreases v.len(),
{
    if v.len() == 0 {
        assert(v =~= Seq::<u8>::empty());
    } else {
        let h = seq![v[0]];
        let t = v.skip(1);
        assert(v =~= h + t);
        crate::bits::bytebits::lemma_bits_of_add(h, t);
        assert(bits_of(h).len() == 8);
        assert(s.take(8) =~= bits_of(h));
        crate::bits::bytebits::lemma_byte_bits(v[0]);
        lemma_bits_val_bound(s.take(8));
        assert(bits_val(s.take(8)) as u64 as u8 == v[0]);
        lemma_map_dec_some(uint_dec(8), byte_to(), s, bits_val(s.take(8)) as u64, 8, Flg::SameVer);
        assert(bits_of(h + t) == bits_of(v));
        assert(bits_of(t) =~= bits_of(v).skip(8));
        assert(s.take((8 * v.len()) as int).skip(8) =~= s.skip(8).take((8 * t.len()) as int));
        assert(bits_of(t) =~= s.skip(8).take((8 * t.len()) as int));
        lemma_octets_list(t, s.skip(8));
        assert(8 + 8 * t.len() == 8 * v.len());
    }
}

impl<'a> BitReader<'a> {
    /// `c` BOOLEANs, a BIT STRING's bits: one read per 56 of them rather than
    /// a `read_bool` each. The caller has checked they are all there.
    #[verifier::rlimit(60)]
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn read_bit_list(&mut self, c: usize) -> (out: Vec<bool>)
        requires old(self).wf(), c <= 8 * old(self).buf@.len() - old(self).pos,
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos == old(self).pos + c,
            out@.len() == c,
            list_dec_rec(c as nat, bool_dec(), old(self).rem())
                == Some::<(Seq<bool>, nat, Flg)>((out@, c as nat, Flg::SameVer)),
    {
        let ghost s = self.rem();
        let ghost p0 = self.pos;
        let mut out: Vec<bool> = Vec::with_capacity(c);
        let mut i: usize = 0;
        proof {
            lemma_list_loop_start(c as nat, bool_dec(), s);
            assert(s.skip(0) =~= s);
            assert(out@ =~= Seq::<bool>::empty());
        }
        while i < c
            invariant
                self.wf(), self.buf == old(self).buf,
                s == old(self).rem(), p0 == old(self).pos,
                c <= 8 * self.buf@.len() - p0,
                i <= c, self.pos == p0 + i, out@.len() == i,
                list_dec_rec(c as nat, bool_dec(), s)
                    == list_cont(out@, i as nat, Flg::SameVer,
                                 list_dec_rec((c - i) as nat, bool_dec(), s.skip(i as int))),
            decreases c - i,
        {
            let k: usize = if c - i > 56 { 56 } else { c - i };
            proof { lemma_rem_skip(self.buf@, p0 as nat, i as nat); }
            let ghost sw = self.rem();
            assert(sw =~= s.skip(i as int));
            let w = match self.read_uint(k) { Some(w) => w, None => { return out; } };
            let mut j: usize = 0;
            while j < k
                invariant
                    i + k <= c, j <= k, 1 <= k <= 56, sw == s.skip(i as int), sw.len() >= k,
                    w == bits_val(sw.take(k as int)) as u64,
                    out@.len() == i + j,
                    list_dec_rec(c as nat, bool_dec(), s)
                        == list_cont(out@, (i + j) as nat, Flg::SameVer,
                                     list_dec_rec((c - i - j) as nat, bool_dec(),
                                                  s.skip((i + j) as int))),
                decreases k - j,
            {
                let sh: u64 = (k - 1 - j) as u64;
                let b = (w >> sh) & 1u64 == 1u64;
                proof {
                    lemma_word_bit(sw, k as nat, j as nat, sh);
                    assert(sw[j as int] == s[(i + j) as int]);
                    lemma_bool_dec_at(s, (i + j) as int);
                    lemma_list_loop_step(c as nat, bool_dec(), s, out@, (i + j) as nat, Flg::SameVer,
                                         (c - i - j) as nat, s.skip((i + j) as int), b, 1, Flg::SameVer);
                    assert(s.skip((i + j) as int).skip(1) =~= s.skip((i + j + 1) as int));
                }
                out.push(b);
                j = j + 1;
            }
            i = i + k;
        }
        proof {
            lemma_list_loop_done(c as nat, bool_dec(), s, out@, c as nat, Flg::SameVer,
                                 s.skip(c as int));
        }
        out
    }
}

impl<'a> BitReader<'a> {
    /// `c` octets, a sized OCTET STRING's: `read_octets`, seven a read, rather
    /// than a `read_byte` each. The caller has checked they are all there.
    #[inline]
    pub fn read_octet_list(&mut self, c: usize) -> (out: Vec<u8>)
        requires old(self).wf(), 8 * c <= 8 * old(self).buf@.len() - old(self).pos,
        ensures
            final(self).wf(),
            final(self).buf == old(self).buf,
            final(self).pos == old(self).pos + 8 * c,
            out@.len() == c,
            list_dec_rec(c as nat, byte_dec(), old(self).rem())
                == Some::<(Seq<u8>, nat, Flg)>((out@, (8 * c) as nat, Flg::SameVer)),
    {
        let ghost s = self.rem();
        let mut out: Vec<u8> = Vec::new();
        let ok = self.read_octets(c, &mut out);
        assert(ok);
        proof {
            assert(bits_of(Seq::<u8>::empty()) =~= Seq::<bool>::empty());
            assert(bits_of(out@) =~= s.take((8 * c) as int));
            assert(bits_of(out@).len() == 8 * out@.len());
            lemma_octets_list(out@, s);
        }
        out
    }
}

/// The seven octets of a 56-bit window, as bits the window's.
#[inline]
pub fn word_octets(w: u64, Ghost(bi): Ghost<Seq<bool>>) -> (a: [u8; 7])
    requires bi.len() >= 56, w == bits_val(bi.take(56)) as u64,
    ensures bits_of(a@) =~= bi.take(56),
{
    let a: [u8; 7] = [
        ((w >> 48u64) & 0xffu64) as u8, ((w >> 40u64) & 0xffu64) as u8,
        ((w >> 32u64) & 0xffu64) as u8, ((w >> 24u64) & 0xffu64) as u8,
        ((w >> 16u64) & 0xffu64) as u8, ((w >> 8u64) & 0xffu64) as u8,
        ((w >> 0u64) & 0xffu64) as u8,
    ];
    proof {
        lemma_word_byte(bi, 56, 0, 48);
        lemma_word_byte(bi, 56, 8, 40);
        lemma_word_byte(bi, 56, 16, 32);
        lemma_word_byte(bi, 56, 24, 24);
        lemma_word_byte(bi, 56, 32, 16);
        lemma_word_byte(bi, 56, 40, 8);
        lemma_word_byte(bi, 56, 48, 0);
        lemma_bits_of_seven(a@);
        let t = bi.take(56);
        assert(t =~= bi.subrange(0, 8) + bi.subrange(8, 16) + bi.subrange(16, 24)
               + bi.subrange(24, 32) + bi.subrange(32, 40) + bi.subrange(40, 48)
               + bi.subrange(48, 56));
    }
    a
}

// ------------------------------------------------------------- writes

/// A BOOLEAN is its one bit.
pub proof fn lemma_bool_enc_bit(b: bool)
    ensures bool_enc()(b) =~= seq![b],
{
    reveal(map_enc);
    reveal_with_fuel(crate::bits::bitspec::p2, 3);
    assert(bool_enc()(b)[0] == b);
}

/// A list of BOOLEANs encodes as the BOOLEANs.
pub proof fn lemma_bool_list_enc(l: Seq<bool>)
    ensures list_enc_rec(l, bool_enc()) =~= l,
    decreases l.len(),
{
    if l.len() > 0 {
        lemma_bool_enc_bit(l[0]);
        lemma_bool_list_enc(l.skip(1));
        assert(seq![l[0]] + l.skip(1) =~= l);
    }
}

/// An octet is its eight bits.
pub proof fn lemma_byte_enc_bits(b: u8)
    ensures byte_enc()(b) =~= bits_of(seq![b]),
{
    reveal(map_enc);
    crate::bits::bitspec::lemma_bits_of_push(Seq::<u8>::empty(), b);
    assert(bits_of(Seq::<u8>::empty()) =~= Seq::<bool>::empty());
    assert(Seq::<u8>::empty().push(b) =~= seq![b]);
}

/// A list of octets encodes as their bits.
pub proof fn lemma_byte_list_enc(l: Seq<u8>)
    ensures list_enc_rec(l, byte_enc()) =~= bits_of(l),
    decreases l.len(),
{
    if l.len() == 0 {
        assert(bits_of(l) =~= Seq::<bool>::empty());
    } else {
        lemma_byte_enc_bits(l[0]);
        lemma_byte_list_enc(l.skip(1));
        assert(l =~= seq![l[0]] + l.skip(1));
        crate::bits::bytebits::lemma_bits_of_add(seq![l[0]], l.skip(1));
    }
}

/// `l[i..i + k]` as one big-endian word.
#[verifier::loop_isolation(false)]
#[inline]
fn pack_bools(l: &[bool], i: usize, k: usize) -> (v: u64)
    requires 1 <= k <= 56, i + k <= l@.len(), i + k <= usize::MAX,
    ensures
        v as nat == bits_val(l@.subrange(i as int, (i + k) as int)),
        (v as nat) < crate::bits::bitspec::p2(k as nat),
{
    let mut v: u64 = 0;
    let mut j: usize = 0;
    proof {
        assert(l@.subrange(i as int, i as int) =~= Seq::<bool>::empty());
        reveal_with_fuel(crate::bits::bitspec::p2, 1);
    }
    while j < k
        invariant
            1 <= k <= 56, j <= k, i + k <= l@.len(), i + k <= usize::MAX,
            v as nat == bits_val(l@.subrange(i as int, (i + j) as int)),
            (v as nat) < crate::bits::bitspec::p2(j as nat),
        decreases k - j,
    {
        let b = l[i + j];
        proof {
            let t = l@.subrange(i as int, (i + j + 1) as int);
            assert(t.drop_last() =~= l@.subrange(i as int, (i + j) as int));
            assert(t.last() == b);
            crate::bits::prim_read::lemma_p2_mono(j as nat, 56);
            crate::bits::prim_read::lemma_p2_56();
            crate::bits::bitspec::lemma_p2_adds(j as nat, 1);
            assert(crate::bits::bitspec::p2(1) == 2) by {
                reveal_with_fuel(crate::bits::bitspec::p2, 2);
            }
        }
        v = v * 2 + if b { 1u64 } else { 0u64 };
        j = j + 1;
    }
    v
}

impl BitWriter {
    /// Bits, 56 a write, packed into one word, rather than a `write_bool`
    /// each: a BIT STRING's (`write_bit_list`), or a preamble's, gathered into
    /// an array (`vasnc`'s `{T}_bmwfast`).
    #[verifier::loop_isolation(false)]
    #[inline]
    pub fn write_bit_slice(&mut self, l: &[bool]) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + l@,
    {
        let ghost w0 = self.written();
        let n = l.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(), self.buf@.len() == old(self).buf@.len(), i <= n, n == l@.len(),
                self.written() =~= w0 + l@.take(i as int),
            decreases n - i,
        {
            let k: usize = if n - i > 56 { 56 } else { n - i };
            let v = pack_bools(l, i, k);
            let ghost sub = l@.subrange(i as int, (i + k) as int);
            proof {
                crate::bits::prim_write::lemma_bits_seq_of_val(sub);
                assert(uint_wf(k as nat)(v));
            }
            if !self.write_uint(k, v) {
                return false;
            }
            proof {
                assert(uint_enc(k as nat)(v) =~= sub);
                assert(l@.take((i + k) as int) =~= l@.take(i as int) + sub);
            }
            i = i + k;
        }
        proof { assert(l@.take(n as int) =~= l@); }
        true
    }

    /// A BIT STRING's bits. Refines `list_enc_rec(_, bool_enc())`.
    #[inline]
    pub fn write_bit_list(&mut self, l: &Vec<bool>) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + list_enc_rec(l@, bool_enc()),
    {
        proof { lemma_bool_list_enc(l@); }
        self.write_bit_slice(l.as_slice())
    }

    /// An OCTET STRING's octets, as `write_slice` copies them. Refines
    /// `list_enc_rec(_, byte_enc())`.
    #[inline]
    pub fn write_octet_list(&mut self, l: &Vec<u8>) -> (ok: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@.len() == old(self).buf@.len(),
            ok ==> final(self).written() =~= old(self).written() + list_enc_rec(l@, byte_enc()),
    {
        if l.len() > usize::MAX / 8 {
            return false;
        }
        let ok = self.write_slice(l.as_slice(), 0, 8 * l.len());
        proof {
            lemma_byte_list_enc(l@);
            assert(bits_of(l@).skip(0).take((8 * l@.len()) as int) =~= bits_of(l@));
        }
        ok
    }
}

} // verus!
