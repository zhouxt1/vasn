//! What a decoder says when it rejects: the bit it was at, what it was
//! reading there, and the path of components that leads to it, e.g.
//! `message.c1.rrcReconfiguration.measConfig: SIZE (1..64) length at bit 211`.
//!
//! A decoder still returns `Option`; the error is written into its
//! `BitReader` on the way out, and read with `BitReader::error`. Diagnostic
//! data, and nothing more: the failure path proves `X_dec()(rem) is None`
//! exactly as before, and nothing here touches the reader's `buf` or `pos`.
//!
//! Not a `Result`, which was 17% slower on DL-DCCH (3.20 against 2.75 us/msg
//! on a fuzzing corpus, before `#[inline]`). Recording costs
//! nothing on the success path: `fail` stores where the reader stopped, which
//! needs no position kept from before the read, and a path step is a bounds
//! check and two stores into a fixed array, with no allocation or call. With
//! everything `#[inline]`, decoding is 1.80 us/msg, and was 1.79 without any
//! of this.
use vstd::prelude::*;
use crate::uper::format::*;
use crate::uper::cursor::BitReader;

verus! {

/// One step of the path, innermost first as it is built.
#[derive(Clone, Copy)]
pub enum Seg {
    /// a SEQUENCE component or a CHOICE alternative, by its ASN.1 identifier
    Field(&'static str),
    /// an element of a SEQUENCE OF
    Index(u64),
}

pub struct DecodeError {
    /// the bit the reader had reached when the item failed, counted from the
    /// start of the message: past whatever of the item it had read
    pub pos: usize,
    /// what was being read there; empty until a decode fails
    pub what: &'static str,
    /// `path[..depth]`, innermost first; `Display` prints it outermost
    /// first. Past `MAX_DEPTH` steps the outermost are left out.
    pub path: [Seg; MAX_DEPTH],
    pub depth: usize,
}

pub const MAX_DEPTH: usize = 32;

impl DecodeError {
    #[inline]
    pub fn empty() -> DecodeError {
        DecodeError { pos: 0, what: "", path: [Seg::Index(0); MAX_DEPTH], depth: 0 }
    }
}

impl<'a> BitReader<'a> {
    /// The item being read, `what`, failed to decode.
    #[verifier::external_body]
    #[inline(always)]
    pub fn fail(&mut self, what: &'static str)
        ensures final(self).buf == old(self).buf, final(self).pos == old(self).pos,
    {
        self.err.pos = self.pos;
        self.err.what = what;
        self.err.depth = 0;
        note_root(what);
    }

    #[verifier::external_body]
    #[inline(always)]
    fn step(&mut self, s: Seg)
        ensures final(self).buf == old(self).buf, final(self).pos == old(self).pos,
    {
        let d = self.err.depth;
        if d < MAX_DEPTH {
            self.err.path[d] = s;
            self.err.depth = d + 1;
        }
    }

    /// The failure was inside component `name` of a SEQUENCE or CHOICE.
    #[inline(always)]
    pub fn fail_in(&mut self, name: &'static str)
        ensures final(self).buf == old(self).buf, final(self).pos == old(self).pos,
    {
        self.step(Seg::Field(name));
    }

    /// The failure was inside element `i` of a SEQUENCE OF.
    #[inline(always)]
    pub fn fail_at(&mut self, i: u64)
        ensures final(self).buf == old(self).buf, final(self).pos == old(self).pos,
    {
        self.step(Seg::Index(i));
    }

    /// The failure was in an open type's content, `len` octets this reader
    /// has just read and `inner`, a reader of its own, decoded; it is placed
    /// in this reader's message. Below 16K octets the content is contiguous
    /// and ends here. A fragmented content is not, and its error is placed
    /// here, at the open type's end.
    #[verifier::external_body]
    #[cold]
    #[inline(never)]
    pub fn adopt(&mut self, inner: &BitReader, len: usize)
        ensures final(self).buf == old(self).buf, final(self).pos == old(self).pos,
    {
        let (e, end) = (&inner.err, self.pos);
        self.err.pos = if len < 16384 && 8 * len <= end && e.pos <= 8 * len {
            end - 8 * len + e.pos
        } else {
            end
        };
        self.err.what = e.what;
        self.err.path = e.path;
        self.err.depth = e.depth;
    }

    /// A read's `Option`, recording on failure what was being read.
    #[inline(always)]
    pub fn got<A>(&mut self, o: Option<A>, what: &'static str) -> (res: Option<A>)
        ensures final(self).buf == old(self).buf, final(self).pos == old(self).pos, res == o,
    {
        match o {
            Some(v) => Some(v),
            None => {
                self.fail(what);
                None
            }
        }
    }

    /// `got` into the flagged shape the composition lemmas expect; every
    /// terminal format is `SameVer` by construction (see `with_same`).
    #[inline(always)]
    pub fn same<A>(&mut self, o: Option<A>, what: &'static str) -> (res: Option<(A, Flg)>)
        ensures
            final(self).buf == old(self).buf, final(self).pos == old(self).pos,
            match o {
                Some(v) => res == Some::<(A, Flg)>((v, Flg::SameVer)),
                None => res is None,
            },
    {
        match o {
            Some(v) => Some((v, Flg::SameVer)),
            None => {
                self.fail(what);
                None
            }
        }
    }
}

} // verus!

thread_local! {
    static ROOT: std::cell::Cell<&'static str> = const { std::cell::Cell::new("") };
}

/// The `what` of the first `fail` since `take_root`: the innermost item of
/// a failure, often the reason itself ("not in the fewest octets"), which
/// the enclosing items' `fail`s replace in `DecodeError::what` with their own
/// names. A decode stops at its first failure, so every `fail` after the
/// first belongs to it. Diagnostics for tools (difftest/afuzz), kept per
/// thread, outside the reader, so that no spec sees it.
#[inline(always)]
fn note_root(what: &'static str) {
    ROOT.with(|r| if r.get().is_empty() { r.set(what) });
}

/// The innermost reason of the failure since the last call (`note_root`),
/// "" if none; and start afresh.
pub fn take_root() -> &'static str {
    ROOT.with(|r| r.replace(""))
}

impl<'a> BitReader<'a> {
    /// Why the last decode from this reader failed.
    #[inline]
    pub fn error(&self) -> &DecodeError {
        &self.err
    }
}

impl std::fmt::Display for DecodeError {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.depth == MAX_DEPTH {
            write!(f, "...")?;
        }
        for (i, s) in self.path[..self.depth].iter().rev().enumerate() {
            match s {
                Seg::Field(n) if i == 0 && self.depth < MAX_DEPTH => write!(f, "{n}")?,
                Seg::Field(n) => write!(f, ".{n}")?,
                Seg::Index(k) => write!(f, "[{k}]")?,
            }
        }
        if self.depth > 0 {
            write!(f, ": ")?;
        }
        write!(f, "{} at bit {}", self.what, self.pos)
    }
}

impl std::fmt::Debug for DecodeError {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}
