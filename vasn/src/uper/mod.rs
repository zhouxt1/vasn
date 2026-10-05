//! Unaligned PER (X.691): what a format is, its combinators, one proved
//! format per X.691 building block, and the cursors that refine them.
pub mod format;
pub mod prim;
pub mod cursor;
pub mod term;
pub mod opt;
pub mod list;
pub mod lendet;
pub mod bound;
pub mod frag;
pub mod fraglist;
pub mod intx;
pub mod opentype;
pub mod seqext;
pub mod err;
pub mod fast;
#[cfg(target_arch = "x86_64")]
pub mod simd;
