//! vbits — bit views of byte buffers, and reading and writing bit fields in
//! them. No encoding rules: this is the layer every bit-precise codec in the
//! workspace shares (vasn's PER, and the EXI codecs to come).
//!
//! * `bitspec`: the ghost model, bytes as a big-endian bit sequence.
//! * `bytebits`: that view of a byte buffer.
//! * `prim_read`, `prim_write`, `fastload`: the primitive bit reads and
//!   writes, and the word-at-a-time load they use.
//! * `lsb`: the LSB-first view (DEFLATE, Brotli), and its window load.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
pub mod bitspec;
pub mod bytebits;
pub mod prim_read;
pub mod prim_write;
pub mod fastload;
pub mod faststore;
pub mod lsb;
