//! vasn — verified, bit-precise ASN.1 PER codec runtimes.
//!
//! * `bits`: the `vbits` crate, re-exported: bit views of byte buffers and
//!   the primitive bit reads and writes. No encoding rules.
//! * `uper`: the unaligned PER formats, their combinators and proofs, and
//!   the cursors generated code threads.
//! * `utf8`, `time`, `oid`, `jer`, `arb`: UTF-8 validation, the forms of the time types and of OID contents, the JER printer and the random
//!   value generator, shared by every encoding.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
pub use vbits as bits;
pub mod uper;
pub mod utf8;
pub mod time;
pub mod oid;
pub mod real;
pub mod jer;
pub mod arb;
