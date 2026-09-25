//! The codecs vuperc generates from `asn1/`, one module per schema. Each is
//! checked in; `cargo test -p vuperc` fails if one is out of date.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
pub mod choice;
pub mod demo;
pub mod enum_ext;
pub mod ext;
pub mod frag;
pub mod its;
pub mod lists;
pub mod optional;
