//! vsimd: 128-bit SIMD for Verus.
//!
//! * `spec`: what each operation computes, on a vector's 16 bytes.
//! * `model`: portable implementations on `[u8; 16]`, proved to compute it.
//! * `x86`: the SSE2 intrinsics, trusted to compute it. This is the crate's
//!   trusted base; `tests/validate.rs` checks it against the CPU, lane
//!   values exhaustively, through the proved models.
//! * `mem`: scalar loads and stores, unchecked, in bounds by their
//!   preconditions (trusted, as `x86`'s loads and stores).
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
pub mod spec;
pub mod model;
pub mod mem;
#[cfg(target_arch = "x86_64")]
pub mod x86;
#[cfg(target_arch = "x86_64")]
pub mod idiom;
