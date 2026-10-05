//! Where our time goes, the same split as asn1c/profile.c: decode and drop
//! timed apart, per message, and heap calls counted by a wrapping allocator.
//!
//!   profile_ours DIR ROUNDS [TYPE]     TYPE as for bench_ours, DL-DCCH-Message if left out
extern crate BCCH_BCH_Message;
extern crate BCCH_DL_SCH_Message;
extern crate DL_CCCH_Message;
extern crate DL_DCCH_Message;
extern crate PCCH_Message;
extern crate UL_CCCH_Message;
extern crate UL_DCCH_Message;
extern crate vasn;

use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::time::Instant;

use vasn::uper::cursor::BitReader;

struct Counting;
static ALLOCS: AtomicU64 = AtomicU64::new(0);
static FREES: AtomicU64 = AtomicU64::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Relaxed);
        System.alloc(l)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        FREES.fetch_add(1, Relaxed);
        System.dealloc(p, l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        ALLOCS.fetch_add(1, Relaxed);
        System.realloc(p, l, n)
    }
}

#[global_allocator]
static A: Counting = Counting;

/// Decodes `m` and drops the value, timing each: (decode, drop) in ns.
macro_rules! timed {
    ($d:path) => {
        |m: &[u8]| {
            let t0 = Instant::now();
            let v = $d(&mut BitReader::new(black_box(m)));
            let t1 = Instant::now();
            drop(black_box(v));
            let t2 = Instant::now();
            ((t1 - t0).as_nanos(), (t2 - t1).as_nanos())
        }
    };
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.get(2).map(String::as_str).unwrap_or("DL-DCCH-Message") {
        "DL-DCCH-Message" => profile(&args, timed!(::DL_DCCH_Message::DL_DCCH_Message_decode)),
        "UL-DCCH-Message" => profile(&args, timed!(::UL_DCCH_Message::UL_DCCH_Message_decode)),
        "PCCH-Message" => profile(&args, timed!(::PCCH_Message::PCCH_Message_decode)),
        "BCCH-BCH-Message" => profile(&args, timed!(::BCCH_BCH_Message::BCCH_BCH_Message_decode)),
        "BCCH-DL-SCH-Message" => profile(&args, timed!(::BCCH_DL_SCH_Message::BCCH_DL_SCH_Message_decode)),
        "UL-CCCH-Message" => profile(&args, timed!(::UL_CCCH_Message::UL_CCCH_Message_decode)),
        "DL-CCCH-Message" => profile(&args, timed!(::DL_CCCH_Message::DL_CCCH_Message_decode)),
        t => {
            eprintln!("{t}: not one of the seven channel messages");
            std::process::exit(2);
        }
    }
}

fn profile(args: &[String], one: impl Fn(&[u8]) -> (u128, u128)) {
    let mut names: Vec<_> = std::fs::read_dir(&args[0]).unwrap().map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "uper")).collect();
    names.sort();
    let msgs: Vec<Vec<u8>> = names.iter().map(|p| std::fs::read(p).unwrap()).collect();
    let rounds: usize = args[1].parse().unwrap();
    let n = msgs.len() as f64;
    let (mut best_dec, mut best_drop, mut clk) = (u128::MAX, u128::MAX, u128::MAX);
    let (mut allocs, mut frees) = (0, 0);
    for r in 0..=rounds {
        let c0 = Instant::now();
        for _ in &msgs {
            let a = Instant::now();
            black_box(a.elapsed());
        }
        let c = c0.elapsed().as_nanos();
        let (mut dec, mut drp) = (0u128, 0u128);
        let (a0, f0) = (ALLOCS.load(Relaxed), FREES.load(Relaxed));
        for m in &msgs {
            let (d, p) = one(m);
            dec += d;
            drp += p;
        }
        allocs = ALLOCS.load(Relaxed) - a0;
        frees = FREES.load(Relaxed) - f0;
        if r > 0 {
            best_dec = best_dec.min(dec);
            best_drop = best_drop.min(drp);
            clk = clk.min(c);
        }
    }
    let oh = clk as f64 / n / 2.0;
    println!(
        "ours  decode {:.1} ns/msg, drop {:.1} ns/msg (clock overhead {:.1} taken off each), \
         {:.1} allocations/msg, {:.1} frees/msg",
        best_dec as f64 / n - oh, best_drop as f64 / n - oh, oh, allocs as f64 / n, frees as f64 / n
    );
}
