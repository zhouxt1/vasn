//! rasn's decoder for one of the seven NR channel messages, on a directory of
//! UPER messages. TYPE is DL-DCCH-Message if left out.
//!
//!   bench_rasn bench DIR ROUNDS [TYPE]  time it, the same way bench_asn1c does
//!   bench_rasn encode DIR ROUNDS [TYPE] time the encoder on the values they decode to
//!   bench_rasn fails DIR [TYPE]         list the messages it fails to decode, or
//!                                       whose value does not re-encode to the input
//!
//! `nr_rasn.rs` is rasn-compiler 0.16.0's output for nr-rrc-17.3.0.asn1,
//! unedited (bench/decode/build.sh regenerates it).
#[allow(clippy::all)]
mod nr_rasn;

use rasn::uper as codec;
const EXT: &str = "uper";

use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::time::Instant;

use nr_rasn::nr_rrc_definitions::{
    BCCHBCHMessage, BCCHDLSCHMessage, DLCCCHMessage, DLDCCHMessage, PCCHMessage, ULCCCHMessage,
    ULDCCHMessage,
};

/// Runs `$f::<T>(..)` with `T` the channel message named `$t`.
macro_rules! with_type {
    ($t:expr, $f:ident($($a:expr),*)) => {
        match $t {
            "DL-DCCH-Message" => $f::<DLDCCHMessage>($($a),*),
            "UL-DCCH-Message" => $f::<ULDCCHMessage>($($a),*),
            "PCCH-Message" => $f::<PCCHMessage>($($a),*),
            "BCCH-BCH-Message" => $f::<BCCHBCHMessage>($($a),*),
            "BCCH-DL-SCH-Message" => $f::<BCCHDLSCHMessage>($($a),*),
            "UL-CCCH-Message" => $f::<ULCCCHMessage>($($a),*),
            "DL-CCCH-Message" => $f::<DLCCCHMessage>($($a),*),
            t => {
                eprintln!("{t}: not one of the seven channel messages");
                std::process::exit(2);
            }
        }
    };
}

fn load(dir: &Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut names: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == EXT))
        .collect();
    names.sort();
    names.into_iter().map(|p| { let b = std::fs::read(&p).unwrap(); (p, b) }).collect()
}

fn bench<T: rasn::Decode>(dir: &Path, rounds: usize) {
    let msgs = load(dir);
    let mut times = Vec::with_capacity(rounds);
    let mut ok = 0;
    for r in 0..=rounds {
        // round 0 warms up
        let t0 = Instant::now();
        let mut good = 0;
        for (_, m) in &msgs {
            let v = codec::decode::<T>(black_box(m));
            good += v.is_ok() as usize;
            drop(black_box(v));
        }
        let dt = t0.elapsed().as_nanos() as f64;
        if r > 0 {
            times.push(dt);
        }
        ok = good;
    }
    times.sort_by(f64::total_cmp);
    let n = msgs.len() as f64;
    println!(
        "rasn  {} messages, {} decoded, min {:.1} ns/msg, median {:.1} ns/msg",
        msgs.len(),
        ok,
        times[0] / n,
        times[rounds / 2] / n
    );
}

/// The encoder on the values the messages decode to; rasn's `encode` returns a
/// new `Vec`, so each message pays an allocation the others do not.
fn encode<T: rasn::Decode + rasn::Encode>(dir: &Path, rounds: usize) {
    let vals: Vec<T> = load(dir).iter().filter_map(|(_, m)| codec::decode::<T>(m).ok()).collect();
    let mut times = Vec::with_capacity(rounds);
    let mut ok = 0;
    for r in 0..=rounds {
        let t0 = Instant::now();
        let mut good = 0;
        for v in &vals {
            let b = codec::encode(black_box(v));
            good += b.is_ok() as usize;
            drop(black_box(b));
        }
        let dt = t0.elapsed().as_nanos() as f64;
        if r > 0 {
            times.push(dt);
        }
        ok = good;
    }
    times.sort_by(f64::total_cmp);
    let n = vals.len() as f64;
    println!(
        "rasn  {} values, {} encoded, min {:.1} ns/msg, median {:.1} ns/msg",
        vals.len(),
        ok,
        times[0] / n,
        times[rounds / 2] / n
    );
}

fn fails<T: rasn::Decode + rasn::Encode>(dir: &Path) {
    for (p, m) in load(dir) {
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        match codec::decode::<T>(&m) {
            Err(e) => println!("{name} decode: {}", e.to_string().replace('\n', " ")),
            Ok(v) => match codec::encode(&v) {
                Err(e) => println!("{name} re-encode: {}", e.to_string().replace('\n', " ")),
                Ok(b) if b != m => println!("{name} re-encodes differently"),
                Ok(_) => {}
            },
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let ty = |rest: &[&str]| rest.first().copied().unwrap_or("DL-DCCH-Message").to_owned();
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["bench", dir, rounds, rest @ ..] => {
            with_type!(ty(rest).as_str(), bench(Path::new(dir), rounds.parse().unwrap()))
        }
        ["encode", dir, rounds, rest @ ..] => {
            with_type!(ty(rest).as_str(), encode(Path::new(dir), rounds.parse().unwrap()))
        }
        ["fails", dir, rest @ ..] => with_type!(ty(rest).as_str(), fails(Path::new(dir))),
        _ => {
            eprintln!("usage: bench_rasn bench DIR ROUNDS [TYPE] | encode DIR ROUNDS [TYPE] | fails DIR [TYPE]");
            std::process::exit(2);
        }
    }
}
