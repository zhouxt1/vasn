//! vasn's decoders for the seven NR RRC channel messages, on a
//! directory of UPER messages. TYPE is one of them, `DL-DCCH-Message` if left
//! out: `UL-DCCH-Message`, `PCCH-Message`, `BCCH-BCH-Message`,
//! `BCCH-DL-SCH-Message`, `UL-CCCH-Message`, `DL-CCCH-Message`.
//!
//!   bench_ours bench DIR ROUNDS [TYPE]  time it, the same way bench_asn1c does
//!   bench_ours why DIR [TYPE]           each message it rejects, and where it stopped
//!   bench_ours jer FILE...              print each DL-DCCH message's value as JER
//!   bench_ours select OUT LIST          build a DL-DCCH corpus from the files named in LIST
//!
//! `bench`: every message is read into memory first. A round decodes each
//! message once and drops the value; the round, not each message, is timed.
//! Prints how many decoded, and the fastest and median round.
//!
//! `select`: keeps a file only if it is a message of exactly this schema --
//! decoded `SameVer`, so no extension addition was stepped over, and with no
//! `Unknown` CHOICE alternative in it -- and writes our verified encoder's
//! encoding of the value, not the file. A fuzzer's input can carry junk after
//! the message, which no decoder reads; re-encoding drops it, and gives the
//! canonical bits, which `SameVer` guarantees are the bits that were decoded.
//! Duplicates are written once.
extern crate BCCH_BCH_Message;
extern crate BCCH_DL_SCH_Message;
extern crate DL_CCCH_Message;
extern crate DL_DCCH_Message;
extern crate PCCH_Message;
extern crate UL_CCCH_Message;
extern crate UL_DCCH_Message;
extern crate vuperx;

use std::collections::HashSet;
use std::hint::black_box;
use std::path::Path;
use std::time::Instant;

use ::DL_DCCH_Message::{DL_DCCH_MessageType_jer, DL_DCCH_Message_decode, DL_DCCH_Message_encode};
use vuperx::cursor::{BitReader, BitWriter};
use vuperx::format::Flg;

/// Runs `$f!(decode)` with `decode` the decoder of the channel message named
/// `$t`, so that each channel's loop is compiled with its decoder inlined.
macro_rules! with_decoder {
    ($t:expr, $f:ident) => {
        match $t {
            "DL-DCCH-Message" => $f!(::DL_DCCH_Message::DL_DCCH_Message_decode),
            "UL-DCCH-Message" => $f!(::UL_DCCH_Message::UL_DCCH_Message_decode),
            "PCCH-Message" => $f!(::PCCH_Message::PCCH_Message_decode),
            "BCCH-BCH-Message" => $f!(::BCCH_BCH_Message::BCCH_BCH_Message_decode),
            "BCCH-DL-SCH-Message" => $f!(::BCCH_DL_SCH_Message::BCCH_DL_SCH_Message_decode),
            "UL-CCCH-Message" => $f!(::UL_CCCH_Message::UL_CCCH_Message_decode),
            "DL-CCCH-Message" => $f!(::DL_CCCH_Message::DL_CCCH_Message_decode),
            t => {
                eprintln!("{t}: not one of the seven channel messages");
                std::process::exit(2);
            }
        }
    };
}

fn load(dir: &Path) -> Vec<Vec<u8>> {
    let mut names: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "uper"))
        .collect();
    names.sort();
    names.iter().map(|p| std::fs::read(p).unwrap()).collect()
}

fn bench(dir: &Path, rounds: usize, decodes: impl Fn(&[u8]) -> bool) {
    let msgs = load(dir);
    let mut times = Vec::with_capacity(rounds);
    let mut ok = 0;
    for r in 0..=rounds {
        // round 0 warms up
        let t0 = Instant::now();
        let mut good = 0;
        for m in &msgs {
            good += decodes(black_box(m)) as usize;
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
        "ours  {} messages, {} decoded, min {:.1} ns/msg, median {:.1} ns/msg",
        msgs.len(),
        ok,
        times[0] / n,
        times[rounds / 2] / n
    );
}

fn select(out: &Path, list: &Path) {
    std::fs::create_dir_all(out).unwrap();
    let files = std::fs::read_to_string(list).unwrap();
    let (mut seen, mut kept, mut dup, mut newer, mut rejected) = (HashSet::new(), 0, 0, 0, 0);
    for f in files.lines() {
        let input = std::fs::read(f).unwrap_or_else(|e| panic!("{f}: {e}"));
        let Some((v, flag)) = DL_DCCH_Message_decode(&mut BitReader::new(&input)) else {
            rejected += 1;
            continue;
        };
        let mut jer = String::new();
        DL_DCCH_MessageType_jer(&v.message, &mut jer);
        if !matches!(flag, Flg::SameVer) || jer.contains("\"?unknown-extension\"") {
            newer += 1;
            continue;
        }
        let mut w = BitWriter::with_capacity(8 * input.len() + 64);
        assert!(DL_DCCH_Message_encode(&mut w, &v), "{f}: the encoder refused a decoded value");
        let bytes = w.buf[..(w.pos + 7) / 8].to_vec();
        if seen.insert(bytes.clone()) {
            std::fs::write(out.join(format!("q{kept:06}.uper")), &bytes).unwrap();
            kept += 1;
        } else {
            dup += 1;
        }
    }
    println!("{kept} kept, {dup} duplicates, {newer} newer-version, {rejected} rejected");
}

/// Every message in `dir` that `decode` rejects, and where it stopped.
fn why<T>(dir: &Path, decode: impl Fn(&mut BitReader) -> Option<T>) {
    let mut files: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    files.sort();
    for f in files {
        let input = std::fs::read(&f).unwrap();
        let mut r = BitReader::new(&input);
        if decode(&mut r).is_none() {
            println!("{}: {}", f.display(), r.error());
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["bench", dir, rounds, ty @ ..] => {
            let (dir, rounds) = (Path::new(dir), rounds.parse().unwrap());
            macro_rules! go {
                ($d:path) => {
                    bench(dir, rounds, |m| {
                        let v = $d(&mut BitReader::new(m));
                        let ok = v.is_some();
                        drop(black_box(v));
                        ok
                    })
                };
            }
            with_decoder!(ty.first().copied().unwrap_or("DL-DCCH-Message"), go)
        }
        ["why", dir, ty @ ..] => {
            let dir = Path::new(dir);
            macro_rules! go {
                ($d:path) => {
                    why(dir, |r| $d(r))
                };
            }
            with_decoder!(ty.first().copied().unwrap_or("DL-DCCH-Message"), go)
        }
        ["select", out, list] => select(Path::new(out), Path::new(list)),
        ["jer", files @ ..] => {
            for f in files {
                let input = std::fs::read(f).unwrap();
                match DL_DCCH_Message_decode(&mut BitReader::new(&input)) {
                    Some((v, _)) => {
                        let mut s = String::new();
                        DL_DCCH_MessageType_jer(&v.message, &mut s);
                        println!("{s}");
                    }
                    None => println!("\"Error\""),
                }
            }
        }
        _ => {
            eprintln!(
                "usage: bench_ours bench DIR ROUNDS [TYPE] | why DIR [TYPE] | jer FILE.. | select OUT LIST"
            );
            std::process::exit(2);
        }
    }
}
