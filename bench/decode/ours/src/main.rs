//! vasn's decoders for the seven NR RRC channel messages, on a
//! directory of UPER messages. TYPE is one of them, `DL-DCCH-Message` if left
//! out: `UL-DCCH-Message`, `PCCH-Message`, `BCCH-BCH-Message`,
//! `BCCH-DL-SCH-Message`, `UL-CCCH-Message`, `DL-CCCH-Message`.
//!
//!   bench_ours bench DIR ROUNDS [TYPE]  time it, the same way bench_asn1c does
//!   bench_ours encode DIR ROUNDS [TYPE] time the encoder on the values the messages decode to
//!   bench_ours encout DIR OUT [TYPE]    write each message's re-encoding to OUT, same name
//!   bench_ours why DIR [TYPE]           each message it rejects, and where it stopped
//!   bench_ours jer FILE...              print each DL-DCCH message's value as JER
//!   bench_ours jerall DIR [TYPE]        each message's JER, flag and bits read, one a line
//!   bench_ours select OUT LIST          build a DL-DCCH corpus from the files named in LIST
//!
//! `bench`: every message is read into memory first. A round decodes each
//! message once and drops the value; the round, not each message, is timed.
//! Prints how many decoded, and the fastest and median round.
//!
//! `encode`: every message is decoded first; a round encodes each value once
//! into one reused 4096-byte writer (`pos` reset, so nothing is cleared or
//! allocated between messages, as asn1c's `*_encode_to_buffer` is timed), and
//! pads it to the octet (`pad_to_octet`).
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
extern crate vasn;

use std::collections::HashSet;
use std::hint::black_box;
use std::path::Path;
use std::time::Instant;

use ::DL_DCCH_Message::{DL_DCCH_MessageType_jer, DL_DCCH_Message_decode, DL_DCCH_Message_encode};
use vasn::uper::cursor::{BitReader, BitWriter};
use vasn::uper::format::Flg;

/// Runs `$f!(decode, jer, encode)` with `decode` the decoder of the channel message named
/// `$t`, so that each channel's loop is compiled with its decoder inlined.
macro_rules! with_decoder {
    ($t:expr, $f:ident) => {
        match $t {
            "DL-DCCH-Message" => $f!(::DL_DCCH_Message::DL_DCCH_Message_decode, ::DL_DCCH_Message::DL_DCCH_Message_jer, ::DL_DCCH_Message::DL_DCCH_Message_encode),
            "UL-DCCH-Message" => $f!(::UL_DCCH_Message::UL_DCCH_Message_decode, ::UL_DCCH_Message::UL_DCCH_Message_jer, ::UL_DCCH_Message::UL_DCCH_Message_encode),
            "PCCH-Message" => $f!(::PCCH_Message::PCCH_Message_decode, ::PCCH_Message::PCCH_Message_jer, ::PCCH_Message::PCCH_Message_encode),
            "BCCH-BCH-Message" => $f!(::BCCH_BCH_Message::BCCH_BCH_Message_decode, ::BCCH_BCH_Message::BCCH_BCH_Message_jer, ::BCCH_BCH_Message::BCCH_BCH_Message_encode),
            "BCCH-DL-SCH-Message" => $f!(::BCCH_DL_SCH_Message::BCCH_DL_SCH_Message_decode, ::BCCH_DL_SCH_Message::BCCH_DL_SCH_Message_jer, ::BCCH_DL_SCH_Message::BCCH_DL_SCH_Message_encode),
            "UL-CCCH-Message" => $f!(::UL_CCCH_Message::UL_CCCH_Message_decode, ::UL_CCCH_Message::UL_CCCH_Message_jer, ::UL_CCCH_Message::UL_CCCH_Message_encode),
            "DL-CCCH-Message" => $f!(::DL_CCCH_Message::DL_CCCH_Message_decode, ::DL_CCCH_Message::DL_CCCH_Message_jer, ::DL_CCCH_Message::DL_CCCH_Message_encode),
            t => {
                eprintln!("{t}: not one of the seven channel messages");
                std::process::exit(2);
            }
        }
    };
}

/// A whole message's encoding, padded to the octet.
macro_rules! enc_padded {
    ($e:path, $w:expr, $v:expr) => {
        $e($w, $v) && $w.pad_to_octet()
    };
}

const EXT: &str = "uper";

fn load(dir: &Path) -> Vec<Vec<u8>> {
    let mut names: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == EXT))
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

/// Encode capacity: above the largest message of any channel (1,813 bytes).
/// `encout` takes another from `ENC_CAP`; `ENC_CAP=exact` gives each message
/// a buffer exactly as long as base's encoding of it (the file of the same
/// name in `ENC_REF`), so that its last fields are written in the buffer's
/// last eight bytes.
const ENC_CAP: usize = 4096;

fn encode_bench<T>(dir: &Path, rounds: usize, decode: impl Fn(&[u8]) -> Option<T>,
                   encode: impl Fn(&mut BitWriter, &T) -> bool) {
    let vals: Vec<T> = load(dir).iter().filter_map(|m| decode(m)).collect();
    let mut w = BitWriter::with_capacity(ENC_CAP);
    let mut times = Vec::with_capacity(rounds);
    let mut ok = 0;
    for r in 0..=rounds {
        let t0 = Instant::now();
        let mut good = 0;
        for v in &vals {
            w.pos = 0;
            good += encode(&mut w, black_box(v)) as usize;
            black_box(&w.buf);
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
        "ours  {} values, {} encoded, min {:.1} ns/msg, median {:.1} ns/msg",
        vals.len(),
        ok,
        times[0] / n,
        times[rounds / 2] / n
    );
}

/// Each message of `dir` decoded and encoded again, written to `out` under its
/// own name; a message that does not decode, or whose value does not encode,
/// is written as an empty file.
fn encout<T>(dir: &Path, out: &Path, decode: impl Fn(&[u8]) -> Option<T>,
             encode: impl Fn(&mut BitWriter, &T) -> bool) {
    std::fs::create_dir_all(out).unwrap();
    let mut files: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    files.sort();
    let cap = std::env::var("ENC_CAP").ok();
    let refdir = std::env::var("ENC_REF").ok();
    let mut w = BitWriter::with_capacity(ENC_CAP);
    for f in files {
        let input = std::fs::read(&f).unwrap();
        match cap.as_deref() {
            None => {}
            Some("exact") => {
                let r = Path::new(refdir.as_deref().expect("ENC_REF")).join(f.file_name().unwrap());
                w = BitWriter::with_capacity(std::fs::metadata(r).unwrap().len() as usize);
            }
            Some(n) => w = BitWriter::with_capacity(n.parse().unwrap()),
        }
        w.pos = 0;
        let bytes = match decode(&input) {
            Some(v) if encode(&mut w, &v) => w.buf[..w.pos / 8].to_vec(),
            _ => Vec::new(),
        };
        std::fs::write(out.join(f.file_name().unwrap()), bytes).unwrap();
    }
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

/// Every message in `dir`, as `FILE BITS FLAG JER` or `FILE reject`: what a
/// change to the decoders must leave exactly as it was.
fn jerall(dir: &Path, decode: impl Fn(&mut BitReader) -> Option<(String, Flg)>) {
    let mut files: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    files.sort();
    for f in files {
        let input = std::fs::read(&f).unwrap();
        let mut r = BitReader::new(&input);
        let name = f.file_name().unwrap().to_string_lossy().into_owned();
        match decode(&mut r) {
            Some((s, flag)) => println!("{name} {} {:?} {s}", r.pos, flag),
            None => println!("{name} reject"),
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["bench", dir, rounds, ty @ ..] => {
            let (dir, rounds) = (Path::new(dir), rounds.parse().unwrap());
            macro_rules! go {
                ($d:path, $j:path, $e:path) => {
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
        ["encode", dir, rounds, ty @ ..] => {
            let (dir, rounds) = (Path::new(dir), rounds.parse().unwrap());
            macro_rules! go {
                ($d:path, $j:path, $e:path) => {
                    encode_bench(dir, rounds, |m| $d(&mut BitReader::new(m)).map(|(v, _)| v),
                                 |w, v| enc_padded!($e, w, v))
                };
            }
            with_decoder!(ty.first().copied().unwrap_or("DL-DCCH-Message"), go)
        }
        ["encout", dir, out, ty @ ..] => {
            let (dir, out) = (Path::new(dir), Path::new(out));
            macro_rules! go {
                ($d:path, $j:path, $e:path) => {
                    encout(dir, out, |m| $d(&mut BitReader::new(m)).map(|(v, _)| v),
                           |w, v| enc_padded!($e, w, v))
                };
            }
            with_decoder!(ty.first().copied().unwrap_or("DL-DCCH-Message"), go)
        }
        ["why", dir, ty @ ..] => {
            let dir = Path::new(dir);
            macro_rules! go {
                ($d:path, $j:path, $e:path) => {
                    why(dir, |r| $d(r))
                };
            }
            with_decoder!(ty.first().copied().unwrap_or("DL-DCCH-Message"), go)
        }
        ["jerall", dir, ty @ ..] => {
            let dir = Path::new(dir);
            macro_rules! go {
                ($d:path, $j:path, $e:path) => {
                    jerall(dir, |r| $d(r).map(|(v, f)| {
                        let mut s = String::new();
                        $j(&v, &mut s);
                        (s, f)
                    }))
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
                "usage: bench_ours bench DIR ROUNDS [TYPE] | encode DIR ROUNDS [TYPE] | encout DIR OUT [TYPE] | why DIR [TYPE] | jerall DIR [TYPE] | jer FILE.. | select OUT LIST"
            );
            std::process::exit(2);
        }
    }
}
