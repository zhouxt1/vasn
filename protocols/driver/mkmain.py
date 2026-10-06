#!/usr/bin/env python3
"""The driver's src/main.rs for TYPE (an ASN.1 type name, or several,
comma-separated) of a `vasnc --crate-dir` build; `bench` and `encode` time
the first.
  driver/mkmain.py TYPE[,TYPE...]   (run in driver/)

The driver, for tools/xcheck.py --driver and bench/:
  driver types                      the types it knows
  driver dec TYPE < hex-lines       per line `ok FLAG BITS REENCODING JER`
                                    or `err WHY` (`err padding: ...` when the
                                    rejection is for a padding bit)
  driver gen TYPE N [SEED]          N random values, encoded: `HEX BITS JER`
  driver bench DIR ROUNDS           decode DIR's .aper files whole, timed
  driver encode DIR ROUNDS          encode their values, timed"""
import sys, re, pathlib
tys = sys.argv[1].split(',')
ty = tys[0]
rn = re.sub(r'-', '_', ty)
rns = [re.sub(r'-', '_', t) for t in tys]
HELPERS = r'''fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }

/// X.691 11.1.3.1: an outermost value whose encoding is empty is sent as one
/// zero octet.
fn outer(w: &BitWriter) -> String {
    if w.pos == 0 { "00".into() } else { hex(&w.buf[..(w.pos + 7) / 8]) }
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    let s = s.trim();
    if s.len() % 2 != 0 { return None; }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok()).collect()
}

fn entropy(seed: u64, n: usize) -> Vec<u8> {
    // splitmix64 of the seed, so neighbouring seeds give unrelated streams
    let mut z = seed.wrapping_add(0x9e3779b97f4a7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    let mut x = (z ^ (z >> 31)) | 1;
    (0..n).map(|_| { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x as u8 }).collect()
}

macro_rules! run {
    ($dec:ident, $enc:ident, $jer:ident, $arb:ident) => {{
        let args: Vec<String> = std::env::args().collect();
        match args[1].as_str() {
            "dec" => {
                for line in std::io::stdin().lock().lines() {
                    let line = line.unwrap();
                    if line.trim().is_empty() { continue; }
                    let Some(b) = unhex(&line) else { println!("err not hex"); continue };
                    let _ = vasn::aper::cursor::take_bad_padding(&b);
                    let mut r = BitReader::new(&b);
                    match $dec(&mut r) {
                        None => match vasn::aper::cursor::take_bad_padding(&b) {
                            Some((at, _)) => println!("err padding: non-zero padding at bit {at} ({})", r.error()),
                            None => println!("err {}", r.error()),
                        },
                        Some((v, f)) => {
                            let mut w = BitWriter::with_capacity(8 * b.len() + (1 << 16));
                            let re = if $enc(&mut w, &v) { outer(&w) } else { "-".into() };
                            let mut j = String::new();
                            $jer(&v, &mut j);
                            let f = if matches!(f, Flg::SameVer) { "SameVer" } else { "DiffVer" };
                            println!("ok {f} {} {re} {j}", w.pos);
                        }
                    }
                }
            }
            "gen" => {
                let n: usize = args[3].parse().unwrap();
                let seed: u64 = args.get(4).map(|s| s.parse().unwrap()).unwrap_or(1);
                for i in 0..n {
                    let e = entropy(seed.wrapping_mul(1 << 32).wrapping_add(i as u64), 4096);
                    let v = $arb(&mut Gen::new(&e));
                    let mut w = BitWriter::with_capacity(1 << 24);
                    if !$enc(&mut w, &v) { println!("err encoder refused"); continue; }
                    let mut j = String::new();
                    $jer(&v, &mut j);
                    println!("{} {} {j}", outer(&w), w.pos);
                }
            }
            c => { eprintln!("unknown command {c}"); std::process::exit(2); }
        }
    }};
}


'''
src = f'''#![allow(non_snake_case, unused_imports)]
extern crate vasn;
{''.join(f"extern crate {r};" + chr(10) for r in rns)}use std::io::BufRead;
use vasn::arb::Gen;
use vasn::uper::cursor::{{BitReader, BitWriter}};
use vasn::uper::format::Flg;
{''.join(f"use {r}::*;" + chr(10) for r in rns)}
{HELPERS}fn main() {{
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("types") {{
{''.join(f'        println!("{t}");' + chr(10) for t in tys)}        return;
    }}
    // bench DIR ROUNDS / encode DIR ROUNDS: as bench_ours, on the `.aper`
    // files of DIR (every message read first; whole rounds timed)
    if matches!(args.get(1).map(String::as_str), Some("bench") | Some("encode")) {{
        let dir = std::path::Path::new(&args[2]);
        let rounds: usize = args[3].parse().unwrap();
        let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|x| x == "aper")).collect();
        names.sort();
        let msgs: Vec<Vec<u8>> = names.iter().map(|p| std::fs::read(p).unwrap()).collect();
        let mut times = Vec::new();
        if args[1] == "bench" {{
            let mut ok = 0;
            for r in 0..=rounds {{
                let t = std::time::Instant::now();
                let mut k = 0;
                for m in &msgs {{
                    let mut rd = BitReader::new(m);
                    if let Some(v) = {rn}_decode_complete(&mut rd) {{ k += 1; std::hint::black_box(v); }}
                }}
                if r > 0 {{ times.push(t.elapsed().as_nanos() as f64 / msgs.len() as f64); }}
                ok = k;
            }}
            times.sort_by(|a, b| a.partial_cmp(b).unwrap());
            println!("ours  {{}} messages, {{}} decoded, min {{:.1}} ns/msg, median {{:.1}} ns/msg",
                     msgs.len(), ok, times[0], times[times.len() / 2]);
        }} else {{
            let vals: Vec<_> = msgs.iter().filter_map(|m| {rn}_decode_complete(&mut BitReader::new(m)).map(|x| x.0)).collect();
            let cap = msgs.iter().map(|m| m.len()).max().unwrap_or(0) * 2 + 4096;
            let mut w = BitWriter::with_capacity(cap);
            let mut ok = 0;
            for r in 0..=rounds {{
                let t = std::time::Instant::now();
                let mut k = 0;
                for v in &vals {{
                    w.pos = 0;
                    if {rn}_encode_complete(&mut w, v) {{ k += 1; }}
                    std::hint::black_box(&w.buf);
                }}
                if r > 0 {{ times.push(t.elapsed().as_nanos() as f64 / vals.len() as f64); }}
                ok = k;
            }}
            times.sort_by(|a, b| a.partial_cmp(b).unwrap());
            println!("ours  {{}} values, {{}} encoded, min {{:.1}} ns/msg, median {{:.1}} ns/msg",
                     vals.len(), ok, times[0], times[times.len() / 2]);
        }}
        return;
    }}
    match args.get(2).map(String::as_str) {{
{''.join(f'        Some("{t}") => run!({r}_decode_complete, {r}_encode_complete, {r}_jer, {r}_arb),' + chr(10) for t, r in zip(tys, rns))}        _ => {{
            eprintln!("usage: driver types | dec TYPE < hex-lines | gen TYPE N [SEED]");
            std::process::exit(2);
        }}
    }}
}}
'''
pathlib.Path('src').mkdir(exist_ok=True)
pathlib.Path('src/main.rs').write_text(src)
