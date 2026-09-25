// SIZE with `ub` >= 64K (X.691 11.9.4.2): the general length determinant,
// fragmenting at 16K bits, octets or components (11.9.3.8).
//
//   cargo run -p vuper-examples --bin frag             the checks below, one line each
//   cargo run -p vuper-examples --bin frag -- --cases  `name hex` per value, to diff against pycrate:
//       tools/frag_pycrate.py prints the same values

use vuperx::cursor::*;
use vuperx::format::*;
use vuperx::frag::LenHead;
use vuper_examples::frag::*;

// Test driver only, so plain Rust, outside `verus!`.

fn hex(w: &BitWriter) -> String {
    w.buf[..(w.pos + 7) / 8].iter().map(|b| format!("{b:02x}")).collect()
}

/// bit i = ((i * 7 + k) % 5 == 0), the pattern tools/frag_pycrate.py uses
fn bits(n: usize, k: usize) -> Vec<bool> {
    (0..n).map(|i| (i * 7 + k) % 5 == 0).collect()
}

fn octets(n: usize) -> Vec<u8> {
    (0..n).map(|i| ((i * 31 + 7) % 256) as u8).collect()
}

fn check(label: &str, ok: bool, fails: &mut usize) {
    println!("{} {label}", if ok { "ok  " } else { "FAIL" });
    if !ok { *fails += 1; }
}

/// Encode, print `name hex`, and check that the decoder gives back the same
/// value, same version, having read every bit written.
macro_rules! case {
    ($cases:expr, $fails:expr, $name:expr, $enc:ident, $dec:ident, $v:expr) => {{
        let v = $v;
        let mut w = BitWriter::with_capacity(1 << 18);
        let ok = $enc(&mut w, &v);
        if $cases {
            println!("{} {}", $name, hex(&w));
        } else {
            let mut r = BitReader::new(&w.buf[..(w.pos + 7) / 8]);
            let back = $dec(&mut r);
            let good = ok && r.pos == w.pos
                && matches!(&back, Some((b, Flg::SameVer)) if *b == v);
            check(&format!("{} round trip, {} bits", $name, w.pos), good, &mut $fails);
        }
    }};
}

fn head(w: &mut BitWriter, h: LenHead) { assert!(w.write_lh(h)); }

fn put_bits(w: &mut BitWriter, n: usize) { for b in bits(n, 0) { assert!(w.write_bool(b)); } }

fn rejects(label: &str, w: &BitWriter, dec: fn(&mut BitReader) -> bool, fails: &mut usize) {
    let mut r = BitReader::new(&w.buf[..(w.pos + 7) / 8]);
    let accepted = dec(&mut r);
    check(&format!("rejects {label}"), !accepted, fails);
    if !accepted { println!("       {}", r.error()); }
}

fn bigbits(r: &mut BitReader) -> bool { BigBits_decode(r).is_some() }
fn fixedbig(r: &mut BitReader) -> bool { FixedBig_decode(r).is_some() }

fn main() {
    let cases = std::env::args().any(|a| a == "--cases");
    let mut fails = 0usize;
    for n in [1, 127, 128, 16383, 16384, 16385, 32768, 49152, 65535, 65536] {
        case!(cases, fails, format!("BigBits/{n}"), BigBits_encode, BigBits_decode, bits(n, 0));
    }
    case!(cases, fails, "FixedBig/65536", FixedBig_encode, FixedBig_decode, bits(65536, 3));
    for n in [0, 1, 16384, 65536, 81921, 100000] {
        case!(cases, fails, format!("BigOctets/{n}"), BigOctets_encode, BigOctets_decode, octets(n));
    }
    for n in [1, 16384, 20000, 65536] {
        case!(cases, fails, format!("BigList/{n}"), BigList_encode, BigList_decode,
              (0..n).map(|i| (i % 8) as i64).collect::<Vec<_>>());
    }
    for n in [3, 16385] {
        case!(cases, fails, format!("NibbleList/{n}"), NibbleList_encode, NibbleList_decode,
              (0..n).map(|i| bits(4, i)).collect::<Vec<_>>());
    }
    for n in [2, 16384] {
        case!(cases, fails, format!("ExtList/{n}"), ExtList_encode, ExtList_decode,
              (0..n).map(|i| Ext {
                  a: i % 2 == 0,
                  group0: if i % 4 == 0 { Some(Ext_ext0 { b: Some(i % 3 == 0) }) } else { None },
              }).collect::<Vec<_>>());
    }
    if cases { return; }

    // what the standard spells out
    let mut w = BitWriter::with_capacity(16);
    assert!(BigBits_encode(&mut w, &vec![true]));
    check("BigBits [1] is 00000001 1: the length is n, not n - lb (11.9.4.2)",
          hex(&w) == "0180" && w.pos == 9, &mut fails);
    let mut w = BitWriter::with_capacity(1 << 14);
    assert!(BigBits_encode(&mut w, &bits(16384, 0)));
    check("16K bits: 11 000001, the bits, then a zero length octet (11.9.3.8.3 NOTE)",
          w.buf[0] == 0xc1 && w.pos == 8 + 16384 + 8 && w.buf[(8 + 16384) / 8] == 0, &mut fails);

    // what a decoder has to refuse
    let mut w = BitWriter::with_capacity(1 << 14);
    head(&mut w, LenHead::Frag(1)); put_bits(&mut w, 16384);
    head(&mut w, LenHead::Frag(1)); put_bits(&mut w, 16384);
    head(&mut w, LenHead::Final(0));
    rejects("two 1-block fragments, where 11.9.3.8.1 requires one of 2", &w, bigbits, &mut fails);

    let mut w = BitWriter::with_capacity(16);
    assert!(w.write_bool(true)); assert!(w.write_bool(false)); assert!(w.write_uint(14, 5));
    put_bits(&mut w, 5);
    rejects("length 5 in the 2-octet form", &w, bigbits, &mut fails);

    let mut w = BitWriter::with_capacity(16);
    head(&mut w, LenHead::Final(0));
    rejects("0 bits, below SIZE (1..65536)", &w, bigbits, &mut fails);

    let mut w = BitWriter::with_capacity(1 << 14);
    head(&mut w, LenHead::Frag(4)); put_bits(&mut w, 65536);
    head(&mut w, LenHead::Final(1)); put_bits(&mut w, 1);
    rejects("65537 bits, above SIZE (1..65536)", &w, bigbits, &mut fails);

    let mut w = BitWriter::with_capacity(1 << 14);
    head(&mut w, LenHead::Frag(3)); put_bits(&mut w, 49152);
    head(&mut w, LenHead::Final(16383)); put_bits(&mut w, 16383);
    rejects("65535 bits as a FixedBig (SIZE (65536))", &w, fixedbig, &mut fails);

    // the old encoding: a 16-bit n - lb, here 0 for one bit
    let mut w = BitWriter::with_capacity(16);
    assert!(w.write_uint(16, 0)); put_bits(&mut w, 1);
    rejects("the pre-11.9.4.2 encoding of [1] (16-bit n - lb)", &w, bigbits, &mut fails);

    let mut w = BitWriter::with_capacity(1 << 14);
    assert!(BigBits_encode(&mut w, &bits(20000, 0)));
    let cut = BitWriter { buf: w.buf[..1000].to_vec(), pos: 8000 };
    rejects("20000 bits, truncated to 1000 octets", &cut, bigbits, &mut fails);

    println!("{}", if fails == 0 { "all checks passed".to_string() } else { format!("{fails} FAILED") });
    if fails > 0 { std::process::exit(1); }
}

