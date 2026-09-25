// OPTIONAL fields: check the presence bitmap lands in front of the fields and
// that both present and absent values round-trip.

use vstd::prelude::*;
use vuperx::cursor::*;
use vuper_examples::optional::*;

verus! {

#[verifier::external_body]
fn show(label: &str, w: &BitWriter) {
    print!("{label}: {} bits ->", w.pos);
    let n = (w.pos + 7) / 8;
    for i in 0..n {
        print!(" {:02x}", w.buf[i]);
    }
    print!("   ");
}

#[verifier::external_body]
fn main() {
    // Two ::= SEQUENCE { a INTEGER(0..15), b Colour OPTIONAL,
    //                    c BOOLEAN, d INTEGER(0..3) OPTIONAL }
    // preamble is 2 bits (b, d), then a=4, b=2 if present, c=1, d=2 if present.
    let m1 = Two { a: 10, b: Some(Colour::green), c: true, d: None };
    let mut w = BitWriter::with_capacity(8);
    let ok = Two_encode(&mut w, &m1);
    show("b present, d absent", &w);
    println!("ok={ok}  (expect 9 bits: 10 1010 01 1 = a9 80)");
    let mut r = BitReader::new(&w.buf);
    match Two_decode(&mut r) {
        Some((b, _)) => println!("                     decoded {b:?} -> {}",
                            if b == m1 { "MATCH" } else { "MISMATCH" }),
        None => println!("                     decode failed"),
    }

    let m2 = Two { a: 10, b: None, c: true, d: Some(3) };
    let mut w2 = BitWriter::with_capacity(8);
    let ok2 = Two_encode(&mut w2, &m2);
    show("b absent, d present", &w2);
    println!("ok={ok2}  (expect 9 bits: 01 1010 1 11)");
    let mut r2 = BitReader::new(&w2.buf);
    match Two_decode(&mut r2) {
        Some((b, _)) => println!("                     decoded {b:?} -> {}",
                            if b == m2 { "MATCH" } else { "MISMATCH" }),
        None => println!("                     decode failed"),
    }

    let m3 = Two { a: 15, b: Some(Colour::blue), c: false, d: Some(1) };
    let mut w3 = BitWriter::with_capacity(8);
    let _ = Two_encode(&mut w3, &m3);
    show("both present       ", &w3);
    let mut r3 = BitReader::new(&w3.buf);
    println!("round trip {}",
             match Two_decode(&mut r3) { Some((b, _)) if b == m3 => "MATCH", _ => "MISMATCH" });

    let m4 = AllOpt { x: None, y: None };
    let mut w4 = BitWriter::with_capacity(8);
    let _ = AllOpt_encode(&mut w4, &m4);
    show("both absent        ", &w4);
    let mut r4 = BitReader::new(&w4.buf);
    println!("round trip {}  (expect just the 2 preamble bits)",
             match AllOpt_decode(&mut r4) { Some((b, _)) if b == m4 => "MATCH", _ => "MISMATCH" });

    // Pinned: preamble 1 (c present), a no bits, b = 1, c no bits -> 11
    let pn = Pinned { a: 5, b: true, c: Some(0) };
    let mut w9 = BitWriter::with_capacity(8);
    let _ = Pinned_encode(&mut w9, &pn);
    show("pinned", &w9);
    println!("(expect 2 bits: 11 = c0)");
    let mut r9 = BitReader::new(&w9.buf);
    match Pinned_decode(&mut r9) {
        Some((b, _)) => println!("                     decoded {b:?} -> {}",
                            if b == pn { "MATCH" } else { "MISMATCH" }),
        None => println!("                     decode failed"),
    }

    // Filter at its defaults: preamble 00, then on = 1 -> 001
    // Filter off defaults: preamble 11, off = dB1 (index 2, "10"), maxCID 3
    // (3-1 in 4 bits, "0010"), on = 0 -> 11 10 0010 0
    for (f, note) in [
        (Filter { off: Q::dB0, maxCID: 15, on: true }, "(expect 3 bits: 001 = 20)"),
        (Filter { off: Q::dB1, maxCID: 3, on: false }, "(expect 9 bits: 11 10 0010 0 = e2 00)"),
    ] {
        let mut w = BitWriter::with_capacity(8);
        let _ = Filter_encode(&mut w, &f);
        show("filter", &w);
        println!("{note}");
        let mut r = BitReader::new(&w.buf);
        match Filter_decode(&mut r) {
            Some((b, _)) => println!("                     decoded {b:?} -> {}",
                                if b == f { "MATCH" } else { "MISMATCH" }),
            None => println!("                     decode failed"),
        }
    }
    // `off` marked present but carrying the default dB0 (index 1): 1 0 01 1.
    // A second encoding of the all-default value, so it must be rejected.
    let bad: [u8; 1] = [0b1001_1000];
    let mut rb = BitReader::new(&bad);
    println!("present default     : {}",
             if Filter_decode(&mut rb).is_none() { "rejected" } else { "ACCEPTED -- should not be" });

    // Refd: preamble 1 (o present), k no bits, b = 0, o no bits -> 10
    let rd = Refd { k: 1, b: false, o: Some(1) };
    let mut wr = BitWriter::with_capacity(8);
    let _ = Refd_encode(&mut wr, &rd);
    show("refd", &wr);
    println!("(expect 2 bits: 10 = 80)");
    let mut rr = BitReader::new(&wr.buf);
    match Refd_decode(&mut rr) {
        Some((b, _)) => println!("                     decoded {b:?} -> {}",
                            if b == rd { "MATCH" } else { "MISMATCH" }),
        None => println!("                     decode failed"),
    }
}

} // verus!
