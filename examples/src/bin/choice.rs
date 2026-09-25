// CHOICE on the wire: an index over the alternatives, then the chosen one.

use vstd::prelude::*;
use vuperx::cursor::*;
use vuper_examples::choice::*;
use vuperx::opt::Null;

verus! {

#[verifier::external_body]
fn show(label: &str, w: &BitWriter, note: &str) {
    print!("{label:<24} {:>2} bits ->", w.pos);
    let n = (w.pos + 7) / 8;
    for i in 0..n { print!(" {:02x}", w.buf[i]); }
    println!("   {note}");
}

#[verifier::external_body]
fn main() {
    // Shape has 3 alternatives -> 2-bit index
    for (v, note) in [
        (Shape::flag(true),          "index 00, bool 1"),
        (Shape::count(10),           "index 01, 4 bits 1010"),
        (Shape::tint(Colour::blue),  "index 10, 2 bits 10"),
    ] {
        let mut w = BitWriter::with_capacity(8);
        let _ = Shape_encode(&mut w, &v);
        show(&format!("{v:?}"), &w, note);
        let mut r = BitReader::new(&w.buf);
        match Shape_decode(&mut r) {
            Some((b, _)) => println!("{:>28} round trip {}", "", if b == v { "MATCH" } else { "MISMATCH" }),
            None => println!("{:>28} decode failed", ""),
        }
    }

    // Pick has 2 alternatives -> 1-bit index
    let p = Pick::no(Colour::green);
    let mut w2 = BitWriter::with_capacity(8);
    let _ = Pick_encode(&mut w2, &p);
    show(&format!("{p:?}"), &w2, "index 1, 2 bits 01");
    let mut r2 = BitReader::new(&w2.buf);
    println!("{:>28} round trip {}", "",
             match Pick_decode(&mut r2) { Some((b, _)) if b == p => "MATCH", _ => "MISMATCH" });

    // Only has 1 alternative -> no index bits at all
    let o = Only::sole(7);
    let mut w3 = BitWriter::with_capacity(8);
    let _ = Only_encode(&mut w3, &o);
    show(&format!("{o:?}"), &w3, "no index, just 4 bits 0111");
    let mut r3 = BitReader::new(&w3.buf);
    println!("{:>28} round trip {}", "",
             match Only_decode(&mut r3) { Some((b, _)) if b == o => "MATCH", _ => "MISMATCH" });

    // NULL as an alternative: the SetupRelease idiom, release carries no bits
    for (v, note) in [
        (Setting::release(Null), "index 0, NULL contributes nothing"),
        (Setting::setup(9),      "index 1, then 4 bits 1001"),
    ] {
        let mut w = BitWriter::with_capacity(8);
        let _ = Setting_encode(&mut w, &v);
        show(&format!("{v:?}"), &w, note);
        let mut r = BitReader::new(&w.buf);
        println!("{:>28} round trip {}", "",
                 match Setting_decode(&mut r) { Some((b, _)) if b == v => "MATCH", _ => "MISMATCH" });
    }

    // an index past the last alternative must be rejected
    let mut bad = BitWriter::with_capacity(8);
    let _ = bad.write_uint(2, 3);   // index 3, but Shape only has 0..2
    let _ = bad.write_uint(4, 0);
    let mut rb = BitReader::new(&bad.buf);
    println!("out-of-range CHOICE index rejected: {}", Shape_decode(&mut rb).is_none());
    // 3 alternatives -> 2-bit index. `ids` is 01, then its count in 1..3 as
    // 2 bits of n-1, then 4 bits per element: 01 01 0001 1111 -> 51 f0.
    for (v, note) in [
        (Carry::none(Null),                      "index 00, nothing"),
        (Carry::ids(vec![1, 15]),                "index 01, count 01, 0001 1111"),
        (Carry::bits(vec![true, false, true, true]), "index 10, 1011"),
    ] {
        let mut w = BitWriter::with_capacity(8);
        let _ = Carry_encode(&mut w, &v);
        show(&format!("{v:?}"), &w, note);
        let mut r = BitReader::new(&w.buf);
        match Carry_decode(&mut r) {
            Some((b, _)) => println!("{:>28} round trip {}", "", if b == v { "MATCH" } else { "MISMATCH" }),
            None => println!("{:>28} decode failed", ""),
        }
    }

    // Extensible: 0 + root index + alternative, or 1 + 7-bit index + open type.
    for (v, note) in [
        (Pet::cat(true),              "0, index 0, bool 1"),
        (Pet::dog(9),                 "0, index 1, 1001"),
        (Pet::fish(Colour::blue),     "1, 0000000, len 1, 10 padded"),
        (Pet::bird(false),            "1, 0000001, len 1, 0 padded"),
        (Pet::Unknown(5, vec![0xab, 0xcd]), "1, 0000101, len 2, ab cd"),
    ] {
        let mut w = BitWriter::with_capacity(8);
        let _ = Pet_encode(&mut w, &v);
        show(&format!("{v:?}"), &w, note);
        let mut r = BitReader::new(&w.buf);
        match Pet_decode(&mut r) {
            Some((b, f)) => println!("{:>28} round trip {}  flag {:?}", "",
                                     if b == v { "MATCH" } else { "MISMATCH" }, f),
            None => println!("{:>28} decode failed", ""),
        }
    }
    // A newer peer's alternative 5: kept, octets and all, and re-encoded to
    // exactly the bits it came from.
    let newer: [u8; 4] = [0x85, 0x02, 0xab, 0xcd];
    let mut r = BitReader::new(&newer);
    match Pet_decode(&mut r) {
        Some((v, f)) => {
            let mut w = BitWriter::with_capacity(8);
            let _ = Pet_encode(&mut w, &v);
            println!("newer peer: {v:?}  flag {f:?}  re-encodes {}",
                     if w.buf[..4] == newer[..] && w.pos == 32 { "IDENTICALLY" } else { "DIFFERENTLY" });
        }
        None => println!("newer peer: decode failed"),
    }
    // Index 64 needs 11.6's long form, which is not built: rejected.
    let long_form: [u8; 3] = [0xc0, 0x00, 0x00];
    let mut r = BitReader::new(&long_form);
    println!("long-form index: {}", if Pet_decode(&mut r).is_none() { "rejected" } else { "ACCEPTED" });

    for (v, note) in [
        (Lone::only(true),        "0, no index, bool 1"),
        (Lone::Unknown(0, vec![]), "1, 0000000, len 0"),
    ] {
        let mut w = BitWriter::with_capacity(8);
        let _ = Lone_encode(&mut w, &v);
        show(&format!("{v:?}"), &w, note);
        let mut r = BitReader::new(&w.buf);
        match Lone_decode(&mut r) {
            Some((b, f)) => println!("{:>28} round trip {}  flag {:?}", "",
                                     if b == v { "MATCH" } else { "MISMATCH" }, f),
            None => println!("{:>28} decode failed", ""),
        }
    }
}

} // verus!
