// SEQUENCE OF, BIT STRING and OCTET STRING on the wire.

use vstd::prelude::*;
use vuperx::cursor::*;
use vuperx::opt::Null;
use vuper_examples::lists::*;

verus! {

#[verifier::external_body]
fn show(label: &str, w: &BitWriter, note: &str) {
    print!("{label:<22} {:>3} bits ->", w.pos);
    let n = (w.pos + 7) / 8;
    for i in 0..n { print!(" {:02x}", w.buf[i]); }
    println!("   {note}");
}

#[verifier::external_body]
fn main() {
    // ColourList ::= SEQUENCE (SIZE(1..8)) OF Colour
    // length range 1..8 is 8 values -> 3 bits; Colour is 3 values -> 2 bits
    let l = vec![Colour::red, Colour::blue];
    let mut w = BitWriter::with_capacity(8);
    let ok = ColourList_encode(&mut w, &l);
    show("ColourList [red,blue]", &w, "expect 7 bits: 001 00 10");
    let mut r = BitReader::new(&w.buf);
    match ColourList_decode(&mut r) {
        Some((b, _)) => println!("{:>26} round trip {}", "", if b == l { "MATCH" } else { "MISMATCH" }),
        None => println!("{:>26} decode failed", ""),
    }
    let _ = ok;

    // Triple ::= SEQUENCE (SIZE(3)) OF Colour -- fixed size, no length determinant
    let t = vec![Colour::green, Colour::green, Colour::blue];
    let mut w2 = BitWriter::with_capacity(8);
    let _ = Triple_encode(&mut w2, &t);
    show("Triple (fixed 3)", &w2, "expect 6 bits, no length field");
    let mut r2 = BitReader::new(&w2.buf);
    println!("{:>26} round trip {}", "",
             match Triple_decode(&mut r2) { Some((b, _)) if b == t => "MATCH", _ => "MISMATCH" });

    // Mask ::= BIT STRING (SIZE(10))
    let m = vec![true, false, true, true, false, false, false, true, true, false];
    let mut w3 = BitWriter::with_capacity(8);
    let _ = Mask_encode(&mut w3, &m);
    show("Mask (BIT STRING 10)", &w3, "expect 10 bits: 1011000110");
    let mut r3 = BitReader::new(&w3.buf);
    println!("{:>26} round trip {}", "",
             match Mask_decode(&mut r3) { Some((b, _)) if b == m => "MATCH", _ => "MISMATCH" });

    // Key ::= OCTET STRING (SIZE(4))
    let k = vec![0xdeu8, 0xad, 0xbe, 0xef];
    let mut w4 = BitWriter::with_capacity(8);
    let _ = Key_encode(&mut w4, &k);
    show("Key (OCTET STRING 4)", &w4, "expect 32 bits: de ad be ef");
    let mut r4 = BitReader::new(&w4.buf);
    println!("{:>26} round trip {}", "",
             match Key_decode(&mut r4) { Some((b, _)) if b == k => "MATCH", _ => "MISMATCH" });

    // VarBits ::= BIT STRING (SIZE(0..16)) -- 17 lengths -> 5-bit determinant
    let v = vec![true, true, false];
    let mut w5 = BitWriter::with_capacity(8);
    let _ = VarBits_encode(&mut w5, &v);
    show("VarBits (0..16), 3 set", &w5, "expect 8 bits: 00011 110");
    let mut r5 = BitReader::new(&w5.buf);
    println!("{:>26} round trip {}", "",
             match VarBits_decode(&mut r5) { Some((b, _)) if b == v => "MATCH", _ => "MISMATCH" });

    // NibbleList: count in 1..2 (1 bit), then 4 bits each: 1 1010 1111 -> d7 80
    let nl = vec![vec![true, false, true, false], vec![true, true, true, true]];
    let mut w5 = BitWriter::with_capacity(8);
    let _ = NibbleList_encode(&mut w5, &nl);
    show("NibbleList", &w5, "expect 9 bits: 1 1010 1111");
    let mut r5 = BitReader::new(&w5.buf);
    println!("{:>26} round trip {}", "",
             match NibbleList_decode(&mut r5) { Some((b, _)) if b == nl => "MATCH", _ => "MISMATCH" });

    // Grid: fixed 2 ColourLists, each 3 bits of count-1 then 2 bits each:
    // 000 00 | 001 10 01 -> 01 90
    let g = vec![vec![Colour::red], vec![Colour::blue, Colour::green]];
    let mut w6 = BitWriter::with_capacity(8);
    let _ = Grid_encode(&mut w6, &g);
    show("Grid", &w6, "expect 12 bits: 00000 0011001");
    let mut r6 = BitReader::new(&w6.buf);
    println!("{:>26} round trip {}", "",
             match Grid_decode(&mut r6) { Some((b, _)) if b == g => "MATCH", _ => "MISMATCH" });

    // TaggedList: count in 0..3 (2 bits), then tag, VarBits' count in 0..16
    // (5 bits) and its bits: 01 1 00011 101 -> 63 a0
    let tl = vec![Tagged { tag: true, bits: vec![true, false, true] }];
    let mut w7 = BitWriter::with_capacity(8);
    let _ = TaggedList_encode(&mut w7, &tl);
    show("TaggedList", &w7, "expect 11 bits: 01 1 00011 101");
    let mut r7 = BitReader::new(&w7.buf);
    println!("{:>26} round trip {}", "",
             match TaggedList_decode(&mut r7) { Some((b, _)) if b == tl => "MATCH", _ => "MISMATCH" });

    // AltList: count 1 bit, a(true) is 0 1, Unknown(3, [ff]) is 1 0000011
    // 00000001 11111111: 1 01 1000001100000001 11111111 -> b0 60 3f e0
    let al = vec![Alt::a(true), Alt::Unknown(3, vec![0xff])];
    let mut w8 = BitWriter::with_capacity(8);
    let _ = AltList_encode(&mut w8, &al);
    show("AltList", &w8, "expect 27 bits");
    let mut r8 = BitReader::new(&w8.buf);
    println!("{:>26} round trip {}", "",
             match AltList_decode(&mut r8) { Some((b, _)) if b == al => "MATCH", _ => "MISMATCH" });

    // Blob: one octet of length, then the octets -> 02 12 34
    let bl = vec![0x12u8, 0x34];
    let mut w9 = BitWriter::with_capacity(8);
    let _ = Blob_encode(&mut w9, &bl);
    show("Blob (unsized)", &w9, "expect 24 bits: 02 12 34");
    let mut r9 = BitReader::new(&w9.buf);
    println!("{:>26} round trip {}", "",
             match Blob_decode(&mut r9) { Some((b, _)) if b == bl => "MATCH", _ => "MISMATCH" });

    // Holder: preamble 0 (inner absent), tag 1, data 00000001 aa, bits 101
    // -> 21 bits: 40 6a a8
    let h = Holder { tag: true, data: vec![0xaa], inner: None, bits: vec![true, false, true] };
    let mut w10 = BitWriter::with_capacity(8);
    let _ = Holder_encode(&mut w10, &h);
    show("Holder", &w10, "expect 21 bits: 0 1 00000001 aa 101");
    let mut r10 = BitReader::new(&w10.buf);
    println!("{:>26} round trip {}", "",
             match Holder_decode(&mut r10) { Some((b, _)) if b == h => "MATCH", _ => "MISMATCH" });

    // Cfg: preamble 1, a = setup (index 1) then Key's 4 octets, b = release
    // (index 0) -> 35 bits: c0 40 80 c1 00
    let c = Cfg { a: Some(SetupRelease_Key::setup(vec![1, 2, 3, 4])),
                  b: SetupRelease_Colour::release(Null) };
    let mut w11 = BitWriter::with_capacity(8);
    let _ = Cfg_encode(&mut w11, &c);
    show("Cfg (SetupRelease)", &w11, "expect 35 bits");
    let mut r11 = BitReader::new(&w11.buf);
    println!("{:>26} round trip {}", "",
             match Cfg_decode(&mut r11) { Some((b, _)) if b == c => "MATCH", _ => "MISMATCH" });
}

} // verus!
