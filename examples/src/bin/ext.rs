// Extensible SEQUENCE: check the extension bit, the count, the bitmap and the
// open types land where X.691 19 says, and that all three decoder branches
// round-trip.

use vstd::prelude::*;
use vasn::uper::cursor::*;
use vasn_examples::ext::*;

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
fn roundtrip(label: &str, m: &Ext) {
    let mut w = BitWriter::with_capacity(16);
    let ok = Ext_encode(&mut w, m);
    show(label, &w);
    if !ok {
        println!("ENCODE FAILED");
        return;
    }
    let mut r = BitReader::new(w.buf.as_slice());
    match Ext_decode(&mut r) {
        Some((v, f)) => {
            let same = v.a == m.a && v.b == m.b && v.c == m.c;
            println!("{}  flag {:?}", if same { "round trip MATCH" } else { "MISMATCH" }, f);
        },
        None => println!("DECODE FAILED"),
    }
}

#[verifier::external_body]
fn roundtrip_room(label: &str, m: &Room) {
    let mut w = BitWriter::with_capacity(16);
    let ok = Room_encode(&mut w, m);
    show(label, &w);
    if !ok { println!("ENCODE FAILED"); return; }
    let mut r = BitReader::new(w.buf.as_slice());
    match Room_decode(&mut r) {
        Some((v, f)) => println!("{}  flag {:?}",
            if v.x == m.x && v.y == m.y { "round trip MATCH" } else { "MISMATCH" }, f),
        None => println!("DECODE FAILED"),
    }
}

#[verifier::external_body]
fn roundtrip_grouped(label: &str, m: &Grouped) {
    let mut w = BitWriter::with_capacity(16);
    let ok = Grouped_encode(&mut w, m);
    show(label, &w);
    if !ok { println!("ENCODE FAILED"); return; }
    let mut r = BitReader::new(w.buf.as_slice());
    match Grouped_decode(&mut r) {
        Some((v, f)) => println!("{}  flag {:?}",
            if v.n == m.n && v.p == m.p && v.group1 == m.group1 { "round trip MATCH" }
            else { "MISMATCH" }, f),
        None => println!("DECODE FAILED"),
    }
}

#[verifier::external_body]
fn roundtrip_one(label: &str, m: &One) {
    let mut w = BitWriter::with_capacity(16);
    let ok = One_encode(&mut w, m);
    show(label, &w);
    if !ok { println!("ENCODE FAILED"); return; }
    let mut r = BitReader::new(w.buf.as_slice());
    match One_decode(&mut r) {
        Some((v, f)) => println!("{}  flag {:?}",
            if v.k == m.k && v.v == m.v { "round trip MATCH" } else { "MISMATCH" }, f),
        None => println!("DECODE FAILED"),
    }
}

#[verifier::external_body]
fn roundtrip_listed(label: &str, m: &Listed) {
    let mut w = BitWriter::with_capacity(16);
    let ok = Listed_encode(&mut w, m);
    show(label, &w);
    if !ok { println!("ENCODE FAILED"); return; }
    let mut r = BitReader::new(w.buf.as_slice());
    match Listed_decode(&mut r) {
        Some((v, f)) => println!("{}  flag {:?}",
            if v.ids == m.ids && v.tag == m.tag && v.more == m.more { "round trip MATCH" }
            else { "MISMATCH" }, f),
        None => println!("DECODE FAILED"),
    }
}

#[verifier::external_body]
fn roundtrip_roomlist(label: &str, m: &RoomList) {
    let mut w = BitWriter::with_capacity(16);
    let ok = RoomList_encode(&mut w, m);
    show(label, &w);
    if !ok { println!("ENCODE FAILED"); return; }
    let mut r = BitReader::new(w.buf.as_slice());
    match RoomList_decode(&mut r) {
        Some((v, f)) => println!("{}  flag {:?}",
            if v.ids == m.ids { "round trip MATCH" } else { "MISMATCH" }, f),
        None => println!("DECODE FAILED"),
    }
}

#[verifier::external_body]
fn roundtrip_carrier(label: &str, m: &Carrier) {
    let mut w = BitWriter::with_capacity(16);
    let ok = Carrier_encode(&mut w, m);
    show(label, &w);
    if !ok { println!("ENCODE FAILED"); return; }
    let mut r = BitReader::new(w.buf.as_slice());
    match Carrier_decode(&mut r) {
        Some((v, f)) => println!("{}  flag {:?}",
            if v.a == m.a && v.xs == m.xs && v.group1 == m.group1 { "round trip MATCH" }
            else { "MISMATCH" }, f),
        None => println!("DECODE FAILED"),
    }
}

#[verifier::external_body]
fn roundtrip_allopt(label: &str, m: &AllOpt) {
    let mut w = BitWriter::with_capacity(16);
    let ok = AllOpt_encode(&mut w, m);
    show(label, &w);
    if !ok { println!("ENCODE FAILED"); return; }
    let mut r = BitReader::new(w.buf.as_slice());
    match AllOpt_decode(&mut r) {
        Some((v, f)) => println!("{}  flag {:?}",
            if v.k == m.k && v.group0 == m.group0 { "round trip MATCH" } else { "MISMATCH" }, f),
        None => println!("DECODE FAILED"),
    }
}

#[verifier::external_body]
fn main() {
    // Ext ::= SEQUENCE { a BOOLEAN, ..., b INTEGER (0..255), c BOOLEAN }
    println!("== extensible SEQUENCE (X.691 19) ==");

    // No addition present: extension bit 0, then the root. Two bits.
    roundtrip("none present     ", &Ext { a: true, b: None, c: None });

    // b present. 1 (ext) + 1 (a) + 7 (nsld 2) + 2 (bitmap) + 8 (open type
    // length: one octet) + 8 (content) = 27 bits.
    roundtrip("b present        ", &Ext { a: true, b: Some(5), c: None });

    // c present: a BOOLEAN inside an open type still occupies a whole octet
    // (11.1.3.1), so the length reads 1 and the content is padded.
    roundtrip("c present        ", &Ext { a: false, b: None, c: Some(true) });

    roundtrip("both present     ", &Ext { a: true, b: Some(255), c: Some(false) });

    // A message from a peer that knows a third addition we have never heard
    // of: count 3, bitmap 001, and one open type we must step over. The value
    // that comes back has both of our additions absent -- which VUPER would
    // reject -- and the flag must be DiffVer.
    //   bit  0      1  (extension bit set)
    //   bit  1      0  (root: a = false)
    //   bits 2-8    0000010  (normally small 3, i.e. 0 then six bits of 3-1)
    //   bits 9-11   001      (bitmap: our two absent, their one present)
    //   bits 12-19  00000001 (open type: one octet)
    //   bits 20-27  00000000 (its content)
    // = 81 10 10 00, 28 bits.
    let newer: [u8; 4] = [0x81, 0x10, 0x10, 0x00];
    let mut r = BitReader::new(&newer);
    match Ext_decode(&mut r) {
        Some((v, f)) => println!(
            "newer peer       : decoded a={} b={:?} c={:?}  flag {:?}  ({} bits read)",
            v.a, v.b, v.c, f, r.pos),
        None => println!("newer peer       : DECODE FAILED"),
    }

    println!();
    // Extensible with nothing after the marker: the encoder can never set the
    // extension bit, so this is 1 + 1 (preamble for y) + 4 (x) = 6 bits.
    roundtrip_room("room, y absent   ", &Room { x: 9, y: None });
    roundtrip_room("room, y present  ", &Room { x: 9, y: Some(true) });

    println!();
    // A single addition: the chain is one link with no pair above it.
    // 1 (ext) + 1 (k) + 7 (count of 1) + 1 (bitmap) + 8 + 8 = 26 bits.
    roundtrip_one("one, absent      ", &One { k: true, v: None });
    roundtrip_one("one, present     ", &One { k: true, v: Some(9) });

    println!();
    // X.691 19.9: the group is one addition. 1 (ext) + 2 (n) + 7 (count 2)
    // + 2 (bitmap) + 8 + 8 (p as an open type) + 8 + 8 (the group as one) = 44.
    roundtrip_grouped("group absent     ",
        &Grouped { n: 2, p: Some(true), group1: None });
    roundtrip_grouped("group present    ",
        &Grouped { n: 2, p: Some(true),
                   group1: Some(Grouped_ext1 { q: 5, r: None }) });
    roundtrip_grouped("group only       ",
        &Grouped { n: 1, p: None,
                   group1: Some(Grouped_ext1 { q: 15, r: Some(true) }) });

    println!();
    // The same, but the addition they have and we do not is *absent*: count 3,
    // bitmap 100, so only our first addition is on the wire and `skip_adds`
    // steps over nothing. Still DiffVer -- the versions differ whatever the
    // bits say.
    //   1 | 1 | 0000010 | 100 | 00000001 | 00000101  = 28 bits
    let newer2: [u8; 4] = [0xC1, 0x40, 0x10, 0x50];
    let mut r3 = BitReader::new(&newer2);
    match Ext_decode(&mut r3) {
        Some((v, f)) => println!(
            "newer, theirs off: decoded a={} b={:?} c={:?}  flag {:?}  ({} bits read)",
            v.a, v.b, v.c, f, r3.pos),
        None => println!("newer, theirs off: DECODE FAILED"),
    }

    println!();
    // A list in the root. 1 (ext) + 1 (preamble: tag) + 2 (count 2 in 1..4)
    // + 3 + 3 = 10 bits -> 17 40.
    roundtrip_listed("listed, no adds  ",
        &Listed { ids: vec![3, 5], tag: None, more: None });
    // The same root, then 7 (count of 1) + 1 (bitmap) + 8 + 8 (a BOOLEAN as
    // an open type, one octet) = 34 bits -> 97 40 40 60 00.
    roundtrip_listed("listed, more     ",
        &Listed { ids: vec![3, 5], tag: None, more: Some(true) });
    roundtrip_listed("listed, tag      ",
        &Listed { ids: vec![0, 1, 2, 7], tag: Some(false), more: None });
    // 1 (ext) + 2 (count 2 in 0..3) + 1 + 1 = 5 bits -> 50.
    roundtrip_roomlist("roomlist         ", &RoomList { ids: vec![true, false] });
    roundtrip_roomlist("roomlist, empty  ", &RoomList { ids: vec![] });

    println!();
    // A list as an addition. 1 (ext) + 1 (a) + 7 (count 2) + 2 (bitmap 10)
    // + 8 (length: one octet) + 8 (count 1 in 1..2 is 1 bit, then 2 bits of
    // 2, padded) = 27 bits -> c0 c0 28 00.
    roundtrip_carrier("carrier, xs      ",
        &Carrier { a: true, xs: Some(vec![2]), group1: None });
    // The group: ys's count (1 bit), its one BOOLEAN, then z -- 110, padded.
    // Bitmap 01 -> c0 a0 38 00.
    roundtrip_carrier("carrier, group   ",
        &Carrier { a: true, xs: None,
                   group1: Some(Carrier_ext1 { ys: vec![true], z: false }) });
    roundtrip_carrier("carrier, both    ",
        &Carrier { a: false, xs: Some(vec![0, 3]),
                   group1: Some(Carrier_ext1 { ys: vec![], z: true }) });
    roundtrip_carrier("carrier, none    ",
        &Carrier { a: false, xs: None, group1: None });

    println!();
    // 1 (ext) + 1 (k) + 7 (count 1) + 1 (bitmap) + 8 (one octet) + 8 (the
    // group's preamble 10, then u = 1, padded) = 26 bits -> c0 40 68 00.
    roundtrip_allopt("allopt, u        ",
        &AllOpt { k: true, group0: Some(AllOpt_ext0 { u: Some(true), v: None }) });
    roundtrip_allopt("allopt, absent   ", &AllOpt { k: true, group0: None });
    // The group present with both components absent: preamble 00, padded.
    // Not an encoding of anything, and VUPER rejects it too.
    let empty_group: [u8; 4] = [0xC0, 0x40, 0x40, 0x00];
    let mut r4 = BitReader::new(&empty_group);
    match AllOpt_decode(&mut r4) {
        Some(_) => println!("empty group      : ACCEPTED -- should have been rejected"),
        None => println!("empty group      : rejected, as 19.9 requires ({})", r4.error()),
    }

    // An all-zero bitmap with the extension bit set is not a legal encoding of
    // anything (19.8 NOTE), so it has to be rejected -- otherwise one value
    // would have two encodings.
    let bogus: [u8; 3] = [0b1_1_000001, 0b_00_000000, 0b00000000];
    let mut r2 = BitReader::new(&bogus);
    match Ext_decode(&mut r2) {
        Some(_) => println!("all-zero bitmap  : ACCEPTED -- should have been rejected"),
        None => println!("all-zero bitmap  : rejected, as 19.8 requires ({})", r2.error()),
    }
}

} // verus!
