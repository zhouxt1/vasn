// Extensible ENUMERATED on the wire (X.691 14.2, 14.3): one bit, then the
// root index as usual, or a normally small index among the extension values.
// Checked by hand, not only round-tripped, and printed as JER (X.697 22).

use vstd::prelude::*;
use vuperx::cursor::*;
use vuper_examples::enum_ext::*;

verus! {

#[verifier::external_body]
fn check(label: &str, h: Holder, want: &str) {
    let mut w = BitWriter::with_capacity(8);
    assert!(Holder_encode(&mut w, &h));
    let got: String = (0..w.pos).map(|i| if w.buf[i / 8] & (0x80 >> (i % 8)) != 0 { '1' } else { '0' }).collect();
    let mut r = BitReader::new(&w.buf);
    let (back, _) = Holder_decode(&mut r).expect("decodes");
    let mut j = String::new();
    Holder_jer(&back, &mut j);
    println!("{label:<16} {got:<16} {j}");
    assert!(got == want, "{label}: {got}, X.691 says {want}");
    assert!(back == h);
}

#[verifier::external_body]
fn main() {
    // preamble (grown OPTIONAL) | rat: ext bit + 2 bits | grown | lone: ext bit, no index | plain: 1 bit
    check("eutra", Holder { rat: RatType::eutra, grown: None, lone: Lone::only, plain: Plain::y },
          "001001"); // 0 grown absent | 010 eutra | 0 lone | 1 y
    check("nr, c", Holder { rat: RatType::nr, grown: Some(Grown::c), lone: Lone::only, plain: Plain::x },
          "100001000"); // 1 grown present | 000 nr | 010 c | 0 lone | 0 x
    // e-v1700 is extension value 1: bit 1, then 11.6's 0 + six bits 000001
    check("utra, e-v1700", Holder { rat: RatType::utra_fdd_v1610, grown: Some(Grown::e_v1700), lone: Lone::only, plain: Plain::x },
          "10111000000100"); // 1 | 011 utra | 1 0000001 e-v1700 | 0 lone | 0 x
    // RatType has no extension values yet, so a set extension bit is no value of it
    let mut r = BitReader::new(&[0b0100_0000u8, 0, 0]);
    let rejected = Holder_decode(&mut r).is_none();
    println!("{:<16} {}", "rat ext bit set", if rejected { "rejected" } else { "ACCEPTED" });
    assert!(rejected);
}

} // verus!
