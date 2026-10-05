// End-to-end check: encode a message with the generated encoder, decode it
// back with the generated decoder, and compare.

use vstd::prelude::*;
use vasn::uper::cursor::*;
use vasn_examples::demo::*;

verus! {

#[verifier::external_body]
fn main() {
    let msg = PDSCH_ServingCellConfig {
        nrofHARQ_ProcessesForPDSCH: 12,
        pucch_Cell: 5,
        xOverhead: XOverhead::xOh12,
        codeBlockGroupTransmission: true,
        alpha: Alpha::alpha07,
    };

    let mut w = BitWriter::with_capacity(16);
    let ok = PDSCH_ServingCellConfig_encode(&mut w, &msg);
    println!("encode ok       : {ok}");
    println!("bits written    : {}", w.pos);
    print!("bytes           :");
    let n = (w.pos + 7) / 8;
    for i in 0..n {
        print!(" {:02x}", w.buf[i]);
    }
    println!();

    let mut r = BitReader::new(&w.buf);
    match PDSCH_ServingCellConfig_decode(&mut r) {
        Some((back, _)) => {
            println!("decoded         : {back:?}");
            println!("bits consumed   : {}", r.pos);
            println!("round trip      : {}", if back == msg { "MATCH" } else { "MISMATCH" });
        }
        None => println!("decode failed"),
    }

    // A value outside INTEGER (1..16) must be rejected, not silently accepted.
    let mut bad = BitWriter::with_capacity(16);
    let _ = bad.write_uint(4, 15);   // nrofHARQ field = 15 -> value 16, in range
    let _ = bad.write_uint(5, 31);   // pucch-Cell = 31, in range
    let _ = bad.write_uint(2, 3);    // xOverhead = 3, but only 0..2 are defined
    let _ = bad.write_uint(1, 1);
    let _ = bad.write_uint(3, 0);
    let mut rb = BitReader::new(&bad.buf);
    println!(
        "out-of-range enum rejected: {}",
        PDSCH_ServingCellConfig_decode(&mut rb).is_none()
    );
}

} // verus!
