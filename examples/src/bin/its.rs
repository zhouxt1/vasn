// Round-trip a real ETSI ITS PDU header through the generated codec.

use vstd::prelude::*;
use vasn::uper::cursor::*;
use vasn_examples::its::*;

verus! {

#[verifier::external_body]
fn main() {
    // ItsPduHeader ::= SEQUENCE { protocolVersion (0..255),
    //                            messageID (0..255), stationID (0..4294967295) }
    // A CAM (messageID 2) from station 12345, protocol version 2.
    let hdr = ItsPduHeader { protocolVersion: 2, messageID: 2, stationID: 12345 };

    let mut w = BitWriter::with_capacity(16);
    let ok = ItsPduHeader_encode(&mut w, &hdr);
    let n = (w.pos + 7) / 8;
    print!("ItsPduHeader  encode ok={ok}  {} bits ->", w.pos);
    for i in 0..n {
        print!(" {:02x}", w.buf[i]);
    }
    println!("   (expected 48 bits -> 02 02 00 00 30 39)");

    let mut r = BitReader::new(&w.buf);
    match ItsPduHeader_decode(&mut r) {
        Some((back, _)) => println!("              decode  {back:?}  round trip {}",
                               if back == hdr { "MATCH" } else { "MISMATCH" }),
        None => println!("              decode failed"),
    }

    // ReferencePosition packs latitude/longitude/confidence/altitude with no
    // padding at all -- the fields land on arbitrary bit offsets.
    let pos = ReferencePosition {
        latitude: 400000000,
        longitude: -740000000,
        positionConfidenceEllipse: PosConfidenceEllipse {
            semiMajorConfidence: 100,
            semiMinorConfidence: 50,
            semiMajorOrientation: 900,
        },
        altitude: Altitude { altitudeValue: 1500, altitudeConfidence: AltitudeConfidence::alt_000_01 },
    };
    let mut w2 = BitWriter::with_capacity(32);
    let ok2 = ReferencePosition_encode(&mut w2, &pos);
    println!("ReferencePosition encode ok={ok2}  {} bits (not a byte multiple)", w2.pos);
    let mut r2 = BitReader::new(&w2.buf);
    match ReferencePosition_decode(&mut r2) {
        Some((back, _)) => println!("              round trip {}",
                               if back == pos { "MATCH" } else { "MISMATCH" }),
        None => println!("              decode failed"),
    }
}

} // verus!
