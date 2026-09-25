//! `vuperx::utf8::utf8_check` is proved equal to the spec `utf8_ok`, which is
//! written by hand from Unicode's Table 3-7. This checks that table: every
//! byte sequence of 1 to 4 octets, 2^32 + 2^24 + 2^16 + 2^8 of them, against
//! Rust's `std::str::from_utf8`. That covers every character, and every pair
//! and triple of short ones. Seconds in release, far longer in debug, so it is
//! not run by default:
//!
//!   cargo test --release -p vuperx --test utf8_exhaustive -- --ignored
use vuperx::utf8::utf8_check;

#[test]
#[ignore]
fn utf8_check_agrees_with_std() {
    let threads = std::thread::available_parallelism().map_or(8, |n| n.get());
    let mut bad = 0u64;
    let mut total = 0u64;
    for len in 1..=3usize {
        for x in 0..(1u32 << (8 * len)) {
            let s = &x.to_be_bytes()[4 - len..];
            total += 1;
            if utf8_check(s) != std::str::from_utf8(s).is_ok() {
                bad += 1;
                println!("differs: {:02x?}", s);
            }
        }
    }
    // four octets: split the first one across threads
    let hs: Vec<_> = (0..threads)
        .map(|t| {
            std::thread::spawn(move || {
                let mut bad = 0u64;
                let mut n = 0u64;
                let mut b0 = t as u32;
                while b0 < 256 {
                    for rest in 0..(1u32 << 24) {
                        let s = ((b0 << 24) | rest).to_be_bytes();
                        n += 1;
                        if utf8_check(&s) != std::str::from_utf8(&s).is_ok() {
                            bad += 1;
                            if bad < 10 {
                                println!("differs: {:02x?}", s);
                            }
                        }
                    }
                    b0 += threads as u32;
                }
                (bad, n)
            })
        })
        .collect();
    for h in hs {
        let (b, n) = h.join().unwrap();
        bad += b;
        total += n;
    }
    println!("{total} sequences of 1 to 4 octets, {bad} where utf8_check and std::str::from_utf8 differ");
    assert_eq!(bad, 0);
}
