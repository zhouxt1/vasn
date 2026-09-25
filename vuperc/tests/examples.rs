//! The codecs checked in under `examples/src/` are exactly what this vuperc
//! generates from `examples/asn1/`. After changing the generator, regenerate
//! them with
//!
//!   cargo run -p vuperc -- examples/asn1/NAME.asn1 examples/src/NAME.rs
use std::path::Path;
use std::process::Command;

const EXAMPLES: &[&str] = &["demo", "optional", "lists", "frag", "choice", "enum_ext", "ext", "its"];

#[test]
fn generated_examples_are_up_to_date() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));
    let mut stale = Vec::new();
    for n in EXAMPLES {
        let out = tmp.join(format!("{n}.rs"));
        let st = Command::new(env!("CARGO_BIN_EXE_vuperc"))
            .arg(root.join(format!("examples/asn1/{n}.asn1")))
            .arg(&out)
            .output()
            .unwrap();
        assert!(st.status.success(), "vuperc failed on {n}: {}", String::from_utf8_lossy(&st.stderr));
        let checked_in = std::fs::read_to_string(root.join(format!("examples/src/{n}.rs"))).unwrap();
        if std::fs::read_to_string(&out).unwrap() != checked_in {
            stale.push(*n);
        }
    }
    assert!(stale.is_empty(), "out of date in examples/src/: {stale:?}");
}
