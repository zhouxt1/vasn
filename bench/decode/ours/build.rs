// Links the seven channel-message closures that bench/decode/build.sh builds into
// bench/decode/nr/ (one rlib per ASN.1 type, opt-level 3), and what they
// depend on: vuperx as the nr/ Makefile builds it (target/verus/), and
// Verus's vstd and builtins, from the directory of the `verus` on PATH.
// NR_DIR, VUPERX_DIR and VERUS_DIR point it at others.
use std::path::PathBuf;

fn main() {
    let here = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let root = here.join("../../..").canonicalize().unwrap();
    let var = |k: &str, d: PathBuf| std::env::var(k).map(PathBuf::from).unwrap_or(d);
    for k in ["NR_DIR", "VUPERX_DIR", "VERUS_DIR"] {
        println!("cargo:rerun-if-env-changed={k}");
    }
    let nr = var("NR_DIR", here.join("../nr"));
    let vuperx = var("VUPERX_DIR", root.join("target/verus"));
    let verus = std::env::var("VERUS_DIR").map(PathBuf::from).unwrap_or_else(|_| {
        let path = std::env::var_os("PATH").unwrap_or_default();
        std::env::split_paths(&path)
            .map(|d| d.join("verus"))
            .find(|v| v.is_file())
            .and_then(|v| v.canonicalize().ok())
            .and_then(|v| v.parent().map(PathBuf::from))
            .expect("verus is not on PATH; set VERUS_DIR to the Verus release directory")
    });
    for dir in [nr, vuperx, verus] {
        println!("cargo:rustc-link-search={}", dir.canonicalize().unwrap().display());
    }
}
