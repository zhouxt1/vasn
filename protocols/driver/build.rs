// Links CRATES (a vasnc --crate-dir build), VASN (vasn as the crate-dir
// Makefile builds it) and Verus's vstd, from the `verus` on PATH.
use std::path::PathBuf;
fn main() {
    for k in ["CRATES", "VASN"] {
        println!("cargo:rerun-if-env-changed={k}");
    }
    let crates = PathBuf::from(std::env::var("CRATES").expect("CRATES"));
    let vasn = PathBuf::from(std::env::var("VASN").expect("VASN"));
    let path = std::env::var_os("PATH").unwrap_or_default();
    let verus = std::env::split_paths(&path)
        .map(|d| d.join("verus"))
        .find(|v| v.is_file())
        .and_then(|v| v.canonicalize().ok())
        .and_then(|v| v.parent().map(PathBuf::from))
        .expect("verus is not on PATH");
    for dir in [&crates, &vasn] {
        println!("cargo:rerun-if-changed={}", dir.display());
    }
    for dir in [crates, vasn, verus] {
        println!("cargo:rustc-link-search={}", dir.canonicalize().unwrap().display());
    }
}
