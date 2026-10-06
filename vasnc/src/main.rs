mod ast;
mod lexer;
mod parser;
mod emit;
mod stats;
mod normalize;
mod constraints;
mod ioc;

use std::process::ExitCode;

/// How deep a recursive type is unrolled (`normalize::unroll_recursion`):
/// a value nested deeper is not decoded.
const RECURSION_LEVELS: usize = 8;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let stats_only = args.iter().any(|a| a == "--stats");
    emit::set_aper(args.iter().any(|a| a == "--aper"));
    let flag = |f: &str| args.iter().position(|a| a == f).and_then(|i| args.get(i + 1));
    let split_dir = flag("--output-dir");
    let crate_dir = flag("--crate-dir");
    let driver = flag("--driver");
    let containing = match flag("--containing").map(|s| s.as_str()) {
        None | Some("octets") => ast::ContainingMode::Octets,
        Some("decode") => ast::ContainingMode::Decode,
        Some(o) => {
            eprintln!("vasnc: --containing is `octets` or `decode`, not `{o}`");
            return ExitCode::from(2);
        }
    };
    // positional arguments: the input files, then the output unless a mode
    // that writes elsewhere is given
    let mut pos: Vec<&String> = Vec::new();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--output-dir" | "--crate-dir" | "--driver" | "--containing" => i += 2,
            a if a.starts_with("--") => i += 1,
            _ => {
                pos.push(&args[i]);
                i += 1;
            }
        }
    }
    let out_path = if stats_only || split_dir.is_some() || crate_dir.is_some() { None } else { pos.pop() };
    // the output is the last name: one that looks like ASN.1 is an input
    // whose output was forgotten, and writing it would destroy it
    if let Some(o) = out_path {
        if o.ends_with(".asn") || o.ends_with(".asn1") {
            eprintln!("vasnc: {o} would be the output, and it looks like an input: give an output (.rs), --stats, --output-dir or --crate-dir");
            return ExitCode::from(2);
        }
    }
    if pos.is_empty() || (out_path.is_none() && !stats_only && split_dir.is_none() && crate_dir.is_none()) {
        eprintln!("usage: vasnc <input.asn1>... <output.rs>");
        eprintln!("       vasnc <input.asn1>... --stats");
        eprintln!("       vasnc <input.asn1>... --output-dir <dir>   (one module per type)");
        eprintln!("       vasnc <input.asn1>... --crate-dir <dir>    (one crate per type + Makefile)");
        eprintln!("       vasnc <input.asn1>... <output.rs> --driver <driver.rs>   (and a test driver)");
        eprintln!("every module of every input is compiled, into one namespace");
        eprintln!("--aper: ALIGNED PER (X.691) instead of UNALIGNED");
        eprintln!("--containing octets (default) | decode: OCTET STRING (CONTAINING T) as its");
        eprintln!("    octets, as asn1c and VUPER do, or as the T they encode, as pycrate does");
        return ExitCode::from(2);
    }
    let mut mods = Vec::new();
    for path in &pos {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("vasnc: cannot read {path}: {e}");
                return ExitCode::from(2);
            }
        };
        match parser::Parser::new(&src).and_then(|mut p| p.parse_modules()) {
            Ok(m) => mods.extend(m),
            Err(e) => {
                eprintln!("vasnc: {path}: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    let nmods = mods.len();
    for (n, m) in ast::unimported(&mods) {
        eprintln!("vasnc: warning: {m} uses `{n}`, which it neither defines nor imports (X.680 13.16)");
    }
    let mut module = match ast::merge(mods) {
        Ok((m, missing)) => {
            for (n, from) in &missing {
                eprintln!("vasnc: warning: `{n}` is imported from {from}, which is not in the input");
            }
            m
        }
        Err(e) => {
            eprintln!("vasnc: {e}");
            return ExitCode::FAILURE;
        }
    };
    if nmods > 1 {
        eprintln!("vasnc: {nmods} modules: {}", module.name);
    }
    let expanded = normalize::expand_params(&mut module);
    // information object classes: after expansion, which puts the object
    // sets in place of their parameters
    match ioc::elaborate(&mut module) {
        Ok(n) if n > 0 => eprintln!("vasnc: {n} open types selected by a component relation constraint"),
        Ok(_) => {}
        Err(e) => {
            eprintln!("vasnc: {e}");
            return ExitCode::FAILURE;
        }
    }
    // effective PER-visible constraints, before hoisting: what is hoisted
    // depends on them (a one-value INTEGER is)
    constraints::resolve(&mut module, containing);
    let hoisted = normalize::hoist(&mut module);
    let broken = normalize::break_containing_cycles(&mut module);
    // recursive types, unrolled: vasnc builds no recursive format
    for scc in normalize::unroll_recursion(&mut module, RECURSION_LEVELS) {
        eprintln!("vasnc: recursive, unrolled {RECURSION_LEVELS} levels deep: {}", scc.join(", "));
    }
    let _ = expanded;
    if stats_only {
        stats::report(&module);
        return ExitCode::SUCCESS;
    }
    let out = emit::emit(&module);
    if let Some(dir) = crate_dir {
        match emit::write_crates(&out, std::path::Path::new(dir)) {
            Ok(n) => eprintln!("vasnc: wrote {n} crates and a Makefile to {dir}/"),
            Err(e) => {
                eprintln!("vasnc: cannot write {dir}: {e}");
                return ExitCode::from(2);
            }
        }
    } else if let Some(dir) = split_dir {
        match emit::write_split(&out, std::path::Path::new(dir)) {
            Ok(n) => eprintln!("vasnc: wrote {n} files to {dir}/"),
            Err(e) => {
                eprintln!("vasnc: cannot write {dir}: {e}");
                return ExitCode::from(2);
            }
        }
    } else if let Err(e) = std::fs::write(out_path.unwrap(), &out.code) {
        eprintln!("vasnc: cannot write {}: {e}", out_path.unwrap());
        return ExitCode::from(2);
    } else if let Some(d) = driver {
        let file = std::path::Path::new(out_path.unwrap()).file_name().unwrap().to_string_lossy().into_owned();
        if let Err(e) = std::fs::write(d, emit::driver(&out, &file)) {
            eprintln!("vasnc: cannot write {d}: {e}");
            return ExitCode::from(2);
        }
    }
    eprintln!(
        "vasnc: {} types compiled, {} skipped ({hoisted} inline types hoisted)",
        out.compiled, out.skipped.len()
    );
    if !broken.is_empty() {
        eprintln!(
            "vasnc: {} CONTAINING kept as octets, their contents leading back to them: {}",
            broken.len(),
            broken.join(", ")
        );
    }
    for (name, why) in &out.skipped {
        eprintln!("  skipped {name}: {why}");
    }
    ExitCode::SUCCESS
}
