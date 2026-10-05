//! Code generation: ASN.1 types become Rust types plus spec functions, an
//! `is_format` proof, and exec decode/encode functions.
//!
//! Every generated proof is a straight chain of the four composition lemmas in
//! `vasn::uper::format`, linear in the number of fields. Nothing here invents proof
//! structure per type, which is what keeps solver time per type bounded.
use crate::ast::*;
use std::collections::HashMap;

/// Whether the output is ALIGNED PER. It never is in this release, which is
/// UNALIGNED only; the branches it guards are left for the ALIGNED variant.
pub(crate) const fn aper() -> bool {
    false
}

/// An encoder applied to a value. A UPER encoding is a function of the value,
/// `e(v)`; an APER one also of the bit position it starts at, `e(pos, v)`
/// (`vasn::aper::format`). `pos` is a spec expression of type `nat`.
pub(crate) fn ea(e: &str, pos: &str, v: &str) -> String {
    if aper() { format!("{e}({pos}, {v})") } else { format!("{e}({v})") }
}

/// The input `k` bits on from `start`, a ghost `nat`: the bits dropped in
/// UPER, the position advanced as well in APER.
pub(crate) fn skip_in(start: &str, k: &str) -> String {
    if aper() { format!("adv({start}, {k})") } else { format!("{start}.skip({k} as int)") }
}

/// Where an exec encoder started, as a `nat`: what `ea` takes in an `ensures`.
pub(crate) const OLD_POS: &str = "old(w).pos as nat";

/// The imports every generated module starts with.
pub fn prelude() -> &'static str {
    if aper() { PRELUDE_APER } else { PRELUDE }
}

/// The step lemmas every generated module brings into scope.
pub fn steps_line() -> &'static str {
    if aper() {
        "broadcast use {format_steps, map_steps, opt_steps, unit_steps, list_steps, flist_steps};\n\n"
    } else {
        "broadcast use {format_steps, map_steps, opt_steps, unit_steps, list_steps};\n\n"
    }
}

/// UPER's generated text, turned into APER's where the two differ only in
/// spelling: a decoder reads `r.at()`, the position with the bits, where UPER
/// reads `r.rem()`. Every lemma call keeps its text, since `vasn::aper`
/// gives its lemmas UPER's names.
fn to_variant(text: String) -> String {
    if !aper() {
        return text;
    }
    text.replace(".rem()", ".at()")
        // the input's bits, where UPER's input is the bits
        .replace("start.len()", "start.1.len()")
        .replace("assert(start.skip(1).skip((r.pos - p1) as int)", "assert(adv(adv(start, 1), (r.pos - p1) as nat)")
        .replace("=~= start.skip((1 + (r.pos - p1)) as int));", "=~= adv(start, (1 + (r.pos - p1)) as nat));")
        .replace("assert(r.at().skip(0) =~= r.at());", "assert(adv(r.at(), 0) =~= r.at());")
        // the exec reads and writes APER has in place of UPER's
        .replace(".read_nsld()", ".read_ansld()")
        .replace(".write_nsld(", ".write_ansld(")
        .replace(".read_bitmap(", ".read_abitmap(")
        .replace(".write_bitmap(", ".write_abitmap(")
        .replace(".skip_adds_run(", ".skip_adds_arun(")
        .replace(".read_frag_ref()", ".read_afrag_ref()")
        .replace(".read_frag()", ".read_afrag()")
        // NULL is UPER's, lifted, so its well-formedness is UPER's `unit_wf`
        .replace("reveal(unit_wf);", "reveal(vasn::uper::opt::unit_wf);")
        .replace("lemma_unit_dec_val(Null, r.at());", "vasn::uper::opt::lemma_unit_dec_val(Null, r.at().1);")
        // BOOLEAN is UPER's, lifted, so seeing through it takes UPER's `map`
        .replace("reveal(map_dec);", "reveal(map_dec); reveal(vasn::uper::prim::map_dec);")
}

pub struct Output {
    pub code: String,
    pub compiled: usize,
    pub skipped: Vec<(String, String)>,
    /// One entry per generated type, for `--output-dir`.
    pub units: Vec<Unit>,
    pub module_name: String,
    /// Every compiled assignment, in the order it compiled, with the code to
    /// decode, encode, print and generate one: what `--driver` exposes.
    pub driven: Vec<Driven>,
}

/// A compiled type as the driver calls it: `Compiled`'s templates, with
/// `{R}`, `{W}`, `{V}`, `{O}`, `{G}` still to fill in.
pub struct Driven {
    pub asn: String,
    pub rust_ty: String,
    pub decode: String,
    pub encode: String,
    pub jer: String,
    pub arb: String,
}

/// A single generated type: its module name, its code, and the modules it
/// needs in scope.
pub struct Unit {
    pub module: String,
    pub code: String,
    pub deps: Vec<String>,
}

/// Every named type this definition mentions, so the split output knows what
/// to import. Hoisting has already turned inline types into references.
pub(crate) fn collect_refs(t: &Type, out: &mut Vec<String>) {
    match t {
        Type::Ref(n) => out.push(n.clone()),
        Type::ParamRef(n, args) => {
            out.push(n.clone());
            out.extend(args.iter().cloned());
        }
        Type::Sequence(root, ext) => {
            for f in root.iter().chain(ext.iter().flatten().flat_map(ExtAdd::fields)) {
                collect_refs(&f.ty, out);
            }
        }
        Type::Choice(root, ext) => {
            for (_, a) in root.iter().chain(ext.iter().flatten()) {
                collect_refs(a, out);
            }
        }
        Type::SequenceOf(_, inner) | Type::Contains(inner) => collect_refs(inner, out),
        _ => {}
    }
}

pub const PRELUDE_APER: &str = "\
#![allow(non_snake_case, non_camel_case_types, unused_imports, unused_variables)]
#![allow(bindings_with_variant_name, unused_parens, unused_braces, unused_comparisons, dead_code)]
use vstd::prelude::*;
use vasn::bits::bitspec::*;
use vasn::aper::format::*;
use vasn::aper::term::*;
use vasn::aper::cursor::*;
use vasn::aper::opt::*;
use vasn::aper::intx::*;
use vasn::aper::list::*;
use vasn::aper::opentype::*;
use vasn::aper::xext::*;
use vasn::aper::xint::*;
use vasn::aper::seqext::*;
use vasn::aper::fraglist::*;
use vasn::aper::complete::*;
use vasn::aper::fast::*;
#[cfg(verus_keep_ghost)]
use vasn::uper::fast::lemma_word_bit;
use vasn::utf8::*;
use vasn::jer::*;
use vasn::arb::Gen;
";

pub const PRELUDE: &str = "\
#![allow(non_snake_case, non_camel_case_types, unused_imports, unused_variables)]
#![allow(bindings_with_variant_name, unused_parens, unused_braces, unused_comparisons, dead_code)]
use vstd::prelude::*;
use vasn::bits::bitspec::*;
use vasn::uper::format::*;
use vasn::uper::prim::*;
use vasn::uper::term::*;
use vasn::uper::cursor::*;
use vasn::uper::opt::*;
use vasn::uper::list::*;
use vasn::uper::lendet::*;
use vasn::uper::frag::*;
use vasn::uper::fraglist::*;
use vasn::uper::intx::*;
use vasn::utf8::*;
use vasn::uper::opentype::*;
use vasn::uper::seqext::*;
use vasn::uper::fast::*;
use vasn::jer::*;
use vasn::arb::Gen;
";

/// What a compiled type looks like to its users.
#[derive(Clone)]
struct Compiled {
    /// Rust type of a value, e.g. `i64` or `Alpha`.
    rust_ty: String,
    /// Prefix of the generated `X_wf()` / `X_enc()` / `X_dec()` functions.
    fmt: String,
    /// Proof call establishing `is_format` for it.
    proof_call: String,
    /// Exec decoder call given a reader expression.
    decode: String,
    /// Exec encoder call given writer and value expressions.
    encode: String,
    /// Facts the caller must re-establish before invoking the lemmas.
    preamble: Vec<String>,
    /// The generated module that defines this format, if any. Terminal formats
    /// come from `vasn` and need no import; an alias shares its target's.
    owner: Option<String>,
    /// The type the *format* is over. This differs from `rust_ty` exactly when
    /// the exec value cannot appear in spec code -- a list is a `Vec` to run
    /// and a `Seq` to reason about.
    spec_ty: Option<String>,
    /// How to get from an exec value to its spec value, with `{V}` standing for
    /// the value. `None` means they are the same thing.
    view: Option<String>,
    /// Appends the value's JER (X.697) to a `String`: `{V}` is a `&T`, `{O}`
    /// the `&mut String`. Unverified; see `vasn::jer`.
    jer: String,
    /// A value of the type from entropy, `{G}` being the `&mut Gen`, within
    /// the type's constraints so that it encodes. Unverified; `vasn::arb`.
    arb: String,
}

impl Compiled {
    /// The type the format is over.
    fn sty(&self) -> String {
        self.spec_ty.clone().unwrap_or_else(|| self.rust_ty.clone())
    }
    /// Whether exec and spec values coincide.
    fn plain(&self) -> bool {
        self.view.is_none()
    }
    /// The spec value of an exec expression.
    fn view_of(&self, v: &str) -> String {
        match &self.view {
            None => v.to_string(),
            Some(t) => t.replace("{V}", v),
        }
    }
}

/// Smallest n with 2^n >= count. UPER encodes a constrained value in exactly
/// this many bits.
fn width_for(count: u64) -> u32 {
    if count <= 1 {
        return 0;
    }
    let mut n = 0u32;
    while (1u128 << n) < count as u128 {
        n += 1;
    }
    n
}

fn lit(n: &Num, values: &HashMap<String, i64>) -> Option<i64> {
    match n {
        Num::Lit(v) => Some(*v),
        Num::Ref(r) => values.get(r).copied(),
    }
}

pub fn emit(module: &Module) -> Output {
    let mut values: HashMap<String, i64> = HashMap::new();
    for a in &module.assignments {
        if let Assignment::Value { name, value } = a {
            values.insert(name.clone(), *value);
        }
    }

    let mut env: HashMap<String, Compiled> = HashMap::new();
    let mut skipped: Vec<(String, String)> = Vec::new();
    let mut body = String::new();
    let mut compiled = 0usize;
    let mut units: Vec<Unit> = Vec::new();
    let mut driven: Vec<Driven> = Vec::new();

    // Repeat until nothing new resolves, so forward references work without a
    // separate topological sort.
    let mut progress = true;
    let mut pending: Vec<(&String, &Type)> = module
        .assignments
        .iter()
        .filter_map(|a| match a {
            Assignment::Type { name, ty } => Some((name, ty)),
            _ => None,
        })
        .collect();

    while progress && !pending.is_empty() {
        progress = false;
        let mut still = Vec::new();
        for (name, ty) in pending {
            match gen_type(name, ty, &env, &values) {
                Ok((text, mut c)) => {
                    let text = to_variant(mark_inline(&text));
                    if !text.is_empty() {
                        // this definition emits its own code, so it owns it
                        let module = rustify(name);
                        c.owner = Some(module.clone());
                        let mut refs = Vec::new();
                        collect_refs(ty, &mut refs);
                        let mut deps: Vec<String> = refs
                            .iter()
                            .filter_map(|r| env.get(r).and_then(|d| d.owner.clone()))
                            .collect();
                        deps.sort();
                        deps.dedup();
                        units.push(Unit { module, code: text.clone(), deps });
                    }
                    body.push_str(&text);
                    if aper() {
                        let ct = to_variant(complete_fns(name, &c));
                        match units.last_mut() {
                            Some(u) if !text.is_empty() => u.code.push_str(&ct),
                            _ => {}
                        }
                        body.push_str(&ct);
                    }
                    driven.push(Driven {
                        asn: name.clone(),
                        rust_ty: c.rust_ty.clone(),
                        decode: c.decode.clone(),
                        encode: c.encode.clone(),
                        jer: c.jer.clone(),
                        arb: c.arb.clone(),
                    });
                    env.insert(name.clone(), c);
                    compiled += 1;
                    progress = true;
                }
                Err(Pending::Unresolved(_)) => still.push((name, ty)),
                Err(Pending::Unsupported(why)) => {
                    skipped.push((name.clone(), why));
                    progress = true;
                }
            }
        }
        pending = still;
    }
    for (name, _) in pending {
        skipped.push((name.clone(), "depends on a type that was skipped".into()));
    }

    let mut code = String::new();
    let _ = &units;
    code.push_str(&format!(
        "// Generated by vasnc from ASN.1 module `{}`. Do not edit.\n{}\n\
         verus! {{\n\n{}",
        module.name, prelude(), steps_line()
    ));
    code.push_str(&body);
    code.push_str("} // verus!\n");

    Output { code, compiled, skipped, units, module_name: module.name.clone(), driven }
}

/// A test driver for a single-file module: plain Rust, outside `verus!`, so
/// it adds nothing to what is trusted. Decodes hex to JER and re-encodes, or
/// encodes random values, for any compiled type by its ASN.1 name. It is what
/// `tools/xcheck.py` compares against pycrate and asn1c.
pub fn driver(out: &Output, module_file: &str) -> String {
    let mut arms = String::new();
    let mut fns = String::new();
    let mut names = Vec::new();
    for (k, d) in out.driven.iter().enumerate() {
        // a template with proof code in it is only used inline; in APER the
        // driver calls the type's complete decoder and encoder instead
        // (X.691 11.1.4), which every type has
        let inline_only = if aper() { vec![&d.jer, &d.arb] } else { vec![&d.decode, &d.encode, &d.jer, &d.arb] };
        if inline_only.iter().any(|t| t.contains("proof")) {
            continue;
        }
        let prim = matches!(d.rust_ty.as_str(), "bool" | "u8" | "u16" | "u32" | "i64" | "Null");
        let ty = &d.rust_ty;
        let rn = rustify(&d.asn);
        let (dec, enc) = if aper() {
            (format!("{rn}_decode_complete(r)"), format!("{rn}_encode_complete(w, v)"))
        } else {
            (d.decode.replace("{R}", "r"),
             d.encode.replace("{W}", "w").replace("{V}", if prim { "*v" } else { "v" }))
        };
        fns.push_str(&format!(
            "fn dec_{k}(r: &mut BitReader) -> Option<({ty}, Flg)> {{ {} }}\n\
             fn enc_{k}(w: &mut BitWriter, v: &{ty}) -> bool {{ {} }}\n\
             fn jer_{k}(v: &{ty}, o: &mut String) {{ {}; }}\n\
             fn arb_{k}(g: &mut Gen) -> {ty} {{ {} }}\n",
            dec,
            enc,
            d.jer.replace("{V}", "v").replace("{O}", "o"),
            d.arb.replace("{G}", "g"),
        ));
        arms.push_str(&format!("        {:?} => run!(dec_{k}, enc_{k}, jer_{k}, arb_{k}),\n", d.asn));
        names.push(format!("{:?}", d.asn));
    }
    let n = names.len();
    format!(r##"// Generated by vasnc --driver from ASN.1 module `{module}`. Do not edit.
//
//   driver types                 the types it knows, one per line
//   driver dec TYPE < hex-lines  per line: `ok FLAG BITS REENC JER`, or `err WHY`
//   driver gen TYPE N [SEED]     N random values: `HEX BITS JER` per line
//
// FLAG is SameVer or DiffVer; REENC is our encoder's encoding of the decoded
// value, BITS its length before the padding to an octet (X.691 11.1.3).
#[path = {module_file:?}]
pub mod m;

use std::io::BufRead;
use vasn::arb::Gen;
use vasn::uper::cursor::{{BitReader, BitWriter}};
use vasn::uper::format::Flg;
#[allow(unused_imports)]
use crate::m::*;
#[allow(unused_imports)]
use vasn::jer::*;
#[allow(unused_imports)]
use vasn::uper::opt::Null;
#[allow(unused_imports)]
use vasn::uper::intx::XRoot;

fn hex(b: &[u8]) -> String {{ b.iter().map(|x| format!("{{x:02x}}")).collect() }}

/// X.691 11.1.3.1: an outermost value whose encoding is empty is sent as one
/// zero octet.
fn outer(w: &BitWriter) -> String {{
    if w.pos == 0 {{ "00".into() }} else {{ hex(&w.buf[..(w.pos + 7) / 8]) }}
}}

fn unhex(s: &str) -> Option<Vec<u8>> {{
    let s = s.trim();
    if s.len() % 2 != 0 {{ return None; }}
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok()).collect()
}}

fn entropy(seed: u64, n: usize) -> Vec<u8> {{
    // splitmix64 of the seed, so neighbouring seeds give unrelated streams
    let mut z = seed.wrapping_add(0x9e3779b97f4a7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    let mut x = (z ^ (z >> 31)) | 1;
    (0..n).map(|_| {{ x ^= x << 13; x ^= x >> 7; x ^= x << 17; x as u8 }}).collect()
}}

macro_rules! run {{
    ($dec:ident, $enc:ident, $jer:ident, $arb:ident) => {{{{
        let args: Vec<String> = std::env::args().collect();
        match args[1].as_str() {{
            "dec" => {{
                for line in std::io::stdin().lock().lines() {{
                    let line = line.unwrap();
                    if line.trim().is_empty() {{ continue; }}
                    let Some(b) = unhex(&line) else {{ println!("err not hex"); continue }};
                    let mut r = BitReader::new(&b);
                    match $dec(&mut r) {{
                        None => println!("err {{}}", r.error()),
                        Some((v, f)) => {{
                            let mut w = BitWriter::with_capacity(8 * b.len() + (1 << 16));
                            let re = if $enc(&mut w, &v) {{ outer(&w) }} else {{ "-".into() }};
                            let mut j = String::new();
                            $jer(&v, &mut j);
                            let f = if matches!(f, Flg::SameVer) {{ "SameVer" }} else {{ "DiffVer" }};
                            println!("ok {{f}} {{}} {{re}} {{j}}", w.pos);
                        }}
                    }}
                }}
            }}
            "gen" => {{
                let n: usize = args[3].parse().unwrap();
                let seed: u64 = args.get(4).map(|s| s.parse().unwrap()).unwrap_or(1);
                for i in 0..n {{
                    let e = entropy(seed.wrapping_mul(1 << 32).wrapping_add(i as u64), 4096);
                    let v = $arb(&mut Gen::new(&e));
                    let mut w = BitWriter::with_capacity(1 << 20);
                    if !$enc(&mut w, &v) {{ println!("err encoder refused"); continue; }}
                    let mut j = String::new();
                    $jer(&v, &mut j);
                    println!("{{}} {{}} {{j}}", outer(&w), w.pos);
                }}
            }}
            c => {{ eprintln!("unknown command {{c}}"); std::process::exit(2); }}
        }}
    }}}};
}}

fn main() {{
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("types") {{
        let ts: [&str; {n}] = [{names}];
        for t in ts {{ println!("{{t}}"); }}
        return;
    }}
    if args.len() < 3 {{
        eprintln!("usage: driver types | dec TYPE < hex-lines | gen TYPE N [SEED]");
        std::process::exit(2);
    }}
    match args[2].as_str() {{
{arms}        t => {{ eprintln!("{{t}}: no such type"); std::process::exit(2); }}
    }}
}}

{fns}"##, module = out.module_name, names = names.join(", "))
}

/// Write one file per type plus a `lib.rs`, the way VUPER's Rocq backend emits
/// one file per definition. A single 24 MB file overflows rustc's stack and is
/// unusable in practice; this also means editing one type only re-checks that
/// type when combined with `--verify-module`.
pub fn write_split(out: &Output, dir: &std::path::Path) -> std::io::Result<usize> {
    std::fs::create_dir_all(dir)?;
    for u in &out.units {
        let mut f = String::new();
        f.push_str(&format!("// Generated by vasnc from `{}`. Do not edit.\n", out.module_name));
        f.push_str(prelude());
        for d in &u.deps {
            if *d != u.module {
                // `pub use`, not `use`: a hoisted inline type mentions its
                // element type in its own public signature, so a module that
                // imports the hoisted type needs the element type's name too.
                f.push_str(&format!("pub use crate::{d}::*;\n"));
            }
        }
        f.push_str("\nverus! {\n\n");
        f.push_str(steps_line());
        f.push_str(&u.code);
        f.push_str("} // verus!\n");
        std::fs::write(dir.join(format!("{}.rs", u.module)), f)?;
    }
    let mut lib = String::new();
    lib.push_str(&format!(
        "// Generated by vasnc from `{}`. Do not edit.\n\
         //! One module per ASN.1 type. Verify a single one with\n\
         //! `verus --crate-type=lib --verify-module <Type> lib.rs`.\n\
         #![allow(non_snake_case, non_camel_case_types)]\n\n",
        out.module_name
    ));
    for u in &out.units {
        lib.push_str(&format!("pub mod {};\n", u.module));
    }
    std::fs::write(dir.join("lib.rs"), lib)?;
    Ok(out.units.len())
}

/// One crate per ASN.1 type, plus a Makefile to drive them.
///
/// Verus's unit of separate compilation is the crate, not the file: a crate
/// exports `.vir` metadata that downstream crates `--import`. Emitting one big
/// crate instead means every run pays for the whole corpus -- and that cost is
/// *superlinear*, since the cross-module name graph grows with it. Measured on
/// NR Rel-17: 49 ms per module across 43 modules, 108 ms per module across
/// 4086.
///
/// Imports are **not** transitive -- a crate must name every ancestor whose
/// spec functions it can see, not just its direct dependencies -- so each rule
/// carries the transitive closure. That is affordable here because the
/// dependency graph is shallow: on NR the median type depends on nothing at
/// all and the worst case is 79.
/// A crate importing more than this many others verifies each exec function
/// at `BIG_RLIMIT`. Under `--containing decode` the message crates import a
/// whole message's closure (`HandoverPreparationInformation-IEs` 3157,
/// `CG-Config-IEs` 3099). Some of their runners go over the default rlimit
/// after their crate's other queries, and some even alone (`RRCResume-IEs`'
/// `enc_t4_run`, which passes at 40). A solver process per function
/// (`spinoff_prover`) is not enough, and makes such a crate 5x slower: the
/// cost per query grows with the context, as
/// `CellGroupConfig`'s does. Without decoding the
/// largest closure is `UE-NR-Capability`'s 2204, below this, so that build is
/// unchanged.
const BIG_ABOVE: usize = 2500;
const BIG_RLIMIT: u32 = 40;

/// `BIG_RLIMIT` on every verified exec function in `code`:
/// each `fn` whose attributes name neither `external` nor an rlimit already.
fn rlimit_all(code: &str) -> String {
    let mut out = String::with_capacity(code.len() + code.len() / 8);
    let mut attrs = String::new();
    for line in code.split_inclusive('\n') {
        let t = line.trim_start();
        if t.starts_with("#[") {
            attrs.push_str(t);
        } else {
            if (t.starts_with("pub fn ") || t.starts_with("fn "))
                && !attrs.contains("external") && !attrs.contains("rlimit")
            {
                out.push_str(&format!("#[verifier::rlimit({BIG_RLIMIT})]\n"));
            }
            attrs.clear();
        }
        out.push_str(line);
    }
    out
}

pub fn write_crates(out: &Output, dir: &std::path::Path) -> std::io::Result<usize> {
    std::fs::create_dir_all(dir)?;
    let direct: HashMap<&str, &Vec<String>> =
        out.units.iter().map(|u| (u.module.as_str(), &u.deps)).collect();

    // transitive closure, memoised; the graph is acyclic because the compiler
    // only emits a type once everything it references has been emitted
    fn closure<'a>(
        m: &'a str,
        direct: &HashMap<&'a str, &'a Vec<String>>,
        memo: &mut HashMap<&'a str, Vec<String>>,
    ) -> Vec<String> {
        if let Some(c) = memo.get(m) {
            return c.clone();
        }
        let mut acc: Vec<String> = Vec::new();
        if let Some(ds) = direct.get(m) {
            for d in ds.iter() {
                if !acc.contains(d) {
                    acc.push(d.clone());
                }
                let key = direct.keys().find(|k| **k == d.as_str()).copied();
                if let Some(k) = key {
                    for t in closure(k, direct, memo) {
                        if !acc.contains(&t) {
                            acc.push(t);
                        }
                    }
                }
            }
        }
        memo.insert(m, acc.clone());
        acc
    }
    let mut memo: HashMap<&str, Vec<String>> = HashMap::new();
    let mut closures: Vec<(String, Vec<String>)> = Vec::new();
    for u in &out.units {
        let c = closure(u.module.as_str(), &direct, &mut memo);
        closures.push((u.module.clone(), c));
    }

    for u in &out.units {
        let mut f = String::new();
        f.push_str(&format!("// Generated by vasnc from `{}`. Do not edit.\n", out.module_name));
        f.push_str(prelude());
        // One crate per type, so a dependency is an extern crate, not a module.
        // The leading `::` is load-bearing: a crate almost always contains a
        // type of its own name, and a bare `use Foo::*` would be ambiguous
        // between the crate and the type it just brought into scope.
        for d in &u.deps {
            if *d != u.module {
                f.push_str(&format!("pub use ::{d}::*;\n"));
            }
        }
        f.push_str("\nverus! {\n\n");
        f.push_str(steps_line());
        let big = closures.iter().any(|(m, c)| *m == u.module && c.len() > BIG_ABOVE);
        f.push_str(&if big { rlimit_all(&u.code) } else { u.code.clone() });
        f.push_str("} // verus!\n");
        std::fs::write(dir.join(format!("{}.rs", u.module)), f)?;
    }

    let mut mk = String::new();
    mk.push_str(&format!(
        "# Generated by vasnc from `{}`. Do not edit.\n\
         #\n\
         # One crate per ASN.1 type. `make -jN` verifies them in dependency\n\
         # order, in parallel, and re-verifies only what actually changed.\n\
         #\n\
         #   make -j$(nproc)          verify everything\n\
         #   make Foo.vir             verify one type and whatever it needs\n\
         #   make clean\n\n\
         # A wide ENUMERATED compiles to a deeply nested if/else chain, which\n\
         # overflows rustc's default stack. This is not optional.\n\
         export RUST_MIN_STACK := 2000000000\n\n\
         # Verus writes the .vir before it verifies, so a crate that fails would\n\
         # otherwise look verified to the next make run.\n\
         .DELETE_ON_ERROR:\n\n\
         # ROOT is a checkout of vasn, for the sources of vasn, of vbits, the\n\
         # bit layer under it, and of vsimd, the SSE2 it copies octets with; all\n\
         # are built here with Verus itself, since their .vir is what each crate\n\
         # imports.\n\
         ROOT ?= ../..\n\
         VERUS ?= verus\n\
         VASN_SRC ?= $(ROOT)/vasn/src\n\
         VBITS_SRC ?= $(ROOT)/vbits/src\n\
         VSIMD_SRC ?= $(ROOT)/vsimd/src\n\
         VASN_DIR ?= $(ROOT)/target/verus\n\
         VASN_VIR ?= $(VASN_DIR)/vasn.vir\n\
         VASN_RLIB ?= $(VASN_DIR)/libvasn.rlib\n\
         VBITS_VIR ?= $(VASN_DIR)/vbits.vir\n\
         VBITS_RLIB ?= $(VASN_DIR)/libvbits.rlib\n\
         VSIMD_VIR ?= $(VASN_DIR)/vsimd.vir\n\
         VSIMD_RLIB ?= $(VASN_DIR)/libvsimd.rlib\n\
         # -L is required even though every dependency is named with --extern:\n\
         # rustc still resolves the transitive rlib chain (vbits behind vasn, and\n\
         # each crate's own) through the search path.\n\
         VFLAGS ?= --crate-type=lib --compile -C opt-level=2 -L . -L $(VASN_DIR)\n\n\
         # MAKEFLAGS= on the recipe, not `unexport`: GNU make re-exports it\n\
         # regardless, and rustc then warns about the jobserver fd it cannot\n\
         # open -- once per crate, which buries the real output.\n\
         RUN = MAKEFLAGS= $(VERUS) $(VFLAGS)\n\n",
        out.module_name
    ));
    mk.push_str("ALL = \\\n");
    for u in &out.units {
        mk.push_str(&format!("\t{}.vir \\\n", u.module));
    }
    mk.push_str("\n.PHONY: all clean\nall: $(ALL)\nclean:\n\trm -f *.vir *.rlib\n\n");
    mk.push_str(
        "$(VBITS_RLIB): $(wildcard $(VBITS_SRC)/*.rs)\n\
         \t@echo '  verus vbits'\n\
         \t@mkdir -p $(VASN_DIR)\n\
         \t@MAKEFLAGS= $(VERUS) --crate-type=lib --crate-name vbits --compile -C opt-level=3 \\\n\
         \t  --export $(VBITS_VIR) $(VBITS_SRC)/lib.rs -o $(VBITS_RLIB)\n\n\
         $(VSIMD_RLIB): $(wildcard $(VSIMD_SRC)/*.rs)\n\
         \t@echo '  verus vsimd'\n\
         \t@mkdir -p $(VASN_DIR)\n\
         \t@MAKEFLAGS= $(VERUS) --crate-type=lib --crate-name vsimd --compile -C opt-level=3 \\\n\
         \t  --triggers-mode silent --export $(VSIMD_VIR) $(VSIMD_SRC)/lib.rs -o $(VSIMD_RLIB)\n\n\
         $(VASN_RLIB): $(wildcard $(VASN_SRC)/*.rs $(VASN_SRC)/*/*.rs) $(VBITS_RLIB) $(VSIMD_RLIB)\n\
         \t@echo '  verus vasn'\n\
         \t@MAKEFLAGS= $(VERUS) --crate-type=lib --crate-name vasn --compile -C opt-level=3 \\\n\
         \t  --import vbits=$(VBITS_VIR) --extern vbits=$(VBITS_RLIB) \\\n\
         \t  --import vsimd=$(VSIMD_VIR) --extern vsimd=$(VSIMD_RLIB) \\\n\
         \t  --export $(VASN_VIR) $(VASN_SRC)/lib.rs -o $(VASN_RLIB)\n\n",
    );
    for (m, clos) in &closures {
        let prereqs: String = clos.iter().map(|d| format!(" {d}.vir")).collect();
        // The imports go in a file of their own, spliced in by the shell. On
        // NR the widest closure is 1402 crates, a 400 KB recipe, and make
        // hands a recipe to `sh -c` as one argument, which Linux caps at
        // 128 KB. The spliced words are separate arguments, and those only
        // have to fit the 2 MB total.
        let imports = if clos.is_empty() {
            String::new()
        } else {
            let lines: String = clos
                .iter()
                .map(|d| format!("--import {d}={d}.vir --extern {d}=lib{d}.rlib\n"))
                .collect();
            std::fs::write(dir.join(format!("{m}.deps")), lines)?;
            format!(" $$(cat {m}.deps)")
        };
        // one concise line per crate; `make -n Foo.vir` prints the full command.
        // vasn is a prerequisite too: rustc refuses an rlib built against
        // another build of it ("can't find crate"), so a rebuilt vasn has
        // to rebuild every crate.
        mk.push_str(&format!(
            "{m}.vir: {m}.rs $(VASN_RLIB){prereqs}\n\
             \t@echo '  verus {m}'\n\
             \t@$(RUN) --crate-name {m} --export {m}.vir \\\n\
             \t  --import vbits=$(VBITS_VIR) --import vsimd=$(VSIMD_VIR) --import vasn=$(VASN_VIR) --extern vasn=$(VASN_RLIB){imports} \\\n\
             \t  {m}.rs -o lib{m}.rlib\n\n"
        ));
    }
    std::fs::write(dir.join("Makefile"), mk)?;
    Ok(out.units.len())
}

enum Pending {
    /// A referenced type is not compiled yet; try again next round.
    Unresolved(#[allow(dead_code)] String),
    Unsupported(String),
}

/// Resolve a field type to something already compiled, or to an inline
/// primitive. Inline anonymous SEQUENCE/ENUMERATED inside a field is not
/// supported yet — those must be hoisted to their own assignment.
fn resolve(
    ty: &Type,
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<Compiled, Pending> {
    match ty {
        Type::Boolean => Ok(Compiled {
            owner: None,
            spec_ty: None,
            view: None,
            rust_ty: "bool".into(),
            fmt: "bool".into(),
            proof_call: "lemma_bool_format();".into(),
            decode: "{ let o_ = {R}.read_bool(); {R}.same(o_, \"BOOLEAN\") }".into(),
            encode: "{W}.write_bool({V})".into(),
            preamble: vec![],
            jer: "jer_bool(*{V}, {O})".into(),
            arb: "{G}.bool()".into(),
        }),
        Type::Integer(IntCons::Range(lb, ub)) => {
            let (lb, ub) = match (lit(lb, values), lit(ub, values)) {
                (Some(a), Some(b)) => (a, b),
                _ => return Err(Pending::Unsupported("INTEGER bound is an unknown value reference".into())),
            };
            if ub == lb {
                // One value, no bits (X.691 13.2.1). The front end hoists
                // `INTEGER (5)` to a named type; this is the case it cannot see,
                // where the bounds are value references that happen to agree --
                // `INTEGER (1..maxNrofCSI-SSB-ResourceSetsPerConfig)`, with that
                // maximum 1. Inline, so the decoder carries its own proof.
                return Ok(Compiled {
                    owner: None,
                    spec_ty: None,
                    view: None,
                    rust_ty: "i64".into(),
                    fmt: format!("int_const_{lb}"),
                    proof_call: format!("lemma_unit_format({lb}i64);"),
                    decode: format!(
                        "{{ proof {{ lemma_unit_dec_val({lb}i64, {{R}}.rem()); }} Some(({lb}i64, Flg::SameVer)) }}"
                    ),
                    encode: format!("{{ proof {{ assert({{W}}.written() + {} =~= {{W}}.written()); }} true }}",
                                    ea("unit_enc::<i64>()", "{W}.pos as nat", "{V}")),
                    preamble: vec![],
                    jer: "jer_int(*{V}, {O})".into(),
                    arb: format!("{lb}i64"),
                });
            }
            if ub < lb {
                return Err(Pending::Unsupported("INTEGER with an empty range".into()));
            }
            let span = (ub as i128) - (lb as i128);
            // the range's size in u128: `INTEGER (MIN64..MAX64)` has 2^64
            // values, which `as u64` would wrap to a 0-bit field
            let count = (span + 1) as u128;
            let mut n = 0u32;
            while (1u128 << n) < count {
                n += 1;
            }
            if n > 56 {
                return Err(Pending::Unsupported(format!(
                    "INTEGER range needs {n} bits; the field cap is 56"
                )));
            }
            if aper() && count > 255 {
                return Ok(aper_int_range(lb, ub, count));
            }
            Ok(Compiled {
                owner: None,
                spec_ty: None,
                view: None,
                rust_ty: "i64".into(),
                fmt: format!("int_range_{lb}_{ub}_{n}"),
                proof_call: format!(
                    "assert(p2({n}) == {}) by {{ reveal_with_fuel(p2, {}); }} \
                     lemma_int_range_format({lb}, {ub}, {n});",
                    1u128 << n,
                    n + 2
                ),
                decode: format!(
                    "{{ let o_ = {{R}}.read_int_range({lb}, {ub}, {n}); {{R}}.same(o_, \"INTEGER ({lb}..{ub})\") }}"
                ),
                encode: format!("{{W}}.write_int_range({lb}, {ub}, {n}, {{V}})"),
                jer: "jer_int(*{V}, {O})".into(),
                arb: format!("{{G}}.range({lb}, {ub})"),
                preamble: vec![format!(
                    "assert(p2({n}) == {}) by {{ reveal_with_fuel(p2, {}); }}",
                    1u128 << n,
                    n + 2
                )],
            })
        }
        Type::Integer(c) => int_with_length(c, values),
        Type::Ref(name) => match env.get(name) {
            Some(c) => Ok(c.clone()),
            None => Err(Pending::Unresolved(name.clone())),
        },
        Type::Enumerated(_, _) => Err(Pending::Unsupported(
            "inline ENUMERATED in a field: hoist it to its own type assignment".into(),
        )),
        Type::Sequence(_, _) => Err(Pending::Unsupported(
            "inline SEQUENCE in a field: hoist it to its own type assignment".into(),
        )),
        Type::Choice(_, _) => Err(Pending::Unsupported("CHOICE is not implemented yet".into())),
        Type::SequenceOf(_, _) => {
            Err(Pending::Unsupported("SEQUENCE OF is not implemented yet".into()))
        }
        Type::BitString(_) | Type::NamedBitString(_) => {
            Err(Pending::Unsupported("BIT STRING is not implemented yet".into()))
        }
        Type::OctetString(_) => {
            Err(Pending::Unsupported("OCTET STRING is not implemented yet".into()))
        }
        Type::Str(..) => Err(Pending::Unsupported("internal: a character string is not a terminal".into())),
        Type::ObjectId | Type::RelativeOid | Type::Real => Err(Pending::Unsupported("internal: an OBJECT IDENTIFIER or REAL is not a terminal".into())),
        Type::Invalid(why) => Err(Pending::Unsupported(why.clone())),
        Type::Contains(_) => Err(Pending::Unsupported("internal: CONTAINING is not hoisted".into())),
        Type::Constrained(..) | Type::EnumeratedNum(..) | Type::Tagged(..) | Type::Set(..) | Type::SetOf(..) => {
            Err(Pending::Unsupported("internal: not resolved by constraints.rs".into()))
        }
        Type::Null => Ok(Compiled {
            owner: None,
            spec_ty: None,
            view: None,
            rust_ty: "Null".into(),
            fmt: "null".into(),
            proof_call: "lemma_null_format();".into(),
            decode: "{ let o_ = {R}.read_null(); {R}.same(o_, \"NULL\") }".into(),
            encode: "{W}.write_null({V})".into(),
            preamble: vec![],
            jer: "jer_null({O})".into(),
            arb: "Null".into(),
        }),
        Type::ParamRef(_, _) => {
            Err(Pending::Unsupported("parameterised types are not implemented yet".into()))
        }
    }
}

/// `#[inline]` on every exec function. Each ASN.1 type is a crate of its
/// own, and without it LLVM does not inline across them: DL-DCCH decoding is
/// 1.80 us/msg marked, against 2.75 before. Spec and
/// proof functions are erased, and are written `spec fn` and `proof fn`, so
/// they are left alone.
fn mark_inline(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + text.len() / 16);
    for line in text.split_inclusive('\n') {
        let t = line.trim_start();
        if t.starts_with("pub fn ") || t.starts_with("fn ") {
            out.push_str(&line[..line.len() - t.len()]);
            out.push_str("#[inline]\n");
        }
        out.push_str(line);
    }
    out
}

fn int_range_defs(c: &Compiled) -> Option<(i64, i64, u32)> {
    let p = c.fmt.strip_prefix("int_range_")?;
    let parts: Vec<&str> = p.split('_').collect();
    // the lower bound may itself be negative and therefore contain no separator
    let n: u32 = parts.last()?.parse().ok()?;
    let ub: i64 = parts[parts.len() - 2].parse().ok()?;
    let lb: i64 = parts[..parts.len() - 2].join("_").parse().ok()?;
    Some((lb, ub, n))
}

/// A terminal whose format is not one of the named ones carries its three
/// spec accessors in `fmt` as `spec:WF|ENC|DEC`.
fn spec_triple(c: &Compiled) -> Option<(String, String, String)> {
    let t = c.fmt.strip_prefix("spec:")?;
    let mut it = t.splitn(3, '|');
    Some((it.next()?.to_string(), it.next()?.to_string(), it.next()?.to_string()))
}

/// A constrained INTEGER whose range is over 255, in the ALIGNED variant
/// (X.691 11.5.7.2 to 11.5.7.4): one or two octets, octet-aligned, or the
/// indefinite length case (`vasn::aper::intx`).
fn aper_int_range(lb: i64, ub: i64, count: u128) -> Compiled {
    let what = format!("INTEGER ({lb}..{ub})");
    let base = |fmt: String, proof: String, pre: String, rd: String, wr: String| Compiled {
        owner: None,
        spec_ty: None,
        view: None,
        rust_ty: "i64".into(),
        fmt,
        proof_call: format!("{pre} {proof}"),
        decode: format!("{{ let o_ = {{R}}.{rd}; {{R}}.same(o_, \"{what}\") }}"),
        encode: format!("{{W}}.{wr}"),
        preamble: vec![pre],
        jer: "jer_int(*{V}, {O})".into(),
        arb: format!("{{G}}.range({lb}, {ub})"),
    };
    if count <= 65536 {
        let n = if count == 256 { 8 } else { 16 };
        let p2 = format!("assert(p2({n}) == {}) by {{ reveal_with_fuel(p2, {}); }}", 1u128 << n, n + 2);
        base(
            format!("spec:aint_range_wf({lb}, {ub}, {n})|aint_range_enc({lb}, {ub}, {n})|aint_range_dec({lb}, {ub}, {n})"),
            format!("lemma_aint_range_format({lb}, {ub}, {n});"),
            format!("{p2} lemma_aint_range_wf_all({lb}, {ub}, {n});"),
            format!("read_aint_range({lb}, {ub}, {n})"),
            format!("write_aint_range({lb}, {ub}, {n}, {{V}})"),
        )
    } else {
        base(
            format!("spec:cwn_big_wf({lb}, {ub})|cwn_big_enc({lb}, {ub})|cwn_big_dec({lb}, {ub})"),
            format!("lemma_cwn_big_format({lb}, {ub});"),
            format!("lemma_cwn_big_wf_all({lb}, {ub});"),
            format!("read_cwn_big({lb}, {ub})"),
            format!("write_cwn_big({lb}, {ub}, {{V}})"),
        )
    }
}

/// An INTEGER with a length, or with an extension bit (X.691 13.1, 13.2.3,
/// 13.2.4): `vasn::uper::intx`.
fn int_with_length(c: &IntCons, values: &HashMap<String, i64>) -> Result<Compiled, Pending> {
    let v = |n: &Num| lit(n, values).ok_or_else(|| Pending::Unsupported("INTEGER bound is an unknown value reference".into()));
    let term = |fmt: String, proof: String, preamble: Vec<String>, rd: String, wr: String, what: String, arb: String| Compiled {
        owner: None,
        spec_ty: None,
        view: None,
        rust_ty: "i64".into(),
        fmt,
        proof_call: proof,
        decode: format!("{{ let o_ = {{R}}.{rd}; {{R}}.same(o_, \"{what}\") }}"),
        encode: format!("{{W}}.{wr}"),
        preamble,
        jer: "jer_int(*{V}, {O})".into(),
        arb,
    };
    let (root, root_arb, out_arb, what, p2f) = match c {
        IntCons::Semi(lb) => {
            let lb = v(lb)?;
            return Ok(term(
                format!("spec:semi_wf({lb})|semi_enc({lb})|semi_dec({lb})"),
                format!("lemma_semi_format({lb});"),
                if aper() { vec![format!("lemma_semi_wf_all({lb});")] } else { vec![] },
                format!("read_{}semi({lb}i64)", if aper() { "a" } else { "" }),
                format!("write_{}semi({lb}i64, {{V}})", if aper() { "a" } else { "" }),
                format!("INTEGER ({lb}..MAX)"),
                format!("{{G}}.above({lb}i64)"),
            ));
        }
        IntCons::None => {
            return Ok(term(
                "spec:uc_wf()|uc_enc()|uc_dec()".into(),
                "lemma_uc_format();".into(),
                if aper() { vec!["lemma_uc_wf_every();".into()] } else { vec![] },
                if aper() { "read_auc()".into() } else { "read_uc()".into() },
                if aper() { "write_auc({V})".into() } else { "write_uc({V})".into() },
                "INTEGER".into(),
                "{G}.wide()".into(),
            ));
        }
        IntCons::RangeExt(a, b) => {
            let (lb, ub) = (v(a)?, v(b)?);
            if lb == ub {
                (
                    format!("XRoot::Const({lb}i64)"),
                    format!("{lb}i64"),
                    format!("{{ let x_ = {{G}}.wide(); if x_ == {lb}i64 {{ x_.wrapping_add(1) }} else {{ x_ }} }}"),
                    format!("INTEGER ({lb}, ...)"),
                    None,
                )
            } else {
                let count = (ub as i128 - lb as i128 + 1) as u128;
                let mut n = 0u32;
                while (1u128 << n) < count {
                    n += 1;
                }
                if n > 56 {
                    return Err(Pending::Unsupported(format!("INTEGER range needs {n} bits; the field cap is 56")));
                }
                (
                    format!("XRoot::Range({lb}i64, {ub}i64, {n})"),
                    format!("{{G}}.range({lb}, {ub})"),
                    format!(
                        "{{ let x_ = {{G}}.wide(); if {lb}i64 <= x_ && x_ <= {ub}i64 {{ if {ub}i64 < i64::MAX {{ {ub}i64 + 1 }} else {{ {lb}i64 - 1 }} }} else {{ x_ }} }}"
                    ),
                    format!("INTEGER ({lb}..{ub}, ...)"),
                    Some(n),
                )
            }
        }
        IntCons::SemiExt(a) => {
            let lb = v(a)?;
            (
                format!("XRoot::Semi({lb}i64)"),
                format!("{{G}}.above({lb}i64)"),
                if lb > i64::MIN {
                    format!("{{ let x_ = {{G}}.wide(); if x_ >= {lb}i64 {{ {lb}i64 - 1 }} else {{ x_ }} }}")
                } else {
                    format!("{{G}}.above({lb}i64)")
                },
                format!("INTEGER ({lb}..MAX, ...)"),
                None,
            )
        }
        IntCons::NoneExt => ("XRoot::All".into(), "{G}.wide()".into(), "{G}.wide()".into(), "INTEGER (..., ...)".into(), None),
        IntCons::Fixed(_) | IntCons::Range(..) => unreachable!("handled by the constrained INTEGER arm"),
    };
    let pre: Vec<String> = match p2f {
        Some(n) => vec![format!("assert(p2({n}) == {}) by {{ reveal_with_fuel(p2, {}); }}", 1u128 << n, n + 2)],
        None => vec![],
    };
    Ok(term(
        format!("spec:xint_r_wf({root})|xint_r_enc({root})|xint_r_dec({root})"),
        format!("{} lemma_xint_r_format({root});", pre.join(" ")),
        pre,
        format!("read_{}xint({root})", if aper() { "a" } else { "" }),
        format!("write_{}xint({root}, {{V}})", if aper() { "a" } else { "" }),
        what,
        format!("{{ if {{G}}.bool() {{ {root_arb} }} else {{ {out_arb} }} }}"),
    ))
}

/// The three spec accessors for an already-resolved component.
fn wf_of(c: &Compiled) -> String {
    if let Some((w, _, _)) = spec_triple(c) {
        return w;
    }
    if let Some(c) = c.fmt.strip_prefix("int_const_") {
        return format!("unit_wf({c}i64)");
    }
    match int_range_defs(c) {
        Some((lb, ub, n)) => format!("int_range_wf({lb}, {ub}, {n})"),
        None if c.fmt == "bool" => "bool_wf()".into(),
        None => format!("{}_wf()", rustify(&c.fmt)),
    }
}
fn enc_of(c: &Compiled) -> String {
    if let Some((_, e, _)) = spec_triple(c) {
        return e;
    }
    if c.fmt.starts_with("int_const_") {
        return "unit_enc::<i64>()".into();
    }
    match int_range_defs(c) {
        Some((lb, ub, n)) => format!("int_range_enc({lb}, {ub}, {n})"),
        None if c.fmt == "bool" => "bool_enc()".into(),
        None => format!("{}_enc()", rustify(&c.fmt)),
    }
}
fn dec_of(c: &Compiled) -> String {
    if let Some((_, _, d)) = spec_triple(c) {
        return d;
    }
    if let Some(c) = c.fmt.strip_prefix("int_const_") {
        return format!("unit_dec({c}i64)");
    }
    match int_range_defs(c) {
        Some((lb, ub, n)) => format!("int_range_dec({lb}, {ub}, {n})"),
        None if c.fmt == "bool" => "bool_dec()".into(),
        None => format!("{}_dec()", rustify(&c.fmt)),
    }
}

/// The whole-message decoder and encoder of an ALIGNED type (X.691 11.1.4,
/// `vasn::aper::complete`): the value from bit 0, then only zero padding to
/// the fewest octets. What a message's bytes are checked against, where the
/// type's own decoder reads a value off the front of whatever follows.
fn complete_fns(name: &str, c: &Compiled) -> String {
    let rn = rustify(name);
    let prim = matches!(c.rust_ty.as_str(), "bool" | "u8" | "u16" | "u32" | "i64" | "Null");
    let (wf, enc, dec) = (wf_of(c), enc_of(c), dec_of(c));
    let (rty, sty) = (&c.rust_ty, c.sty());
    let vv = c.view_of("v");
    let vm = c.view_of("(*v)");
    let mut pre = String::new();
    for p in &c.preamble {
        pre.push_str(&format!("    proof {{ {p} }}\n"));
    }
    format!(
        "// ---------------------------------------------------------------- {name}, complete (X.691 11.1.4)
pub fn {rn}_decode_complete(r: &mut BitReader) -> (res: Option<({rty}, Flg)>)
    requires old(r).wf(), old(r).pos == 0,
    ensures final(r).wf(), final(r).buf == old(r).buf,
        match res {{
            Some((v, f)) => complete_dec({dec}, bits_of(old(r).buf@)) == Some::<({sty}, Flg)>(({vv}, f)),
            None => complete_dec({dec}, bits_of(old(r).buf@)) is None,
        }},
{{
{pre}    proof {{ {proof} lemma_complete({wf}, {enc}, {dec}); }}
    let ghost b = bits_of(r.buf@);
    proof {{ assert(b.skip(0) =~= b); }}
    match {decode} {{
        Some((v, f)) => {{
            proof {{
                assert(b.len() == 8 * r.buf@.len());
                assert(b.len() % 8 == 0 && b.len() / 8 == r.buf@.len()) by (nonlinear_arith)
                    requires b.len() == 8 * r.buf@.len();
            }}
            if r.check_complete() {{
                Some((v, f))
            }} else {{
                r.fail(\"padding after the value: zero bits to the fewest octets (X.691 11.1.4)\");
                None
            }}
        }}
        None => None,
    }}
}}

pub fn {rn}_encode_complete(w: &mut BitWriter, v: &{rty}) -> (ok: bool)
    requires old(w).wf(), old(w).pos == 0, {wf}({vm}),
    ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),
        ok ==> final(w).written() =~= complete_enc({enc}, {vm}),
{{
{pre}    proof {{ {proof} lemma_written_len(*w); assert(w.written() =~= Seq::<bool>::empty()); }}
    if !{encode} {{ return false; }}
    proof {{ lemma_written_len(*w); }}
    w.pad_open()
}}

",
        proof = c.proof_call,
        decode = c.decode.replace("{R}", "r"),
        encode = c.encode.replace("{W}", "w").replace("{V}", if prim { "*v" } else { "v" }),
    )
}

mod aper_list;
mod choice_ext;
mod enum_ext;

fn gen_type(
    name: &str,
    ty: &Type,
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    match ty {
        Type::Enumerated(root, None) => gen_enum(name, root),
        Type::Enumerated(root, Some(ext)) => enum_ext::gen_enum_ext(name, root, ext),
        Type::Integer(IntCons::Fixed(v)) => gen_int_const(name, v, values),
        Type::Integer(IntCons::Range(a, b)) if lit(a, values).is_some() && lit(a, values) == lit(b, values) => {
            gen_int_const(name, a, values)
        }
        Type::Sequence(root, None) => gen_sequence(name, root, env, values, None),
        Type::SequenceOf(sc, inner) => {
            let elem = resolve(inner, env, values)?;
            gen_list_type(name, sc, elem, ListKind::Of, values)
        }
        Type::Choice(root, None) => gen_choice(name, root, env, values),
        Type::Choice(root, Some(ext)) => choice_ext::gen_choice_ext(name, root, ext, env, values),
        Type::BitString(sc) => gen_list_type(name, sc, bit_elem(), ListKind::Bits, values),
        Type::Str(StringKind::Utf8, _, _) => Ok(gen_utf8(name)),
        Type::ObjectId => Ok(gen_oid(name, false)),
        Type::RelativeOid => Ok(gen_oid(name, true)),
        Type::Real => Ok(gen_real(name)),
        Type::Str(kind, _, _) if kind.octets() => Ok(gen_octet_chars(name)),
        Type::Str(k @ (StringKind::GeneralizedTime | StringKind::UtcTime), _, _) => {
            // X.691 10.6.5: the VisibleString, in X.690 11.7's or 11.8's form
            let (base_text, bc) = gen_kmstring(&format!("{name}-chars"), k, &SizeCons::None, &None, values)?;
            let (ok, check, what, arb) = if *k == StringKind::UtcTime {
                ("utctime_ok", "utctime_check", "UTCTime: not YYMMDDHHMMSSZ (X.690 11.8, X.691 10.6.5)",
                 "{ format!(\"{:02}{:02}{:02}{:02}{:02}{:02}Z\", g.range(0, 99), g.range(1, 12), g.range(1, 31), g.range(0, 23), g.range(0, 59), g.range(0, 59)).into_bytes() }")
            } else {
                ("gtime_ok", "gtime_check", "GeneralizedTime: not YYYYMMDDHHMMSS[.F]Z (X.690 11.7, X.691 10.6.5)",
                 "{ let f = if g.bool() { String::new() } else { let mut f = format!(\".{}\", g.range(0, 999)); while f.ends_with('0') { f.pop(); } if f == \".\" { f.clear(); } f }; format!(\"{:04}{:02}{:02}{:02}{:02}{:02}{f}Z\", g.range(0, 9999), g.range(1, 12), g.range(1, 31), g.range(0, 23), g.range(0, 59), g.range(0, 59)).into_bytes() }")
            };
            let (wtext, wc) = restrict_wrap(
                &rustify(name),
                &bc,
                &format!("|s: Seq<u8>| vasn::time::{ok}(s)"),
                &format!("!vasn::time::{check}(v.as_slice())"),
                what,
                arb,
            );
            Ok((format!("{base_text}{wtext}"), wc))
        }
        Type::Str(kind, sc, alpha) => gen_kmstring(name, kind, sc, alpha, values),
        Type::NamedBitString(sc) => {
            // X.691 16.2, 16.3: the plain bit list, restricted to its shortest
            // form. The list is compiled under a name of its own, and the type
            // is that format restricted to no trailing 0 bit above `lb`
            let lb = match sc {
                SizeCons::None => 0,
                SizeCons::Fixed(n) | SizeCons::Range(n, _) | SizeCons::RangeExt(n, _)
                | SizeCons::Semi(n) | SizeCons::SemiExt(n) => {
                    lit(n, values).ok_or_else(|| Pending::Unsupported("SIZE bound is not a known literal".into()))?
                }
            };
            let (base_text, bc) = gen_list_type(&format!("{name}-bits"), sc, bit_elem(), ListKind::Bits, values)?;
            let rn = rustify(name);
            let (wtext, wc) = restrict_wrap(
                &rn,
                &bc,
                &format!("|s: Seq<bool>| s.len() <= {lb} || s[s.len() - 1]"),
                &format!("v.len() > {lb} && !v[v.len() - 1]"),
                "BIT STRING with named bits: a trailing 0 bit (X.691 16.3)",
                &format!("{{ let mut v = {}; while v.len() > {lb} && !v[v.len() - 1] {{ v.pop(); }} v }}", bc.arb.replace("{G}", "g")),
            );
            Ok((format!("{base_text}{wtext}"), wc))
        }
        Type::OctetString(sc) => gen_list_type(name, sc, byte_elem(), ListKind::Octets, values),
        Type::Sequence(root, Some(adds)) => gen_sequence_ext(name, root, adds, env, values),
        Type::Contains(inner) => Ok(gen_contains(name, &resolve(inner, env, values)?)),
        // A bare alias: reuse the target's format under a new Rust name.
        other => {
            let c = resolve(other, env, values)?;
            Ok((String::new(), c))
        }
    }
}

/// An extensible SEQUENCE (X.691 19).
///
/// Built in two halves. The root is an ordinary SEQUENCE, generated under a
/// hidden name by the machinery that already exists. The additions are a
/// right-nested chain of `opt(bm[i], open_type(F_i))` indexed by the presence
/// bitmap, and every hypothesis `ext_adds_ok` asks for is structural for a
/// chain of that shape. `lemma_ext_format` joins the two.
/// The JER members of an extensible SEQUENCE's root fields, over `v: &{rn}`
/// (whose struct carries them directly).
fn jer_root_members(
    root: &[Field],
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<String, Pending> {
    let mut out = String::new();
    for f in root {
        let cc = resolve(&f.ty, env, values)?;
        let presence = match &f.presence {
            Presence::Mandatory => String::new(),
            Presence::Optional => "opt".to_string(),
            Presence::Default(d) => default_expr(d, &cc)?,
        };
        out.push_str(&jer_member_of(&f.name, &rustify(&f.name), &cc, &presence));
    }
    Ok(out)
}

/// The generator's field initialisers for an extensible SEQUENCE's root.
fn arb_root_members(
    root: &[Field],
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<String, Pending> {
    let mut out = String::new();
    for f in root {
        let cc = resolve(&f.ty, env, values)?;
        let presence = match &f.presence {
            Presence::Mandatory => String::new(),
            Presence::Optional => "opt".to_string(),
            Presence::Default(d) => default_expr(d, &cc)?,
        };
        out.push_str(&format!("        {}: {},\n", rustify(&f.name), arb_member(&cc, &presence)));
    }
    Ok(out)
}

fn gen_sequence_ext(
    name: &str,
    root: &[Field],
    adds: &[ExtAdd],
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    let rn = rustify(name);
    let c = adds.len();
    if c == 0 {
        return gen_sequence_ext_empty(name, root, env, values);
    }
    if c >= 16384 {
        return Err(Pending::Unsupported(
            "a SEQUENCE with 16384 or more extension additions needs a fragmenting count".into(),
        ));
    }
    // the root, as its own type under a hidden name, with its encoder emitted
    // over this struct so that nothing has to be copied out of `&{rn}`
    let root_name = format!("{name}-root");
    let rrn = rustify(&root_name);
    let (root_text, root_c) = gen_sequence(&root_name, root, env, values, Some(&EncOver {
        fnp: format!("{rrn}_x"),
        mty: rn.clone(),
        view: format!("{rn}_rview"),
    }))?;
    let rsname = root_c.sty();

    // The additions. X.691 19.9: a `[[ ]]` group is **one** addition, whose
    // content is an ordinary sequence encoded per 19.2-19.6 -- a preamble for
    // its OPTIONAL components, but no extension bit of its own. That is
    // exactly what `gen_sequence` emits, so a group is a hidden type and then
    // an addition like any other.
    let mut parts: Vec<(String, Compiled)> = Vec::new();
    let mut group_text = String::new();
    for (i, a) in adds.iter().enumerate() {
        let (fname, cc) = match a {
            ExtAdd::One(f) => {
                let cc = resolve(&f.ty, env, values)?;
                match &f.presence {
                    // X.691 19.5: a DEFAULT addition equal to its default is
                    // not encoded (the bitmap bit is 0), so the addition's own
                    // format excludes the default, and a decoder that meets it
                    // encoded explicitly rejects it, as for a root component
                    Presence::Default(d) => {
                        let dv = default_expr(d, &cc)?;
                        let (wtext, wc) = restrict_wrap(
                            &format!("{rn}_dflt{i}"),
                            &cc,
                            &format!("|v: {}| v != {dv}", cc.sty()),
                            &format!("v == {dv}"),
                            "DEFAULT value, encoded explicitly (X.691 19.5)",
                            &cc.arb.replace("{G}", "g"),
                        );
                        group_text.push_str(&wtext);
                        (f.name.clone(), wc)
                    }
                    _ => (f.name.clone(), cc),
                }
            }
            ExtAdd::Group(g) => {
                let gname = format!("{name}-ext{i}");
                let (gtext, gc) = gen_sequence(&gname, g, env, values, None)?;
                group_text.push_str(&gtext);
                // X.691 19.9: a group whose component values are all missing
                // is a missing addition. That can happen only when every
                // component is OPTIONAL or DEFAULT; a DEFAULT one is missing
                // when it equals its default (19.5)
                let gc = if g.iter().all(|f| matches!(f.presence, Presence::Optional | Presence::Default(_))) {
                    let mut dfts = Vec::new();
                    for f in g {
                        dfts.push(match &f.presence {
                            Presence::Default(d) => Some(default_expr(d, &resolve(&f.ty, env, values)?)?),
                            _ => None,
                        });
                    }
                    let (wtext, wc) = group_nonempty(&format!("{rn}_g{i}"), g, &dfts, &gc);
                    group_text.push_str(&wtext);
                    wc
                } else {
                    gc
                };
                (format!("group{i}"), gc)
            },
        };
        parts.push((fname, cc));
    }
    let last = c - 1;
    // Whether any addition holds a list, and so has an exec value that is not
    // its own spec value. The additions chain is then stated over spec tuples
    // `{rn}_AT{i}` and run over exec tuples `{rn}_EAT{i}`, with a view between.
    let add_view = parts.iter().any(|(_, cc)| !cc.plain());

    // exec and spec type of addition `i`, which is always OPTIONAL
    let aty = |i: usize| -> String { format!("Option<{}>", parts[i].1.rust_ty) };
    let asty = |i: usize| -> String { format!("Option<{}>", parts[i].1.sty()) };
    let at = |i: usize| -> String {
        if i == last { asty(last) } else { format!("{rn}_AT{i}") }
    };
    let et = |i: usize| -> String {
        if i == last { aty(last) } else if add_view { format!("{rn}_EAT{i}") } else { format!("{rn}_AT{i}") }
    };
    // spec view of an exec `Option` of addition `i`; a match would move it
    let view_add = |i: usize, v: &str| -> String {
        let cc = &parts[i].1;
        if cc.plain() {
            v.to_string()
        } else {
            format!("if {v} is Some {{ Some({}) }} else {{ None }}", cc.view_of(&format!("{v}->Some_0")))
        }
    };
    // spec view of an exec suffix tuple from level `i`
    let view_at = |i: usize, v: &str| -> String {
        if i == last { view_add(last, v) }
        else if add_view { format!("{rn}_view_at{i}({v})") }
        else { v.to_string() }
    };
    let awf = |i: usize| -> String { format!("{rn}_awf_t{i}(bm)") };
    let aenc = |i: usize| -> String { format!("{rn}_aenc_t{i}(bm)") };
    let adec = |i: usize| -> String { format!("{rn}_adec_t{i}(bm)") };
    // the i-th addition's own format, before `opt` wraps it
    let iw = |i: usize| -> String { wf_of(&parts[i].1) };
    let ie = |i: usize| -> String { format!("open_enc({})", enc_of(&parts[i].1)) };
    let id = |i: usize| -> String { format!("open_dec({})", dec_of(&parts[i].1)) };
    let ow = |i: usize| -> String { format!("opt_wf(bm[{i}], {})", iw(i)) };
    let oe = |i: usize| -> String { format!("opt_enc(bm[{i}], {})", ie(i)) };
    let od = |i: usize| -> String { format!("opt_dec(bm[{i}], {})", id(i)) };

    let preambles = {
        let mut out = String::new();
        let mut seen = std::collections::HashSet::new();
        for (_, cc) in &parts {
            for pr in &cc.preamble {
                if seen.insert(pr.clone()) {
                    out.push_str(&format!("    proof {{ {pr} }}\n"));
                }
            }
        }
        out
    };

    let mut s = String::new();
    s.push_str(&root_text);
    s.push_str(&group_text);
    s.push_str(&format!(
        "// ------------------------------------------------- {name} (extensible)\n"
    ));

    // ---------------------------------------------------------- the family
    for i in (0..last).rev() {
        s.push_str(&format!("pub type {rn}_AT{i} = ({}, {});\n", asty(i), at(i + 1)));
        if add_view {
            s.push_str(&format!("pub type {rn}_EAT{i} = ({}, {});\n", aty(i), et(i + 1)));
        }
    }
    if add_view {
        for i in (0..last).rev() {
            s.push_str(&format!(
                "pub open spec fn {rn}_view_at{i}(v: {}) -> {} {{ ({}, {}) }}\n",
                et(i), at(i), view_add(i, "v.0"), view_at(i + 1, "v.1")
            ));
        }
    }
    s.push('\n');
    for i in (0..c).rev() {
        let (w, e, d) = if i == last {
            (ow(last), oe(last), od(last))
        } else {
            (
                format!("pair_wf({}, {})", ow(i), awf(i + 1)),
                format!("pair_enc({}, {})", oe(i), aenc(i + 1)),
                format!("pair_dec({}, {})", od(i), adec(i + 1)),
            )
        };
        // Opaque above the leaf, so each level sees one `pair` and a name for
        // the rest. The leaf is a single `opt` and stays transparent: there is
        // nothing below it to hide, and it is what the runners' contracts are
        // stated in.
        let op = if i == last { "" } else { "#[verifier::opaque]\n" };
        s.push_str(&format!(
            "{op}pub open spec fn {rn}_awf_t{i}(bm: Seq<bool>) -> Wf<{}> {{ {w} }}\n\
             {op}pub open spec fn {rn}_aenc_t{i}(bm: Seq<bool>) -> Enc<{}> {{ {e} }}\n\
             {op}pub open spec fn {rn}_adec_t{i}(bm: Seq<bool>) -> Dec<{}> {{ {d} }}\n",
            at(i), at(i), at(i)
        ));
    }
    s.push_str(&format!(
        "\npub open spec fn {rn}_wa() -> spec_fn(Seq<bool>) -> Wf<{0}> {{ |bm: Seq<bool>| {rn}_awf_t0(bm) }}\n\
         pub open spec fn {rn}_ea() -> spec_fn(Seq<bool>) -> Enc<{0}> {{ |bm: Seq<bool>| {rn}_aenc_t0(bm) }}\n\
         pub open spec fn {rn}_da() -> spec_fn(Seq<bool>) -> Dec<{0}> {{ |bm: Seq<bool>| {rn}_adec_t0(bm) }}\n",
        at(0)
    ));
    // the presence bitmap of a value, and the all-absent value. Addition `i`
    // sits at `.1` repeated `i` times, then `.0` unless it is the last.
    let proj_of = |base: &str, i: usize| -> String {
        let mut e = base.to_string();
        for _ in 0..i {
            e.push_str(".1");
        }
        if i != last {
            e.push_str(".0");
        }
        e
    };
    let proj = |i: usize| -> String { proj_of("e", i) };
    let bmof_items: Vec<String> = (0..c).map(|i| format!("{} is Some", proj(i))).collect();
    s.push_str(&format!(
        "pub open spec fn {rn}_bmof() -> spec_fn({}) -> Seq<bool> {{ |e: {}| seq![{}] }}\n",
        at(0), at(0), bmof_items.join(", ")
    ));
    let mut e0 = format!("None::<{}>", parts[last].1.sty());
    for i in (0..last).rev() {
        e0 = format!("(None::<{}>, {})", parts[i].1.sty(), e0);
    }
    s.push_str(&format!("pub open spec fn {rn}_e0() -> {} {{ {e0} }}\n\n", at(0)));
    // The suffix of the additions that level `i` still has to encode, named
    // and opaque, exactly as the root's `{rn}_tup_t{{i}}` is. Without it the
    // encoder carries all `c` additions' postconditions and an `c`-term
    // sequence equation in one query, which is over the rlimit by four
    // additions.
    for i in (0..last).rev() {
        s.push_str(&format!(
            "#[verifier::opaque]\npub open spec fn {rn}_asuf_t{i}(m: {rn}) -> {} {{ ({}, {}) }}\n",
            at(i), view_add(i, &format!("m.{}", rustify(&parts[i].0))),
            if i + 1 == last {
                view_add(last, &format!("m.{}", rustify(&parts[last].0)))
            } else {
                format!("{rn}_asuf_t{}(m)", i + 1)
            }
        ));
    }
    if last > 0 {
        s.push_str(&format!(
            "\npub proof fn {rn}_asuf0(m: {rn})\n\
             \x20   ensures {rn}_asuf_t0(m) == {rn}_from({rn}_view(m)).1,\n{{\n"
        ));
        for i in 0..last {
            s.push_str(&format!("    reveal({rn}_asuf_t{i});\n"));
        }
        s.push_str("}\n");
    }
    s.push('\n');

    // ------------------------------------------- hypothesis 1, one per level
    for i in (0..c).rev() {
        s.push_str(&format!(
            "pub proof fn {rn}_adds_format_t{i}(bm: Seq<bool>)\n\
             \x20   ensures is_format({}, {}, {}),\n{{\n\
             {}",
            awf(i), aenc(i), adec(i),
            if i == last { String::new() } else {
                format!("\x20   reveal({rn}_awf_t{i}); reveal({rn}_aenc_t{i}); reveal({rn}_adec_t{i});\n")
            }
        ));
        s.push_str(&format!("    {}\n", parts[i].1.proof_call));
        s.push_str(&format!(
            "    lemma_open_format({}, {}, {});\n\
             \x20   lemma_opt_format(bm[{i}], {}, {}, {});\n",
            iw(i), enc_of(&parts[i].1), dec_of(&parts[i].1),
            iw(i), ie(i), id(i)
        ));
        if i != last {
            s.push_str(&format!("    {rn}_adds_format_t{}(bm);\n", i + 1));
            s.push_str(&format!(
                "    lemma_pair_format({}, {}, {}, {}, {}, {});\n",
                ow(i), oe(i), od(i), awf(i + 1), aenc(i + 1), adec(i + 1)
            ));
        }
        s.push_str("}\n\n");
    }

    // ------------------------------------------ the three hypotheses, joined
    // APER: four times the default rlimit; once the encoders took the faster
    // writers, NR's `RF-Parameters` went over, its own text unchanged
    s.push_str(&format!(
        "{}pub proof fn {rn}_adds_ok()\n\
         \x20   ensures ext_adds_ok({c}, {rn}_wa(), {rn}_ea(), {rn}_da(), {rn}_bmof(), {rn}_e0()),\n\
         {{\n\
         \x20   reveal(opt_wf);\n\
         {}\
         \x20   assert forall|bm: Seq<bool>| bm.len() == {c} implies\n\
         \x20       is_format(#[trigger] {rn}_wa()(bm), {rn}_ea()(bm), {rn}_da()(bm))\n\
         \x20   by {{ {rn}_adds_format_t0(bm); }}\n\
         \x20   // `opt_wf` pins each addition's presence to its bitmap bit\n\
         \x20   assert forall|bm: Seq<bool>, e: {}| bm.len() == {c} && #[trigger] {rn}_wa()(bm)(e)\n\
         \x20       implies {rn}_bmof()(e) == bm\n\
         \x20   by {{ assert({rn}_bmof()(e) =~= bm); }}\n\
         \x20   assert(zeros({c}).len() == {c});\n\
         \x20   assert forall|e: {}| #[trigger] {rn}_wa()(zeros({c}))(e) implies e == {rn}_e0()\n\
         \x20   by {{ }}\n\
         \x20   assert({rn}_wa()(zeros({c}))({rn}_e0()));\n}}\n\n",
        if aper() { "#[verifier::rlimit(40)]\n" } else { "" },
        (0..last).map(|i| format!("    reveal({rn}_awf_t{i});\n")).collect::<String>(),
        at(0), at(0)
    ));

    // ------------------------------------------------------- the whole type
    let root_fields: Vec<String> = root.iter().map(|f| f.name.clone()).collect();
    let needs_view = !root_c.plain() || add_view;
    let sname = if needs_view { format!("{rn}_S") } else { rn.clone() };
    let add_fields: Vec<(String, String, String, String)> = (0..c).map(|i| {
        let f = rustify(&parts[i].0);
        (f.clone(), aty(i), asty(i), view_add(i, &format!("m.{f}")))
    }).collect();
    s.push_str(&ext_struct(&rn, &rsname, root, &add_fields, env, values, needs_view)?);

    let full_ty = format!("({rsname}, {})", at(0));
    let root_of = |v: &str| -> String {
        let mut out = format!("{rsname} {{ ");
        for f in &root_fields {
            out.push_str(&format!("{0}: {v}.{0}, ", rustify(f)));
        }
        out.push('}');
        out
    };
    let adds_of = |v: &str| -> String {
        let mut out = format!("{v}.{}", rustify(&parts[last].0));
        for i in (0..last).rev() {
            out = format!("({v}.{}, {})", rustify(&parts[i].0), out);
        }
        out
    };
    let mut to_fields = String::new();
    for f in &root_fields {
        to_fields.push_str(&format!("{}: t.0.{}, ", rustify(f), rustify(f)));
    }
    for i in 0..c {
        to_fields.push_str(&format!("{}: {}, ", rustify(&parts[i].0), proj_of("t.1", i)));
    }
    s.push_str(&format!(
        "pub open spec fn {rn}_to(t: {full_ty}) -> {sname} {{ {sname} {{ {to_fields}}} }}\n\
         pub open spec fn {rn}_from(m: {sname}) -> {full_ty} {{ ({}, {}) }}\n\
         pub open spec fn {rn}_to_f() -> spec_fn({full_ty}) -> {sname} {{ |t: {full_ty}| {rn}_to(t) }}\n\
         pub open spec fn {rn}_from_f() -> spec_fn({sname}) -> {full_ty} {{ |m: {sname}| {rn}_from(m) }}\n\n",
        root_of("m"), adds_of("m")
    ));
    s.push_str(&format!(
        "pub open spec fn {rn}_full_wf() -> Wf<{full_ty}> {{ ext_wf({rrn}_wf(), {c}, {rn}_wa(), {rn}_bmof()) }}\n\
         pub open spec fn {rn}_full_enc() -> Enc<{full_ty}> {{ ext_enc({rrn}_enc(), {c}, {rn}_ea(), {rn}_bmof()) }}\n\
         pub open spec fn {rn}_full_dec() -> Dec<{full_ty}> {{ ext_dec({rrn}_dec(), {c}, {rn}_da(), {rn}_e0()) }}\n\
         pub open spec fn {rn}_wf() -> Wf<{sname}> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_enc() -> Enc<{sname}> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_dec() -> Dec<{sname}> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n"
    ));
    s.push_str(&format!(
        "pub proof fn {rn}_is_format()\n\
         \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n{{\n\
         \x20   {rrn}_is_format();\n\
         \x20   {rn}_adds_ok();\n\
         \x20   lemma_ext_format({rrn}_wf(), {rrn}_enc(), {rrn}_dec(), {c},\n\
         \x20                    {rn}_wa(), {rn}_ea(), {rn}_da(), {rn}_bmof(), {rn}_e0());\n\
         \x20   assert forall|t: {full_ty}| {rn}_full_wf()(t) implies\n\
         \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t by {{ }}\n\
         \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(),\n\
         \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n\
         pub proof fn {rn}_field_bounds(m: &{rn})\n\
         \x20   requires {rn}_wf()({rn}_view(*m)),\n\
         \x20   ensures {rn}_full_wf()({rn}_from({rn}_view(*m))),\n{{\n\
         \x20   assert({rn}_from_f()({rn}_to_f()({rn}_from({rn}_view(*m)))) == {rn}_from({rn}_view(*m)));\n}}\n\n"
    ));

    // ----------------------------------------------- one addition, each way
    //
    // An addition is an open type, so the content is encoded into a scratch
    // buffer and measured before the determinant can be written, and on the
    // way back it is copied out and decoded from its own reader. `open_dec`
    // is stated over the extracted content, and a fragmented open type's
    // octets are not contiguous on the wire in any case.
    for i in 0..c {
        let (iwf, ienc, idec) = (iw(i), enc_of(&parts[i].1), dec_of(&parts[i].1));
        let pre: String = parts[i].1.preamble.iter()
            .map(|pr| format!("    proof {{ {pr} }}\n")).collect();
        let inner_dec = parts[i].1.decode.replace("{R}", "r2");
        // a single addition's errors are named after it; a group's components
        // name themselves
        let wrap = |e: &str| -> String {
            match &adds[i] {
                ExtAdd::One(f) => format!("{e} r.fail_in(\"{}\");", f.name),
                ExtAdd::Group(_) => e.to_string(),
            }
        };
        // APER's content lies whole in the buffer, octet-aligned: borrowed
        // rather than copied (`read_afrag_ref`)
        let oref = if aper() { "_ref" } else { "" };
        // Two runners: the open type alone, then OPTIONAL around it. As one
        // function, NR's `RF_Parameters_a6_run` went over the rlimit (at any
        // rlimit up to 20, and only under the default seed) though alone it
        // verified at 3; split, each query carries half the lemmas.
        s.push_str(&format!(
            "pub fn {rn}_a{i}_open(r: &mut BitReader) -> (res: Option<({ity}, Flg)>)\n\
             \x20   requires old(r).wf(),\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v, f)) => open_dec({idec})(old(r).rem())\n\
             \x20               == Some::<({isty}, nat, Flg)>(({vv}, (final(r).pos - old(r).pos) as nat, f)),\n\
             \x20           None => open_dec({idec})(old(r).rem()).is_none(),\n\
             \x20       }},\n{{\n{pre}\
             \x20   let ghost start = r.rem();\n\
             \x20   let ghost p0 = r.pos;\n\
             \x20   let content = match r.read_frag{oref}() {{\n\
             \x20       Some(cb) => cb,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_open_dec_none_len({idec}, start); }}\n\
             \x20           {e_len} return None;\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   let ghost k = (r.pos - p0) as nat;\n\
             \x20   let ghost cbits = bits_of(content@);\n\
             \x20   let mut r2 = BitReader::new(content.as_slice());\n\
             \x20   // by reference, so `{{R}}` works for both a method call on the\n\
             \x20   // reader and a generated decoder taking `&mut`\n\
             \x20   let r2 = &mut r2;\n{at0}\
             \x20   let (v, f) = match {inner_dec} {{\n\
             \x20       Some(vf) => vf,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_open_dec_none_content({idec}, start, cbits, k); }}\n\
             \x20           {e_in} return None;\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   let ghost k2 = r2.pos as nat;\n\
             \x20   if !ot_octets_eq(r2.pos, content.len()) || !r2.check_zero_tail() {{\n\
             \x20       proof {{ lemma_open_dec_none_pad({idec}, start, cbits, k); }}\n\
             \x20       {e_pad} return None;\n\
             \x20   }}\n\
             \x20   proof {{\n\
             \x20       assert(cbits.len() / 8 == content@.len()) by (nonlinear_arith)\n\
             \x20           requires cbits.len() == 8 * content@.len();\n\
             \x20       assert(cbits.skip(k2 as int) =~= zeros((cbits.len() - k2) as nat));\n\
             \x20       lemma_open_dec_some({idec}, start, cbits, k, {vv}, k2, f);\n\
             \x20   }}\n\
             \x20   Some((v, f))\n}}\n\n\
             pub fn {rn}_a{i}_run(r: &mut BitReader, present: bool) -> (res: Option<({aty}, Flg)>)\n\
             \x20   requires old(r).wf(),\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v, f)) => opt_dec(present, open_dec({idec}))(old(r).rem())\n\
             \x20               == Some::<({asty}, nat, Flg)>(({va}, (final(r).pos - old(r).pos) as nat, f)),\n\
             \x20           None => opt_dec(present, open_dec({idec}))(old(r).rem()).is_none(),\n\
             \x20       }},\n{{\n\
             \x20   let ghost start = r.rem();\n\
             \x20   let ghost p0 = r.pos;\n\
             \x20   if !present {{\n\
             \x20       proof {{ lemma_opt_dec_absent(open_dec({idec}), start); }}\n\
             \x20       return Some((None, Flg::SameVer));\n\
             \x20   }}\n\
             \x20   match {rn}_a{i}_open(r) {{\n\
             \x20       Some((v, f)) => {{\n\
             \x20           proof {{\n\
             \x20               lemma_opt_dec_some(open_enc({ienc}), open_dec({idec}), start, {vv},\n\
             \x20                                  (r.pos - p0) as nat, f);\n\
             \x20           }}\n\
             \x20           Some((Some(v), f))\n\
             \x20       }}\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_opt_dec_fail(open_dec({idec}), start); }}\n\
             \x20           None\n\
             \x20       }}\n\
             \x20   }}\n}}\n\n",
            ity = parts[i].1.rust_ty,
            isty = parts[i].1.sty(),
            aty = aty(i),
            asty = asty(i),
            va = view_add(i, "v"),
            vv = parts[i].1.view_of("v"),
            e_len = wrap("r.fail(\"open type length\");"),
            e_in = wrap("r.adopt(r2, content.len());"),
            e_pad = wrap("r.fail(\"open type padding\");"),
            // an open type's content is a complete encoding: it starts at 0
            at0 = if aper() { "\x20   proof { assert(r2.at() == (0nat, cbits)); }\n" } else { "" },
        ));

        let byref = !(parts[i].1.rust_ty == "bool" || parts[i].1.rust_ty == "i64"
                      || parts[i].1.rust_ty == "Null");
        let inner_enc = parts[i].1.encode.replace("{W}", "sc")
            .replace("{V}", if byref { "x" } else { "*x" });
        s.push_str(&format!(
            "pub fn {rn}_a{i}_enc_run(w: &mut BitWriter, present: bool, v: &{}) -> (ok: bool)\n\
             \x20   requires old(w).wf(), opt_wf(present, {iwf})({sv}),\n\
             \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
             \x20       ok ==> final(w).written()\n\
             \x20           =~= old(w).written() + {oe},\n\
             {{\n{pre}\
             \x20   proof {{ reveal(opt_wf); reveal(opt_enc); }}\n\
             \x20   let ghost w0 = *w;\n\
             \x20   match v {{\n\
             \x20       None => {{\n\
             \x20           proof {{ assert(w0.written()\n\
             \x20               + {oe0} =~= w0.written()); }}\n\
             \x20           true\n\
             \x20       }}\n\
             \x20       Some(x) => {{\n\
             \x20           // the content is part of the output, so the output's own\n\
             \x20           // buffer is always large enough to measure it in\n\
             \x20           let mut sc_ = w.scratch();\n\
             \x20           let sc = &mut sc_;\n\
             \x20           if !{inner_enc} {{ return false; }}\n\
             \x20           proof {{ lemma_ot_body_shape({ienc}, {sx}); }}\n\
             \x20           if !sc.pad_open() {{ return false; }}\n\
             \x20           proof {{ assert(bits_of(sc.buf@).take(sc.pos as int)\n\
             \x20                           =~= ot_body({ienc0}, {sx})); }}\n\
             \x20           let ok_ = w.write_{a}open(sc.buf.as_slice(), sc.pos,\n\
             \x20                                    Ghost({ienc}), Ghost({sx}));\n\
             \x20           w.give_back(sc_);\n\
             \x20           ok_\n\
             \x20       }}\n\
             \x20   }}\n}}\n\n",
            aty(i),
            sv = view_add(i, "(*v)"),
            sx = parts[i].1.view_of("(*x)"),
            oe = ea(&format!("opt_enc(present, open_enc({ienc}))"), OLD_POS, &view_add(i, "(*v)")),
            oe0 = ea(&format!("opt_enc(present, open_enc({ienc}))"), "w0.pos as nat", &view_add(i, "(*v)")),
            ienc0 = if aper() { format!("at0_enc({ienc})") } else { ienc.clone() },
            a = if aper() { "a" } else { "" },
        ));
    }

    // ---------------------------------------- the additions, as a pair chain
    for i in (0..last).rev() {
        let tail = if i + 1 == last {
            format!("{rn}_a{}_run(r, bm[{}])", last, last)
        } else {
            format!("{rn}_adec_t{}_run(r, bm)", i + 1)
        };
        let tailv = if i + 1 == last {
            format!("v{}", last)
        } else {
            format!("v{}", i + 1)
        };
        s.push_str(&format!(
            "pub fn {rn}_adec_t{i}_run(r: &mut BitReader, bm: &Vec<bool>) -> (res: Option<({}, Flg)>)\n\
             \x20   requires old(r).wf(), bm@.len() == {c},\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v, f)) => {rn}_adec_t{i}(bm@)(old(r).rem())\n\
             \x20               == Some::<({}, nat, Flg)>(({}, (final(r).pos - old(r).pos) as nat, f)),\n\
             \x20           None => {rn}_adec_t{i}(bm@)(old(r).rem()).is_none(),\n\
             \x20       }},\n{{\n\
             \x20   proof {{ reveal({rn}_adec_t{i}); {} }}\n\
             \x20   let ghost start = r.rem();\n\
             \x20   let ghost p0 = r.pos;\n\
             \x20   let (v{i}, f{i}) = match {rn}_a{i}_run(r, bm[{i}]) {{\n\
             \x20       Some(x) => x,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_pair_dec_none_fst({}, {}, start); }}\n\
             \x20           return None;\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n\
             \x20   let ghost kh = (r.pos - p0) as nat;\n\
             \x20   let ghost p1 = r.pos;\n\
             \x20   let ({tailv}, ft) = match {tail} {{\n\
             \x20       Some(x) => x,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_pair_dec_none_snd({}, {}, start, {hv}, kh, f{i}); }}\n\
             \x20           return None;\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{\n\
             \x20       lemma_pair_dec_some({}, {}, start, {hv}, kh, f{i},\n\
             \x20                           {tv}, (r.pos - p1) as nat, ft);\n\
             \x20   }}\n\
             \x20   Some(((v{i}, {tailv}), flg_join(f{i}, ft)))\n}}\n\n",
            et(i), at(i), view_at(i, "v"),
            String::new(),
            od(i).replace(&format!("bm[{i}]"), &format!("bm@[{i}]")), adec(i + 1).replace("(bm)", "(bm@)"),
            od(i).replace(&format!("bm[{i}]"), &format!("bm@[{i}]")), adec(i + 1).replace("(bm)", "(bm@)"),
            od(i).replace(&format!("bm[{i}]"), &format!("bm@[{i}]")), adec(i + 1).replace("(bm)", "(bm@)"),
            hv = view_add(i, &format!("v{i}")),
            tv = view_at(i + 1, &tailv),
        ));
    }
    let adec_run0 = if last == 0 {
        format!("{rn}_a0_run(r, bmu[0])")
    } else {
        format!("{rn}_adec_t0_run(r, &bmu)")
    };

    // ------------------------------------------------ the tail, three ways
    s.push_str(&format!(
        "pub fn {rn}_tail_run(r: &mut BitReader) -> (res: Option<({}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((e, f)) => ext_tail_dec({c}, {rn}_da(), old(r).rem())\n\
         \x20               == Some::<({}, nat, Flg)>(({}, (final(r).pos - old(r).pos) as nat, f)),\n\
         \x20           None => ext_tail_dec({c}, {rn}_da(), old(r).rem()).is_none(),\n\
         \x20       }},\n{{\n\
         \x20   let ghost start = r.rem();\n\
         \x20   let ghost p0 = r.pos;\n\
         \x20   let n = match r.read_nsld() {{ Some(n) => n, None => {{ r.fail(\"extension addition count\"); return None }} }};\n\
         \x20   proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n\
         \x20   let p1 = r.pos;\n\
         \x20   let bm = match r.read_bitmap(n as usize) {{ Some(v) => v, None => {{ r.fail(\"extension bitmap\"); return None }} }};\n\
         \x20   proof {{ lemma_rem_skip(r.buf@, p1 as nat, (r.pos - p1) as nat); }}\n\
         \x20   let p2p = r.pos;\n\
         \x20   // 19.8 NOTE: the extension bit is only set when something is present\n\
         \x20   if all_absent_run(&bm) {{ {{ r.fail(\"extension bitmap, all zero (X.691 19.8)\"); return None; }} }}\n\
         \x20   let bmu = bm_fit(&bm, {c});\n\
         \x20   let (e, fe) = match {adec_run0} {{ Some(x) => x, None => return None }};\n\
         \x20   proof {{ lemma_rem_skip(r.buf@, p2p as nat, (r.pos - p2p) as nat); }}\n\
         \x20   if n > {c} {{\n\
         \x20       // additions this schema has never heard of, stepped over by length\n\
         \x20       if !r.skip_adds_run(&bm, {c}) {{ {{ r.fail(\"unknown extension addition\"); return None; }} }}\n\
         \x20       proof {{ assert(bm@.skip({c}) == bm@.skip({c}int)); }}\n\
         \x20       Some((e, Flg::DiffVer))\n\
         \x20   }} else if n < {c} {{\n\
         \x20       Some((e, Flg::DiffVer))\n\
         \x20   }} else {{\n\
         \x20       Some((e, fe))\n\
         \x20   }}\n}}\n\n",
        et(0), at(0), view_at(0, "e")
    ));

    // ------------------------------------------------------------- decode
    let mut mk_fields = String::new();
    for f in &root_fields {
        mk_fields.push_str(&format!("{0}: root.{0}, ", rustify(f)));
    }
    let mut none_fields = String::new();
    for i in 0..c {
        none_fields.push_str(&format!("{}: None, ", rustify(&parts[i].0)));
    }
    let mut some_fields = String::new();
    for i in 0..c {
        some_fields.push_str(&format!("{}: {}, ", rustify(&parts[i].0), proj_of("e", i)));
    }
    // twice the default rlimit: once its module's encoders took the faster
    // writers, NR's `CellGroupConfig_decode` went over, its own text unchanged
    // (a module's queries share one solver)
    s.push_str(&format!(
        "#[verifier::rlimit(20)]\n\
         pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v, f)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<({sname}, nat, Flg)>(({rn}_view(v), (final(r).pos - old(r).pos) as nat, f)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n{{\n\
         \x20   let ghost start = r.rem();\n\
         \x20   let ghost p0 = r.pos;\n\
         \x20   let ext = match r.read_bool() {{\n\
         \x20       Some(b) => b,\n\
         \x20       None => {{\n\
         \x20           // `bool_dec` only fails on an empty sequence, which is the\n\
         \x20           // guard the spec puts in front of everything else\n\
         \x20           proof {{\n\
         \x20               reveal(map_dec);\n\
         \x20               assert(start.len() == 0);\n\
         \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           {{ r.fail(\"extension bit\"); return None; }}\n\
         \x20       }}\n\
         \x20   }};\n\
         \x20   proof {{\n\
         \x20       reveal(map_dec);\n\
         \x20       assert(start.len() >= 1);\n\
         \x20       lemma_bool_dec_bit(start);\n\
         \x20       lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat);\n\
         \x20   }}\n\
         \x20   let p1 = r.pos;\n\
         \x20   let (root, fr) = match {rrn}_decode(r) {{\n\
         \x20       Some(x) => x,\n\
         \x20       None => {{\n\
         \x20           proof {{ lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start); }}\n\
         \x20           return None;\n\
         \x20       }}\n\
         \x20   }};\n\
         \x20   proof {{\n\
         \x20       lemma_rem_skip(r.buf@, p1 as nat, (r.pos - p1) as nat);\n\
         \x20       assert(start.skip(1).skip((r.pos - p1) as int)\n\
         \x20              =~= start.skip((1 + (r.pos - p1)) as int));\n\
         \x20   }}\n\
         \x20   let ghost kr = (r.pos - p1) as nat;\n\
         \x20   // the root's fields are moved into the result below\n\
         \x20   let ghost rv = {rrn}_view(root);\n\
         \x20   let p2p = r.pos;\n\
         \x20   if !ext {{\n\
         \x20       proof {{\n\
         \x20           lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start,\n\
         \x20                              (rv, {rn}_e0()), (1 + kr) as nat, fr);\n\
         \x20       }}\n\
         \x20       return Some(({rn} {{ {mk_fields}{none_fields}}}, fr));\n\
         \x20   }}\n\
         \x20   match {rn}_tail_run(r) {{\n\
         \x20       Some((e, ft)) => {{\n\
         \x20           let ghost ev = {ev};\n\
         \x20           proof {{\n\
         \x20               lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, (rv, ev),\n\
         \x20                                  (1 + kr + (r.pos - p2p)) as nat, flg_add(fr, ft));\n\
         \x20           }}\n\
         \x20           Some(({rn} {{ {mk_fields}{some_fields}}}, flg_join(fr, ft)))\n\
         \x20       }}\n\
         \x20       None => {{\n\
         \x20           proof {{ lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start); }}\n\
         \x20           None\n\
         \x20       }}\n\
         \x20   }}\n}}\n\n",
        ev = view_at(0, "e")
    ));

    // ------------------------------------------------------------- encode
    //
    // One runner per addition, chained, each carrying only its own suffix --
    // the same shape as the root's `X_enc_t{i}_run`. Emitting the `c` calls
    // flat put all `c` postconditions and a `c`-term sequence equation into
    // `X_encode_long`'s single query, which is over the rlimit by four
    // additions.
    for i in (0..last).rev() {
        s.push_str(&format!(
            "pub fn {rn}_aenc_t{i}_run(w: &mut BitWriter, bm: &Vec<bool>, m: &{rn}) -> (ok: bool)\n\
             \x20   requires old(w).wf(), bm@.len() == {c},\n\
             \x20       {rn}_awf_t{i}(bm@)({rn}_asuf_t{i}(*m)),\n\
             \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
             \x20       ok ==> final(w).written()\n\
             \x20           =~= old(w).written() + {},\n\
             {{\n\
             \x20   proof {{\n\
             \x20       reveal({rn}_asuf_t{i});\n\
             \x20       reveal({rn}_awf_t{i});\n\
             \x20       reveal({rn}_aenc_t{i});\n\
             \x20   }}\n\
             \x20   if !{rn}_a{i}_enc_run(w, bm[{i}], &m.{}) {{ return false; }}\n\
             \x20   if !{} {{ return false; }}\n\
             \x20   true\n}}\n\n",
            ea(&format!("{rn}_aenc_t{i}(bm@)"), OLD_POS, &format!("{rn}_asuf_t{i}(*m)")),
            rustify(&parts[i].0),
            if i + 1 == last {
                format!("{rn}_a{}_enc_run(w, bm[{}], &m.{})", last, last, rustify(&parts[last].0))
            } else {
                format!("{rn}_aenc_t{}_run(w, bm, m)", i + 1)
            }
        ));
    }
    let adds_enc = if last == 0 {
        format!("    if !{rn}_a0_enc_run(w, bm[0], &m.{}) {{ return false; }}\n",
                rustify(&parts[0].0))
    } else {
        format!("    if !{rn}_aenc_t0_run(w, &bm, m) {{ return false; }}\n")
    };
    let bdecl: String = (0..c).map(|i| format!(
        "    let b{i} = m.{}.is_some();\n", rustify(&parts[i].0))).collect();
    let bvals: String = (0..c).map(|i| format!("b{i}")).collect::<Vec<_>>().join(", ");

    // The two shapes `ext_enc` can take, each as its own equation. Left inline
    // in the encoders they unfold `{rn}_enc`, `ext_enc`'s branch, `{rn}_from`
    // and `{rn}_bmof` in the same query as the writer calls, which is enough
    // to put a wide type over the rlimit -- and, as everywhere else here, it
    // is enough to pass alone and fail with the rest of the module in scope.
    // In APER each part starts where the one before it ended.
    let (pp, pa) = if aper() { ("pos: nat, ", "p0, ") } else { ("", "") };
    let root_e = ea(&format!("{rrn}_enc()"), "pos + 1", &format!("{rn}_rview(*m)"));
    let bmof_m = format!("{rn}_bmof()({rn}_from({rn}_view(*m)).1)");
    let long_rhs = if aper() {
        let p2 = format!("(pos + 1 + {root_e}.len())");
        let cnt = format!("ext_count_enc({p2}, {c})");
        let p3 = format!("({p2} + {cnt}.len())");
        let bmb = format!("ext_bm_enc({c})({p3}, {bmof_m})");
        format!("seq![true] + {root_e}\n\x20       + {cnt} + {bmb}\n\
                 \x20       + {rn}_ea()({bmof_m})({p3} + {bmb}.len(), {rn}_from({rn}_view(*m)).1)")
    } else {
        format!("seq![true] + {root_e}\n\x20       + ext_count_enc({c}) + ext_bm_enc({c})({bmof_m})\n\
                 \x20       + {rn}_ea()({bmof_m})({rn}_from({rn}_view(*m)).1)")
    };
    s.push_str(&format!(
        "pub proof fn {rn}_enc_short({pp}m: &{rn})\n\
         \x20   requires {rn}_wf()({rn}_view(*m)), all_absent({bmof_m}),\n\
         \x20   ensures {} =~= seq![false] + {root_e},\n\
         {{\n\x20   {rn}_field_bounds(m);\n\x20   {rn}_rview_ok(*m);\n}}\n\n\
         pub proof fn {rn}_enc_long({pp}m: &{rn})\n\
         \x20   requires {rn}_wf()({rn}_view(*m)), !all_absent({bmof_m}),\n\
         \x20   ensures {} =~= {long_rhs},\n\
         {{\n\x20   {rn}_field_bounds(m);\n\x20   {rn}_rview_ok(*m);\n}}\n\n",
        ea(&format!("{rn}_enc()"), "pos", &format!("{rn}_view(*m)")),
        ea(&format!("{rn}_enc()"), "pos", &format!("{rn}_view(*m)")),
    ));
    s.push_str(&format!(
        "pub fn {rn}_encode_short(w: &mut BitWriter, m: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({rn}_view(*m)), all_absent({rn}_bmof()({rn}_from({rn}_view(*m)).1)),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {enc},\n\
         {{\n{preambles}\
         {p0l}\
         \x20   proof {{ {rn}_enc_short({pa}m); {rn}_field_bounds(m); lemma_bool_enc_seq(false); }}\n\
         \x20   let ghost w0 = *w;\n\
         \x20   if !w.write_bool(false) {{ return false; }}\n\
         \x20   if !{rrn}_x_encode(w, m) {{ return false; }}\n\
         \x20   true\n}}\n\n",
        enc = ea(&format!("{rn}_enc()"), OLD_POS, &format!("{rn}_view(*m)")),
        p0l = if aper() { "\x20   let ghost p0 = w.pos as nat;\n" } else { "" },
    ));
    // APER: four times the default rlimit; once the encoders took the faster
    // writers, NR's `RF-ParametersMRDC` went over, its own text unchanged
    s.push_str(&format!(
        "{rl}pub fn {rn}_encode_long(w: &mut BitWriter, m: &{rn}, bm: &Vec<bool>) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({rn}_view(*m)), !all_absent({rn}_bmof()({rn}_from({rn}_view(*m)).1)),\n\
         \x20       bm@ == {rn}_bmof()({rn}_from({rn}_view(*m)).1),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {enc},\n\
         {{\n{preambles}\
         {p0l}\
         \x20   proof {{\n\
         \x20       {rn}_enc_long({pa}m); {rn}_field_bounds(m); lemma_bool_enc_seq(true);\n\
         {}\
         \x20   }}\n\
         \x20   let ghost w0 = *w;\n\
         \x20   if !w.write_bool(true) {{ return false; }}\n\
         \x20   if !{rrn}_x_encode(w, m) {{ return false; }}\n\
         \x20   if !w.write_nsld({c}) {{ return false; }}\n\
         \x20   if !w.write_bitmap(bm) {{ return false; }}\n\
         {adds_enc}\
         \x20   true\n}}\n\n",
        if last > 0 { format!("    {rn}_asuf0(*m);\n") } else { String::new() },
        enc = ea(&format!("{rn}_enc()"), OLD_POS, &format!("{rn}_view(*m)")),
        rl = if aper() { "#[verifier::rlimit(40)]\n" } else { "" },
        p0l = if aper() { "\x20   let ghost p0 = w.pos as nat;\n" } else { "" },
    ));
    // The bitmap as a `Vec`, in a query of its own. Built inline, its `c`
    // pushes and the `=~=` against `{rn}_bmof` shared a query with the record's
    // whole view and every writer call; with 14 additions and a 29-field
    // root (NR's `BandNR`) both encoders went over the rlimit.
    // Stated over the opaque additions record, not `{rn}_from({rn}_view(..)).1`,
    // which unfolds the record's whole view; `{rn}_encode` bridges the two
    // with `{rn}_asuf0`. And `vec![..]`, not `c` pushes: Verus cannot show 14
    // pushes equal to a 14-element `seq![..]` at the default rlimit at all,
    // even in a file of its own, while the macro form takes 0.3 s.
    let (adds_of, adds_reveal, adds_bridge) = if last > 0 {
        (
            format!("{rn}_asuf_t0(*m)"),
            (0..last).map(|i| format!("reveal({rn}_asuf_t{i}); ")).collect::<String>(),
            format!("    proof {{ {rn}_asuf0(*m); }}\n"),
        )
    } else {
        (format!("{rn}_from({rn}_view(*m)).1"), String::new(), String::new())
    };
    s.push_str(&format!(
        "pub fn {rn}_bm_vec(m: &{rn}) -> (bm: Vec<bool>)\n\
         \x20   ensures bm@ == {rn}_bmof()({adds_of}),\n\
         {{\n\
         {bdecl}\
         \x20   let bm: Vec<bool> = vec![{bvals}];\n\
         \x20   proof {{ {adds_reveal}assert(bm@ =~= {rn}_bmof()({adds_of})); }}\n\
         \x20   bm\n}}\n\n"
    ));
    s.push_str(&format!(
        "pub fn {rn}_encode(w: &mut BitWriter, m: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({rn}_view(*m)),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {},\n\
         {{\n\
         \x20   let bm = {rn}_bm_vec(m);\n\
         {adds_bridge}\
         \x20   if all_absent_run(&bm) {{\n\
         \x20       {rn}_encode_short(w, m)\n\
         \x20   }} else {{\n\
         \x20       {rn}_encode_long(w, m, &bm)\n\
         \x20   }}\n}}\n\n",
        ea(&format!("{rn}_enc()"), OLD_POS, &format!("{rn}_view(*m)")),
    ));

    // X.697 27.3 over root and additions alike; a group's components are
    // components of this SEQUENCE, so its members are spliced in unwrapped
    let mut members = jer_root_members(root, env, values)?;
    for (i, a) in adds.iter().enumerate() {
        let (fname, cc) = &parts[i];
        members.push_str(&match a {
            ExtAdd::One(f) => jer_member_of(&f.name, &rustify(fname), cc, "opt"),
            ExtAdd::Group(_) => format!(
                "    if let Some(x) = &v.{} {{ {}_jer_members(x, o, first); }}\n",
                rustify(fname), cc.rust_ty
            ),
        });
    }
    s.push_str(&jer_seq(&rn, &members));
    // an addition present or not as the entropy says; a group whose every
    // component is OPTIONAL or DEFAULT is absent when they are all missing
    // (X.691 19.9), which is also the only value its format admits
    let mut lit = format!("    {rn} {{\n{}", arb_root_members(root, env, values)?);
    for (i, a) in adds.iter().enumerate() {
        let (fname, cc) = &parts[i];
        let val = cc.arb.replace("{G}", "g");
        lit.push_str(&match a {
            ExtAdd::Group(gf) if gf.iter().all(|f| matches!(f.presence, Presence::Optional | Presence::Default(_))) => {
                let mut missing = Vec::new();
                for f in gf {
                    missing.push(match &f.presence {
                        Presence::Default(d) => {
                            format!("x.{} == {}", rustify(&f.name), default_expr(d, &resolve(&f.ty, env, values)?)?)
                        }
                        _ => format!("x.{}.is_none()", rustify(&f.name)),
                    });
                }
                let none = missing.join(" && ");
                format!(
                    "        {}: if g.bool() {{ let x = {val}; if {none} {{ None }} else {{ Some(x) }} }} else {{ None }},\n",
                    rustify(fname)
                )
            }
            // a DEFAULT addition equal to its default is the absent one
            ExtAdd::One(f) if matches!(f.presence, Presence::Default(_)) => {
                let Presence::Default(d) = &f.presence else { unreachable!() };
                let dv = default_expr(d, &resolve(&f.ty, env, values)?)?;
                format!(
                    "        {}: if g.bool() {{ let x = {val}; if x == {dv} {{ None }} else {{ Some(x) }} }} else {{ None }},\n",
                    rustify(fname)
                )
            }
            _ => format!("        {}: if g.bool() {{ Some({val}) }} else {{ None }},\n", rustify(fname)),
        });
    }
    lit.push_str("    }\n");
    s.push_str(&arb_fn(&rn, &lit));
    Ok((s, Compiled {
        jer: format!("{rn}_jer({{V}}, {{O}})"),
        arb: format!("{rn}_arb({{G}})"),
        rust_ty: rn.clone(),
        fmt: rn.clone(),
        proof_call: format!("{rn}_is_format();"),
        decode: format!("{rn}_decode({{R}})"),
        encode: format!("{rn}_encode({{W}}, {{V}})"),
        preamble: vec![],
        owner: None,
        spec_ty: if needs_view { Some(sname.clone()) } else { None },
        view: if needs_view { Some(format!("{rn}_view({{V}})")) } else { None },
    }))
}

/// A `[[ ]]` group whose every component is OPTIONAL, narrowed to exclude the
/// value with all of them absent.
///
/// X.691 19.9 has the group absent altogether in that case, so present-but-
/// empty is not an encoding of anything. Without this the generated type has
/// two values for one abstract value -- `None` and `Some` of the empty group --
/// which encode differently. That does not break injectivity, but a decoder
/// that accepts the second is laxer than the standard, and than VUPER, whose
/// `restrict_add_format check_all_none` rejects it in both directions.
fn group_nonempty(wn: &str, g: &[Field], dfts: &[Option<String>], gc: &Compiled) -> (String, Compiled) {
    let gn = &gc.fmt;
    let sty = gc.sty();
    let fields: Vec<String> = g.iter().map(|f| rustify(&f.name)).collect();
    // present: an OPTIONAL one is `Some`, a DEFAULT one differs from its default
    let spec_any = fields
        .iter()
        .zip(dfts)
        .map(|(f, d)| match d {
            Some(dv) => format!("v.{f} != {dv}"),
            None => format!("v.{f} is Some"),
        })
        .collect::<Vec<_>>()
        .join(" || ");
    let exec_none = fields
        .iter()
        .zip(dfts)
        .map(|(f, d)| match d {
            Some(dv) => format!("v.{f} == {dv}"),
            None => format!("v.{f}.is_none()"),
        })
        .collect::<Vec<_>>()
        .join(" && ");
    let vv = gc.view_of("v");
    let vm = gc.view_of("*v");
    let text = format!(
        "// ------------------------------------ {gn}, with at least one component
         pub open spec fn {wn}_some() -> spec_fn({sty}) -> bool {{ |v: {sty}| {spec_any} }}
         pub open spec fn {wn}_wf() -> Wf<{sty}> {{ restrict_wf({gn}_wf(), {wn}_some()) }}
         pub open spec fn {wn}_enc() -> Enc<{sty}> {{ {gn}_enc() }}
         pub open spec fn {wn}_dec() -> Dec<{sty}> {{ restrict_dec({gn}_dec(), {wn}_some()) }}

         pub proof fn {wn}_is_format()
             ensures is_format({wn}_wf(), {wn}_enc(), {wn}_dec()),
{{
             {gn}_is_format();
             lemma_restrict_format({gn}_wf(), {gn}_enc(), {gn}_dec(), {wn}_some());
}}

         pub fn {wn}_decode(r: &mut BitReader) -> (res: Option<({rty}, Flg)>)
             requires old(r).wf(),
             ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,
                 match res {{
                     Some((v, f)) => {wn}_dec()(old(r).rem())
                         == Some::<({sty}, nat, Flg)>(({vv}, (final(r).pos - old(r).pos) as nat, f)),
                     None => {wn}_dec()(old(r).rem()).is_none(),
                 }},
{{
             let ghost start = r.rem();
             let ghost p0 = r.pos;
             match {gn}_decode(r) {{
                 Some((v, f)) => {{
                     if {exec_none} {{
                         proof {{ lemma_restrict_dec_none({gn}_dec(), {wn}_some(), start); }}
                         {{ r.fail(\"extension group, present but empty (X.691 19.9)\"); None }}
                     }} else {{
                         proof {{ lemma_restrict_dec_some({gn}_dec(), {wn}_some(), start, {vv},
                                                         (r.pos - p0) as nat, f); }}
                         Some((v, f))
                     }}
                 }}
                 None => {{
                     proof {{ lemma_restrict_dec_none({gn}_dec(), {wn}_some(), start); }}
                     None
                 }}
             }}
}}

         pub fn {wn}_encode(w: &mut BitWriter, v: &{rty}) -> (ok: bool)
             requires old(w).wf(), {wn}_wf()({vm}),
             ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),
                 ok ==> final(w).written() =~= old(w).written() + {wenc},
{{
             proof {{ lemma_restrict_wf_val({gn}_wf(), {wn}_some(), {vm}); }}
             {gn}_encode(w, v)
}}

",
        rty = gc.rust_ty,
        wenc = ea(&format!("{wn}_enc()"), OLD_POS, &vm),
    );
    let wc = Compiled {
        fmt: wn.to_string(),
        proof_call: format!("{wn}_is_format();"),
        decode: format!("{wn}_decode({{R}})"),
        encode: format!("{wn}_encode({{W}}, {{V}})"),
        ..gc.clone()
    };
    (text, wc)
}

/// Type `rn` as `base` restricted to the values satisfying `spec_pred` (a
/// closure over the spec value), with a decoder that rejects the rest
/// (`exec_bad`, over the exec value `v`) as `why`. `lemma_restrict_format`
/// carries the proof; the generator is `arb`, which only makes values that
/// satisfy the predicate. `base` may be a named format or a terminal one
/// (`int_range`, `bool`), used inline.
fn restrict_wrap(rn: &str, base: &Compiled, spec_pred: &str, exec_bad: &str, why: &str, arb: &str) -> (String, Compiled) {
    let (bwf, benc, bdec) = (wf_of(base), enc_of(base), dec_of(base));
    let prim = matches!(base.rust_ty.as_str(), "bool" | "u8" | "u16" | "u32" | "i64" | "Null");
    let bdecode = base.decode.replace("{R}", "r");
    // a primitive is passed by value, as its own encoder takes it
    let bencode = base.encode.replace("{W}", "w").replace("{V}", "v");
    let vparam = if prim { base.rust_ty.clone() } else { format!("&{}", base.rust_ty) };
    let bproof = &base.proof_call;
    // the base's proof preamble: wrapped in exec code, bare in a proof fn
    let mut pre = String::new();
    let mut pre_proof = String::new();
    for p in &base.preamble {
        pre.push_str(&format!("    proof {{ {p} }}\n"));
        pre_proof.push_str(&format!("    {p}\n"));
    }
    let sty = base.sty();
    let rty = &base.rust_ty;
    let vv = base.view_of("v");
    let vm = if prim { base.view_of("v") } else { base.view_of("(*v)") };
    let text = format!(
        "// ---------------------------------------------------------------- {rn}
pub open spec fn {rn}_ok() -> spec_fn({sty}) -> bool {{ {spec_pred} }}
pub open spec fn {rn}_wf() -> Wf<{sty}> {{ restrict_wf({bwf}, {rn}_ok()) }}
pub open spec fn {rn}_enc() -> Enc<{sty}> {{ {benc} }}
pub open spec fn {rn}_dec() -> Dec<{sty}> {{ restrict_dec({bdec}, {rn}_ok()) }}

pub proof fn {rn}_is_format()
    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),
{{
{pre_proof}    {bproof}
    lemma_restrict_format({bwf}, {benc}, {bdec}, {rn}_ok());
}}

pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rty}, Flg)>)
    requires old(r).wf(),
    ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,
        match res {{
            Some((v, f)) => {rn}_dec()(old(r).rem())
                == Some::<({sty}, nat, Flg)>(({vv}, (final(r).pos - old(r).pos) as nat, f)),
            None => {rn}_dec()(old(r).rem()).is_none(),
        }},
{{
{pre}    let ghost start = r.rem();
    let ghost p0 = r.pos;
    match {bdecode} {{
        Some((v, f)) => {{
            if {exec_bad} {{
                proof {{ lemma_restrict_dec_none({bdec}, {rn}_ok(), start); }}
                {{ r.fail(\"{why}\"); None }}
            }} else {{
                proof {{ lemma_restrict_dec_some({bdec}, {rn}_ok(), start, {vv}, (r.pos - p0) as nat, f); }}
                Some((v, f))
            }}
        }}
        None => {{
            proof {{ lemma_restrict_dec_none({bdec}, {rn}_ok(), start); }}
            None
        }}
    }}
}}

pub fn {rn}_encode(w: &mut BitWriter, v: {vparam}) -> (ok: bool)
    requires old(w).wf(), {rn}_wf()({vm}),
    ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),
        ok ==> final(w).written() =~= old(w).written() + {wenc},
{{
{pre}    proof {{ lemma_restrict_wf_val({bwf}, {rn}_ok(), {vm}); }}
    {bencode}
}}

#[verifier::external]
pub fn {rn}_arb(g: &mut Gen) -> {rty} {{ {arb} }}

",
        wenc = ea(&format!("{rn}_enc()"), OLD_POS, &vm),
    );
    let wc = Compiled {
        fmt: rn.to_string(),
        proof_call: format!("{rn}_is_format();"),
        decode: format!("{rn}_decode({{R}})"),
        encode: format!("{rn}_encode({{W}}, {{V}})"),
        arb: format!("{rn}_arb({{G}})"),
        preamble: vec![],
        ..base.clone()
    };
    (text, wc)
}

/// An extensible SEQUENCE's struct: its root fields flat, then its additions.
/// When any of them holds a list, also the spec companion `{rn}_S` the format
/// is stated over, exactly as `gen_sequence` does; `{rn}_view` maps one to the
/// other either way, and `{rn}_rview` picks the root's spec value out of an
/// exec value, which is what the root's encoders are emitted against.
///
/// `adds` is (field, exec type, spec type, spec view of `m.field`).
fn ext_struct(
    rn: &str,
    rsname: &str,
    root: &[Field],
    adds: &[(String, String, String, String)],
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
    needs_view: bool,
) -> Result<String, Pending> {
    // (field, exec type, spec type, spec view of `m.field`)
    let mut fields: Vec<(String, String, String, String)> = Vec::new();
    for f in root {
        let cc = resolve(&f.ty, env, values)?;
        let fname = rustify(&f.name);
        let m = format!("m.{fname}");
        fields.push(if !matches!(f.presence, Presence::Optional) {
            (fname, cc.rust_ty.clone(), cc.sty(), cc.view_of(&m))
        } else {
            let view = if cc.plain() {
                m.clone()
            } else {
                // a match here would move the value; the accessor keeps it a view
                format!("if {m} is Some {{ Some({}) }} else {{ None }}", cc.view_of(&format!("{m}->Some_0")))
            };
            (fname, format!("Option<{}>", cc.rust_ty), format!("Option<{}>", cc.sty()), view)
        });
    }
    fields.extend(adds.iter().cloned());

    let mut s = String::new();
    let derives = if needs_view {
        "#[derive(PartialEq, Eq, Debug)]"
    } else {
        "#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]"
    };
    s.push_str(&format!("{derives}\npub struct {rn} {{\n"));
    for (f, t, _, _) in &fields {
        s.push_str(&format!("    pub {f}: {t},\n"));
    }
    s.push_str("}\n\n");
    if needs_view {
        s.push_str(&format!("pub struct {rn}_S {{\n"));
        for (f, _, t, _) in &fields {
            s.push_str(&format!("    pub {f}: {t},\n"));
        }
        s.push_str("}\n\n");
        s.push_str(&format!("pub open spec fn {rn}_view(m: {rn}) -> {rn}_S {{\n    {rn}_S {{\n"));
        for (f, _, _, v) in &fields {
            s.push_str(&format!("        {f}: {v},\n"));
        }
        s.push_str("    }\n}\n");
    } else {
        s.push_str(&format!("pub open spec fn {rn}_view(m: {rn}) -> {rn} {{ m }}\n"));
    }
    // A single literal, not `{rn}_from({rn}_view(m)).0`: the root's encoders
    // mention this in every query, and the composed form unfolds two n-field
    // literals where one will do -- enough to put a 17-field NR root over the
    // rlimit. That the two agree is proved once, in `{rn}_rview_ok`.
    s.push_str(&format!("pub open spec fn {rn}_rview(m: {rn}) -> {rsname} {{\n    {rsname} {{\n"));
    for (f, _, _, v) in &fields[..root.len()] {
        s.push_str(&format!("        {f}: {v},\n"));
    }
    s.push_str("    }\n}\n\n");
    s.push_str(&format!(
        "pub proof fn {rn}_rview_ok(m: {rn})\n\
         \x20   ensures {rn}_rview(m) == {rn}_from({rn}_view(m)).0,\n{{\n}}\n\n"
    ));
    Ok(s)
}

/// `SEQUENCE { a, b, ... }` -- extensible, but with nothing after the marker.
///
/// Very common: ETSI ITS marks six types this way and 3GPP does it constantly,
/// to leave room for a later version without spending anything now. The
/// encoder always writes a clear extension bit, because there is nothing it
/// could add; the decoder still has to accept a set one, read the count and
/// bitmap a newer peer sent, step over every addition it names, and report
/// `DiffVer`.
///
/// It is the same combinator with `c == 0`. The additions record is then a
/// type with one value and no bits -- `Null` -- and its bitmap is empty, so
/// `ext_enc`'s long branch is unreachable and `ext_dec` only ever takes the
/// `n > c` one.
fn gen_sequence_ext_empty(
    name: &str,
    root: &[Field],
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    let rn = rustify(name);
    let root_name = format!("{name}-root");
    let rrn = rustify(&root_name);
    let (root_text, root_c) = gen_sequence(&root_name, root, env, values, Some(&EncOver {
        fnp: format!("{rrn}_x"),
        mty: rn.clone(),
        view: format!("{rn}_rview"),
    }))?;
    let rsname = root_c.sty();
    let full_ty = format!("({rsname}, Null)");

    let mut s = String::new();
    s.push_str(&root_text);
    s.push_str(&format!(
        "// ------------------------------------------- {name} (extensible, no additions)\n"
    ));
    s.push_str(&format!(
        "pub open spec fn {rn}_wa() -> spec_fn(Seq<bool>) -> Wf<Null> {{ |bm: Seq<bool>| null_wf() }}\n\
         pub open spec fn {rn}_ea() -> spec_fn(Seq<bool>) -> Enc<Null> {{ |bm: Seq<bool>| null_enc() }}\n\
         pub open spec fn {rn}_da() -> spec_fn(Seq<bool>) -> Dec<Null> {{ |bm: Seq<bool>| null_dec() }}\n\
         pub open spec fn {rn}_bmof() -> spec_fn(Null) -> Seq<bool> {{ |e: Null| Seq::<bool>::empty() }}\n\
         pub open spec fn {rn}_e0() -> Null {{ Null }}\n\n\
         pub proof fn {rn}_adds_ok()\n\
         \x20   ensures ext_adds_ok(0, {rn}_wa(), {rn}_ea(), {rn}_da(), {rn}_bmof(), {rn}_e0()),\n\
         {{\n\
         \x20   lemma_null_format();\n\
         \x20   reveal(unit_wf);\n\
         \x20   assert forall|bm: Seq<bool>| bm.len() == 0 implies\n\
         \x20       is_format(#[trigger] {rn}_wa()(bm), {rn}_ea()(bm), {rn}_da()(bm)) by {{ }}\n\
         \x20   assert forall|bm: Seq<bool>, e: Null| bm.len() == 0 && #[trigger] {rn}_wa()(bm)(e)\n\
         \x20       implies {rn}_bmof()(e) == bm by {{ assert({rn}_bmof()(e) =~= bm); }}\n\
         \x20   assert forall|e: Null| #[trigger] {rn}_wa()(zeros(0))(e) implies e == {rn}_e0()\n\
         \x20   by {{ }}\n\
         \x20   assert({rn}_wa()(zeros(0))({rn}_e0()));\n}}\n\n"
    ));

    let root_fields: Vec<String> = root.iter().map(|f| f.name.clone()).collect();
    let needs_view = !root_c.plain();
    let sname = if needs_view { format!("{rn}_S") } else { rn.clone() };
    s.push_str(&ext_struct(&rn, &rsname, root, &[], env, values, needs_view)?);
    let root_of = |v: &str| -> String {
        let mut out = format!("{rsname} {{ ");
        for f in &root_fields {
            out.push_str(&format!("{0}: {v}.{0}, ", rustify(f)));
        }
        out.push('}');
        out
    };
    let mut to_fields = String::new();
    let mut mk_fields = String::new();
    for f in &root_fields {
        to_fields.push_str(&format!("{0}: t.0.{0}, ", rustify(f)));
        mk_fields.push_str(&format!("{0}: root.{0}, ", rustify(f)));
    }
    s.push_str(&format!(
        "pub open spec fn {rn}_to(t: {full_ty}) -> {sname} {{ {sname} {{ {to_fields}}} }}\n\
         pub open spec fn {rn}_from(m: {sname}) -> {full_ty} {{ ({}, Null) }}\n\
         pub open spec fn {rn}_to_f() -> spec_fn({full_ty}) -> {sname} {{ |t: {full_ty}| {rn}_to(t) }}\n\
         pub open spec fn {rn}_from_f() -> spec_fn({sname}) -> {full_ty} {{ |m: {sname}| {rn}_from(m) }}\n\
         pub open spec fn {rn}_full_wf() -> Wf<{full_ty}> {{ ext_wf({rrn}_wf(), 0, {rn}_wa(), {rn}_bmof()) }}\n\
         pub open spec fn {rn}_full_enc() -> Enc<{full_ty}> {{ ext_enc({rrn}_enc(), 0, {rn}_ea(), {rn}_bmof()) }}\n\
         pub open spec fn {rn}_full_dec() -> Dec<{full_ty}> {{ ext_dec({rrn}_dec(), 0, {rn}_da(), {rn}_e0()) }}\n\
         pub open spec fn {rn}_wf() -> Wf<{sname}> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_enc() -> Enc<{sname}> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_dec() -> Dec<{sname}> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n\
         pub proof fn {rn}_is_format()\n\
         \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n{{\n\
         \x20   {rrn}_is_format();\n\
         \x20   {rn}_adds_ok();\n\
         \x20   lemma_ext_format({rrn}_wf(), {rrn}_enc(), {rrn}_dec(), 0,\n\
         \x20                    {rn}_wa(), {rn}_ea(), {rn}_da(), {rn}_bmof(), {rn}_e0());\n\
         \x20   assert forall|t: {full_ty}| {rn}_full_wf()(t) implies\n\
         \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t by {{ }}\n\
         \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(),\n\
         \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n\
         pub proof fn {rn}_field_bounds(m: &{rn})\n\
         \x20   requires {rn}_wf()({rn}_view(*m)),\n\
         \x20   ensures {rn}_full_wf()({rn}_from({rn}_view(*m))),\n{{\n\
         \x20   assert({rn}_from_f()({rn}_to_f()({rn}_from({rn}_view(*m)))) == {rn}_from({rn}_view(*m)));\n}}\n\n",
        root_of("m")
    ));

    // the tail: only reachable from a peer that has additions we do not
    s.push_str(&format!(
        "pub fn {rn}_tail_run(r: &mut BitReader) -> (res: Option<(Null, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((e, f)) => ext_tail_dec(0, {rn}_da(), old(r).rem())\n\
         \x20               == Some::<(Null, nat, Flg)>((e, (final(r).pos - old(r).pos) as nat, f)),\n\
         \x20           None => ext_tail_dec(0, {rn}_da(), old(r).rem()).is_none(),\n\
         \x20       }},\n{{\n\
         \x20   let ghost start = r.rem();\n\
         \x20   let ghost p0 = r.pos;\n\
         \x20   let n = match r.read_nsld() {{ Some(n) => n, None => {{ r.fail(\"extension addition count\"); return None }} }};\n\
         \x20   proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n\
         \x20   let p1 = r.pos;\n\
         \x20   let bm = match r.read_bitmap(n as usize) {{ Some(v) => v, None => {{ r.fail(\"extension bitmap\"); return None }} }};\n\
         \x20   proof {{ lemma_rem_skip(r.buf@, p1 as nat, (r.pos - p1) as nat); }}\n\
         \x20   if all_absent_run(&bm) {{ {{ r.fail(\"extension bitmap, all zero (X.691 19.8)\"); return None; }} }}\n\
         \x20   // every addition is one we have never heard of, so every one is\n\
         \x20   // stepped over by its open type's length, and the empty additions\n\
         \x20   // record itself costs no bits\n\
         \x20   proof {{\n\
         \x20       assert(bm@.take(0) =~= Seq::<bool>::empty());\n\
         \x20       lemma_unit_dec_val(Null, r.rem());\n\
         \x20       assert(r.rem().skip(0) =~= r.rem());\n\
         \x20   }}\n\
         \x20   if !r.skip_adds_run(&bm, 0) {{ {{ r.fail(\"unknown extension addition\"); return None; }} }}\n\
         \x20   proof {{ assert(bm@.skip(0) == bm@.skip(0int)); }}\n\
         \x20   Some((Null, Flg::DiffVer))\n}}\n\n"
    ));

    s.push_str(&format!(
        "pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v, f)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<({sname}, nat, Flg)>(({rn}_view(v), (final(r).pos - old(r).pos) as nat, f)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n{{\n\
         \x20   let ghost start = r.rem();\n\
         \x20   let ghost p0 = r.pos;\n\
         \x20   let ext = match r.read_bool() {{\n\
         \x20       Some(b) => b,\n\
         \x20       None => {{\n\
         \x20           proof {{\n\
         \x20               reveal(map_dec);\n\
         \x20               assert(start.len() == 0);\n\
         \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           {{ r.fail(\"extension bit\"); return None; }}\n\
         \x20       }}\n\
         \x20   }};\n\
         \x20   proof {{\n\
         \x20       reveal(map_dec);\n\
         \x20       assert(start.len() >= 1);\n\
         \x20       lemma_bool_dec_bit(start);\n\
         \x20       lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat);\n\
         \x20   }}\n\
         \x20   let p1 = r.pos;\n\
         \x20   let (root, fr) = match {rrn}_decode(r) {{\n\
         \x20       Some(x) => x,\n\
         \x20       None => {{\n\
         \x20           proof {{ lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start); }}\n\
         \x20           return None;\n\
         \x20       }}\n\
         \x20   }};\n\
         \x20   proof {{\n\
         \x20       lemma_rem_skip(r.buf@, p1 as nat, (r.pos - p1) as nat);\n\
         \x20       assert(start.skip(1).skip((r.pos - p1) as int)\n\
         \x20              =~= start.skip((1 + (r.pos - p1)) as int));\n\
         \x20   }}\n\
         \x20   let ghost kr = (r.pos - p1) as nat;\n\
         \x20   // the root's fields are moved into the result below\n\
         \x20   let ghost rv = {rrn}_view(root);\n\
         \x20   let p2p = r.pos;\n\
         \x20   if !ext {{\n\
         \x20       proof {{\n\
         \x20           lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start,\n\
         \x20                              (rv, {rn}_e0()), (1 + kr) as nat, fr);\n\
         \x20       }}\n\
         \x20       return Some(({rn} {{ {mk_fields}}}, fr));\n\
         \x20   }}\n\
         \x20   match {rn}_tail_run(r) {{\n\
         \x20       Some((e, ft)) => {{\n\
         \x20           proof {{\n\
         \x20               lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, (rv, e),\n\
         \x20                                  (1 + kr + (r.pos - p2p)) as nat, flg_add(fr, ft));\n\
         \x20           }}\n\
         \x20           Some(({rn} {{ {mk_fields}}}, flg_join(fr, ft)))\n\
         \x20       }}\n\
         \x20       None => {{\n\
         \x20           proof {{ lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start); }}\n\
         \x20           None\n\
         \x20       }}\n\
         \x20   }}\n}}\n\n"
    ));

    s.push_str(&format!(
        "pub fn {rn}_encode(w: &mut BitWriter, m: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({rn}_view(*m)),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {},\n\
         {{\n\
         \x20   proof {{ {rn}_field_bounds(m); {rn}_rview_ok(*m); lemma_bool_enc_seq(false); }}\n\
         \x20   let ghost w0 = *w;\n\
         \x20   // nothing could be added, so the extension bit is always clear\n\
         \x20   proof {{ assert({rn}_bmof()(Null) =~= zeros(0)); }}\n\
         \x20   if !w.write_bool(false) {{ return false; }}\n\
         \x20   if !{rrn}_x_encode(w, m) {{ return false; }}\n\
         \x20   proof {{ assert(w0.written() + seq![false] + {}\n\
         \x20                   =~= w0.written() + {}); }}\n\
         \x20   true\n}}\n\n",
        ea(&format!("{rn}_enc()"), OLD_POS, &format!("{rn}_view(*m)")),
        ea(&format!("{rrn}_enc()"), "w0.pos as nat + 1", &format!("{rn}_rview(*m)")),
        ea(&format!("{rn}_enc()"), "w0.pos as nat", &format!("{rn}_view(*m)")),
    ));

    s.push_str(&jer_seq(&rn, &jer_root_members(root, env, values)?));
    s.push_str(&arb_fn(&rn, &format!("    {rn} {{\n{}    }}\n", arb_root_members(root, env, values)?)));
    Ok((s, Compiled {
        jer: format!("{rn}_jer({{V}}, {{O}})"),
        arb: format!("{rn}_arb({{G}})"),
        rust_ty: rn.clone(),
        fmt: rn.clone(),
        proof_call: format!("{rn}_is_format();"),
        decode: format!("{rn}_decode({{R}})"),
        encode: format!("{rn}_encode({{W}}, {{V}})"),
        preamble: vec![],
        owner: None,
        spec_ty: if needs_view { Some(sname.clone()) } else { None },
        view: if needs_view { Some(format!("{rn}_view({{V}})")) } else { None },
    }))
}

/// `{rn}_jer`, the JER printer of a generated type, around `body` -- which
/// sees the value as `v: &{rn}` and the output as `o`. External to Verus:
/// printing is not part of any format, so there is nothing to prove.
fn jer_fn(rn: &str, body: &str) -> String {
    format!(
        "#[verifier::external]\n\
         pub fn {rn}_jer(v: &{rn}, o: &mut String) {{\n{body}}}\n\n"
    )
}

/// `{rn}_arb`, a value of the type from entropy, around `body`, which sees
/// the generator as `g`. External to Verus, like the printers.
fn arb_fn(rn: &str, body: &str) -> String {
    format!(
        "#[verifier::external]\n\
         pub fn {rn}_arb(g: &mut Gen) -> {rn} {{\n{body}}}\n\n"
    )
}

/// One of the type's values; only those the schema has.
fn arb_enum(rn: &str, vals: &[String]) -> String {
    let mut body = format!("    match g.pick({}) {{\n", vals.len());
    for (i, x) in vals.iter().enumerate() {
        let arm = if i + 1 == vals.len() { "_".to_string() } else { i.to_string() };
        body.push_str(&format!("        {arm} => {rn}::{},\n", rustify(x)));
    }
    body.push_str("    }\n");
    arb_fn(rn, &body)
}

/// The value of one component as an expression: present or not as the
/// entropy says, and a DEFAULT one either its default or anything.
fn arb_member(c: &Compiled, presence: &str) -> String {
    let a = c.arb.replace("{G}", "g");
    match presence {
        "opt" => format!("if g.bool() {{ Some({a}) }} else {{ None }}"),
        "" => a,
        dv => format!("if g.bool() {{ {a} }} else {{ {dv} }}"),
    }
}

/// X.697 22: an enumeration item is its identifier, as a JSON string.
fn jer_enum(rn: &str, vals: &[String]) -> String {
    let mut body = String::from("    match v {\n");
    for x in vals {
        body.push_str(&format!("        {rn}::{} => jer_ident(\"{x}\", o),\n", rustify(x)));
    }
    body.push_str("    }\n");
    jer_fn(rn, &body)
}

/// The width of an ENUMERATED or CHOICE root index over `k` values (X.691
/// 14.2, 23.6: a constrained whole number, 0 to `k - 1`), the terminal it is,
/// and the spec length a decoder read, for a decoder whose input was `start`.
/// UPER's is the `n`-bit field. So is APER's up to 255 values (11.5.7.1); from
/// 256 it is octet-aligned, one octet for 256 and two up to 64K (11.5.7.2,
/// 11.5.7.3). Over 64K values APER is not built.
fn aper_index(k: u64) -> Option<(u32, &'static str, String)> {
    if aper() && k > 255 {
        if k > 65536 {
            return None;
        }
        let n = if k == 256 { 8 } else { 16 };
        return Some((n, "auint", "(r.pos - {S}.0) as nat".into()));
    }
    let n = width_for(k);
    if n > 56 { None } else { Some((n, "uint", n.to_string())) }
}

/// `{rn}::vals[v]` for `lo <= v <= hi`, as nested ifs that halve the range.
fn enum_bsearch(rn: &str, vals: &[String], lo: usize, hi: usize) -> String {
    if lo == hi {
        return format!("{rn}::{}", rustify(&vals[lo]));
    }
    let mid = (lo + hi + 1) / 2;
    format!("if v < {mid} {{ {} }} else {{ {} }}", enum_bsearch(rn, vals, lo, mid - 1), enum_bsearch(rn, vals, mid, hi))
}

/// The proof over `enum_bsearch`'s cases, one branch per half.
fn enum_bsearch_proof(lo: usize, hi: usize) -> String {
    if lo == hi {
        return format!("assert(v == {lo});");
    }
    let mid = (lo + hi + 1) / 2;
    format!("if v < {mid} {{ {} }} else {{ {} }}", enum_bsearch_proof(lo, mid - 1), enum_bsearch_proof(mid, hi))
}

fn gen_enum(name: &str, vals: &[String]) -> Result<(String, Compiled), Pending> {
    let rn = rustify(name);
    let k = vals.len() as u64;
    if k == 0 {
        return Err(Pending::Unsupported("ENUMERATED with no values".into()));
    }
    if k == 1 {
        // X.691: a constrained whole number whose range is 1 occupies no bits.
        let only = rustify(&vals[0]);
        let text = format!(
            "// ---------------------------------------------------------------- {name}\n\
             #[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]\n\
             pub enum {rn} {{ {only} }}\n\n\
             pub open spec fn {rn}_wf() -> Wf<{rn}> {{ unit_wf({rn}::{only}) }}\n\
             pub open spec fn {rn}_enc() -> Enc<{rn}> {{ unit_enc() }}\n\
             pub open spec fn {rn}_dec() -> Dec<{rn}> {{ unit_dec({rn}::{only}) }}\n\n\
             pub proof fn {rn}_is_format()\n\
             \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
             {{ lemma_unit_format({rn}::{only}); }}\n\n\
             pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
             \x20   requires old(r).wf(),\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v, f)) => {rn}_dec()(old(r).rem())\n\
             \x20               == Some::<({rn}, nat, Flg)>((v, (final(r).pos - old(r).pos) as nat, f)),\n\
             \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
             \x20       }},\n\
             {{\n\
             \x20   proof {{ lemma_unit_dec_val({rn}::{only}, r.rem()); }}\n\
             \x20   Some(({rn}::{only}, Flg::SameVer))\n}}\n\n\
             pub fn {rn}_encode(w: &mut BitWriter, e: &{rn}) -> (ok: bool)\n\
             \x20   requires old(w).wf(),\n\
             \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
             \x20       ok ==> final(w).written() =~= old(w).written() + {enc},\n\
             {{\n\
             \x20   proof {{ assert(old(w).written() + {enc} =~= old(w).written()); }}\n\
             \x20   true\n}}\n\n",
            enc = ea(&format!("{rn}_enc()"), OLD_POS, "*e")
        );
        return Ok((
            text + &jer_enum(&rn, vals) + &arb_enum(&rn, vals),
            Compiled {
                rust_ty: rn.clone(),
                fmt: rn.clone(),
                proof_call: format!("{rn}_is_format();"),
                decode: format!("{rn}_decode({{R}})"),
                encode: format!("{rn}_encode({{W}}, {{V}})"),
                preamble: vec![],
                owner: None,
                spec_ty: None,
                view: None,
                jer: format!("{rn}_jer({{V}}, {{O}})"),
                arb: format!("{rn}_arb({{G}})"),
            },
        ));
    }
    let (n, u, ulen) = match aper_index(k) {
        Some(x) => x,
        None => return Err(Pending::Unsupported("ENUMERATED is too wide".into())),
    };
    let ulen_s = ulen.replace("{S}", "start");
    let max = k - 1;
    let mut s = String::new();

    s.push_str(&format!("// ---------------------------------------------------------------- {name}\n"));
    s.push_str(&format!("#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]\npub enum {rn} {{\n"));
    for v in vals {
        s.push_str(&format!("    {},\n", rustify(v)));
    }
    s.push_str("}\n\n");

    // to / from
    s.push_str(&format!("pub open spec fn {rn}_to(v: u64) -> {rn} {{\n"));
    if k > 255 {
        // a binary search, log k deep: over a chain of k the proof that
        // `from` undoes `to` blows the rlimit
        s.push_str(&format!("    {}\n}}\n\n", enum_bsearch(&rn, vals, 0, vals.len() - 1)));
    } else {
        for (i, v) in vals.iter().enumerate() {
            if i + 1 == vals.len() {
                s.push_str(&format!("    {rn}::{}\n", rustify(v)));
            } else {
                s.push_str(&format!("    if v == {i} {{ {rn}::{} }} else {{\n", rustify(v)));
            }
        }
        for _ in 0..vals.len() - 1 {
            s.push_str("    }\n");
        }
        s.push_str("}\n\n");
    }

    s.push_str(&format!("pub open spec fn {rn}_from(e: {rn}) -> u64 {{\n    match e {{\n"));
    for (i, v) in vals.iter().enumerate() {
        s.push_str(&format!("        {rn}::{} => {i},\n", rustify(v)));
    }
    s.push_str("    }\n}\n\n");

    // spec-function accessors, routed through named functions so the closures
    // referred to in different places are the same value
    s.push_str(&format!(
        "pub open spec fn {rn}_ok() -> spec_fn(u64) -> bool {{ |v: u64| v <= {max} }}\n\
         pub open spec fn {rn}_to_f() -> spec_fn(u64) -> {rn} {{ |v: u64| {rn}_to(v) }}\n\
         pub open spec fn {rn}_from_f() -> spec_fn({rn}) -> u64 {{ |e: {rn}| {rn}_from(e) }}\n\
         pub open spec fn {rn}_base_wf() -> Wf<u64> {{ restrict_wf({u}_wf({n}), {rn}_ok()) }}\n\
         pub open spec fn {rn}_base_dec() -> Dec<u64> {{ restrict_dec({u}_dec({n}), {rn}_ok()) }}\n\
         pub open spec fn {rn}_wf() -> Wf<{rn}> {{ map_wf({rn}_base_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_enc() -> Enc<{rn}> {{ map_enc({u}_enc({n}), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_dec() -> Dec<{rn}> {{ map_dec({rn}_base_dec(), {rn}_to_f()) }}\n\n"
    ));

    // a wide one: `from` undoes `to`, a case at a time down the same search
    let inv_call = if k > 255 {
        s.push_str(&format!(
            "#[verifier::rlimit({})]\nproof fn {rn}_inv(v: u64)\n    requires v <= {max},\n    ensures {rn}_from({rn}_to(v)) == v,\n{{\n    {}\n}}\n\n",
            (k / 5).max(20),
            enum_bsearch_proof(0, vals.len() - 1)
        ));
        format!("{rn}_lemma_restrict_wf_val(v); {rn}_inv(v); ")
    } else {
        String::new()
    };
    let inv_call = inv_call.replace(&format!("{rn}_lemma_restrict_wf_val(v);"), &format!("lemma_restrict_wf_val({u}_wf({n}), {rn}_ok(), v);"));
    s.push_str(&format!(
        "pub proof fn {rn}_is_format()\n    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n{{\n\
         \x20   lemma_{u}_format({n});\n\
         \x20   lemma_restrict_format({u}_wf({n}), {u}_enc({n}), {u}_dec({n}), {rn}_ok());\n\
         \x20   assert forall|v: u64| {rn}_base_wf()(v) implies\n\
         \x20       #[trigger] {rn}_from_f()({rn}_to_f()(v)) == v by {{ {inv_call}}}\n\
         \x20   lemma_map_format({rn}_base_wf(), {u}_enc({n}), {rn}_base_dec(),\n\
         \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n"
    ));

    // exec conversions
    s.push_str(&format!(
        "pub fn {rn}_of_u64(v: u64) -> (e: {rn})\n    requires v <= {max},\n    ensures e == {rn}_to(v),\n{{\n"
    ));
    if k > 255 {
        // a binary search, log k deep: over a chain of k the proof that
        // `from` undoes `to` blows the rlimit
        s.push_str(&format!("    {}\n}}\n\n", enum_bsearch(&rn, vals, 0, vals.len() - 1)));
    } else {
        for (i, v) in vals.iter().enumerate() {
            if i + 1 == vals.len() {
                s.push_str(&format!("    {rn}::{}\n", rustify(v)));
            } else {
                s.push_str(&format!("    if v == {i} {{ {rn}::{} }} else {{\n", rustify(v)));
            }
        }
        for _ in 0..vals.len() - 1 {
            s.push_str("    }\n");
        }
        s.push_str("}\n\n");
    }

    s.push_str(&format!(
        "pub fn {rn}_as_u64(e: &{rn}) -> (v: u64)\n    ensures v == {rn}_from(*e),\n{{\n    match e {{\n"
    ));
    for (i, v) in vals.iter().enumerate() {
        s.push_str(&format!("        {rn}::{} => {i},\n", rustify(v)));
    }
    s.push_str("    }\n}\n\n");

    // exec decode / encode
    s.push_str(&format!(
        "pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures\n\
         \x20       final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v, f)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<({rn}, nat, Flg)>((v,\n\
         \x20                                        (final(r).pos - old(r).pos) as nat, f)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n\
         {{\n\
         \x20   let ghost start = r.rem();\n\
         \x20   match r.read_{u}({n}) {{\n\
         \x20       Some(v) => if v <= {max} {{\n\
         \x20           proof {{\n\
         \x20               lemma_restrict_dec_some({u}_dec({n}), {rn}_ok(), start, v, {ulen_s}, Flg::SameVer);\n\
         \x20               lemma_map_dec_some({rn}_base_dec(), {rn}_to_f(), start, v, {ulen_s}, Flg::SameVer);\n\
         \x20           }}\n\
         \x20           Some(({rn}_of_u64(v), Flg::SameVer))\n\
         \x20       }} else {{\n\
         \x20           proof {{\n\
         \x20               lemma_restrict_dec_none({u}_dec({n}), {rn}_ok(), start);\n\
         \x20               lemma_map_dec_none({rn}_base_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           {{ r.fail(\"ENUMERATED index (0..{max})\"); None }}\n\
         \x20       }},\n\
         \x20       None => {{\n\
         \x20           proof {{\n\
         \x20               lemma_restrict_dec_none({u}_dec({n}), {rn}_ok(), start);\n\
         \x20               lemma_map_dec_none({rn}_base_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           {{ r.fail(\"ENUMERATED index (0..{max})\"); None }}\n\
         \x20       }}\n\
         \x20   }}\n}}\n\n"
    ));

    s.push_str(&format!(
        "pub fn {rn}_encode(w: &mut BitWriter, e: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(),\n\
         \x20   ensures\n\
         \x20       final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {},\n\
         {{\n\
         \x20   let v = {rn}_as_u64(e);\n\
         \x20   proof {{ assert(uint_wf({n} as nat)(v)) by {{ reveal_with_fuel(p2, {}); }} }}\n\
         \x20   w.write_{u}({n}, v)\n}}\n\n",
        ea(&format!("{rn}_enc()"), OLD_POS, "*e"),
        n + 2
    ));

    s.push_str(&jer_enum(&rn, vals));
    s.push_str(&arb_enum(&rn, vals));
    Ok((
        s,
        Compiled {
            rust_ty: rn.clone(),
            fmt: rn.clone(),
            proof_call: format!("{rn}_is_format();"),
            decode: format!("{rn}_decode({{R}})"),
            encode: format!("{rn}_encode({{W}}, {{V}})"),
            preamble: vec![],
            owner: None,
            spec_ty: None,
            view: None,
            jer: format!("{rn}_jer({{V}}, {{O}})"),
            arb: format!("{rn}_arb({{G}})"),
        },
    ))
}

/// Where a SEQUENCE's exec encoder reads its fields from.
///
/// Normally the SEQUENCE's own struct. An extensible SEQUENCE's root is a
/// hidden SEQUENCE whose fields live flat in the *outer* struct, and building
/// the root struct out of `&Outer` would be a copy -- illegal once a field is
/// a `Vec`. So the root's encoders are emitted over the outer struct instead:
/// the body only ever says `m.{field}`, and the spec side is reached through
/// `view`, a spec function from the exec type to the root's spec value.
struct EncOver {
    /// prefix of the generated exec encoder functions
    fnp: String,
    /// the exec type they take
    mty: String,
    /// spec fn: `mty` -> the SEQUENCE's spec value
    view: String,
}

/// A leaf or an inner node of a `Tree`.
#[derive(Clone, Copy)]
enum Kid {
    Leaf(usize),
    Node(usize),
}

/// The shape a record's fields are paired in: a balanced binary tree over
/// the leaves `0..n`, depth log n.
///
/// It used to be a right-nested chain, `T{i} = (field_i, T{i+1})`, and that
/// is what made wide SEQUENCEs slow. Verus's lowering of a type to its SMT
/// type id (`typ_to_ids`) takes time exponential in the type's *depth* --
/// a bare `(u8, (u8, ...))` alias chain doubles in cost with every level,
/// 14 s at depth 22, while the same leaves as a balanced tree of aliases stay
/// at 0.27 s. The bits are the same either way, `pair` being associative.
///
/// Nodes are numbered in preorder, so the root is node 0 and a node's
/// children come after it. Up to three leaves the tree is the chain, node
/// for node, so small types generate exactly what they used to.
struct Tree {
    root: Kid,
    /// `nodes[id]` = (left, right)
    nodes: Vec<(Kid, Kid)>,
    /// the `.0`/`.1` projection path from the root to each leaf
    paths: Vec<String>,
    /// and to each node
    node_paths: Vec<String>,
}

/// A preamble of `k` bits, read as one word per 56 bits rather than one
/// `read_bool` per bit (`vasn::uper::fast`). For each node, `{rn}_bmval{id}`
/// is its value as bits of the input and `{rn}_bmval{id}_ok` proves the
/// node's decoder gives it; `{rn}_bmfast` checks that all `k` bits are there
/// once, reads the words, and splits them. Short of `k` bits it leaves the
/// failure to `{rn}_bmdec0_run`, which says which bit was missing.
///
/// They live in a module of their own: in the type's module, functions that
/// never use them got slower to verify, `CellGroupConfig`'s encoders from
/// 0.3 s to 38 s, and the crate from 2 to 17 minutes.
fn bm_fast(rn: &str, bmt: &Tree, k: usize) -> String {
    let mut s = format!(
        "pub mod {rn}_bm_fast {{\nuse super::*;\n\n{}}}\npub use {rn}_bm_fast::*;\n\n",
        bm_fast_items(rn, bmt, k)
    );
    // the encoder's in a module of their own too: beside the decoder's,
    // `CellGroupConfig_decode` went over the rlimit
    if k <= BM_WFAST_MAX {
        s.push_str(&format!(
            "pub mod {rn}_bm_wfast {{\nuse super::*;\n\n{}}}\npub use {rn}_bm_wfast::*;\n\n",
            bm_write_fast(rn, bmt, k)
        ));
    }
    s
}

fn bm_fast_items(rn: &str, bmt: &Tree, k: usize) -> String {
    let span = |b: Kid| -> (usize, usize) {
        match b {
            Kid::Leaf(j) => (j, 1),
            Kid::Node(id) => {
                let l = bmt.leaves(id);
                (l[0], l.len())
            }
        }
    };
    let val = |b: Kid| -> String {
        match b {
            Kid::Leaf(j) => format!("s[{j}]"),
            Kid::Node(id) => format!("{rn}_bmval{id}(s)"),
        }
    };
    let dec = |b: Kid| -> String {
        match b {
            Kid::Leaf(_) => "bool_dec()".into(),
            Kid::Node(id) => format!("{rn}_bmdec{id}()"),
        }
    };
    // APER states each node's decoder at a position, `adv(i, o)`, where UPER
    // has `s.skip(o)`; the bits, and so the values, are the same
    let ap = aper();
    let ok = |b: Kid| -> String {
        match (b, ap) {
            (Kid::Leaf(j), false) => format!("lemma_bool_dec_at(s, {j});"),
            (Kid::Node(id), false) => format!("{rn}_bmval{id}_ok(s);"),
            (Kid::Leaf(j), true) => format!("lemma_bool_dec_at(i, {j});"),
            (Kid::Node(id), true) => format!("{rn}_bmval{id}_ok(i);"),
        }
    };
    let mut s = String::new();
    for id in (0..bmt.nodes.len()).rev() {
        let (l, r) = bmt.nodes[id];
        let (o, n) = span(Kid::Node(id));
        let nl = span(l).1;
        if ap {
            s.push_str(&format!(
                "#[verifier::opaque]\n\
                 pub open spec fn {rn}_bmval{id}(s: Seq<bool>) -> {rn}_BM{id} {{ ({}, {}) }}\n\n\
                 pub proof fn {rn}_bmval{id}_ok(i: In)\n\
                 \x20   requires i.1.len() >= {k},\n\
                 \x20   ensures {rn}_bmdec{id}()(adv(i, {o}))\n\
                 \x20       == Some::<({rn}_BM{id}, nat, Flg)>(({rn}_bmval{id}(i.1), {n}nat, Flg::SameVer)),\n{{\n\
                 \x20   let s = i.1;\n\
                 \x20   reveal({rn}_bmval{id});\n\
                 \x20   {}\n\
                 \x20   {}\n\
                 \x20   lemma_adv_adv(i, {o}, {nl});\n\
                 \x20   lemma_pair_dec_some({}, {}, adv(i, {o}), {}, {nl}, Flg::SameVer, {}, {}, Flg::SameVer);\n}}\n\n",
                val(l), val(r), ok(l), ok(r),
                dec(l), dec(r), val(l), val(r), span(r).1,
            ));
            continue;
        }
        s.push_str(&format!(
            "#[verifier::opaque]\n\
             pub open spec fn {rn}_bmval{id}(s: Seq<bool>) -> {rn}_BM{id} {{ ({}, {}) }}\n\n\
             pub proof fn {rn}_bmval{id}_ok(s: Seq<bool>)\n\
             \x20   requires s.len() >= {k},\n\
             \x20   ensures {rn}_bmdec{id}()(s.skip({o}))\n\
             \x20       == Some::<({rn}_BM{id}, nat, Flg)>(({rn}_bmval{id}(s), {n}nat, Flg::SameVer)),\n{{\n\
             \x20   reveal({rn}_bmval{id});\n\
             \x20   {}\n\
             \x20   {}\n\
             \x20   assert(s.skip({o}).skip({nl}) =~= s.skip({}));\n\
             \x20   lemma_pair_dec_some({}, {}, s.skip({o}), {}, {nl}, Flg::SameVer, {}, {}, Flg::SameVer);\n}}\n\n",
            val(l), val(r), ok(l), ok(r), o + nl,
            dec(l), dec(r), val(l), val(r), span(r).1,
        ));
    }
    let input = if ap { "at" } else { "rem" };
    // the bits from the cursor on: `to_variant` makes any `.rem()` APER's
    // `.at()`, so APER's are spelled out as its second half
    let bits = if ap { "at().1" } else { "rem()" };
    s.push_str(&format!(
        "#[inline]\n\
         pub fn {rn}_bmfast(r: &mut BitReader) -> (res: Option<{rn}_BM0>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some(v) => {rn}_bmdec0()(old(r).{input}())\n\
         \x20               == Some::<({rn}_BM0, nat, Flg)>((v, (final(r).pos - old(r).pos) as nat,\n\
         \x20                                               Flg::SameVer)),\n\
         \x20           None => {rn}_bmdec0()(old(r).{input}()).is_none(),\n\
         \x20       }},\n{{\n\
         \x20   if {k} > r.buf.len() * 8 - r.pos {{\n\
         \x20       return {rn}_bmdec0_run(r);\n\
         \x20   }}\n\
         \x20   let ghost s = r.{bits};\n{}\
         \x20   let ghost p0 = r.pos;\n",
        if ap { "    let ghost i = r.at();\n" } else { "" }
    ));
    let mut proofs = String::new();
    // the value node by node, children first, each shown to be its node's
    // `bmval` with only that one revealed: one reveal of the whole tree is
    // too much for a wide preamble
    let kid = |b: Kid| -> String {
        match b {
            Kid::Leaf(j) => format!("b{j}_"),
            Kid::Node(id) => format!("n{id}_"),
        }
    };
    let mut nodes = String::new();
    let mut reveals = String::new();
    for id in (0..bmt.nodes.len()).rev() {
        let (l, r) = bmt.nodes[id];
        nodes.push_str(&format!("    let n{id}_ = ({}, {});\n", kid(l), kid(r)));
        reveals.push_str(&format!(
            "        assert(n{id}_ == {rn}_bmval{id}(s)) by {{ reveal({rn}_bmval{id}); }}\n"
        ));
    }
    let mut c = 0;
    while 56 * c < k {
        let kc = (k - 56 * c).min(56);
        let o = 56 * c;
        if c > 0 {
            s.push_str(&format!(
                "    proof {{ lemma_rem_skip(r.buf@, p0 as nat, {o}nat); }}\n"
            ));
        }
        s.push_str(&format!(
            "    let ghost s{c}_ = r.{bits};\n\
             \x20   proof {{ assert(s{c}_ =~= s.skip({o})); }}\n\
             \x20   let w{c}_ = match r.read_uint({kc}) {{ Some(w) => w, None => return None }};\n"
        ));
        for jj in 0..kc {
            let j = o + jj;
            let sh = kc - 1 - jj;
            s.push_str(&format!("    let b{j}_ = (w{c}_ >> {sh}u64) & 1u64 == 1u64;\n"));
            proofs.push_str(&format!("        lemma_word_bit(s{c}_, {kc}, {jj}, {sh}u64);\n"));
        }
        c += 1;
    }
    s.push_str(&format!(
        "{nodes}\
         \x20   proof {{\n{proofs}{reveals}\
         \x20       {rn}_bmval0_ok({});\n\
         \x20       assert(s.skip(0) =~= s);\n\
         \x20   }}\n\
         \x20   Some(n0_)\n}}\n\n",
        if ap { "i" } else { "s" }
    ));
    s
}

/// The widest preamble written as one word (`bm_write_fast`).
const BM_WFAST_MAX: usize = 32;

/// The preamble written as one word per 56 bits rather than a `write_bool`
/// per bit: `{rn}_bmseq{id}` is a node's bits in order, `{rn}_bmseq{id}_ok`
/// proves the node's encoder writes them, and `{rn}_bmwfast` packs the leaves
/// into an array and writes it (`write_bit_slice`). APER's encoders take a
/// position and ignore it, so its lemmas hold at every position.
fn bm_write_fast(rn: &str, bmt: &Tree, k: usize) -> String {
    let ap = aper();
    let mut s = String::new();
    for id in (0..bmt.nodes.len()).rev() {
        let (l, r) = bmt.nodes[id];
        let part = |b: Kid, v: &str| -> (String, String) {
            match b {
                Kid::Leaf(_) => (
                    format!("seq![{v}]"),
                    if ap { format!("lemma_abool_enc_bit({v});") } else { format!("lemma_bool_enc_bit({v});") },
                ),
                Kid::Node(c) => (format!("{rn}_bmseq{c}({v})"), format!("{rn}_bmseq{c}_ok({v});")),
            }
        };
        let (ls, lok) = part(l, "v.0");
        let (rs, rok) = part(r, "v.1");
        let ens = if ap {
            format!("forall|pos: nat| #[trigger] {rn}_bmenc{id}()(pos, v) == {rn}_bmseq{id}(v)")
        } else {
            format!("{rn}_bmenc{id}()(v) == {rn}_bmseq{id}(v)")
        };
        s.push_str(&format!(
            "#[verifier::opaque]\n\
             pub open spec fn {rn}_bmseq{id}(v: {rn}_BM{id}) -> Seq<bool> {{ {ls} + {rs} }}\n\n\
             pub proof fn {rn}_bmseq{id}_ok(v: {rn}_BM{id})\n\
             \x20   ensures {ens},\n{{\n\
             \x20   reveal({rn}_bmseq{id});\n\
             \x20   reveal(pair_enc);\n\
             \x20   {lok}\n\
             \x20   {rok}\n}}\n\n"
        ));
    }
    let leaves: Vec<String> = (0..k).map(|j| bmt.proj("v", j)).collect();
    let mut node_eqs = String::new();
    for id in (0..bmt.nodes.len()).rev() {
        let lv: Vec<String> = bmt.leaves(id).iter().map(|&j| bmt.proj("v", j)).collect();
        node_eqs.push_str(&format!(
            "        assert({rn}_bmseq{id}(v{}) =~= seq![{}]) by {{ reveal({rn}_bmseq{id}); }}\n",
            bmt.node_paths[id], lv.join(", ")
        ));
    }
    s.push_str(&format!(
        "#[inline]\n\
         pub fn {rn}_bmwfast(w: &mut BitWriter, v: {rn}_BM0) -> (ok: bool)\n\
         \x20   requires old(w).wf(),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {enc},\n{{\n\
         \x20   let a: [bool; {k}] = [{lits}];\n\
         \x20   proof {{\n\
         \x20       {rn}_bmseq0_ok(v);\n\
         {node_eqs}\
         \x20       assert(a@ =~= {rn}_bmseq0(v));\n\
         \x20   }}\n\
         \x20   w.write_bit_slice(a.as_slice())\n}}\n\n",
        enc = ea(&format!("{rn}_bmenc0()"), OLD_POS, "v"),
        lits = leaves.join(", "),
    ));
    s
}

impl Tree {
    fn new(n: usize) -> Tree {
        fn build(lo: usize, hi: usize, path: String, t: &mut Tree) -> Kid {
            if hi - lo == 1 {
                t.paths[lo] = path;
                return Kid::Leaf(lo);
            }
            let id = t.nodes.len();
            t.nodes.push((Kid::Leaf(0), Kid::Leaf(0)));
            t.node_paths.push(path.clone());
            // the smaller half on the left, which is what keeps three leaves
            // a chain
            let mid = lo + (hi - lo) / 2;
            let l = build(lo, mid, format!("{path}.0"), t);
            let r = build(mid, hi, format!("{path}.1"), t);
            t.nodes[id] = (l, r);
            Kid::Node(id)
        }
        let mut t = Tree {
            root: Kid::Leaf(0),
            nodes: Vec::new(),
            paths: vec![String::new(); n],
            node_paths: Vec::new(),
        };
        t.root = build(0, n, String::new(), &mut t);
        t
    }

    /// Leaf `i` of a value `v` of the tree's type.
    fn proj(&self, v: &str, i: usize) -> String {
        format!("{v}{}", self.paths[i])
    }

    /// The leaves under node `id`, in order.
    fn leaves(&self, id: usize) -> Vec<usize> {
        let mut out = Vec::new();
        let mut stack = vec![Kid::Node(id)];
        while let Some(k) = stack.pop() {
            match k {
                Kid::Leaf(i) => out.push(i),
                Kid::Node(c) => {
                    let (l, r) = self.nodes[c];
                    stack.push(r);
                    stack.push(l);
                }
            }
        }
        out
    }

    /// Leaf `i` of a value `v` of node `id`'s type, `i` being under `id`.
    fn proj_in(&self, v: &str, id: usize, i: usize) -> String {
        format!("{v}{}", &self.paths[i][self.node_paths[id].len()..])
    }

    /// A tuple literal in the tree's shape.
    fn lit(&self, leaf: &dyn Fn(usize) -> String) -> String {
        self.lit_at(self.root, leaf)
    }

    fn lit_at(&self, k: Kid, leaf: &dyn Fn(usize) -> String) -> String {
        match k {
            Kid::Leaf(i) => leaf(i),
            Kid::Node(id) => {
                let (l, r) = self.nodes[id];
                format!("({}, {})", self.lit_at(l, leaf), self.lit_at(r, leaf))
            }
        }
    }
}

/// X.697 27.3: a SEQUENCE is an object with one member per component that is
/// present, named by the component's identifier. Emitted as two functions:
/// `{rn}_jer_members` writes the members alone, so that an extension group --
/// whose components X.697 counts as components of the enclosing SEQUENCE --
/// can be spliced into its parent's object; `{rn}_jer` adds the braces.
///
/// A DEFAULT component is always written. An absent DEFAULT component has the
/// default as its value, so it is part of the abstract value whether or not
/// the UPER encoding carried it, and X.697 27.3 encodes the abstract value:
/// writing it is a correct JER encoding. It also makes two decoders' prints of
/// one value the same JSON, which is what a differential test compares.
/// VUPER writes it too.
fn jer_seq(rn: &str, members: &str) -> String {
    format!(
        "#[verifier::external]\n\
         pub fn {rn}_jer_members(v: &{rn}, o: &mut String, first: &mut bool) {{\n{members}}}\n\n"
    ) + &jer_fn(
        rn,
        &format!(
            "    o.push('{{');\n\
             \x20   let mut first = true;\n\
             \x20   {rn}_jer_members(v, o, &mut first);\n\
             \x20   o.push('}}');\n"
        ),
    )
}

/// The members of one component, `v.{field}` being its value.
fn jer_member_of(asn_name: &str, field: &str, c: &Compiled, presence: &str) -> String {
    let put = |val: &str| -> String {
        format!(
            "jer_member(\"{asn_name}\", first, o); {};",
            c.jer.replace("{V}", val).replace("{O}", "o")
        )
    };
    match presence {
        "opt" => format!("    if let Some(x) = &v.{field} {{ {} }}\n", put("x")),
        "" => format!("    {{ {} }}\n", put(&format!("&v.{field}"))),
        _default => format!("    {{ {} }}\n", put(&format!("&v.{field}"))),
    }
}

fn gen_sequence(
    name: &str,
    fields: &[Field],
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
    enc_over: Option<&EncOver>,
) -> Result<(String, Compiled), Pending> {
    let own = EncOver {
        fnp: rustify(name),
        mty: rustify(name),
        view: format!("{}_view", rustify(name)),
    };
    let eo = enc_over.unwrap_or(&own);
    if fields.is_empty() {
        // No fields and no extension marker: nothing to encode, so the same
        // 0-bit format as a single-value ENUMERATED.
        let rn = rustify(name);
        let text = format!(
            "// ---------------------------------------------------------------- {name}\n\
             #[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]\n\
             pub struct {rn} {{}}\n\n\
             pub open spec fn {rn}_wf() -> Wf<{rn}> {{ unit_wf({rn} {{}}) }}\n\
             pub open spec fn {rn}_enc() -> Enc<{rn}> {{ unit_enc() }}\n\
             pub open spec fn {rn}_dec() -> Dec<{rn}> {{ unit_dec({rn} {{}}) }}\n\n\
             pub proof fn {rn}_is_format()\n\
             \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
             {{ lemma_unit_format({rn} {{}}); }}\n\n\
             pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
             \x20   requires old(r).wf(),\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v, f)) => {rn}_dec()(old(r).rem())\n\
             \x20               == Some::<({rn}, nat, Flg)>((v, (final(r).pos - old(r).pos) as nat, f)),\n\
             \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
             \x20       }},\n\
             {{\n\
             \x20   proof {{ lemma_unit_dec_val({rn} {{}}, r.rem()); }}\n\
             \x20   Some(({rn} {{}}, Flg::SameVer))\n}}\n\n\
             pub open spec fn {rn}_view(m: {rn}) -> {rn} {{ m }}\n\n\
             pub fn {fnp}_encode(w: &mut BitWriter, m: &{mty}) -> (ok: bool)\n\
             \x20   requires old(w).wf(),\n\
             \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
             \x20       ok ==> final(w).written() =~= old(w).written() + {enc},\n\
             {{\n\
             \x20   proof {{ assert(old(w).written() + {enc} =~= old(w).written()); }}\n\
             \x20   true\n}}\n\n",
            fnp = eo.fnp, mty = eo.mty,
            enc = ea(&format!("{rn}_enc()"), OLD_POS, &format!("{}(*m)", eo.view))
        );
        return Ok((
            text + &jer_seq(&rn, "") + &arb_fn(&rn, &format!("    {rn} {{}}\n")),
            Compiled {
                rust_ty: rn.clone(),
                fmt: rn.clone(),
                proof_call: format!("{rn}_is_format();"),
                decode: format!("{rn}_decode({{R}})"),
                encode: format!("{rn}_encode({{W}}, {{V}})"),
                preamble: vec![],
                owner: None,
                spec_ty: None,
                view: None,
                jer: format!("{rn}_jer({{V}}, {{O}})"),
                arb: format!("{rn}_arb({{G}})"),
            },
        ));
    }
    let rn = rustify(name);

    // field i, its component format, and -- if OPTIONAL or DEFAULT -- its
    // index in the presence bitmap
    let mut parts: Vec<(String, Compiled, Option<usize>)> = Vec::new();
    // A DEFAULT field's default, as an expression good in spec and exec code
    // alike. The field keeps its plain type, as in VUPER: its preamble bit is
    // `value != default`, the encoder omits it when equal, and the decoder
    // returns the default on a clear bit and rejects a set one carrying the
    // default -- that would be a second encoding of the same value.
    let mut dft: Vec<Option<String>> = Vec::new();
    let mut k = 0usize;
    for f in fields {
        let c = resolve(&f.ty, env, values)?;
        let oj = if matches!(f.presence, Presence::Optional | Presence::Default(_)) {
            k += 1;
            Some(k - 1)
        } else {
            None
        };
        dft.push(match &f.presence {
            Presence::Default(d) => Some(default_expr(d, &c)?),
            _ => None,
        });
        parts.push((rustify(&f.name), c, oj));
    }
    let is_opt = |i: usize| parts[i].2.is_some() && dft[i].is_none();
    let n = parts.len();
    // the body's fields, and the presence bitmap's bits, each paired as a tree
    let bt = Tree::new(n);
    let bmt = Tree::new(k.max(1));
    let nn = bt.nodes.len();

    let rust_ty = |i: usize| -> String {
        let c = &parts[i].1;
        match parts[i].2 {
            Some(_) if is_opt(i) => format!("Option<{}>", c.rust_ty),
            _ => c.rust_ty.clone(),
        }
    };
    // The format is over spec values, which differ from exec values exactly
    // where a field holds a list.
    let spec_ty = |i: usize| -> String {
        let c = &parts[i].1;
        match parts[i].2 {
            Some(_) if is_opt(i) => format!("Option<{}>", c.sty()),
            _ => c.sty(),
        }
    };
    let needs_view = parts.iter().any(|(_, c, _)| !c.plain());
    let sname = if needs_view { format!("{rn}_S") } else { rn.clone() };
    // exec expression -> spec expression, lifted through Option for OPTIONAL
    let view_field = |i: usize, v: &str| -> String {
        let c = &parts[i].1;
        if c.plain() {
            v.to_string()
        } else if is_opt(i) {
            // a match here would move the value; the accessor keeps it a view
            format!(
                "if {v} is Some {{ Some({}) }} else {{ None }}",
                c.view_of(&format!("{v}->Some_0"))
            )
        } else {
            c.view_of(v)
        }
    };
    // bitmap tuple: `bool` at a leaf, `{rn}_BM{id}` at a node
    let bm_kty = |b: Kid| -> String {
        match b {
            Kid::Leaf(_) => "bool".into(),
            Kid::Node(id) => format!("{rn}_BM{id}"),
        }
    };
    let bm_root = bm_kty(bmt.root);
    // projection of bitmap entry j out of a bitmap-typed expression
    let bm_proj = |v: &str, j: usize| -> String { bmt.proj(v, j) };
    let bm_entry = |i: usize| -> String {
        match parts[i].2 {
            Some(j) => bm_proj("bm", j),
            None => String::new(),
        }
    };
    let bmarg = if k > 0 { format!("bm: {bm_root}") } else { String::new() };
    let bmparam = if k > 0 { format!("({bmarg})") } else { "()".into() };
    let bmcall = if k > 0 { "(bm)".to_string() } else { "()".into() };

    // per-field spec accessors, wrapped in `opt_*` for OPTIONAL fields
    let f_wf = |i: usize| -> String {
        match (parts[i].2, &dft[i]) {
            (Some(j), Some(dv)) => { let _ = dv; format!("(if {} {{ restrict_wf({}, {rn}_dft{i}_ne()) }} else {{ unit_wf({}) }})", bm_proj("bm", j), wf_of(&parts[i].1), dv) }
            (Some(j), None) => format!("opt_wf({}, {})", bm_proj("bm", j), wf_of(&parts[i].1)),
            (None, _) => wf_of(&parts[i].1),
        }
    };
    let f_enc = |i: usize| -> String {
        match (parts[i].2, &dft[i]) {
            (Some(j), Some(dv)) => { let _ = dv; format!("(if {} {{ {} }} else {{ unit_enc() }})", bm_proj("bm", j), enc_of(&parts[i].1)) }
            (Some(j), None) => format!("opt_enc({}, {})", bm_proj("bm", j), enc_of(&parts[i].1)),
            (None, _) => enc_of(&parts[i].1),
        }
    };
    let f_dec = |i: usize| -> String {
        match (parts[i].2, &dft[i]) {
            (Some(j), Some(dv)) => { let _ = dv; format!("(if {} {{ restrict_dec({}, {rn}_dft{i}_ne()) }} else {{ unit_dec({}) }})", bm_proj("bm", j), dec_of(&parts[i].1), dv) }
            (Some(j), None) => format!("opt_dec({}, {})", bm_proj("bm", j), dec_of(&parts[i].1)),
            (None, _) => dec_of(&parts[i].1),
        }
    };

    // A subtree of the body is a field at a leaf and a named pair at a node;
    // everything below is stated per node over its two kids.
    let ty = |b: Kid| -> String {
        match b { Kid::Leaf(i) => spec_ty(i), Kid::Node(id) => format!("{rn}_T{id}") }
    };
    let wf_t = |b: Kid| -> String {
        match b { Kid::Leaf(i) => f_wf(i), Kid::Node(id) => format!("{rn}_wf_t{id}{bmcall}") }
    };
    let enc_t = |b: Kid| -> String {
        match b { Kid::Leaf(i) => f_enc(i), Kid::Node(id) => format!("{rn}_enc_t{id}{bmcall}") }
    };
    let dec_t = |b: Kid| -> String {
        match b { Kid::Leaf(i) => f_dec(i), Kid::Node(id) => format!("{rn}_dec_t{id}{bmcall}") }
    };
    let root = bt.root;
    let mut s = String::new();
    s.push_str(&format!("// ---------------------------------------------------------------- {name}\n"));
    for i in 0..n {
        if let Some(dv) = &dft[i] {
            let t = parts[i].1.sty();
            s.push_str(&format!(
                "pub open spec fn {rn}_dft{i}_ne() -> spec_fn({t}) -> bool {{ |a: {t}| a != {dv} }}\n"
            ));
        }
    }
    let derives = if needs_view {
        "#[derive(PartialEq, Eq, Debug)]"
    } else {
        "#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]"
    };
    s.push_str(&format!("{derives}\npub struct {rn} {{\n"));
    for (i, (fname, _, _)) in parts.iter().enumerate() {
        s.push_str(&format!("    pub {fname}: {},\n", rust_ty(i)));
    }
    s.push_str("}\n\n");
    if needs_view {
        // A list is a Vec to run and a Seq to reason about, so the format is
        // stated over this companion and the exec decoder proves its result
        // views to the value the spec decoded.
        s.push_str(&format!("pub struct {sname} {{\n"));
        for (i, (fname, _, _)) in parts.iter().enumerate() {
            s.push_str(&format!("    pub {fname}: {},\n", spec_ty(i)));
        }
        s.push_str("}\n\n");
        s.push_str(&format!("pub open spec fn {rn}_view(m: {rn}) -> {sname} {{\n    {sname} {{\n"));
        for (i, (fname, _, _)) in parts.iter().enumerate() {
            s.push_str(&format!("        {fname}: {},\n", view_field(i, &format!("m.{fname}"))));
        }
        s.push_str("    }\n}\n\n");
    } else {
        s.push_str(&format!("pub open spec fn {rn}_view(m: {rn}) -> {rn} {{ m }}\n\n"));
    }

    let ety = |b: Kid| -> String {
        match b { Kid::Leaf(i) => rust_ty(i), Kid::Node(id) => format!("{rn}_ET{id}") }
    };
    // an exec subtree's spec value
    let view_k = |b: Kid, v: &str| -> String {
        match b { Kid::Leaf(i) => view_field(i, v), Kid::Node(id) => format!("{rn}_view_t{id}({v})") }
    };
    // Children before parents: in preorder a node's kids have larger ids.
    for id in (0..nn).rev() {
        let (l, r) = bt.nodes[id];
        s.push_str(&format!("pub type {rn}_T{id} = ({}, {});\n", ty(l), ty(r)));
        s.push_str(&format!("pub type {rn}_ET{id} = ({}, {});\n", ety(l), ety(r)));
    }
    for id in (0..nn).rev() {
        let (l, r) = bt.nodes[id];
        s.push_str(&format!(
            "pub open spec fn {rn}_view_t{id}(v: {}) -> {} {{ ({}, {}) }}\n",
            ety(Kid::Node(id)), ty(Kid::Node(id)), view_k(l, "v.0"), view_k(r, "v.1")
        ));
    }
    let tup_k = |b: Kid| -> String {
        match b { Kid::Leaf(i) => format!("m.{}", parts[i].0), Kid::Node(id) => format!("{rn}_tup_t{id}(m)") }
    };
    for id in (0..nn).rev() {
        let (l, r) = bt.nodes[id];
        s.push_str(&format!(
            "#[verifier::opaque]\npub open spec fn {rn}_tup_t{id}(m: {sname}) -> {} {{ ({}, {}) }}\n",
            ty(Kid::Node(id)), tup_k(l), tup_k(r)
        ));
    }
    if k > 0 {
        for id in (0..bmt.nodes.len()).rev() {
            let (l, r) = bmt.nodes[id];
            s.push_str(&format!("pub type {rn}_BM{id} = ({}, {});\n", bm_kty(l), bm_kty(r)));
        }
    }
    s.push('\n');

    // ---------------------------------------------------------- the bitmap
    if k > 0 {
        let bm_wf = |b: Kid| -> String {
            match b { Kid::Leaf(_) => "bool_wf()".into(), Kid::Node(id) => format!("{rn}_bmwf{id}()") }
        };
        let bm_enc = |b: Kid| -> String {
            match b { Kid::Leaf(_) => "bool_enc()".into(), Kid::Node(id) => format!("{rn}_bmenc{id}()") }
        };
        let bm_dec = |b: Kid| -> String {
            match b { Kid::Leaf(_) => "bool_dec()".into(), Kid::Node(id) => format!("{rn}_bmdec{id}()") }
        };
        let nbm = bmt.nodes.len();
        for id in (0..nbm).rev() {
            let (l, r) = bmt.nodes[id];
            let t = bm_kty(Kid::Node(id));
            s.push_str(&format!(
                "pub open spec fn {rn}_bmwf{id}() -> Wf<{t}> {{ pair_wf({}, {}) }}\n\
                 pub open spec fn {rn}_bmenc{id}() -> Enc<{t}> {{ pair_enc({}, {}) }}\n\
                 pub open spec fn {rn}_bmdec{id}() -> Dec<{t}> {{ pair_dec({}, {}) }}\n",
                bm_wf(l), bm_wf(r), bm_enc(l), bm_enc(r), bm_dec(l), bm_dec(r),
            ));
        }
        s.push_str(&format!(
            "pub open spec fn {rn}_bm_wf() -> Wf<{bm_root}> {{ {} }}\n\
             pub open spec fn {rn}_bm_enc() -> Enc<{bm_root}> {{ {} }}\n\
             pub open spec fn {rn}_bm_dec() -> Dec<{bm_root}> {{ {} }}\n\n",
            bm_wf(bmt.root), bm_enc(bmt.root), bm_dec(bmt.root)
        ));
        s.push_str(&format!(
            "pub proof fn {rn}_bm_is_format()\n\
             \x20   ensures is_format({rn}_bm_wf(), {rn}_bm_enc(), {rn}_bm_dec()),\n{{\n\
             \x20   lemma_bool_format();\n"
        ));
        for id in (0..nbm).rev() {
            let (l, r) = bmt.nodes[id];
            s.push_str(&format!(
                "    lemma_pair_format({}, {}, {}, {}, {}, {});\n",
                bm_wf(l), bm_enc(l), bm_dec(l), bm_wf(r), bm_enc(r), bm_dec(r)
            ));
        }
        s.push_str("}\n\n");

        // exec: read and write the bitmap, one helper per node
        let bm_read = |b: Kid| -> String {
            match b {
                Kid::Leaf(_) => "{ let o_ = r.read_bool(); r.got(o_, \"preamble\") }".into(),
                Kid::Node(id) => format!("{rn}_bmdec{id}_run(r)"),
            }
        };
        let bm_write = |b: Kid, v: &str| -> String {
            match b {
                Kid::Leaf(_) => format!("w.write_bool({v})"),
                Kid::Node(id) => format!("{rn}_bmenc{id}_run(w, {v})"),
            }
        };
        for id in (0..nbm).rev() {
            let (l, r) = bmt.nodes[id];
            let t = bm_kty(Kid::Node(id));
            let (headr, tailr) = (bm_read(l), bm_read(r));
            let (headd, taild) = (bm_dec(l), bm_dec(r));
            s.push_str(&format!(
                "pub fn {rn}_bmdec{id}_run(r: &mut BitReader) -> (res: Option<{t}>)\n\
                 \x20   requires old(r).wf(),\n\
                 \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
                 \x20       match res {{\n\
                 \x20           Some(v) => {rn}_bmdec{id}()(old(r).rem())\n\
                 \x20               == Some::<({t}, nat, Flg)>((v, (final(r).pos - old(r).pos) as nat,\n\
                 \x20                                          Flg::SameVer)),\n\
                 \x20           None => {rn}_bmdec{id}()(old(r).rem()).is_none(),\n\
                 \x20       }},\n{{\n\
                 \x20   let ghost start = r.rem();\n\
                 \x20   let ghost p0 = r.pos;\n\
                 \x20   let head = match {headr} {{\n\
                 \x20       Some(v) => v,\n\
                 \x20       None => {{\n\
                 \x20           proof {{ lemma_pair_dec_none_fst({headd}, {taild}, start); }}\n\
                 \x20           return None;\n\
                 \x20       }}\n\
                 \x20   }};\n\
                 \x20   proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n\
                 \x20   let ghost kh = (r.pos - p0) as nat;\n\
                 \x20   let ghost p1 = r.pos;\n\
                 \x20   let tail = match {tailr} {{\n\
                 \x20       Some(v) => v,\n\
                 \x20       None => {{\n\
                 \x20           proof {{ lemma_pair_dec_none_snd({headd}, {taild}, start, head, kh,\n\
                 \x20                                            Flg::SameVer); }}\n\
                 \x20           return None;\n\
                 \x20       }}\n\
                 \x20   }};\n\
                 \x20   proof {{ lemma_pair_dec_some({headd}, {taild}, start, head, kh, Flg::SameVer,\n\
                 \x20                               tail, (r.pos - p1) as nat, Flg::SameVer); }}\n\
                 \x20   Some((head, tail))\n}}\n\n"
            ));
            s.push_str(&format!(
                "pub fn {rn}_bmenc{id}_run(w: &mut BitWriter, v: {t}) -> (ok: bool)\n\
                 \x20   requires old(w).wf(),\n\
                 \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
                 \x20       ok ==> final(w).written() =~= old(w).written() + {},\n{{\n\
                 \x20   if !{} {{ return false; }}\n\
                 \x20   if !{} {{ return false; }}\n\
                 \x20   true\n}}\n\n",
                ea(&format!("{rn}_bmenc{id}()"), OLD_POS, "v"),
                bm_write(l, "v.0"), bm_write(r, "v.1")
            ));
        }
        if nbm > 0 {
            s.push_str(&bm_fast(&rn, &bmt, k));
        }
    }

    // ------------------------------------------------- struct <-> tuple maps
    let body_ty = ty(root);
    let full_ty = if k > 0 { format!("({bm_root}, {body_ty})") } else { body_ty.clone() };
    let tv = if k > 0 { "t.1" } else { "t" };
    s.push_str(&format!("pub open spec fn {rn}_to(t: {full_ty}) -> {sname} {{\n    {sname} {{\n"));
    for (i, (fname, _, _)) in parts.iter().enumerate() {
        s.push_str(&format!("        {fname}: {},\n", bt.proj(tv, i)));
    }
    s.push_str("    }\n}\n\n");

    let body_expr = bt.lit(&|i| format!("m.{}", parts[i].0));
    s.push_str(&format!(
        "pub open spec fn {rn}_body(m: {sname}) -> {body_ty} {{ {body_expr} }}\n"
    ));
    if k > 0 {
        // a DEFAULT field's bit is "differs from the default"
        let bits: Vec<String> = (0..n).filter(|&i| parts[i].2.is_some()).map(|i| match &dft[i] {
            Some(dv) => format!("m.{} != {dv}", parts[i].0),
            None => format!("m.{} is Some", parts[i].0),
        }).collect();
        let bm_expr = bmt.lit(&|j| bits[j].clone());
        // Opaque, because its body is a literal: an encoder that knows
        // `bmv == {rn}_bm(..)` otherwise has every bit's `pair_enc` step fire
        // on it and reasons about k one-bit sequences in its `=~=`. At 48
        // fields that put `{rn}_encode` over the rlimit. Only the round trip
        // and `{fnp}_bm_run` need to see inside.
        s.push_str(&format!(
            "#[verifier::opaque]\n\
             pub open spec fn {rn}_bm(m: {sname}) -> {bm_root} {{ {bm_expr} }}\n\
             pub open spec fn {rn}_from(m: {sname}) -> {full_ty} {{ ({rn}_bm(m), {rn}_body(m)) }}\n"
        ));
    } else {
        s.push_str(&format!(
            "pub open spec fn {rn}_from(m: {sname}) -> {full_ty} {{ {rn}_body(m) }}\n"
        ));
    }
    s.push_str(&format!(
        "pub open spec fn {rn}_to_f() -> spec_fn({full_ty}) -> {sname} {{ |t: {full_ty}| {rn}_to(t) }}\n\
         pub open spec fn {rn}_from_f() -> spec_fn({sname}) -> {full_ty} {{ |m: {sname}| {rn}_from(m) }}\n\n"
    ));
    // The one place the whole tree is unfolded: `{rn}_body` is the record as
    // a flat nested tuple, `{rn}_tup_t0` is the same thing built a node at a
    // time. Proved once here, O(n), so that no node has to.
    if nn > 0 {
        s.push_str(&format!(
            "pub proof fn {rn}_tup0(m: {sname})\n\
             \x20   ensures {rn}_tup_t0(m) == {rn}_body(m),\n{{\n"
        ));
        for id in 0..nn {
            s.push_str(&format!("    reveal({rn}_tup_t{id});\n"));
        }
        s.push_str("}\n\n");
    }

    // ----------------------------------------------- body subtree spec fns
    for id in (0..nn).rev() {
        let (l, r) = bt.nodes[id];
        let t = ty(Kid::Node(id));
        s.push_str(&format!(
            "#[verifier::opaque]\n\
             pub open spec fn {rn}_wf_t{id}{bmparam} -> Wf<{t}> {{ pair_wf({}, {}) }}\n\
             #[verifier::opaque]\n\
             pub open spec fn {rn}_enc_t{id}{bmparam} -> Enc<{t}> {{ pair_enc({}, {}) }}\n\
             #[verifier::opaque]\n\
             pub open spec fn {rn}_dec_t{id}{bmparam} -> Dec<{t}> {{ pair_dec({}, {}) }}\n",
            wf_t(l), wf_t(r),
            enc_t(l), enc_t(r),
            dec_t(l), dec_t(r),
        ));
    }
    s.push('\n');
    if k > 0 {
        s.push_str(&format!(
            "pub open spec fn {rn}_body_wf() -> spec_fn({bm_root}) -> Wf<{body_ty}> {{ |bm: {bm_root}| {} }}\n\
             pub open spec fn {rn}_body_enc() -> spec_fn({bm_root}) -> Enc<{body_ty}> {{ |bm: {bm_root}| {} }}\n\
             pub open spec fn {rn}_body_dec() -> spec_fn({bm_root}) -> Dec<{body_ty}> {{ |bm: {bm_root}| {} }}\n\n",
            wf_t(root), enc_t(root), dec_t(root),
        ));
        s.push_str(&format!(
            "pub open spec fn {rn}_full_wf() -> Wf<{full_ty}> {{ dep_wf({rn}_bm_wf(), {rn}_body_wf()) }}\n\
             pub open spec fn {rn}_full_enc() -> Enc<{full_ty}> {{ dep_enc({rn}_bm_enc(), {rn}_body_enc()) }}\n\
             pub open spec fn {rn}_full_dec() -> Dec<{full_ty}> {{ dep_dec({rn}_bm_dec(), {rn}_body_dec()) }}\n\n"
        ));
    } else {
        s.push_str(&format!(
            "pub open spec fn {rn}_full_wf() -> Wf<{full_ty}> {{ {} }}\n\
             pub open spec fn {rn}_full_enc() -> Enc<{full_ty}> {{ {} }}\n\
             pub open spec fn {rn}_full_dec() -> Dec<{full_ty}> {{ {} }}\n\n",
            wf_t(root), enc_t(root), dec_t(root)
        ));
    }
    s.push_str(&format!(
        "pub open spec fn {rn}_wf() -> Wf<{sname}> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_enc() -> Enc<{sname}> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_dec() -> Dec<{sname}> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n"
    ));

    // ------------------------------------------------------------- proofs
    let body_sig = if k > 0 { format!("(bm: {bm_root})") } else { "()".into() };

    // One helper per node, not one proof for the whole record. Emitting the
    // n-1 `lemma_pair_format` applications flat makes a single proof whose term
    // size grows with the field count, and wide 3GPP SEQUENCEs then blow the
    // default rlimit -- measured on NR, where a handful of ~40-field types did
    // exactly that. Split this way each helper is O(1) for the solver and the
    // type's total cost is linear, matching what the decoders already do.
    let field_proof = |i: usize| -> String {
        // `proof_call` already carries whatever facts it needs inline
        let mut out = String::new();
        out.push_str(&format!("    {}\n", parts[i].1.proof_call));
        match (parts[i].2, &dft[i]) {
            (Some(_), Some(dv)) => out.push_str(&format!(
                "    lemma_restrict_format({}, {}, {}, {rn}_dft{i}_ne());\n\
                 \x20   lemma_unit_format({dv});\n",
                wf_of(&parts[i].1), enc_of(&parts[i].1), dec_of(&parts[i].1)
            )),
            (Some(j), None) => out.push_str(&format!(
                "    lemma_opt_format({}, {}, {}, {});\n",
                bm_proj("bm", j),
                wf_of(&parts[i].1), enc_of(&parts[i].1), dec_of(&parts[i].1)
            )),
            _ => {}
        }
        out
    };
    let kid_proof = |b: Kid| -> String {
        match b {
            Kid::Leaf(i) => field_proof(i),
            Kid::Node(id) => format!("    {rn}_body_is_format_t{id}{bmcall};\n"),
        }
    };
    for id in (0..nn).rev() {
        let (l, r) = bt.nodes[id];
        let me = Kid::Node(id);
        s.push_str(&format!(
            "pub proof fn {rn}_body_is_format_t{id}{body_sig}\n\
             \x20   ensures is_format({}, {}, {}),\n{{\n\
             \x20   reveal({rn}_wf_t{id}); reveal({rn}_enc_t{id}); reveal({rn}_dec_t{id});\n{}{}",
            wf_t(me), enc_t(me), dec_t(me), kid_proof(l), kid_proof(r)
        ));
        s.push_str(&format!(
            "    lemma_pair_format({}, {}, {}, {}, {}, {});\n}}\n\n",
            wf_t(l), enc_t(l), dec_t(l), wf_t(r), enc_t(r), dec_t(r)
        ));
    }
    s.push_str(&format!(
        "pub proof fn {rn}_body_is_format{body_sig}\n\
         \x20   ensures is_format({}, {}, {}),\n{{\n",
        wf_t(root), enc_t(root), dec_t(root)
    ));
    // a single-field SEQUENCE has no pair at all
    s.push_str(&kid_proof(root));
    s.push_str("}\n\n");

    // `{rn}_to`/`{rn}_from` round-tripping needs each OPTIONAL or DEFAULT
    // field to agree with its bit in the bitmap, which is what `opt_wf` says
    // and the opaque tree hides. Revealing every node in one query was
    // enough, but it is O(n) reveals with the `opt_wf` step lemma firing
    // across all of them, and at 64 fields that alone blew the rlimit. So
    // each node states its own leaves' agreement as ground facts, from its
    // kids' -- one reveal per node, like everything else here.
    let has_bits = |id: usize| bt.leaves(id).iter().any(|&i| parts[i].2.is_some());
    let use_bits = k > 0 && nn > 0;
    if use_bits {
        for id in (0..nn).rev() {
            if !has_bits(id) {
                continue;
            }
            let (l, r) = bt.nodes[id];
            let facts: Vec<String> = bt.leaves(id).into_iter().filter_map(|i| {
                let j = parts[i].2?;
                let x = bt.proj_in("t", id, i);
                Some(match &dft[i] {
                    Some(dv) => format!("({x} != {dv}) == {}", bm_proj("bm", j)),
                    None => format!("({x} is Some) == {}", bm_proj("bm", j)),
                })
            }).collect();
            s.push_str(&format!(
                "pub proof fn {rn}_bits_t{id}(bm: {bm_root}, t: {})\n\
                 \x20   requires {rn}_wf_t{id}(bm)(t),\n\
                 \x20   ensures\n",
                ty(Kid::Node(id))
            ));
            for f in &facts {
                s.push_str(&format!("        {f},\n"));
            }
            s.push_str(&format!(
                "{{\n    reveal({rn}_wf_t{id});\n\
                 \x20   lemma_pair_wf_val({}, {}, t.0, t.1);\n\
                 \x20   assert(t == (t.0, t.1));\n",
                wf_t(l), wf_t(r)
            ));
            for (kid, v) in [(l, "t.0"), (r, "t.1")] {
                if let Kid::Node(c) = kid {
                    if has_bits(c) {
                        s.push_str(&format!("    {rn}_bits_t{c}(bm, {v});\n"));
                    }
                }
            }
            s.push_str("}\n\n");
        }
    }
    if use_bits {
        // its own query: inline in `{rn}_is_format`, next to the dep and map
        // lemmas, the same proof went over the rlimit at 64 fields
        s.push_str(&format!(
            "pub proof fn {rn}_rt(t: {full_ty})\n\
             \x20   requires {rn}_full_wf()(t),\n\
             \x20   ensures {rn}_from_f()({rn}_to_f()(t)) == t,\n\
             {{\n    reveal({rn}_bm);\n    {rn}_bits_t0(t.0, t.1);\n}}\n\n"
        ));
    }
    s.push_str(&format!(
        "pub proof fn {rn}_is_format()\n    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n{{\n"
    ));
    if !use_bits {
        for id in 0..nn {
            s.push_str(&format!("    reveal({rn}_wf_t{id});\n"));
        }
        if k > 0 {
            s.push_str(&format!("    reveal({rn}_bm);\n"));
        }
    }
    if k > 0 {
        s.push_str(&format!(
            "    {rn}_bm_is_format();\n\
             \x20   assert forall|bm: {}| {rn}_bm_wf()(bm) implies\n\
             \x20       is_format(#[trigger] {rn}_body_wf()(bm), {rn}_body_enc()(bm), {rn}_body_dec()(bm))\n\
             \x20   by {{ {rn}_body_is_format(bm); }}\n\
             \x20   lemma_dep_format({rn}_bm_wf(), {rn}_bm_enc(), {rn}_bm_dec(),\n\
             \x20                    {rn}_body_wf(), {rn}_body_enc(), {rn}_body_dec());\n",
            bm_root
        ));
    } else {
        s.push_str(&format!("    {rn}_body_is_format();\n"));
    }
    let rt_hint = if use_bits { format!(" {rn}_rt(t); ") } else { " ".into() };
    s.push_str(&format!(
        "    assert forall|t: {full_ty}| {rn}_full_wf()(t) implies\n\
         \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t by {{{rt_hint}}}\n\
         \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(),\n\
         \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n"
    ));

    // over the spec value, so the encoders can reach it through whichever
    // view they were emitted with
    s.push_str(&format!(
        "pub proof fn {rn}_field_bounds(v: {sname})\n\
         \x20   requires {rn}_wf()(v),\n\
         \x20   ensures {rn}_full_wf()({rn}_from(v)),\n{{\n\
         \x20   assert({rn}_from_f()({rn}_to_f()({rn}_from(v))) == {rn}_from(v));\n}}\n\n"
    ));

    let preambles = {
        let mut out = String::new();
        let mut seen = std::collections::HashSet::new();
        for (_, c, _) in &parts {
            for p in &c.preamble {
                if seen.insert(p.clone()) {
                    out.push_str(&format!("    proof {{ {p} }}\n"));
                }
            }
        }
        out
    };
    let bmdecl = if k > 0 { format!(", bm: {bm_root}") } else { String::new() };

    // ------------------------------------------------------------- decode
    // Each OPTIONAL field gets its own runner carrying the `opt_dec` contract,
    // so the presence check lives in one place and the surrounding pair chain
    // treats optional and mandatory fields identically.
    for i in 0..n {
        if let (Some(_), Some(dv)) = (parts[i].2, &dft[i]) {
            // DEFAULT: the same contract, with the field's own format
            let (d, ne) = (dec_of(&parts[i].1), format!("{rn}_dft{i}_ne()"));
            let fd = format!("(if present {{ restrict_dec({d}, {ne}) }} else {{ unit_dec({dv}) }})");
            s.push_str(&format!(
                "pub fn {rn}_f{i}_run(r: &mut BitReader, present: bool) -> (res: Option<({}, Flg)>)\n\
                 \x20   requires old(r).wf(),\n\
                 \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
                 \x20       match res {{\n\
                 \x20           Some((v, f)) => {fd}(old(r).rem())\n\
                 \x20               == Some::<({}, nat, Flg)>((v, (final(r).pos - old(r).pos) as nat, f)),\n\
                 \x20           None => {fd}(old(r).rem()).is_none(),\n\
                 \x20       }},\n{{\n{preambles}\
                 \x20   let ghost start = r.rem();\n\
                 \x20   let ghost p0 = r.pos;\n\
                 \x20   if present {{\n\
                 \x20       match {} {{\n\
                 \x20           Some((v, f)) => {{\n\
                 \x20               // present but equal to the default: not an encoding of anything\n\
                 \x20               if v == {dv} {{\n\
                 \x20                   proof {{ lemma_restrict_dec_none({d}, {ne}, start); }}\n\
                 \x20                   {{ r.fail(\"DEFAULT value, encoded explicitly\"); None }}\n\
                 \x20               }} else {{\n\
                 \x20                   proof {{ lemma_restrict_dec_some({d}, {ne}, start, v, (r.pos - p0) as nat, f); }}\n\
                 \x20                   Some((v, f))\n\
                 \x20               }}\n\
                 \x20           }}\n\
                 \x20           None => {{\n\
                 \x20               proof {{ lemma_restrict_dec_none({d}, {ne}, start); }}\n\
                 \x20               None\n\
                 \x20           }}\n\
                 \x20       }}\n\
                 \x20   }} else {{\n\
                 \x20       proof {{ lemma_unit_dec_val({dv}, start); }}\n\
                 \x20       Some(({dv}, Flg::SameVer))\n\
                 \x20   }}\n}}\n\n",
                rust_ty(i), spec_ty(i), parts[i].1.decode.replace("{R}", "r"),
            ));
        } else if let Some(j) = parts[i].2 {
            s.push_str(&format!(
                "pub fn {rn}_f{i}_run(r: &mut BitReader, present: bool) -> (res: Option<({}, Flg)>)\n\
                 \x20   requires old(r).wf(),\n\
                 \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
                 \x20       match res {{\n\
                 \x20           Some((v, f)) => opt_dec(present, {})(old(r).rem())\n\
                 \x20               == Some::<({}, nat, Flg)>(({},\n\
                 \x20                                    (final(r).pos - old(r).pos) as nat, f)),\n\
                 \x20           None => opt_dec(present, {})(old(r).rem()).is_none(),\n\
                 \x20       }},\n{{\n{preambles}\
                 \x20   let ghost start = r.rem();\n\
                 \x20   let ghost p0 = r.pos;\n\
                 \x20   if present {{\n\
                 \x20       match {} {{\n\
                 \x20           Some((v, f)) => {{\n\
                 \x20               proof {{ lemma_opt_dec_some({}, {}, start, {},\n\
                 \x20                                          (r.pos - p0) as nat, f); }}\n\
                 \x20               Some((Some(v), f))\n\
                 \x20           }}\n\
                 \x20           None => {{\n\
                 \x20               proof {{ lemma_opt_dec_fail({}, start); }}\n\
                 \x20               None\n\
                 \x20           }}\n\
                 \x20       }}\n\
                 \x20   }} else {{\n\
                 \x20       proof {{ lemma_opt_dec_absent({}, start); }}\n\
                 \x20       Some((None, Flg::SameVer))\n\
                 \x20   }}\n}}\n\n",
                rust_ty(i), dec_of(&parts[i].1), spec_ty(i), view_field(i, "v"),
                dec_of(&parts[i].1),
                parts[i].1.decode.replace("{R}", "r"),
                enc_of(&parts[i].1), dec_of(&parts[i].1), parts[i].1.view_of("v"),
                dec_of(&parts[i].1), dec_of(&parts[i].1)
            ));
            let _ = j;
        }
    }

    // an OPTIONAL field's runner already carries the `opt_dec` contract, so a
    // leaf and a node look the same to the pair above them
    let dec_run = |b: Kid| -> String {
        match b {
            Kid::Leaf(i) => field_decode(&parts, i, &rn, &bm_entry(i)),
            Kid::Node(id) => format!("{rn}_dec_t{id}_run(r{})", if k > 0 { ", bm" } else { "" }),
        }
    };
    // the error a failed kid hands up: a field's is named after it, a node's
    // already names whichever field it came from
    let dec_err = |b: Kid| -> String {
        match b {
            Kid::Leaf(i) => format!("r.fail_in(\"{}\");", fields[i].name),
            Kid::Node(_) => String::new(),
        }
    };
    for id in (0..nn).rev() {
        let (l, r) = bt.nodes[id];
        let me = Kid::Node(id);
        let tail_call = dec_run(r);
        s.push_str(&format!(
            "pub fn {rn}_dec_t{id}_run(r: &mut BitReader{bmdecl}) -> (res: Option<({}, Flg)>)\n\
             \x20   requires old(r).wf(),\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v, f)) => {}(old(r).rem())\n\
             \x20               == Some::<({}, nat, Flg)>(({rn}_view_t{id}(v),\n\
             \x20                                    (final(r).pos - old(r).pos) as nat, f)),\n\
             \x20           None => {}(old(r).rem()).is_none(),\n\
             \x20       }},\n{{\n{preambles}\
             \x20   proof {{ reveal({rn}_dec_t{id}); }}\n\
             \x20   let ghost start = r.rem();\n\
             \x20   let ghost p0 = r.pos;\n",
            ety(me), dec_t(me), ty(me), dec_t(me)
        ));
        s.push_str(&format!(
            "    let (head, fh) = match {} {{\n\
             \x20       Some(vf) => vf,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_pair_dec_none_fst({}, {}, start); }}\n\
             \x20           {} return None;\n\
             \x20       }}\n\
             \x20   }};\n",
            dec_run(l), dec_t(l), dec_t(r), dec_err(l)
        ));
        s.push_str(&format!(
            "    proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n\
             \x20   let ghost kh = (r.pos - p0) as nat;\n\
             \x20   let ghost p1 = r.pos;\n\
             \x20   let (tail, ft) = match {tail_call} {{\n\
             \x20       Some(vf) => vf,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_pair_dec_none_snd({}, {}, start, {}, kh, fh); }}\n\
             \x20           {} return None;\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_pair_dec_some({}, {}, start, {}, kh, fh, {},\n\
             \x20                               (r.pos - p1) as nat, ft); }}\n\
             \x20   Some(((head, tail), flg_join(fh, ft)))\n}}\n\n",
            dec_t(l), dec_t(r), view_k(l, "head"), dec_err(r),
            dec_t(l), dec_t(r), view_k(l, "head"),
            view_k(r, "tail")
        ));
    }

    s.push_str(&format!(
        "pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v, f)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<({sname}, nat, Flg)>(({rn}_view(v),\n\
         \x20                                        (final(r).pos - old(r).pos) as nat, f)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n{{\n{preambles}\
         \x20   let ghost start = r.rem();\n\
         \x20   let ghost p0 = r.pos;\n"
    ));
    let body_spec = view_k(root, "body");
    if k > 0 {
        let bmrun = match bmt.root {
            Kid::Leaf(_) => "{ let o_ = r.read_bool(); r.got(o_, \"preamble\") }".to_string(),
            Kid::Node(_) => format!("{rn}_bmfast(r)"),
        };
        s.push_str(&format!(
            "    let bm = match {bmrun} {{\n\
             \x20       Some(v) => v,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               lemma_dep_dec_none_fst({rn}_bm_dec(), {rn}_body_dec(), start);\n\
             \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
             \x20           }}\n\
             \x20           return None;\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n\
             \x20   let ghost kbm = (r.pos - p0) as nat;\n\
             \x20   let ghost p1 = r.pos;\n\
             \x20   let (body, fb) = match {} {{\n\
             \x20       Some(vf) => vf,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               lemma_dep_dec_none_snd({rn}_bm_dec(), {rn}_body_dec(), start, bm, kbm,\n\
             \x20                                     Flg::SameVer);\n\
             \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
             \x20           }}\n\
             \x20           {body_err} return None;\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{\n\
             \x20       lemma_dep_dec_some({rn}_bm_dec(), {rn}_body_dec(), start, bm, kbm, Flg::SameVer,\n\
             \x20                          {}, (r.pos - p1) as nat, fb);\n\
             \x20       lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, (bm, {}),\n\
             \x20                          (r.pos - p0) as nat, fb);\n\
             \x20   }}\n",
            dec_run(root),
            body_spec, body_spec,
            body_err = dec_err(root),
        ));
    } else {
        s.push_str(&format!(
            "    let (body, fb) = match {} {{\n\
             \x20       Some(vf) => vf,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start); }}\n\
             \x20           {} return None;\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, {},\n\
             \x20                              (r.pos - p0) as nat, fb); }}\n",
            dec_run(root),
            dec_err(root),
            body_spec
        ));
    }
    s.push_str(&format!("    Some(({rn} {{ "));
    for (i, (fname, _, _)) in parts.iter().enumerate() {
        s.push_str(&format!("{fname}: {}, ", bt.proj("body", i)));
    }
    s.push_str("}, fb))\n}\n\n");

    // ------------------------------------------------------------- encode
    // Each node takes the bitmap as a parameter and the well-formedness of
    // *its own subtree* as a precondition, the way the decoder runners already
    // do. Before, every level called `{rn}_field_bounds` and re-derived the
    // whole record's `pair_wf` chain from `{rn}_wf()` -- O(n) terms at each of
    // n levels. Now a node reveals one `tup_t` and one `wf_t`/`enc_t`, hands
    // its kids' obligations to their own runners, and is O(1).
    let (fnp, mty, view) = (&eo.fnp, &eo.mty, &eo.view);
    // The subtree of the record that node `id` has to encode, named rather
    // than spelled out. Writing the nested tuple inline made every level's
    // `ensures` O(n-i) in the field count, so the generated text and the
    // solver's term were both O(n^2) -- which is what blew the rlimit on the
    // widest NR encoders. `{rn}_tup_t{id}` is opaque, so a node that reveals
    // its own definition sees exactly one pair and stops.
    let tup_t = |id: usize| -> String { format!("{rn}_tup_t{id}({view}(*m))") };
    let bmdecl_enc = if k > 0 { format!(", bm: {bm_root}") } else { String::new() };
    let bmpass = if k > 0 { ", bm" } else { "" };
    let enc_run = |b: Kid| -> String {
        match b {
            Kid::Leaf(i) => field_encode_expr(&parts, &dft, i),
            Kid::Node(id) => format!("{fnp}_enc_t{id}_run(w{bmpass}, m)"),
        }
    };
    for id in (0..nn).rev() {
        let (l, r) = bt.nodes[id];
        let me = Kid::Node(id);
        s.push_str(&format!(
            "pub fn {fnp}_enc_t{id}_run(w: &mut BitWriter{bmdecl_enc}, m: &{mty}) -> (ok: bool)\n\
             \x20   requires old(w).wf(), {}({}),\n\
             \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
             \x20       ok ==> final(w).written() =~= old(w).written() + {},\n{{\n{preambles}\
             \x20   proof {{ reveal({rn}_tup_t{id}); reveal({rn}_wf_t{id}); reveal({rn}_enc_t{id}); }}\n",
            wf_t(me), tup_t(id), ea(&enc_t(me), OLD_POS, &tup_t(id))
        ));
        s.push_str(&format!("    if !{} {{ return false; }}\n", enc_run(l)));
        s.push_str(&format!("    if !{} {{ return false; }}\n    true\n}}\n\n", enc_run(r)));
    }
    // Everything `{rn}_encode` needs to know about the spec, packaged into one
    // proof: the tree's own precondition, and the split of `{rn}_enc`
    // into the bitmap's bits and the body's. Both sides of that split mention
    // `{rn}_body`, which is a flat n-tuple, so leaving it inline in the
    // encoder made `{rn}_encode` itself O(n) -- the last place it still was,
    // and the seven NR types that still exceeded the rlimit were all this
    // function. Here it is one query, and the encoder's own is O(1).
    let bmv_of = if k > 0 { format!("{rn}_bm(v)") } else { String::new() };
    let tup0 = format!("{rn}_tup_t0(v)");
    if n > 1 {
        let (wf0, enc0) = if k > 0 {
            (format!("{rn}_wf_t0({bmv_of})"), format!("{rn}_enc_t0({bmv_of})"))
        } else {
            (format!("{rn}_wf_t0()"), format!("{rn}_enc_t0()"))
        };
        // In APER the body starts where the bitmap ends.
        let split = if k > 0 {
            let bm = ea(&format!("{rn}_bm_enc()"), "pos", &bmv_of);
            format!("{bm} + {}", ea(&enc0, &format!("pos + {bm}.len()"), &tup0))
        } else {
            ea(&enc0, "pos", &tup0)
        };
        let pos_param = if aper() { "pos: nat, " } else { "" };
        s.push_str(&format!(
            "pub proof fn {rn}_enc_pre({pos_param}v: {sname})\n\
             \x20   requires {rn}_wf()(v),\n\
             \x20   ensures {wf0}({tup0}),\n\
             \x20       {} =~= {split},\n{{\n\
             \x20   {rn}_field_bounds(v);\n\
             \x20   {rn}_tup0(v);\n\
             \x20   assert({} =~= {});\n}}\n\n",
            ea(&format!("{rn}_enc()"), "pos", "v"),
            ea(&format!("{rn}_enc()"), "pos", "v"),
            ea(&format!("{rn}_full_enc()"), "pos", &format!("{rn}_from(v)")),
        ));
    }
    if k > 0 {
        // Building the preamble bitmap is the one remaining O(k) step, and
        // `{rn}_view(*m)` is itself O(n) for a record with list fields -- a
        // `Seq` view per field. Left inline it put both into `{rn}_encode`'s
        // query, which was enough to push the widest NR types over the rlimit
        // even though the same function verifies on its own.
        let bits: Vec<String> = (0..n).filter(|&i| parts[i].2.is_some()).map(|i| match &dft[i] {
            Some(dv) => format!("m.{} != {dv}", parts[i].0),
            None => format!("m.{}.is_some()", parts[i].0),
        }).collect();
        let bm_val = bmt.lit(&|j| bits[j].clone());
        s.push_str(&format!(
            "pub fn {fnp}_bm_run(m: &{mty}) -> (bmv: {})\n\
             \x20   ensures bmv == {rn}_bm({view}(*m)),\n\
             {{\n    proof {{ reveal({rn}_bm); }}\n    {bm_val}\n}}\n\n",
            bm_root
        ));
    }
    s.push_str(&format!(
        "pub fn {fnp}_encode(w: &mut BitWriter, m: &{mty}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({view}(*m)),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {},\n{{\n{preambles}{}",
        ea(&format!("{rn}_enc()"), OLD_POS, &format!("{view}(*m)")),
        if aper() { "    let ghost p0 = w.pos as nat;\n" } else { "" },
    ));
    if n > 1 {
        let pos_arg = if aper() { "p0, " } else { "" };
        s.push_str(&format!("    proof {{ {rn}_enc_pre({pos_arg}{view}(*m)); }}\n"));
    } else {
        s.push_str(&format!("    proof {{ {rn}_field_bounds({view}(*m)); }}\n"));
    }
    if k > 0 {
        let bmw = match bmt.root {
            Kid::Leaf(_) => "w.write_bool(bmv)".to_string(),
            // one word, up to 32 bits: past that `{rn}_bmwfast`'s proof goes
            // over the rlimit (NR's 64-bit `MIMO-ParametersPerBand` ext6, even
            // at 40)
            Kid::Node(_) if k <= BM_WFAST_MAX => format!("{rn}_bmwfast(w, bmv)"),
            Kid::Node(_) => format!("{rn}_bmenc0_run(w, bmv)"),
        };
        s.push_str(&format!(
            "    let bmv = {fnp}_bm_run(m);\n\
             \x20   if !{bmw} {{ return false; }}\n"
        ));
    }
    if n == 1 {
        s.push_str(&format!("    let ok = {};\n", field_encode_expr(&parts, &dft, 0)));
        s.push_str(&format!(
            "    proof {{ assert({}\n\
             \x20                 =~= {}); }}\n",
            ea(&format!("{rn}_enc()"), "p0", &format!("{view}(*m)")),
            ea(&format!("{rn}_full_enc()"), "p0", &format!("{rn}_from({view}(*m))")),
        ));
    } else {
        s.push_str(&format!(
            "    let ok = {fnp}_enc_t0_run(w{}, m);\n",
            if k > 0 { ", bmv" } else { "" }
        ));
    }
    s.push_str("    ok\n}\n\n");

    let mut members = String::new();
    for (i, f) in fields.iter().enumerate() {
        let presence = match (&dft[i], is_opt(i)) {
            (Some(dv), _) => dv.clone(),
            (None, true) => "opt".to_string(),
            (None, false) => String::new(),
        };
        members.push_str(&jer_member_of(&f.name, &parts[i].0, &parts[i].1, &presence));
    }
    s.push_str(&jer_seq(&rn, &members));
    let mut lit = format!("    {rn} {{\n");
    for (i, _) in fields.iter().enumerate() {
        let presence = match (&dft[i], is_opt(i)) {
            (Some(dv), _) => dv.clone(),
            (None, true) => "opt".to_string(),
            (None, false) => String::new(),
        };
        lit.push_str(&format!("        {}: {},\n", parts[i].0, arb_member(&parts[i].1, &presence)));
    }
    lit.push_str("    }\n");
    s.push_str(&arb_fn(&rn, &lit));
    Ok((
        s,
        Compiled {
            jer: format!("{rn}_jer({{V}}, {{O}})"),
            arb: format!("{rn}_arb({{G}})"),
            rust_ty: rn.clone(),
            fmt: rn.clone(),
            proof_call: format!("{rn}_is_format();"),
            decode: format!("{rn}_decode({{R}})"),
            encode: format!("{rn}_encode({{W}}, {{V}})"),
            preamble: vec![],
            owner: None,
            // A SEQUENCE holding a list has a spec companion, and that has to
            // be visible to whoever nests it -- otherwise the parent writes the
            // exec type into spec positions and nothing typechecks.
            spec_ty: if needs_view { Some(sname.clone()) } else { None },
            view: if needs_view { Some(format!("{rn}_view({{V}})")) } else { None },
        },
    ))
}

/// A DEFAULT value as an expression of the field's type, valid in spec and
/// exec code alike. Only what 3GPP and ETSI use: an INTEGER, an ENUMERATED
/// value, a BOOLEAN.
fn default_expr(d: &DefaultVal, c: &Compiled) -> Result<String, Pending> {
    if !c.plain() {
        return Err(Pending::Unsupported("a DEFAULT on a type holding a list is not implemented yet".into()));
    }
    match d {
        DefaultVal::Int(v) if c.rust_ty == "i64" => Ok(format!("{v}i64")),
        DefaultVal::Bool(b) if c.rust_ty == "bool" => Ok(b.to_string()),
        DefaultVal::Name(n) if !matches!(c.rust_ty.as_str(), "i64" | "bool" | "Null") => {
            Ok(format!("{}::{}", c.rust_ty, rustify(n)))
        }
        _ => Err(Pending::Unsupported("a DEFAULT of this kind is not implemented yet".into())),
    }
}

/// The decoder call for field `i`: its own runner if OPTIONAL, else the
/// component's decoder directly.
fn field_decode(
    parts: &[(String, Compiled, Option<usize>)],
    i: usize,
    rn: &str,
    bm_entry: &str,
) -> String {
    match parts[i].2 {
        Some(_) => format!("{rn}_f{i}_run(r, {bm_entry})"),
        None => parts[i].1.decode.replace("{R}", "r"),
    }
}

fn field_encode_expr(parts: &[(String, Compiled, Option<usize>)], dft: &[Option<String>], i: usize) -> String {
    let (fname, c, oj) = &parts[i];
    let byref = !(c.rust_ty == "bool" || c.rust_ty == "i64" || c.rust_ty == "Null");
    if let Some(dv) = &dft[i] {
        // DEFAULT: omitted exactly when equal to the default
        let inner = c
            .encode
            .replace("{W}", "w")
            .replace("{V}", &if byref { format!("&m.{fname}") } else { format!("m.{fname}") });
        return format!("if m.{fname} != {dv} {{ {inner} }} else {{ true }}");
    }
    match oj {
        None => c
            .encode
            .replace("{W}", "w")
            .replace("{V}", &if byref { format!("&m.{fname}") } else { format!("m.{fname}") }),
        Some(_) => {
            let inner = c
                .encode
                .replace("{W}", "w")
                .replace("{V}", if byref { "v" } else { "*v" });
            format!("match &m.{fname} {{ Some(v) => {inner}, None => true }}")
        }
    }
}

fn bit_elem() -> Compiled {
    Compiled {
        owner: None,
        spec_ty: None,
        view: None,
        rust_ty: "bool".into(),
        fmt: "bool".into(),
        proof_call: "lemma_bool_format();".into(),
        decode: "{ let o_ = {R}.read_bool(); {R}.same(o_, \"bit\") }".into(),
        encode: "{W}.write_bool({V})".into(),
        preamble: vec![],
        jer: "jer_bool(*{V}, {O})".into(),
        arb: "{G}.bool()".into(),
    }
}

fn byte_elem() -> Compiled {
    Compiled {
        owner: None,
        spec_ty: None,
        view: None,
        rust_ty: "u8".into(),
        fmt: "byte".into(),
        proof_call: "lemma_byte_format();".into(),
        decode: "{ let o_ = {R}.read_byte(); {R}.same(o_, \"octet\") }".into(),
        encode: "{W}.write_byte({V})".into(),
        preamble: vec![],
        jer: "jer_int(*{V} as i64, {O})".into(),
        arb: "({G}.bits(8) as u8)".into(),
    }
}

/// The `p2(n)` value a generated proof needs, with just enough fuel.
fn p2_fact(n: u32) -> String {
    format!(
        "assert(p2({n}) == {}) by {{ reveal_with_fuel(p2, {}); }}",
        1u128 << n,
        n + 2
    )
}

/// Which ASN.1 type a list format is, which only JER needs to know: the
/// three share one format, but X.697 prints each differently (24, 25, 28).
#[derive(Clone, Copy, PartialEq)]
enum ListKind {
    Bits,
    Octets,
    Of,
    /// a known-multiplier character string (X.697 38.1), its characters `b`
    /// bits each
    Chars(u32),
}

/// SEQUENCE OF, BIT STRING and OCTET STRING are the same shape: a length
/// determinant -- absent when the size is fixed -- followed by that many
/// elements. The generated decoder loops while the spec recurses, and the
/// bridge is the three `list_loop` lemmas.
fn gen_list_type(
    name: &str,
    sc: &SizeCons,
    elem: Compiled,
    kind: ListKind,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    let rn = rustify(name);
    let ety = elem.rust_ty.clone();
    // The format is over the elements' spec values. When those differ from
    // the exec ones -- an element that itself holds a list -- the loops below
    // reason about `{rn}_lview(v@)`, the `Vec`'s contents each mapped through
    // the element's view, rather than about `v@` directly. A plain element
    // keeps `v@` so that nothing about the existing lists changes.
    let sty = elem.sty();
    let eplain = elem.plain();
    let lv = |e: &str| -> String {
        if eplain { e.to_string() } else { format!("{rn}_lview({e})") }
    };
    let xv = elem.view_of("x_");
    // the encoder holds the element by reference
    let xvr = elem.view_of("(*x_)");
    let ewf = wf_of(&elem);
    let eenc = enc_of(&elem);
    let edec = dec_of(&elem);
    let edecode = elem.decode.replace("{R}", "r");
    let eencode = elem
        .encode
        .replace("{W}", "w")
        .replace("{V}", if ety == "bool" || ety == "u8" || ety == "u16" || ety == "u32" || ety == "i64" || ety == "Null" {
            "*x_"
        } else {
            "x_"
        });
    let mut eprefix = String::new();
    for p in &elem.preamble {
        eprefix.push_str(&format!("    proof {{ {p} }}\n"));
    }

    let (lb, ub) = match sc {
        SizeCons::Fixed(n) => match lit(n, values) {
            Some(v) if v >= 0 => (v as u64, v as u64),
            _ => return Err(Pending::Unsupported("SIZE bound is not a known literal".into())),
        },
        SizeCons::Range(a, b) => match (lit(a, values), lit(b, values)) {
            (Some(x), Some(y)) if 0 <= x && x <= y => (x as u64, y as u64),
            _ => return Err(Pending::Unsupported("SIZE bound is not a known literal".into())),
        },
        SizeCons::None if elem.fmt == "byte" => return Ok(gen_octets_unsized(name)),
        // X.691 11.9.4.2: no upper bound is a semi-constrained length, the
        // general determinant holding `n`, fragmenting: `fraglist` with no ub
        SizeCons::None => return Ok(gen_list_frag(name, 0, u64::MAX, elem, kind)),
        SizeCons::Semi(a) => match lit(a, values) {
            Some(v) if v >= 0 => return Ok(gen_list_frag(name, v as u64, u64::MAX, elem, kind)),
            _ => return Err(Pending::Unsupported("SIZE bound is not a known literal".into())),
        },
        SizeCons::RangeExt(a, b) => match (lit(a, values), lit(b, values)) {
            (Some(x), Some(y)) if 0 <= x && x <= y => return gen_list_ext(name, x as u64, Some(y as u64), elem, kind, values),
            _ => return Err(Pending::Unsupported("SIZE bound is not a known literal".into())),
        },
        SizeCons::SemiExt(a) => match lit(a, values) {
            Some(v) if v >= 0 => return gen_list_ext(name, v as u64, None, elem, kind, values),
            _ => return Err(Pending::Unsupported("SIZE bound is not a known literal".into())),
        },
    };
    // X.691 11.9.4.2 (and 11.9.1 for a fixed size): from `ub` = 64K on, the
    // length is the general determinant holding `n`, fragmenting at 16K
    if ub >= 65536 {
        return Ok(gen_list_frag(name, lb, ub, elem, kind));
    }
    if aper() {
        return aper_list::gen_sized(name, lb, ub, elem, kind);
    }
    let w = width_for(ub - lb + 1);
    if w > 56 {
        return Err(Pending::Unsupported("SIZE range needs more than 56 bits".into()));
    }
    let fixed = lb == ub;
    let pf = p2_fact(w);

    let mut s = String::new();
    s.push_str(&format!(
        "// ---------------------------------------------------------------- {name}\n"
    ));
    s.push_str(&format!("pub type {rn} = Vec<{ety}>;\n\n"));
    if !eplain {
        s.push_str(&format!(
            "pub open spec fn {rn}_lview(s: Seq<{ety}>) -> Seq<{sty}> {{ s.map_values(|x_: {ety}| {xv}) }}\n\n"
        ));
    }

    if fixed {
        s.push_str(&format!(
            "pub open spec fn {rn}_wf() -> Wf<Seq<{sty}>> {{ list_wf({lb}, {ewf}) }}\n\
             pub open spec fn {rn}_enc() -> Enc<Seq<{sty}>> {{ list_enc({lb}, {eenc}) }}\n\
             pub open spec fn {rn}_dec() -> Dec<Seq<{sty}>> {{ list_dec({lb}, {edec}) }}\n\n\
             pub proof fn {rn}_is_format()\n\
             \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
             {{\n    {}\n    lemma_list_format({lb}, {ewf}, {eenc}, {edec});\n}}\n\n",
            elem.proof_call
        ));
    } else {
        s.push_str(&format!(
            "pub open spec fn {rn}_to(t: (u64, Seq<{sty}>)) -> Seq<{sty}> {{ t.1 }}\n\
             pub open spec fn {rn}_from(l: Seq<{sty}>) -> (u64, Seq<{sty}>) {{ (l.len() as u64, l) }}\n\
             pub open spec fn {rn}_to_f() -> spec_fn((u64, Seq<{sty}>)) -> Seq<{sty}> {{ |t: (u64, Seq<{sty}>)| {rn}_to(t) }}\n\
             pub open spec fn {rn}_from_f() -> spec_fn(Seq<{sty}>) -> (u64, Seq<{sty}>) {{ |l: Seq<{sty}>| {rn}_from(l) }}\n\
             pub open spec fn {rn}_full_wf() -> Wf<(u64, Seq<{sty}>)> {{ sized_wf({lb}, {ub}, {w}, {ewf}) }}\n\
             pub open spec fn {rn}_full_enc() -> Enc<(u64, Seq<{sty}>)> {{ sized_enc({lb}, {ub}, {w}, {eenc}) }}\n\
             pub open spec fn {rn}_full_dec() -> Dec<(u64, Seq<{sty}>)> {{ sized_dec({lb}, {ub}, {w}, {edec}) }}\n\
             pub open spec fn {rn}_wf() -> Wf<Seq<{sty}>> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
             pub open spec fn {rn}_enc() -> Enc<Seq<{sty}>> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
             pub open spec fn {rn}_dec() -> Dec<Seq<{sty}>> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n\
             pub proof fn {rn}_is_format()\n\
             \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
             {{\n    {}\n    {pf}\n    vasn::bits::prim_read::lemma_p2_56();\n\
             \x20   lemma_sized_format({lb}, {ub}, {w}, {ewf}, {eenc}, {edec});\n\
             \x20   assert forall|t: (u64, Seq<{sty}>)| {rn}_full_wf()(t) implies\n\
             \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t by {{ }}\n\
             \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(),\n\
             \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n",
            elem.proof_call
        ));
    }

    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v_, f_)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<(Seq<{sty}>, nat, Flg)>(({},\n\
         \x20                                                 (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n\
         {{\n{eprefix}\
         \x20   let ghost start = old(r).rem();\n\
         \x20   let ghost p0 = old(r).pos;\n",
        lv("v_@")
    ));
    if fixed {
        s.push_str(&format!("    let c_: u64 = {lb};\n"));
    } else {
        s.push_str(&format!(
            "    proof {{ {pf} vasn::bits::prim_read::lemma_p2_56(); }}\n\
             \x20   let c_ = match r.read_ulen({lb}, {ub}, {w}) {{\n\
             \x20       Some(v_) => v_,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               lemma_dep_dec_none_fst(ulen_dec({lb}, {ub}, {w}), list_dec_f({edec}), start);\n\
             \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
             \x20           }}\n\
             \x20           {{ r.fail(\"SIZE ({lb}..{ub}) length\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n"
        ));
    }
    // a BIT STRING's bits or an OCTET STRING's octets, all there: one bulk
    // read (vasn::uper::fast); otherwise element by element, which says
    // where the input ran out
    let bulk = match (elem.fmt.as_str(), eplain) {
        ("bool", true) | ("byte", true) if !aper() => {
            let (rd, need, adv) = if elem.fmt == "bool" {
                ("read_bit_list", "(c_ as usize) <= left_", "c_ as nat")
            } else {
                ("read_octet_list", "8 * (c_ as usize) <= left_", "(8 * c_) as nat")
            };
            format!(
                "    let bulk_: bool = {need};\n\
                 \x20   let mut out_: Vec<{ety}> = if bulk_ {{ r.{rd}(c_ as usize) }} else {{\n\
                 \x20       Vec::with_capacity(if (c_ as usize) < left_ {{ c_ as usize }} else {{ left_ }})\n\
                 \x20   }};\n\
                 \x20   let mut i_: u64 = if bulk_ {{ c_ }} else {{ 0 }};\n\
                 \x20   proof {{\n\
                 \x20       if bulk_ {{\n\
                 \x20           lemma_rem_skip(r.buf@, p1 as nat, {adv});\n\
                 \x20           assert(r.rem() =~= body.skip(({adv}) as int));\n\
                 \x20           assert(out_@ + Seq::<{ety}>::empty() =~= out_@);\n\
                 \x20       }} else {{\n\
                 \x20           lemma_list_loop_start(c_ as nat, {edec}, body);\n\
                 \x20       }}\n\
                 \x20   }}\n"
            )
        }
        _ => format!(
            "    let mut out_: Vec<{ety}> = Vec::with_capacity(if (c_ as usize) < left_ {{ c_ as usize }} else {{ left_ }});\n\
             \x20   let mut i_: u64 = 0;\n\
             \x20   proof {{ lemma_list_loop_start(c_ as nat, {edec}, body); }}\n"
        ),
    };
    s.push_str(&format!(
        "    {klen_def}\n\
         \x20   let ghost body = r.rem();\n\
         \x20   let ghost p1 = r.pos;\n\
         \x20   proof {{\n\
         \x20       assert(body =~= start.skip(klen as int));\n\
         \x20       assert(p0 + klen == p1);\n\
         \x20   }}\n\
         \x20   // sized from the count, but never past one element per bit left,\n\
         \x20   // so a hostile count cannot make a short input allocate much\n\
         \x20   let left_: usize = r.buf.len() * 8 - r.pos;\n{bulk}\
         \x20   let mut fa_: Flg = Flg::SameVer;\n\
         \x20   while i_ < c_\n\
         \x20       invariant\n\
         \x20           r.wf(), r.buf == old(r).buf, r.pos >= p1, p1 >= p0,\n\
         \x20           p0 == old(r).pos, start == old(r).rem(),\n\
         \x20           body == start.skip(klen as int), p0 + klen == p1,\n\
         \x20           out_@.len() == i_, i_ <= c_,\n\
         \x20           list_dec_rec(c_ as nat, {edec}, body)\n\
         \x20               == list_cont({ov}, (r.pos - p1) as nat, fa_,\n\
         \x20                            list_dec_rec((c_ - i_) as nat, {edec}, r.rem())),\n\
         \x20       decreases c_ - i_,\n\
         \x20   {{\n\
         \x20       let ghost bi = r.rem();\n\
         \x20       let ghost pi = r.pos;\n\
         \x20       let (x_, fx_) = match {edecode} {{\n\
         \x20           Some(vf_) => vf_,\n\
         \x20           None => {{\n\
         \x20               proof {{\n\
         \x20                   lemma_list_loop_fail(c_ as nat, {edec}, body, {ov},\n\
         \x20                                        (pi - p1) as nat, fa_, (c_ - i_) as nat, bi);\n\
         \x20                   lemma_list_dec_val(c_ as nat, {edec}, body);\n\
         \x20                  assert(list_dec_f({edec})(c_) == list_dec(c_ as nat, {edec}));\n"
    , klen_def = if fixed { "let ghost klen = 0nat;" } else { "let ghost klen = (r.pos - p0) as nat;" },
      ov = lv("out_@")));
    if !fixed {
        s.push_str(&format!(
            "                   lemma_dep_dec_none_snd(ulen_dec({lb}, {ub}, {w}), list_dec_f({edec}),\n\
             \x20                                         start, c_, klen, Flg::SameVer);\n\
             \x20                  lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n"
        ));
    }
    s.push_str(&format!(
        "               }}\n\
         \x20               {{ r.fail_at(i_); return None; }}\n\
         \x20           }}\n\
         \x20       }};\n\
         \x20       let ghost sx_ = {xv};\n\
         \x20       let ghost ov_ = {ov};\n\
         \x20       proof {{\n\
         \x20           lemma_rem_skip(r.buf@, pi as nat, (r.pos - pi) as nat);\n\
         \x20           lemma_list_loop_step(c_ as nat, {edec}, body, ov_, (pi - p1) as nat, fa_,\n\
         \x20                                (c_ - i_) as nat, bi, sx_, (r.pos - pi) as nat, fx_);\n\
         \x20       }}\n\
         \x20       out_.push(x_);\n\
         \x20       proof {{ assert({ov} =~= ov_.push(sx_)); }}\n\
         \x20       fa_ = flg_join(fa_, fx_);\n\
         \x20       i_ = i_ + 1;\n\
         \x20   }}\n\
         \x20   proof {{\n\
         \x20       lemma_list_loop_done(c_ as nat, {edec}, body, {ov}, (r.pos - p1) as nat, fa_,\n\
         \x20                            r.rem());\n\
         \x20       lemma_list_dec_val(c_ as nat, {edec}, body);\n",
        ov = lv("out_@")
    ));
    if !fixed {
        s.push_str(&format!(
            "        lemma_dep_dec_some(ulen_dec({lb}, {ub}, {w}), list_dec_f({edec}),\n\
             \x20                       start, c_, klen, Flg::SameVer, {ov}, (r.pos - p1) as nat, fa_);\n\
             \x20   lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, (c_, {ov}),\n\
             \x20                      (r.pos - p0) as nat, fa_);\n",
            ov = lv("out_@")
        ));
    }
    s.push_str("    }\n    Some((out_, fa_))\n}\n\n");

    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         pub fn {rn}_encode(w: &mut BitWriter, l: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({lvl}),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {rn}_enc()({lvl}),\n\
         {{\n{eprefix}",
        lvl = lv("l@")
    ));
    if !fixed {
        s.push_str(&format!(
            "    proof {{\n\
             \x20       {pf}\n\
             \x20       vasn::bits::prim_read::lemma_p2_56();\n\
             \x20       lemma_ulen_wf_bound({lb}, {ub}, {w}, {lvl}.len() as u64);\n\
             \x20   }}\n\
             \x20   if !w.write_ulen({lb}, {ub}, {w}, l.len() as u64) {{ return false; }}\n",
            lvl = lv("l@")
        ));
    }
    // a BIT STRING's bits or an OCTET STRING's octets: one bulk write
    // (vasn::uper::fast) rather than one per element
    let bulk_wr = match (elem.fmt.as_str(), eplain) {
        ("bool", true) => Some("write_bit_list"),
        ("byte", true) => Some("write_octet_list"),
        _ => None,
    };
    if let Some(wr) = bulk_wr {
        s.push_str(&format!(
            "    if !w.{wr}(l) {{ return false; }}\n\
             \x20   true\n}}\n\n"
        ));
    } else {
    s.push_str(&format!(
        "    let ghost mid = w.written();\n\
         \x20   let mut j_: usize = 0;\n\
         \x20   while j_ < l.len()\n\
         \x20       invariant\n\
         \x20           w.wf(), j_ <= l@.len(), w.buf@.len() == old(w).buf@.len(),\n\
         \x20           w.written() =~= mid + list_enc_rec({lvl}.take(j_ as int), {eenc}),\n\
         \x20       decreases l@.len() - j_,\n\
         \x20   {{\n\
         \x20       let ghost pre = {lvl}.take(j_ as int);\n\
         \x20       let x_ = &l[j_];\n\
         {xfact}\
         \x20       if !{eencode} {{ return false; }}\n\
         \x20       proof {{\n\
         \x20           lemma_list_enc_push(pre, {eenc}, {lvl}[j_ as int]);\n\
         \x20           assert({lvl}.take(j_ as int + 1) =~= pre.push({lvl}[j_ as int]));\n\
         \x20       }}\n\
         \x20       j_ = j_ + 1;\n\
         \x20   }}\n\
         \x20   proof {{ assert({lvl}.take({lvl}.len() as int) =~= {lvl}); }}\n\
         \x20   true\n}}\n\n",
        lvl = lv("l@"),
        // only for an element with a view: a plain list's encoder is left
        // exactly as it was, and one extra fact is enough to put a wide
        // element's loop over the rlimit
        xfact = if eplain { String::new() } else {
            format!("\x20       proof {{ assert({xvr} == {}[j_ as int]); }}\n", lv("l@"))
        }
    ));
    }

    // X.697 24 (BIT STRING: fixed size is bare hex, otherwise value and
    // length), 25.3 (OCTET STRING: hex), 28 (SEQUENCE OF: an array)
    let jbody = match kind {
        ListKind::Bits if fixed => "    jer_bits_fixed(v, o);\n".to_string(),
        ListKind::Bits => "    jer_bits_var(v, o);\n".to_string(),
        ListKind::Octets => "    jer_octets(v, o);\n".to_string(),
        ListKind::Chars(_) => "    jer_chars(v, o);\n".to_string(),
        ListKind::Of => format!(
            "    o.push('[');\n\
             \x20   for (i, x) in v.iter().enumerate() {{\n\
             \x20       if i > 0 {{ o.push(','); }}\n\
             \x20       {};\n\
             \x20   }}\n\
             \x20   o.push(']');\n",
            elem.jer.replace("{V}", "x").replace("{O}", "o")
        ),
    };
    s.push_str(&jer_fn(&rn, &jbody));
    // the element type's generator, `lb..=ub` of them (`Gen::len` keeps it short)
    s.push_str(&arb_fn(
        &rn,
        &format!(
            "    let n = g.len({lb}, {ub});\n    (0..n).map(|_| {}).collect()\n",
            elem.arb.replace("{G}", "g")
        ),
    ));
    Ok((
        s,
        Compiled {
            jer: format!("{rn}_jer({{V}}, {{O}})"),
            arb: format!("{rn}_arb({{G}})"),
            owner: None,
            rust_ty: format!("Vec<{ety}>"),
            spec_ty: Some(format!("Seq<{sty}>")),
            view: Some(if eplain { "{V}@".into() } else { format!("{rn}_lview({{V}}@)") }),
            fmt: rn.clone(),
            proof_call: format!("{rn}_is_format();"),
            decode: format!("{rn}_decode({{R}})"),
            encode: format!("{rn}_encode({{W}}, {{V}})"),
            preamble: vec![],
        },
    ))
}

/// A known-multiplier character string (X.691 30.5): a list of characters,
/// each `b` bits for an effective alphabet of N characters (30.5.2), holding
/// the character's code if every code fits in `b` bits and its index in the
/// sorted alphabet if not (30.5.4). The character format is generated per type
/// from the alphabet's ranges; the length is the ordinary list's (30.5.6, 30.5.7).
fn gen_kmstring(
    name: &str,
    kind: &StringKind,
    sc: &SizeCons,
    alpha: &Option<Vec<(u32, u32)>>,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    let rn = rustify(name);
    // the alphabet's runs of consecutive codes, sorted
    let mut ranges: Vec<(u64, u64)> = Vec::new();
    let mut rs: Vec<(u32, u32)> = alpha.clone().or_else(|| crate::constraints::alphabet(kind)).unwrap_or_default();
    rs.sort();
    for (lo, hi) in rs {
        match ranges.last_mut() {
            Some(r) if r.1 + 1 >= lo as u64 => r.1 = r.1.max(hi as u64),
            _ => ranges.push((lo as u64, hi as u64)),
        }
    }
    if ranges.is_empty() {
        return Err(Pending::Unsupported("a character string with no characters".into()));
    }
    let n: u64 = ranges.iter().map(|(lo, hi)| hi - lo + 1).sum();
    let max = ranges.last().unwrap().1;
    // a character is a u8, u16 or u32 by the largest code it can have
    let cty = if max <= 0xff { "u8" } else if max <= 0xffff { "u16" } else { "u32" };
    let mut b = 0u32;
    while (1u64 << b) < n {
        b += 1;
    }
    // 30.5.2: in the ALIGNED variant, the smallest power of two at least B
    if aper() && b > 0 {
        b = b.next_power_of_two();
    }
    // the i-th character, as an expression over `v` (an index)
    let mut nth = String::new();
    let mut acc = 0u64;
    for (k, (lo, hi)) in ranges.iter().enumerate() {
        let sz = hi - lo + 1;
        if k + 1 < ranges.len() {
            nth.push_str(&format!("if v < {} {{ ((v - {acc}u64) + {lo}u64) as {cty} }} else ", acc + sz));
        } else {
            nth.push_str(&format!("{{ ((v - {acc}u64) + {lo}u64) as {cty} }}"));
        }
        acc += sz;
    }
    let mut idx = String::new();
    let mut acc = 0u64;
    for (lo, hi) in &ranges {
        idx.push_str(&format!("if {lo}{cty} <= c && c <= {hi}{cty} {{ ((c as u64 - {lo}u64) + {acc}u64) as u64 }} else "));
        acc += hi - lo + 1;
    }
    idx.push_str("{ 0u64 }");
    let codes0 = ranges[0].0;
    let elem;
    let mut s = String::new();
    if b == 0 {
        // one character, no bits (as for a one-value INTEGER)
        let c = codes0;
        elem = Compiled {
            owner: None,
            spec_ty: None,
            view: None,
            rust_ty: cty.into(),
            fmt: format!("spec:unit_wf({c}{cty})|unit_enc::<{cty}>()|unit_dec({c}{cty})"),
            proof_call: format!("lemma_unit_format({c}{cty});"),
            decode: format!("{{ proof {{ lemma_unit_dec_val({c}{cty}, {{R}}.rem()); }} Some(({c}{cty}, Flg::SameVer)) }}"),
            encode: format!("{{ proof {{ reveal(unit_enc); assert({{W}}.written() + {} =~= {{W}}.written()); }} true }}",
                            ea(&format!("unit_enc::<{cty}>()"), "{W}.pos as nat", "{V}")),
            preamble: vec![],
            jer: "jer_int(*{V} as i64, {O})".into(),
            arb: format!("{c}{cty}"),
        };
    } else {
        let direct = max < (1u64 << b);
        let ok = if direct {
            ranges.iter().map(|(lo, hi)| format!("({lo}u64 <= v && v <= {hi}u64)")).collect::<Vec<_>>().join(" || ")
        } else {
            format!("v < {n}u64")
        };
        let to = if direct { format!("(v as {cty})") } else { format!("({nth})") };
        let from = if direct { "(c as u64)".to_string() } else { format!("({idx})") };
        let pf = p2_fact(b);
        s.push_str(&format!(
            "// ------------------------------------------ {name}: a character, {b} bits, {how} (X.691 30.5.4)
pub open spec fn {rn}_cok() -> spec_fn(u64) -> bool {{ |v: u64| {ok} }}
pub open spec fn {rn}_cto() -> spec_fn(u64) -> {cty} {{ |v: u64| {to} }}
pub open spec fn {rn}_cfrom() -> spec_fn({cty}) -> u64 {{ |c: {cty}| {from} }}
pub open spec fn {rn}_c_wf() -> Wf<{cty}> {{ map_wf(restrict_wf(uint_wf({b}), {rn}_cok()), {rn}_cto(), {rn}_cfrom()) }}
pub open spec fn {rn}_c_enc() -> Enc<{cty}> {{ map_enc(uint_enc({b}), {rn}_cfrom()) }}
pub open spec fn {rn}_c_dec() -> Dec<{cty}> {{ map_dec(restrict_dec(uint_dec({b}), {rn}_cok()), {rn}_cto()) }}

pub proof fn {rn}_c_is_format()
    ensures is_format({rn}_c_wf(), {rn}_c_enc(), {rn}_c_dec()),
{{
    {pf}
    lemma_uint_format({b});
    lemma_restrict_format(uint_wf({b}), uint_enc({b}), uint_dec({b}), {rn}_cok());
    assert forall|v: u64| restrict_wf(uint_wf({b}), {rn}_cok())(v) implies #[trigger] {rn}_cfrom()({rn}_cto()(v)) == v by {{
        lemma_restrict_wf_val(uint_wf({b}), {rn}_cok(), v);
    }}
    lemma_map_format(restrict_wf(uint_wf({b}), {rn}_cok()), uint_enc({b}), restrict_dec(uint_dec({b}), {rn}_cok()),
                     {rn}_cto(), {rn}_cfrom());
}}

pub fn {rn}_c_decode(r: &mut BitReader) -> (res: Option<({cty}, Flg)>)
    requires old(r).wf(),
    ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,
        match res {{
            Some((c, f)) => {rn}_c_dec()(old(r).rem())
                == Some::<({cty}, nat, Flg)>((c, (final(r).pos - old(r).pos) as nat, f)),
            None => {rn}_c_dec()(old(r).rem()).is_none(),
        }},
{{
    proof {{ {pf} }}
    let ghost start = r.rem();
    match r.read_uint({b}) {{
        Some(v) => {{
            if {ok} {{
                proof {{
                    lemma_restrict_dec_some(uint_dec({b}), {rn}_cok(), start, v, {b}, Flg::SameVer);
                    lemma_map_dec_some(restrict_dec(uint_dec({b}), {rn}_cok()), {rn}_cto(), start, v, {b}, Flg::SameVer);
                }}
                Some(({to}, Flg::SameVer))
            }} else {{
                proof {{
                    lemma_restrict_dec_none(uint_dec({b}), {rn}_cok(), start);
                    lemma_map_dec_none(restrict_dec(uint_dec({b}), {rn}_cok()), {rn}_cto(), start);
                }}
                {{ r.fail(\"a character outside the permitted alphabet\"); None }}
            }}
        }}
        None => {{
            proof {{
                lemma_restrict_dec_none(uint_dec({b}), {rn}_cok(), start);
                lemma_map_dec_none(restrict_dec(uint_dec({b}), {rn}_cok()), {rn}_cto(), start);
            }}
            {{ r.fail(\"a character\"); None }}
        }}
    }}
}}

pub fn {rn}_c_encode(w: &mut BitWriter, c: {cty}) -> (ok: bool)
    requires old(w).wf(), {rn}_c_wf()(c),
    ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),
        ok ==> final(w).written() =~= old(w).written() + {cenc},
{{
    proof {{
        {pf}
        lemma_map_wf_val(restrict_wf(uint_wf({b}), {rn}_cok()), {rn}_cto(), {rn}_cfrom(), c);
        lemma_restrict_wf_val(uint_wf({b}), {rn}_cok(), {rn}_cfrom()(c));
        lemma_map_enc_val(uint_enc({b}), {rn}_cfrom(), {cpos}c);
    }}
    let v: u64 = {from};
    w.write_uint({b}, v)
}}

#[verifier::external]
pub fn {rn}_c_arb(g: &mut Gen) -> {cty} {{ {carb} }}

",
            how = if direct { "its code" } else { "its index" },
            // a code past the octet: one that is a Unicode character, so that
            // every JER printer can show it; the decoder takes them all
            carb = if cty == "u8" {
                format!("let v = g.range(0, {}) as u64; {nth}", n - 1)
            } else {
                format!("for _ in 0..8 {{ let v = g.range(0, {}) as u64; let c = {nth}; \
                         if char::from_u32(c as u32).is_some() {{ return c; }} }} {{ let v = 0u64; {nth} }}", (n - 1).min(0x2ffff))
            },
            cenc = ea(&format!("{rn}_c_enc()"), OLD_POS, "c"),
            cpos = if aper() { "old(w).pos as nat, " } else { "" },
        ));
        elem = Compiled {
            owner: None,
            spec_ty: None,
            view: None,
            rust_ty: cty.into(),
            fmt: format!("spec:{rn}_c_wf()|{rn}_c_enc()|{rn}_c_dec()"),
            proof_call: format!("{rn}_c_is_format();"),
            decode: format!("{rn}_c_decode({{R}})"),
            encode: format!("{rn}_c_encode({{W}}, {{V}})"),
            preamble: vec![],
            jer: "jer_int(*{V} as i64, {O})".into(),
            arb: format!("{rn}_c_arb({{G}})"),
        };
    }
    let (ltext, lc) = gen_list_type(name, sc, elem, ListKind::Chars(b), values)?;
    s.push_str(&ltext);
    Ok((s, lc))
}

/// UTF8String (X.691 30.6): its UTF-8 octets, with a length in octets
/// whatever its constraints, which are never PER-visible. Octets that are not
/// UTF-8 encode no string, so the octet list is restricted to `utf8_ok`.
fn gen_utf8(name: &str) -> (String, Compiled) {
    let rn = rustify(name);
    let (btext, bc) = gen_list_frag(&format!("{name}-octets"), 0, u64::MAX, byte_elem(), ListKind::Octets);
    let arb = "{ let n = g.len(0, 15); let s: String = (0..n).map(|_| { let cp = match g.bits(2) { 0 => g.range(0x20, 0x7e), 1 => g.range(0xa0, 0x7ff), 2 => g.range(0x800, 0xd7ff), _ => g.range(0x10000, 0x10ffff) }; char::from_u32(cp as u32).unwrap_or('?') }).collect(); s.into_bytes() }";
    let (wtext, mut wc) = restrict_wrap(
        &rn,
        &bc,
        "|s: Seq<u8>| utf8_ok(s)",
        "!utf8_check(v.as_slice())",
        "UTF8String: octets that are not UTF-8 (X.691 30.6)",
        arb,
    );
    wc.jer = "jer_utf8({V}, {O})".into();
    (format!("{btext}{wtext}"), wc)
}

/// OBJECT IDENTIFIER and RELATIVE-OID (X.691 24, 25): the BER contents octets
/// (X.690 8.19, 8.20) with a semi-constrained length in octets, which is an
/// unconstrained OCTET STRING's encoding. Octets that are not the contents of
/// any value are rejected (`vasn::oid`).
fn gen_oid(name: &str, relative: bool) -> (String, Compiled) {
    let rn = rustify(name);
    let (btext, bc) = gen_list_frag(&format!("{name}-octets"), 0, u64::MAX, byte_elem(), ListKind::Octets);
    let what = if relative { "RELATIVE-OID" } else { "OBJECT IDENTIFIER" };
    let (wtext, mut wc) = restrict_wrap(
        &rn,
        &bc,
        "|s: Seq<u8>| vasn::oid::oid_ok(s)",
        "!vasn::oid::oid_check(v.as_slice())",
        &format!("{what}: not the contents of one (X.690 8.19.2)"),
        &format!("g.oid({relative})"),
    );
    wc.jer = if relative { "jer_roid({V}, {O})" } else { "jer_oid({V}, {O})" }.into();
    (format!("{btext}{wtext}"), wc)
}

/// REAL (X.691 15): the CER/DER contents octets (X.690 8.5, 11.3) with an
/// unconstrained length, an unconstrained OCTET STRING's encoding. Octets not
/// in that form are rejected (`vasn::real`), so that each value has one
/// encoding.
fn gen_real(name: &str) -> (String, Compiled) {
    let rn = rustify(name);
    let (btext, bc) = gen_list_frag(&format!("{name}-octets"), 0, u64::MAX, byte_elem(), ListKind::Octets);
    let (wtext, mut wc) = restrict_wrap(
        &rn,
        &bc,
        "|s: Seq<u8>| vasn::real::real_ok(s)",
        "!vasn::real::real_check(v.as_slice())",
        "REAL: not in the CER/DER form (X.690 11.3, X.691 15)",
        "g.real()",
    );
    wc.jer = "jer_real({V}, {O})".into();
    (format!("{btext}{wtext}"), wc)
}

/// A string that is not known-multiplier, other than UTF8String (X.691 30.6):
/// GeneralString, GraphicString, TeletexString, VideotexString,
/// ObjectDescriptor. Its "base encoding" (X.690 8.23.5) is the octets of the
/// ISO/IEC 2022 escapes and characters, taken as they are: an unconstrained
/// OCTET STRING, printed as the characters of those codes.
fn gen_octet_chars(name: &str) -> (String, Compiled) {
    let visible = Compiled { arb: "({G}.range(32, 126) as u8)".into(), ..byte_elem() };
    let (text, mut c) = gen_list_frag(name, 0, u64::MAX, visible, ListKind::Octets);
    c.jer = "jer_octet_chars({V}, {O})".into();
    (text, c)
}

/// A SEQUENCE OF, BIT STRING or OCTET STRING with an extensible SIZE (X.691
/// 16.6, 17.3, 20.4): one bit, 0 if the size is in the root and then the root's
/// encoding, 1 if not and then the size as a semi-constrained whole number. The
/// root is the list compiled as if not extensible (`{name}-sroot`), the
/// extension a list of any size (`{name}-sext`) restricted to sizes outside the
/// root (10.4.3), and the type `vasn::uper::fraglist`'s extension bit over the two.
fn gen_list_ext(
    name: &str,
    lb: u64,
    ub: Option<u64>,
    elem: Compiled,
    kind: ListKind,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    let rn = rustify(name);
    let root_sc = match ub {
        Some(u) if u == lb => SizeCons::Fixed(Num::Lit(lb as i64)),
        Some(u) => SizeCons::Range(Num::Lit(lb as i64), Num::Lit(u as i64)),
        None => SizeCons::Semi(Num::Lit(lb as i64)),
    };
    let (rtext, rc) = gen_list_type(&format!("{name}-sroot"), &root_sc, elem.clone(), kind, values)?;
    let (etext, ec) = gen_list_frag(&format!("{name}-sext"), 0, u64::MAX, elem.clone(), kind);
    let sty = ec.sty();
    let rty = ec.rust_ty.clone();
    let inr = |x: &str| match ub {
        Some(u) => format!("{lb} <= {x}.len() && {x}.len() <= {u}"),
        None => format!("{lb} <= {x}.len()"),
    };
    let earb = elem.arb.replace("{G}", "g");
    // a size outside the root: below lb, or above ub
    let out_arb = match ub {
        Some(u) if lb > 0 => format!(
            "{{ let n: usize = if g.bool() {{ g.len(0, {}) }} else {{ {} + g.bits(2) as usize }}; (0..n).map(|_| {earb}).collect() }}",
            lb - 1,
            u + 1
        ),
        Some(u) => format!("{{ let n: usize = {} + g.bits(2) as usize; (0..n).map(|_| {earb}).collect() }}", u + 1),
        None if lb > 0 => format!("{{ let n: usize = g.len(0, {}); (0..n).map(|_| {earb}).collect() }}", lb - 1),
        None => rc.arb.replace("{G}", "g"),
    };
    let (otext, oc) = restrict_wrap(
        &format!("{rn}_sout"),
        &ec,
        &format!("|s: {sty}| !({})", inr("s")),
        &inr("v"),
        "extensible SIZE: a size in the root sent as an extension (X.691 10.4.3)",
        &out_arb,
    );
    let (rwf, renc, rdec) = (wf_of(&rc), enc_of(&rc), dec_of(&rc));
    let (owf, oenc, odec) = (wf_of(&oc), enc_of(&oc), dec_of(&oc));
    // the root's well-formedness bounds the size: the reason differs by shape
    let root_bound = match &root_sc {
        SizeCons::Fixed(_) => format!("assert({rwf}(s) ==> s.len() == {lb});"),
        SizeCons::Range(..) if aper() => {
            let u = ub.unwrap();
            let (w, a) = aper_list::length_field(lb, u);
            let al = aper_list::contents_aligned(kind, lb, u);
            let rr = rustify(&format!("{name}-sroot"));
            format!(
                "if {rwf}(s) {{\n\
                 \x20           lemma_map_wf_val({rr}_full_wf(), {rr}_to_f(), {rr}_from_f(), s);\n\
                 \x20           lemma_dep_wf_val(alen_wf({lb}, {u}, {w}, {a}), list_wf_f({al}, {ew}), s.len() as u64, s);\n\
                 \x20           lemma_alen_wf_bound({lb}, {u}, {w}, {a}, s.len() as u64);\n\
                 \x20       }}",
                ew = wf_of(&elem)
            )
        }
        SizeCons::Range(..) => {
            let w = width_for(ub.unwrap() - lb + 1);
            let rr = rustify(&format!("{name}-sroot"));
            format!(
                "if {rwf}(s) {{\n\
                 \x20           lemma_map_wf_val({rr}_full_wf(), {rr}_to_f(), {rr}_from_f(), s);\n\
                 \x20           lemma_dep_wf_val(ulen_wf({lb}, {u}, {w}), list_wf_f({ew}), s.len() as u64, s);\n\
                 \x20           lemma_ulen_wf_bound({lb}, {u}, {w}, s.len() as u64);\n\
                 \x20       }}",
                u = ub.unwrap(),
                ew = wf_of(&elem)
            )
        }
        _ => format!("lemma_restrict_wf_val(flist_wf({}), flist_ok({lb}, {}), s);", wf_of(&elem), u64::MAX),
    };
    let pf = match &root_sc {
        SizeCons::Range(..) if aper() => format!("{} vasn::bits::prim_read::lemma_p2_56();",
                                                 p2_fact(aper_list::length_field(lb, ub.unwrap()).0)),
        SizeCons::Range(..) => format!("{} vasn::bits::prim_read::lemma_p2_56();", p2_fact(width_for(ub.unwrap() - lb + 1))),
        _ => String::new(),
    };
    let lvl = ec.view_of("l");
    let jer_body = ec.jer.replace("{V}", "v").replace("{O}", "o");
    let mut s = String::new();
    s.push_str(&rtext);
    s.push_str(&etext);
    s.push_str(&otext);
    s.push_str(&format!(
        "// ---------------------------------------------------------------- {name}
pub type {rn} = {rty};

pub open spec fn {rn}_in() -> spec_fn({sty}) -> bool {{ |s: {sty}| {sin} }}
pub open spec fn {rn}_wf() -> Wf<{sty}> {{ xext_wf({rwf}, {owf}, {rn}_in()) }}
pub open spec fn {rn}_enc() -> Enc<{sty}> {{ xext_enc({renc}, {oenc}, {rn}_in()) }}
pub open spec fn {rn}_dec() -> Dec<{sty}> {{ xext_dec({rdec}, {odec}) }}

pub proof fn {rn}_is_format()
    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),
{{
    {rproof}
    {oproof}
    {pf}
    assert forall|s: {sty}| #[trigger] {rwf}(s) implies {rn}_in()(s) by {{
        {root_bound}
    }}
    assert forall|s: {sty}| #[trigger] {owf}(s) implies !{rn}_in()(s) by {{
        lemma_restrict_wf_val({ewf2}, {rn}_sout_ok(), s);
    }}
    lemma_xext_format({rwf}, {renc}, {rdec}, {owf}, {oenc}, {odec}, {rn}_in());
}}

pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rty}, Flg)>)
    requires old(r).wf(),
    ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,
        match res {{
            Some((v, f)) => {rn}_dec()(old(r).rem())
                == Some::<({sty}, nat, Flg)>(({vv}, (final(r).pos - old(r).pos) as nat, f)),
            None => {rn}_dec()(old(r).rem()).is_none(),
        }},
{{
    let ghost start = r.rem();
    let ghost p0 = r.pos;
    let ghost d2 = xext_alt_dec({rdec}, {odec});
    let ghost full = dep_dec(bool_dec(), d2);
    let x = match r.read_bool() {{
        Some(x) => x,
        None => {{
            proof {{
                lemma_dep_dec_none_fst(bool_dec(), d2, start);
                lemma_map_dec_none(full, xext_to(), start);
            }}
            {{ r.fail(\"extensible SIZE: extension bit\"); return None; }}
        }}
    }};
    proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}
    let ghost kb = (r.pos - p0) as nat;
    let ghost p1 = r.pos;
    let got = if !x {{ {rdecode} }} else {{ {odecode} }};
    match got {{
        Some((v, f)) => {{
            proof {{
                lemma_dep_dec_some(bool_dec(), d2, start, x, kb, Flg::SameVer, {vv}, (r.pos - p1) as nat, f);
                lemma_map_dec_some(full, xext_to(), start, (x, {vv}), (r.pos - p0) as nat, flg_add(Flg::SameVer, f));
            }}
            Some((v, f))
        }}
        None => {{
            proof {{
                lemma_dep_dec_none_snd(bool_dec(), d2, start, x, kb, Flg::SameVer);
                lemma_map_dec_none(full, xext_to(), start);
            }}
            None
        }}
    }}
}}

pub fn {rn}_encode(w: &mut BitWriter, l: &{rty}) -> (ok: bool)
    requires old(w).wf(), {rn}_wf()({lvl}),
    ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),
        ok ==> final(w).written() =~= old(w).written() + {xenc},
{{
    let inr = {einr};
    proof {{
        lemma_xext_enc({renc}, {oenc}, {rwf}, {owf}, {rn}_in(), {xpos}{lvl});
        assert(inr == {rn}_in()({lvl}));
    }}
    let ghost w0 = w.written();
    if !w.write_bool(!inr) {{ return false; }}
    let ok = if inr {{ {rencode} }} else {{ {oencode} }};
    ok
}}

#[verifier::external]
pub fn {rn}_jer(v: &{rn}, o: &mut String) {{ {jer_body}; }}

#[verifier::external]
pub fn {rn}_arb(g: &mut Gen) -> {rn} {{ if g.bool() {{ {rarb} }} else {{ {oarb} }} }}

",
        sin = inr("s"),
        rproof = rc.proof_call,
        oproof = oc.proof_call,
        ewf2 = wf_of(&ec),
        vv = ec.view_of("v"),
        rdecode = rc.decode.replace("{R}", "r"),
        odecode = oc.decode.replace("{R}", "r"),
        rencode = rc.encode.replace("{W}", "w").replace("{V}", "l"),
        oencode = oc.encode.replace("{W}", "w").replace("{V}", "l"),
        einr = inr("l"),
        rarb = rc.arb.replace("{G}", "g"),
        oarb = oc.arb.replace("{G}", "g"),
        xenc = ea(&format!("{rn}_enc()"), OLD_POS, &lvl),
        xpos = if aper() { "w.pos as nat, " } else { "" },
    ));
    Ok((
        s,
        Compiled {
            jer: format!("{rn}_jer({{V}}, {{O}})"),
            arb: format!("{rn}_arb({{G}})"),
            owner: None,
            rust_ty: rty.clone(),
            spec_ty: ec.spec_ty.clone(),
            view: ec.view.clone(),
            fmt: rn.clone(),
            proof_call: format!("{rn}_is_format();"),
            decode: format!("{rn}_decode({{R}})"),
            encode: format!("{rn}_encode({{W}}, {{V}})"),
            preamble: vec![],
        },
    ))
}

/// A SEQUENCE OF, BIT STRING or OCTET STRING whose SIZE has `ub` >= 64K
/// (X.691 11.9.4.2): the general length determinant, counting `n` itself and
/// fragmenting at 16K elements (11.9.3.8), which is `vasn::uper::fraglist`. The
/// decoder reads a head, then that fragment's elements with the ordinary
/// element loop (`{rn}_frag_dec`), until a final head; the SIZE is checked on
/// the result, as the spec's `restrict` does.
fn gen_list_frag(name: &str, lb: u64, ub: u64, elem: Compiled, kind: ListKind) -> (String, Compiled) {
    if aper() {
        return aper_list::gen_frag(name, lb, ub, elem, kind);
    }
    let rn = rustify(name);
    let ety = elem.rust_ty.clone();
    let sty = elem.sty();
    let eplain = elem.plain();
    let lv = |e: &str| -> String {
        if eplain { e.to_string() } else { format!("{rn}_lview({e})") }
    };
    let xv = elem.view_of("x_");
    let xvr = elem.view_of("(*x_)");
    let ewf = wf_of(&elem);
    let eenc = enc_of(&elem);
    let edec = dec_of(&elem);
    let edecode = elem.decode.replace("{R}", "r");
    let eencode = elem
        .encode
        .replace("{W}", "w")
        .replace("{V}", if ety == "bool" || ety == "u8" || ety == "u16" || ety == "u32" || ety == "i64" || ety == "Null" {
            "*x_"
        } else {
            "x_"
        });
    let mut eprefix = String::new();
    for p in &elem.preamble {
        eprefix.push_str(&format!("    proof {{ {p} }}\n"));
    }
    let fixed = lb == ub;
    let unbounded = ub == u64::MAX;
    let what = if fixed {
        format!("SIZE ({lb})")
    } else if unbounded {
        format!("SIZE ({lb}..MAX)")
    } else {
        format!("SIZE ({lb}..{ub})")
    };
    let (lo, lho, lout, lold) = (lv("l@"), lv("out_@"), lv("final(out_)@"), lv("old(out_)@"));

    let mut s = String::new();
    s.push_str(&format!(
        "// ---------------------------------------------------------------- {name}\n"
    ));
    s.push_str(&format!("pub type {rn} = Vec<{ety}>;\n\n"));
    if !eplain {
        s.push_str(&format!(
            "pub open spec fn {rn}_lview(s: Seq<{ety}>) -> Seq<{sty}> {{ s.map_values(|x_: {ety}| {xv}) }}\n\n"
        ));
    }
    s.push_str(&format!(
        "pub open spec fn {rn}_wf() -> Wf<Seq<{sty}>> {{ fsized_wf({lb}, {ub}, {ewf}) }}\n\
         pub open spec fn {rn}_enc() -> Enc<Seq<{sty}>> {{ fsized_enc({eenc}) }}\n\
         pub open spec fn {rn}_dec() -> Dec<Seq<{sty}>> {{ fsized_dec({lb}, {ub}, {edec}) }}\n\n\
         pub proof fn {rn}_is_format()\n\
         \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
         {{\n    {}\n    lemma_fsized_format({lb}, {ub}, {ewf}, {eenc}, {edec});\n}}\n\n",
        elem.proof_call
    ));

    // one fragment's `c_` elements, appended to `out_`
    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         pub fn {rn}_frag_dec(r: &mut BitReader, out_: &mut Vec<{ety}>, c_: u64) -> (res: Option<Flg>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       final(out_)@.len() >= old(out_)@.len(),\n\
         \x20       {lout}.take(old(out_)@.len() as int) == {lold},\n\
         \x20       match res {{\n\
         \x20           Some(f_) => list_dec_rec(c_ as nat, {edec}, old(r).rem())\n\
         \x20               == Some::<(Seq<{sty}>, nat, Flg)>(({lout}.skip(old(out_)@.len() as int),\n\
         \x20                                                 (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => list_dec_rec(c_ as nat, {edec}, old(r).rem()).is_none(),\n\
         \x20       }},\n\
         {{\n{eprefix}\
         \x20   let ghost body = old(r).rem();\n\
         \x20   let ghost p1 = old(r).pos;\n\
         \x20   let ghost o0 = {lho};\n\
         \x20   let n0 = out_.len();\n\
         \x20   let mut i_: u64 = 0;\n\
         \x20   let mut fa_: Flg = Flg::SameVer;\n\
         \x20   proof {{\n\
         \x20       lemma_list_loop_start(c_ as nat, {edec}, body);\n\
         \x20       assert({lho}.skip(n0 as int) =~= Seq::<{sty}>::empty());\n\
         \x20       assert({lho}.take(n0 as int) =~= o0);\n\
         \x20   }}\n\
         \x20   while i_ < c_\n\
         \x20       invariant\n\
         \x20           r.wf(), r.buf == old(r).buf, r.pos >= p1, p1 == old(r).pos,\n\
         \x20           body == old(r).rem(), o0 == {lold}, n0 == o0.len(),\n\
         \x20           out_@.len() == n0 + i_, i_ <= c_,\n\
         \x20           {lho}.take(n0 as int) == o0,\n\
         \x20           list_dec_rec(c_ as nat, {edec}, body)\n\
         \x20               == list_cont({lho}.skip(n0 as int), (r.pos - p1) as nat, fa_,\n\
         \x20                            list_dec_rec((c_ - i_) as nat, {edec}, r.rem())),\n\
         \x20       decreases c_ - i_,\n\
         \x20   {{\n\
         \x20       let ghost bi = r.rem();\n\
         \x20       let ghost pi = r.pos;\n\
         \x20       let (x_, fx_) = match {edecode} {{\n\
         \x20           Some(vf_) => vf_,\n\
         \x20           None => {{\n\
         \x20               proof {{\n\
         \x20                   lemma_list_loop_fail(c_ as nat, {edec}, body, {lho}.skip(n0 as int),\n\
         \x20                                        (pi - p1) as nat, fa_, (c_ - i_) as nat, bi);\n\
         \x20               }}\n\
         \x20               let at_: u64 = if n0 as u64 <= u64::MAX - i_ {{ n0 as u64 + i_ }} else {{ i_ }};\n\
         \x20               {{ r.fail_at(at_); return None; }}\n\
         \x20           }}\n\
         \x20       }};\n\
         \x20       let ghost sx_ = {xv};\n\
         \x20       let ghost all_ = {lho};\n\
         \x20       let ghost ov_ = all_.skip(n0 as int);\n\
         \x20       proof {{\n\
         \x20           lemma_rem_skip(r.buf@, pi as nat, (r.pos - pi) as nat);\n\
         \x20           lemma_list_loop_step(c_ as nat, {edec}, body, ov_, (pi - p1) as nat, fa_,\n\
         \x20                                (c_ - i_) as nat, bi, sx_, (r.pos - pi) as nat, fx_);\n\
         \x20       }}\n\
         \x20       out_.push(x_);\n\
         \x20       proof {{\n\
         \x20           assert({lho} =~= all_.push(sx_));\n\
         \x20           assert({lho}.skip(n0 as int) =~= ov_.push(sx_));\n\
         \x20           assert({lho}.take(n0 as int) =~= all_.take(n0 as int));\n\
         \x20       }}\n\
         \x20       fa_ = flg_join(fa_, fx_);\n\
         \x20       i_ = i_ + 1;\n\
         \x20   }}\n\
         \x20   proof {{\n\
         \x20       lemma_list_loop_done(c_ as nat, {edec}, body, {lho}.skip(n0 as int),\n\
         \x20                            (r.pos - p1) as nat, fa_, r.rem());\n\
         \x20   }}\n\
         \x20   Some(fa_)\n\
         }}\n\n"
    ));

    // the heads, and the SIZE check at the end
    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v_, f_)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<(Seq<{sty}>, nat, Flg)>(({v},\n\
         \x20                                                 (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n\
         {{\n{eprefix}\
         \x20   let ghost start = old(r).rem();\n\
         \x20   let ghost p0 = old(r).pos;\n\
         \x20   let mut out_: Vec<{ety}> = Vec::new();\n\
         \x20   let mut fa_: Flg = Flg::SameVer;\n\
         \x20   let mut pending_: bool = false;\n\
         \x20   proof {{\n\
         \x20       lemma_flist_loop_start({edec}, start);\n\
         \x20       assert({lho} =~= Seq::<{sty}>::empty());\n\
         \x20       lemma_flist_dec_val({edec}, start);\n\
         \x20   }}\n\
         \x20   loop\n\
         \x20       invariant\n\
         \x20           r.wf(), r.buf == old(r).buf, p0 == old(r).pos, start == old(r).rem(),\n\
         \x20           r.pos >= p0,\n\
         \x20           r.rem() == start.skip((r.pos - p0) as int),\n\
         \x20           (r.pos - p0) + r.rem().len() == start.len(),\n\
         \x20           flist_dec({edec})(start) == flist_dec_rec({edec}, start),\n\
         \x20           flist_dec_rec({edec}, start)\n\
         \x20               == flist_cont({lho}, (r.pos - p0) as nat, fa_, pending_,\n\
         \x20                             flist_dec_rec({edec}, r.rem())),\n\
         \x20       decreases 8 * r.buf@.len() - r.pos,\n\
         \x20   {{\n\
         \x20       let ghost cur = r.rem();\n\
         \x20       let ghost consumed = (r.pos - p0) as nat;\n\
         \x20       let ghost acc = {lho};\n\
         \x20       let ph = r.pos;\n\
         \x20       let h = match r.read_lh() {{\n\
         \x20           Some(h) => h,\n\
         \x20           None => {{\n\
         \x20               proof {{\n\
         \x20                   lemma_flist_loop_fail({edec}, start, cur, acc, consumed, fa_, pending_);\n\
         \x20                   lemma_restrict_dec_none(flist_dec({edec}), flist_ok({lb}, {ub}), start);\n\
         \x20               }}\n\
         \x20               {{ r.fail(\"{what} length\"); return None; }}\n\
         \x20           }}\n\
         \x20       }};\n\
         \x20       proof {{\n\
         \x20           lemma_lh_dec_facts(cur);\n\
         \x20           lemma_lh_wf_iff(h);\n\
         \x20           lemma_rem_skip(r.buf@, ph as nat, (r.pos - ph) as nat);\n\
         \x20       }}\n\
         \x20       let ghost k = (r.pos - ph) as nat;\n\
         \x20       let (c_, last_) = match h {{\n\
         \x20           LenHead::Final(n) => (n, true),\n\
         \x20           LenHead::Frag(m) => {{\n\
         \x20               // 11.9.3.8.1: after a fragment below the cap, only a final head\n\
         \x20               if pending_ {{\n\
         \x20                   proof {{\n\
         \x20                       lemma_flist_loop_pending({edec}, start, cur, acc, consumed, fa_, m, k);\n\
         \x20                       lemma_restrict_dec_none(flist_dec({edec}), flist_ok({lb}, {ub}), start);\n\
         \x20                   }}\n\
         \x20                   {{ r.fail(\"{what} length: fragment after a short fragment\"); return None; }}\n\
         \x20               }}\n\
         \x20               (m * 16384, false)\n\
         \x20           }}\n\
         \x20       }};\n\
         \x20       let ghost hm: u64 = match h {{ LenHead::Final(n) => n, LenHead::Frag(m) => m }};\n\
         \x20       proof {{\n\
         \x20           assert(h == if last_ {{ LenHead::Final(hm) }} else {{ LenHead::Frag(hm) }});\n\
         \x20           assert(c_ as nat == if last_ {{ hm as nat }} else {{ (hm as nat) * 16384 }});\n\
         \x20       }}\n\
         \x20       let ghost pc = r.pos;\n\
         \x20       let fx_ = match {rn}_frag_dec(r, &mut out_, c_) {{\n\
         \x20           Some(f) => f,\n\
         \x20           None => {{\n\
         \x20               proof {{\n\
         \x20                   assert(cur.skip(k as int) =~= bits_of(r.buf@).skip(pc as int));\n\
         \x20                   lemma_flist_loop_fail({edec}, start, cur, acc, consumed, fa_, pending_);\n\
         \x20                   lemma_restrict_dec_none(flist_dec({edec}), flist_ok({lb}, {ub}), start);\n\
         \x20               }}\n\
         \x20               return None;\n\
         \x20           }}\n\
         \x20       }};\n\
         \x20       let ghost l1 = {lho}.skip(acc.len() as int);\n\
         \x20       let ghost k1 = (r.pos - pc) as nat;\n\
         \x20       proof {{\n\
         \x20           assert(cur.skip(k as int) =~= bits_of(r.buf@).skip(pc as int));\n\
         \x20           assert({lho} =~= acc + l1);\n\
         \x20           lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat);\n\
         \x20           assert(k + k1 <= cur.len());\n\
         \x20       }}\n\
         \x20       if last_ {{\n\
         \x20           proof {{\n\
         \x20               lemma_flist_loop_final({edec}, start, cur, acc, consumed, fa_, pending_,\n\
         \x20                                      hm, k, l1, k1, fx_);\n\
         \x20           }}\n\
         \x20           let f_ = flg_join(fa_, fx_);\n\
         \x20           let n_ = out_.len();\n\
         \x20           if {sizebad} {{\n\
         \x20               proof {{ lemma_restrict_dec_none(flist_dec({edec}), flist_ok({lb}, {ub}), start); }}\n\
         \x20               {{ r.fail(\"{what}\"); return None; }}\n\
         \x20           }}\n\
         \x20           proof {{\n\
         \x20               lemma_restrict_dec_some(flist_dec({edec}), flist_ok({lb}, {ub}), start, {lho},\n\
         \x20                                       (r.pos - p0) as nat, f_);\n\
         \x20           }}\n\
         \x20           return Some((out_, f_));\n\
         \x20       }}\n\
         \x20       proof {{\n\
         \x20           lemma_flist_loop_frag({edec}, start, cur, acc, consumed, fa_, hm, k, l1, k1, fx_);\n\
         \x20       }}\n\
         \x20       fa_ = flg_join(fa_, fx_);\n\
         \x20       pending_ = c_ < 4 * 16384;\n\
         \x20   }}\n\
         }}\n\n",
        v = lv("v_@"),
        sizebad = match (lb == 0, unbounded) {
            (true, true) => "false".to_string(),
            (false, true) => format!("n_ < {lb}"),
            (true, false) => format!("n_ > {ub}"),
            (false, false) => format!("n_ < {lb} || n_ > {ub}"),
        }
    ));

    // the encoder: `cnt` elements from `from` on, then the heads around them
    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         pub fn {rn}_frag_enc(w: &mut BitWriter, l: &{rn}, from: usize, cnt: usize) -> (ok: bool)\n\
         \x20   requires old(w).wf(), from + cnt <= l@.len(),\n\
         \x20       forall|i: int| 0 <= i < {lo}.len() ==> #[trigger] {ewf}({lo}[i]),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written()\n\
         \x20           =~= old(w).written() + list_enc_rec({lo}.subrange(from as int, (from + cnt) as int), {eenc}),\n\
         {{\n{eprefix}\
         \x20   let ghost mid = w.written();\n\
         \x20   let n_ = l.len();\n\
         \x20   let end_ = from + cnt;\n\
         \x20   let mut j_: usize = from;\n\
         \x20   proof {{ assert({lo}.subrange(from as int, from as int) =~= Seq::<{sty}>::empty()); }}\n\
         \x20   while j_ < end_\n\
         \x20       invariant\n\
         \x20           w.wf(), from <= j_ <= end_, end_ == from + cnt, from + cnt <= l@.len(),\n\
         \x20           w.buf@.len() == old(w).buf@.len(),\n\
         \x20           w.written() =~= mid + list_enc_rec({lo}.subrange(from as int, j_ as int), {eenc}),\n\
         \x20       decreases end_ - j_,\n\
         \x20   {{\n\
         \x20       let ghost pre = {lo}.subrange(from as int, j_ as int);\n\
         \x20       let x_ = &l[j_];\n\
         {xfact}\
         \x20       proof {{ assert({ewf}({lo}[j_ as int])); }}\n\
         \x20       if !{eencode} {{ return false; }}\n\
         \x20       proof {{\n\
         \x20           lemma_list_enc_push(pre, {eenc}, {lo}[j_ as int]);\n\
         \x20           assert({lo}.subrange(from as int, j_ as int + 1) =~= pre.push({lo}[j_ as int]));\n\
         \x20       }}\n\
         \x20       j_ = j_ + 1;\n\
         \x20   }}\n\
         \x20   true\n\
         }}\n\n\
         #[verifier::loop_isolation(false)]\n\
         pub fn {rn}_encode(w: &mut BitWriter, l: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({lo}),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {rn}_enc()({lo}),\n\
         {{\n{eprefix}\
         \x20   let ghost s = {lo};\n\
         \x20   let ghost w0 = w.written();\n\
         \x20   proof {{\n\
         \x20       lemma_restrict_wf_val(flist_wf({ewf}), flist_ok({lb}, {ub}), s);\n\
         \x20       lemma_flist_wf_val({ewf}, s);\n\
         \x20       lemma_flist_enc_val({eenc}, s);\n\
         \x20       assert(s.skip(0) =~= s);\n\
         \x20   }}\n\
         \x20   let n = l.len();\n\
         \x20   let mut off: usize = 0;\n\
         \x20   while n - off >= 16384\n\
         \x20       invariant\n\
         \x20           w.wf(), w.buf@.len() == old(w).buf@.len(),\n\
         \x20           off <= n, n == l@.len(), s == {lo}, s.len() == n,\n\
         \x20           forall|i: int| 0 <= i < s.len() ==> #[trigger] {ewf}(s[i]),\n\
         \x20           w.written() + flist_enc_rec(s.skip(off as int), {eenc}) =~= w0 + flist_enc_rec(s, {eenc}),\n\
         \x20       decreases n - off,\n\
         \x20   {{\n\
         \x20       let left = n - off;\n\
         \x20       let m: usize = if left / 16384 >= 4 {{ 4 }} else {{ left / 16384 }};\n\
         \x20       proof {{\n\
         \x20           lemma_flist_enc_step(s, {eenc}, off as nat, m as nat);\n\
         \x20           lemma_lh_wf_iff(LenHead::Frag(m as u64));\n\
         \x20       }}\n\
         \x20       let ghost before = w.written();\n\
         \x20       if !w.write_lh(LenHead::Frag(m as u64)) {{ return false; }}\n\
         \x20       if !{rn}_frag_enc(w, l, off, m * 16384) {{ return false; }}\n\
         \x20       proof {{\n\
         \x20           lemma_flist_enc_loop_step(before, w.written(), w0, s, {eenc}, off as nat, m as nat);\n\
         \x20       }}\n\
         \x20       off = off + m * 16384;\n\
         \x20   }}\n\
         \x20   proof {{\n\
         \x20       lemma_flist_enc_last(s, {eenc}, off as nat);\n\
         \x20       lemma_lh_wf_iff(LenHead::Final((n - off) as u64));\n\
         \x20   }}\n\
         \x20   let ghost before = w.written();\n\
         \x20   if !w.write_lh(LenHead::Final((n - off) as u64)) {{ return false; }}\n\
         \x20   if !{rn}_frag_enc(w, l, off, n - off) {{ return false; }}\n\
         \x20   proof {{\n\
         \x20       lemma_flist_enc_loop_last(before, w.written(), w0, s, {eenc}, off as nat);\n\
         \x20   }}\n\
         \x20   true\n\
         }}\n\n",
        xfact = if eplain { String::new() } else {
            format!("\x20       proof {{ assert({xvr} == {lo}[j_ as int]); }}\n")
        }
    ));

    let jbody = match kind {
        ListKind::Bits if fixed => "    jer_bits_fixed(v, o);\n".to_string(),
        ListKind::Bits => "    jer_bits_var(v, o);\n".to_string(),
        ListKind::Octets => "    jer_octets(v, o);\n".to_string(),
        ListKind::Chars(_) => "    jer_chars(v, o);\n".to_string(),
        ListKind::Of => format!(
            "    o.push('[');\n\
             \x20   for (i, x) in v.iter().enumerate() {{\n\
             \x20       if i > 0 {{ o.push(','); }}\n\
             \x20       {};\n\
             \x20   }}\n\
             \x20   o.push(']');\n",
            elem.jer.replace("{V}", "x").replace("{O}", "o")
        ),
    };
    s.push_str(&jer_fn(&rn, &jbody));
    s.push_str(&arb_fn(
        &rn,
        &format!(
            "    let n = g.len({lb}, {ub});\n    (0..n).map(|_| {}).collect()\n",
            elem.arb.replace("{G}", "g")
        ),
    ));
    (
        s,
        Compiled {
            jer: format!("{rn}_jer({{V}}, {{O}})"),
            arb: format!("{rn}_arb({{G}})"),
            owner: None,
            rust_ty: format!("Vec<{ety}>"),
            spec_ty: Some(format!("Seq<{sty}>")),
            view: Some(if eplain { "{V}@".into() } else { format!("{rn}_lview({{V}}@)") }),
            fmt: rn.clone(),
            proof_call: format!("{rn}_is_format();"),
            decode: format!("{rn}_decode({{R}})"),
            encode: format!("{rn}_encode({{W}}, {{V}})"),
            preamble: vec![],
        },
    )
}

/// `INTEGER (c)`: a constrained whole number whose range holds one value,
/// which X.691 13.2.1 encodes in no bits at all. `unit` over `i64`.
fn gen_int_const(name: &str, v: &Num, values: &HashMap<String, i64>) -> Result<(String, Compiled), Pending> {
    let Some(c) = lit(v, values) else {
        return Err(Pending::Unsupported("INTEGER bound is an unknown value reference".into()));
    };
    let rn = rustify(name);
    let s = format!(
        "// ---------------------------------------------------------------- {name}\n\
         pub open spec fn {rn}_wf() -> Wf<i64> {{ unit_wf({c}i64) }}\n\
         pub open spec fn {rn}_enc() -> Enc<i64> {{ unit_enc() }}\n\
         pub open spec fn {rn}_dec() -> Dec<i64> {{ unit_dec({c}i64) }}\n\n\
         pub proof fn {rn}_is_format()\n\
         \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
         {{\n    lemma_unit_format({c}i64);\n}}\n\n\
         pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<(i64, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v_, f_)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<(i64, nat, Flg)>((v_, (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n\
         {{\n\
         \x20   proof {{ lemma_unit_dec_val({c}i64, old(r).rem()); }}\n\
         \x20   Some(({c}i64, Flg::SameVer))\n}}\n\n\
         pub fn {rn}_encode(w: &mut BitWriter, v: i64) -> (ok: bool)\n\
         \x20   requires old(w).wf(),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {enc},\n\
         {{\n\
         \x20   proof {{ lemma_unit_enc_val({uarg}); assert(old(w).written() + {enc} =~= old(w).written()); }}\n\
         \x20   true\n}}\n\n",
        enc = ea(&format!("{rn}_enc()"), OLD_POS, "v"),
        uarg = if aper() { "old(w).pos as nat, v" } else { "v" },
    );
    Ok((s, Compiled {
        owner: None,
        rust_ty: "i64".into(),
        spec_ty: None,
        view: None,
        fmt: rn.clone(),
        proof_call: format!("{rn}_is_format();"),
        decode: format!("{rn}_decode({{R}})"),
        encode: format!("{rn}_encode({{W}}, {{V}})"),
        preamble: vec![],
        jer: "jer_int(*{V}, {O})".into(),
        arb: format!("{c}i64"),
    }))
}

/// `OCTET STRING (CONTAINING X)` under `--containing decode`: an `X`, whose
/// complete encoding (X.691 11.1: padded to whole octets, and one octet if
/// empty) is the value of an unconstrained OCTET STRING. That is exactly an
/// open type (11.2), so the format is `open(X)` and the code the one an
/// extension addition gets, without the OPTIONAL around it. The value is the
/// `X` itself, under an alias.
fn gen_contains(name: &str, x: &Compiled) -> (String, Compiled) {
    let rn = rustify(name);
    let (xwf, xenc, xdec) = (wf_of(x), enc_of(x), dec_of(x));
    let prim = matches!(x.rust_ty.as_str(), "bool" | "u8" | "u16" | "u32" | "i64" | "Null");
    let rty = &x.rust_ty;
    let sty = x.sty();
    let vparam = if prim { rty.clone() } else { format!("&{rty}") };
    let vv = x.view_of("v");
    let vm = if prim { x.view_of("v") } else { x.view_of("(*v)") };
    let xdecode = x.decode.replace("{R}", "r2");
    let xencode = x.encode.replace("{W}", "sc").replace("{V}", "v");
    let mut pre = String::new();
    let mut pre_proof = String::new();
    for p in &x.preamble {
        pre.push_str(&format!("    proof {{ {p} }}\n"));
        pre_proof.push_str(&format!("    {p}\n"));
    }
    let xproof = &x.proof_call;
    let oref = if aper() { "_ref" } else { "" };
    let text = format!(
        "// ---------------------------------------------------------------- {name}
pub type {rn} = {rty};

// opaque: `X` is typically a whole message (`RRCReconfiguration`), and a
// type holding this one must not unfold into it
#[verifier::opaque]
pub open spec fn {rn}_wf() -> Wf<{sty}> {{ {xwf} }}
#[verifier::opaque]
pub open spec fn {rn}_enc() -> Enc<{sty}> {{ open_enc({xenc}) }}
#[verifier::opaque]
pub open spec fn {rn}_dec() -> Dec<{sty}> {{ open_dec({xdec}) }}

pub proof fn {rn}_is_format()
    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),
{{
    reveal({rn}_wf); reveal({rn}_enc); reveal({rn}_dec);
{pre_proof}    {xproof}
    lemma_open_format({xwf}, {xenc}, {xdec});
}}

pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rty}, Flg)>)
    requires old(r).wf(),
    ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,
        match res {{
            Some((v, f)) => {rn}_dec()(old(r).rem())
                == Some::<({sty}, nat, Flg)>(({vv}, (final(r).pos - old(r).pos) as nat, f)),
            None => {rn}_dec()(old(r).rem()).is_none(),
        }},
{{
{pre}    proof {{ reveal({rn}_dec); }}
    let ghost start = r.rem();
    let ghost p0 = r.pos;
    let content = match r.read_frag{oref}() {{
        Some(cb) => cb,
        None => {{
            proof {{ lemma_open_dec_none_len({xdec}, start); }}
            r.fail(\"CONTAINING: length\");
            return None;
        }}
    }};
    let ghost k = (r.pos - p0) as nat;
    let ghost cbits = bits_of(content@);
    let mut r2 = BitReader::new(content.as_slice());
    let r2 = &mut r2;
{at0}    let (v, f) = match {xdecode} {{
        Some(vf) => vf,
        None => {{
            proof {{ lemma_open_dec_none_content({xdec}, start, cbits, k); }}
            r.adopt(r2, content.len());
            return None;
        }}
    }};
    let ghost k2 = r2.pos as nat;
    if !ot_octets_eq(r2.pos, content.len()) || !r2.check_zero_tail() {{
        proof {{ lemma_open_dec_none_pad({xdec}, start, cbits, k); }}
        r.fail(\"CONTAINING: not the complete encoding of one value\");
        return None;
    }}
    proof {{
        assert(cbits.len() / 8 == content@.len()) by (nonlinear_arith)
            requires cbits.len() == 8 * content@.len();
        assert(cbits.skip(k2 as int) =~= zeros((cbits.len() - k2) as nat));
        lemma_open_dec_some({xdec}, start, cbits, k, {vv}, k2, f);
    }}
    Some((v, f))
}}

pub fn {rn}_encode(w: &mut BitWriter, v: {vparam}) -> (ok: bool)
    requires old(w).wf(), {rn}_wf()({vm}),
    ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),
        ok ==> final(w).written() =~= old(w).written() + {cenc},
{{
{pre}    proof {{ reveal({rn}_wf); reveal({rn}_enc); }}
    // the content is part of the output, so the output's own buffer is
    // always large enough to measure it in
    let mut sc_ = w.scratch();
    let sc = &mut sc_;
    if !{xencode} {{ return false; }}
    proof {{ lemma_ot_body_shape({xenc}, {vm}); }}
    if !sc.pad_open() {{ return false; }}
    proof {{ assert(bits_of(sc.buf@).take(sc.pos as int) =~= ot_body({xenc0}, {vm})); }}
    let ok_ = w.write_{a}open(sc.buf.as_slice(), sc.pos, Ghost({xenc}), Ghost({vm}));
    w.give_back(sc_);
    ok_
}}

",
        at0 = if aper() { "    proof { assert(r2.at() == (0nat, cbits)); }\n" } else { "" },
        cenc = ea(&format!("{rn}_enc()"), OLD_POS, &vm),
        xenc0 = if aper() { format!("at0_enc({xenc})") } else { xenc.clone() },
        a = if aper() { "a" } else { "" },
    );
    let jer = x.jer.clone();
    let c = Compiled {
        fmt: rn.clone(),
        proof_call: format!("{rn}_is_format();"),
        decode: format!("{rn}_decode({{R}})"),
        encode: format!("{rn}_encode({{W}}, {{V}})"),
        preamble: vec![],
        // X.697 25.4: `{"containing": <the value's JER>}`
        jer: format!("{{ {O}.push_str(\"{{\\\"containing\\\":\"); {jer}; {O}.push('}}'); }}", O = "{O}"),
        ..x.clone()
    };
    (text, c)
}

/// An OCTET STRING with no size constraint: a general length determinant in
/// octets, fragmenting at 16K (11.9.3.8.2 a), then the octets. That is exactly
/// the `frag` format an open type already rides on, so the spec value is its
/// bit sequence and the exec value the `Vec<u8>`, with `bits_of` between.
///
/// `OCTET STRING (CONTAINING X)` arrives here too -- the parser keeps only
/// SIZE constraints -- and is treated as raw octets, as VUPER does. Decoding
/// the contents as an `X` is a separate step, not taken yet.
fn gen_octets_unsized(name: &str) -> (String, Compiled) {
    let rn = rustify(name);
    let s = format!(
        "// ---------------------------------------------------------------- {name}\n\
         pub type {rn} = Vec<u8>;\n\n\
         pub open spec fn {rn}_wf() -> Wf<Seq<bool>> {{ frag_wf() }}\n\
         pub open spec fn {rn}_enc() -> Enc<Seq<bool>> {{ frag_enc() }}\n\
         pub open spec fn {rn}_dec() -> Dec<Seq<bool>> {{ frag_dec() }}\n\n\
         pub proof fn {rn}_is_format()\n\
         \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
         {{\n    lemma_frag_format();\n}}\n\n\
         pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v_, f_)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<(Seq<bool>, nat, Flg)>((bits_of(v_@), (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n\
         {{\n\
         \x20   let o_ = r.read_{a}frag();\n\
         \x20   r.same(o_, \"OCTET STRING length\")\n}}\n\n\
         pub fn {rn}_encode(w: &mut BitWriter, l: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()(bits_of(l@)),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {enc},\n\
         {{\n\
         \x20   if l.len() > usize::MAX / 8 {{ return false; }}\n\
         \x20   proof {{\n\
         {reveal}\
         \x20       assert(bits_of(l@).skip(0).take((8 * l.len()) as int) =~= bits_of(l@));\n\
         \x20   }}\n\
         \x20   w.write_{a}frag(l.as_slice(), 0, 8 * l.len())\n}}\n\n",
        a = if aper() { "a" } else { "" },
        enc = ea(&format!("{rn}_enc()"), OLD_POS, "bits_of(l@)"),
        // `frag_enc` is UPER's opaque combinator; APER's is not opaque
        reveal = if aper() { "" } else { "\x20       reveal(frag_enc);\n" },
    );
    let s = s + &jer_fn(&rn, "    jer_octets(v, o);\n")
        + &arb_fn(&rn, "    let n = g.len(0, 64);\n    (0..n).map(|_| g.bits(8) as u8).collect()\n");
    (s, Compiled {
        jer: format!("{rn}_jer({{V}}, {{O}})"),
        arb: format!("{rn}_arb({{G}})"),
        owner: None,
        rust_ty: "Vec<u8>".into(),
        spec_ty: Some("Seq<bool>".into()),
        view: Some("bits_of({V}@)".into()),
        fmt: rn.clone(),
        proof_call: format!("{rn}_is_format();"),
        decode: format!("{rn}_decode({{R}})"),
        encode: format!("{rn}_encode({{W}}, {{V}})"),
        preamble: vec![],
    })
}

/// CHOICE: an index over the alternatives, then the chosen one.
///
/// No new combinator is needed. The index is a restricted `uint`; each
/// alternative is the inner format `map`ped into its variant of the generated
/// enum, so all the branches share one payload type; and `dep` makes the
/// payload depend on the index. The obligation that the index agrees with the
/// variant falls out structurally, the same way the SEQUENCE presence bitmap
/// does.
/// X.697 31.3: a CHOICE is an object with exactly one member, named by the
/// chosen alternative's identifier. `alts` pairs each ASN.1 identifier with
/// its Rust variant and component.
fn jer_choice(rn: &str, alts: &[(String, String, Compiled)], extra_arms: &str) -> String {
    let mut body = String::from("    o.push('{');\n    let mut first = true;\n    match v {\n");
    for (asn, an, c) in alts {
        body.push_str(&format!(
            "        {rn}::{an}(x) => {{ jer_member(\"{asn}\", &mut first, o); {}; }}\n",
            c.jer.replace("{V}", "x").replace("{O}", "o")
        ));
    }
    body.push_str(extra_arms);
    body.push_str("    }\n    o.push('}');\n");
    jer_fn(rn, &body)
}

/// One of the alternatives the schema has, never an unknown one.
fn arb_choice(rn: &str, alts: &[(String, String, Compiled)]) -> String {
    let mut body = format!("    match g.pick({}) {{\n", alts.len());
    for (i, (_, an, c)) in alts.iter().enumerate() {
        let arm = if i + 1 == alts.len() { "_".to_string() } else { i.to_string() };
        body.push_str(&format!("        {arm} => {rn}::{an}({}),\n", c.arb.replace("{G}", "g")));
    }
    body.push_str("    }\n");
    arb_fn(rn, &body)
}

fn gen_choice(
    name: &str,
    alts: &[(String, Type)],
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    if alts.is_empty() {
        return Err(Pending::Unsupported("CHOICE with no alternatives".into()));
    }
    let rn = rustify(name);
    let mut parts: Vec<(String, Compiled)> = Vec::new();
    for (n, t) in alts {
        let c = resolve(t, env, values)?;
        parts.push((rustify(n), c));
    }
    let n = parts.len();
    let (w, u, ulen) = match aper_index(n as u64) {
        Some(x) => x,
        None => return Err(Pending::Unsupported("CHOICE has too many alternatives".into())),
    };
    let ulen = ulen.replace("{S}", "start");
    let max = (n - 1) as u64;
    let single = n == 1;

    let mut s = String::new();
    s.push_str(&format!(
        "// ---------------------------------------------------------------- {name}\n"
    ));
    // An alternative carrying a list makes the whole enum non-`Copy`, and the
    // format is then stated over a spec companion `{rn}_S`, exactly as for a
    // SEQUENCE: a `Vec` to run, a `Seq` to reason about.
    let needs_view = parts.iter().any(|(_, c)| !c.plain());
    let sname = if needs_view { format!("{rn}_S") } else { rn.clone() };
    let derives = if needs_view {
        "#[derive(PartialEq, Eq, Debug)]"
    } else {
        "#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]"
    };
    s.push_str(&format!("{derives}\npub enum {rn} {{\n"));
    for (an, c) in &parts {
        s.push_str(&format!("    {an}({}),\n", c.rust_ty));
    }
    s.push_str("}\n\n");
    if needs_view {
        s.push_str(&format!("pub enum {sname} {{\n"));
        for (an, c) in &parts {
            s.push_str(&format!("    {an}({}),\n", c.sty()));
        }
        s.push_str("}\n\n");
        s.push_str(&format!("pub open spec fn {rn}_view(v: {rn}) -> {sname} {{\n    match v {{\n"));
        for (an, c) in &parts {
            s.push_str(&format!("        {rn}::{an}(x) => {sname}::{an}({}),\n", c.view_of("x")));
        }
        s.push_str("    }\n}\n\n");
    } else {
        s.push_str(&format!("pub open spec fn {rn}_view(v: {rn}) -> {rn} {{ v }}\n\n"));
    }

    // tag
    s.push_str(&format!("pub open spec fn {rn}_tag(v: {sname}) -> u64 {{\n    match v {{\n"));
    for (i, (an, _)) in parts.iter().enumerate() {
        s.push_str(&format!("        {sname}::{an}(_) => {i},\n"));
    }
    s.push_str("    }\n}\n\n");
    s.push_str(&format!(
        "pub fn {rn}_tag_exec(v: &{rn}) -> (i: u64)\n    ensures i == {rn}_tag({rn}_view(*v)),\n{{\n    match v {{\n"
    ));
    for (i, (an, _)) in parts.iter().enumerate() {
        s.push_str(&format!("        {rn}::{an}(_) => {i},\n"));
    }
    s.push_str("    }\n}\n\n");

    // injection / projection per alternative
    for (i, (an, c)) in parts.iter().enumerate() {
        let ty = c.sty();
        let catch_all = if n == 1 { "" } else { ", _ => vstd::pervasive::arbitrary()" };
        s.push_str(&format!(
            "pub open spec fn {rn}_inj{i}() -> spec_fn({ty}) -> {sname} {{ |x: {ty}| {sname}::{an}(x) }}\n\
             pub open spec fn {rn}_prj{i}() -> spec_fn({sname}) -> {ty} {{\n\
             \x20   |v: {sname}| match v {{ {sname}::{an}(x) => x{catch_all} }}\n}}\n"
        ));
    }
    s.push('\n');

    // index format
    if single {
        s.push_str(&format!(
            "pub open spec fn {rn}_idx_wf() -> Wf<u64> {{ unit_wf(0u64) }}\n\
             pub open spec fn {rn}_idx_enc() -> Enc<u64> {{ unit_enc() }}\n\
             pub open spec fn {rn}_idx_dec() -> Dec<u64> {{ unit_dec(0u64) }}\n\n"
        ));
    } else {
        s.push_str(&format!(
            "pub open spec fn {rn}_idx_ok() -> spec_fn(u64) -> bool {{ |i: u64| i <= {max} }}\n\
             pub open spec fn {rn}_idx_wf() -> Wf<u64> {{ restrict_wf({u}_wf({w}), {rn}_idx_ok()) }}\n\
             pub open spec fn {rn}_idx_enc() -> Enc<u64> {{ {u}_enc({w}) }}\n\
             pub open spec fn {rn}_idx_dec() -> Dec<u64> {{ restrict_dec({u}_dec({w}), {rn}_idx_ok()) }}\n\n"
        ));
    }

    // the alternative chosen by the index
    let chain = |kind: &str| -> String {
        let mut out = String::new();
        for i in 0..n - 1 {
            out.push_str(&format!(
                "if i == {i} {{ map_{kind}({}, {}) }} else {{ ",
                match kind {
                    "wf" => format!("{}, {rn}_inj{i}(), {rn}_prj{i}()", wf_of(&parts[i].1)),
                    "enc" => format!("{}, {rn}_prj{i}()", enc_of(&parts[i].1)),
                    _ => format!("{}, {rn}_inj{i}()", dec_of(&parts[i].1)),
                },
                ""
            ));
        }
        let last = n - 1;
        out.push_str(&format!(
            "map_{kind}({})",
            match kind {
                "wf" => format!("{}, {rn}_inj{last}(), {rn}_prj{last}()", wf_of(&parts[last].1)),
                "enc" => format!("{}, {rn}_prj{last}()", enc_of(&parts[last].1)),
                _ => format!("{}, {rn}_inj{last}()", dec_of(&parts[last].1)),
            }
        ));
        for _ in 0..n - 1 {
            out.push_str(" }");
        }
        out
    };
    s.push_str(&format!(
        "pub open spec fn {rn}_alt_wf() -> spec_fn(u64) -> Wf<{sname}> {{ |i: u64| {} }}\n\
         pub open spec fn {rn}_alt_enc() -> spec_fn(u64) -> Enc<{sname}> {{ |i: u64| {} }}\n\
         pub open spec fn {rn}_alt_dec() -> spec_fn(u64) -> Dec<{sname}> {{ |i: u64| {} }}\n\n",
        chain("wf"),
        chain("enc"),
        chain("dec")
    ));

    s.push_str(&format!(
        "pub open spec fn {rn}_to(t: (u64, {sname})) -> {sname} {{ t.1 }}\n\
         pub open spec fn {rn}_from(v: {sname}) -> (u64, {sname}) {{ ({rn}_tag(v), v) }}\n\
         pub open spec fn {rn}_to_f() -> spec_fn((u64, {sname})) -> {sname} {{ |t: (u64, {sname})| {rn}_to(t) }}\n\
         pub open spec fn {rn}_from_f() -> spec_fn({sname}) -> (u64, {sname}) {{ |v: {sname}| {rn}_from(v) }}\n\
         pub open spec fn {rn}_full_wf() -> Wf<(u64, {sname})> {{ dep_wf({rn}_idx_wf(), {rn}_alt_wf()) }}\n\
         pub open spec fn {rn}_full_enc() -> Enc<(u64, {sname})> {{ dep_enc({rn}_idx_enc(), {rn}_alt_enc()) }}\n\
         pub open spec fn {rn}_full_dec() -> Dec<(u64, {sname})> {{ dep_dec({rn}_idx_dec(), {rn}_alt_dec()) }}\n\
         pub open spec fn {rn}_wf() -> Wf<{sname}> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_enc() -> Enc<{sname}> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_dec() -> Dec<{sname}> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n"
    ));

    // ------------------------------------------------------------- the proof
    s.push_str(&format!(
        "pub proof fn {rn}_is_format()\n    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n{{\n"
    ));
    if single {
        s.push_str(&format!("    lemma_unit_format(0u64);\n"));
    } else {
        s.push_str(&format!(
            "    {}\n    lemma_{u}_format({w});\n\
             \x20   lemma_restrict_format({u}_wf({w}), {u}_enc({w}), {u}_dec({w}), {rn}_idx_ok());\n",
            p2_fact(w)
        ));
    }
    let mut seen = std::collections::HashSet::new();
    for (_, c) in &parts {
        if seen.insert(c.proof_call.clone()) {
            s.push_str(&format!("    {}\n", c.proof_call));
        }
    }
    for (i, (_, c)) in parts.iter().enumerate() {
        s.push_str(&format!(
            "    assert forall|x: {}| {}(x) implies\n\
             \x20       #[trigger] {rn}_prj{i}()({rn}_inj{i}()(x)) == x by {{ }}\n\
             \x20   lemma_map_format({}, {}, {}, {rn}_inj{i}(), {rn}_prj{i}());\n",
            c.sty(),
            wf_of(c),
            wf_of(c),
            enc_of(c),
            dec_of(c)
        ));
    }
    s.push_str(&format!(
        "    assert forall|i: u64| {rn}_idx_wf()(i) implies\n\
         \x20       is_format(#[trigger] {rn}_alt_wf()(i), {rn}_alt_enc()(i), {rn}_alt_dec()(i))\n\
         \x20   by {{ }}\n\
         \x20   lemma_dep_format({rn}_idx_wf(), {rn}_idx_enc(), {rn}_idx_dec(),\n\
         \x20                    {rn}_alt_wf(), {rn}_alt_enc(), {rn}_alt_dec());\n\
         \x20   assert forall|t: (u64, {sname})| {rn}_full_wf()(t) implies\n\
         \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t by {{ }}\n\
         \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(),\n\
         \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n"
    ));

    s.push_str(&format!(
        "pub proof fn {rn}_alt_bounds(v: {sname})\n\
         \x20   requires {rn}_wf()(v),\n\
         \x20   ensures {rn}_idx_wf()({rn}_tag(v)), {rn}_alt_wf()({rn}_tag(v))(v),\n\
         {{\n    assert({rn}_from_f()({rn}_to_f()({rn}_from(v))) == {rn}_from(v));\n}}\n\n"
    ));

    // ------------------------------------------------------------- decode
    let preamble = {
        let mut out = String::new();
        let mut seen = std::collections::HashSet::new();
        for (_, c) in &parts {
            for p in &c.preamble {
                if seen.insert(p.clone()) {
                    out.push_str(&format!("    proof {{ {p} }}\n"));
                }
            }
        }
        out
    };
    s.push_str(&format!(
        "pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v_, f_)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<({sname}, nat, Flg)>(({rn}_view(v_), (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n{{\n{preamble}\
         \x20   let ghost start = old(r).rem();\n\
         \x20   let ghost p0 = old(r).pos;\n"
    ));
    if single {
        s.push_str(&format!(
            "    let i_: u64 = 0;\n\
             \x20   proof {{ lemma_unit_dec_val(0u64, start); }}\n"
        ));
    } else {
        s.push_str(&format!(
            "    proof {{ {} }}\n\
             \x20   let i_ = match r.read_{u}({w}) {{\n\
             \x20       Some(v_) => v_,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               lemma_restrict_dec_none({u}_dec({w}), {rn}_idx_ok(), start);\n\
             \x20               lemma_dep_dec_none_fst({rn}_idx_dec(), {rn}_alt_dec(), start);\n\
             \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
             \x20           }}\n\
             \x20           {{ r.fail(\"CHOICE index (0..{max})\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   if i_ > {max} {{\n\
             \x20       proof {{\n\
             \x20           lemma_restrict_dec_none({u}_dec({w}), {rn}_idx_ok(), start);\n\
             \x20           lemma_dep_dec_none_fst({rn}_idx_dec(), {rn}_alt_dec(), start);\n\
             \x20           lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
             \x20       }}\n\
             \x20       {{ r.fail(\"CHOICE index (0..{max})\"); return None; }}\n\
             \x20   }}\n\
             \x20   proof {{\n\
             \x20       lemma_restrict_dec_some({u}_dec({w}), {rn}_idx_ok(), start, i_, {ulen},\n\
             \x20                               Flg::SameVer);\n\
             \x20       lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat);\n\
             \x20   }}\n",
            p2_fact(w)
        ));
    }
    // One runner per alternative, stated against `{rn}_alt_dec()` at the index
    // it was given, so the dispatcher never unfolds the alternatives chain
    // (see `choice_ext.rs`, where a 37-alternative CHOICE made this O(n^2)).
    s.push_str(&format!(
        "    let ghost kidx = (r.pos - p0) as nat;\n\
         \x20   let ghost p1 = r.pos;\n\
         \x20   proof {{ assert(r.rem() {} {}); }}\n\
         \x20   let got = {};\n\
         \x20   match got {{\n\
         \x20       Some((v_, f_)) => {{\n\
         \x20           proof {{\n\
         \x20               lemma_dep_dec_some({rn}_idx_dec(), {rn}_alt_dec(), start, i_, kidx, Flg::SameVer,\n\
         \x20                                  {rn}_view(v_), (r.pos - p1) as nat, f_);\n\
         \x20               lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, (i_, {rn}_view(v_)),\n\
         \x20                                  (r.pos - p0) as nat, f_);\n\
         \x20           }}\n\
         \x20           Some((v_, f_))\n\
         \x20       }}\n\
         \x20       None => {{\n\
         \x20           proof {{\n\
         \x20               lemma_dep_dec_none_snd({rn}_idx_dec(), {rn}_alt_dec(), start, i_, kidx, Flg::SameVer);\n\
         \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           None\n\
         \x20       }}\n\
         \x20   }}\n}}\n\n",
        if aper() { "==" } else { "=~=" },
        skip_in("start", "kidx"),
        (0..n).map(|i| {
            if n == 1 { format!("{rn}_alt0_run(r, i_)") }
            else if i == 0 { format!("if i_ == 0 {{ {rn}_alt0_run(r, i_) }}") }
            else if i + 1 == n { format!(" else {{ {rn}_alt{i}_run(r, i_) }}") }
            else { format!(" else if i_ == {i} {{ {rn}_alt{i}_run(r, i_) }}") }
        }).collect::<String>()
    ));
    for (i, (an, c)) in parts.iter().enumerate() {
        let dc = dec_of(c);
        let asn = &alts[i].0;
        s.push_str(&format!(
            "pub fn {rn}_alt{i}_run(r: &mut BitReader, i_: u64) -> (res: Option<({rn}, Flg)>)\n\
             \x20   requires old(r).wf(), i_ == {i},\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v_, f_)) => {rn}_alt_dec()(i_)(old(r).rem())\n\
             \x20               == Some::<({sname}, nat, Flg)>(({rn}_view(v_), (final(r).pos - old(r).pos) as nat, f_)),\n\
             \x20           None => {rn}_alt_dec()(i_)(old(r).rem()).is_none(),\n\
             \x20       }},\n{{\n{preamble}\
             \x20   let ghost start = old(r).rem();\n\
             \x20   let ghost p0 = old(r).pos;\n\
             \x20   let (v_, f_) = match {} {{\n\
             \x20       Some(xf_) => xf_,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_map_dec_none({dc}, {rn}_inj{i}(), start); }}\n\
             \x20           {{ r.fail_in(\"{asn}\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_map_dec_some({dc}, {rn}_inj{i}(), start, {}, (r.pos - p0) as nat, f_); }}\n\
             \x20   Some(({rn}::{an}(v_), f_))\n}}\n\n",
            c.decode.replace("{R}", "r"),
            c.view_of("v_"),
        ));
    }

    // ------------------------------------------------------------- encode
    s.push_str(&format!(
        "pub fn {rn}_encode(w: &mut BitWriter, v: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({rn}_view(*v)),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {},\n\
         {{\n{preamble}\
         \x20   proof {{ {rn}_alt_bounds({rn}_view(*v)); }}\n",
        ea(&format!("{rn}_enc()"), OLD_POS, &format!("{rn}_view(*v)"))
    ));
    if !single {
        s.push_str(&format!(
            "    proof {{ {} }}\n\
             \x20   let i_ = {rn}_tag_exec(v);\n\
             \x20   if !w.write_{u}({w}, i_) {{ return false; }}\n",
            p2_fact(w)
        ));
    }
    s.push_str("    match v {\n");
    for (i, (an, c)) in parts.iter().enumerate() {
        let inner = c
            .encode
            .replace("{W}", "w")
            .replace("{V}", if c.rust_ty == "bool" || c.rust_ty == "i64" || c.rust_ty == "Null" { "*x_" } else { "x_" });
        s.push_str(&format!("        {rn}::{an}(x_) => {inner},\n"));
        let _ = i;
    }
    s.push_str("    }\n}\n\n");

    let jalts: Vec<(String, String, Compiled)> = alts
        .iter()
        .zip(parts.iter())
        .map(|((asn, _), (an, c))| (asn.clone(), an.clone(), c.clone()))
        .collect();
    s.push_str(&jer_choice(&rn, &jalts, ""));
    s.push_str(&arb_choice(&rn, &jalts));
    Ok((
        s,
        Compiled {
            jer: format!("{rn}_jer({{V}}, {{O}})"),
            arb: format!("{rn}_arb({{G}})"),
            owner: None,
            spec_ty: if needs_view { Some(sname.clone()) } else { None },
            view: if needs_view { Some(format!("{rn}_view({{V}})")) } else { None },
            rust_ty: rn.clone(),
            fmt: rn.clone(),
            proof_call: format!("{rn}_is_format();"),
            decode: format!("{rn}_decode({{R}})"),
            encode: format!("{rn}_encode({{W}}, {{V}})"),
            preamble: vec![],
        },
    ))
}
