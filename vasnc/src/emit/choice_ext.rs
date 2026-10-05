//! Extensible CHOICE (X.691 23).
//!
//! ```text
//! enc(v) = [0] + root_idx(i) + enc_i(v)          v a root alternative
//!        | [1] + nsnnwn(j)   + open(enc_j(v))    v an extension alternative
//!        | [1] + nsnnwn(k)   + frag(raw)         v = Unknown(k, raw)
//! ```
//!
//! No new combinator: it is `dep` on the extension bit, whose two branches
//! are each a `dep` on an index -- the root one exactly today's CHOICE, the
//! extension one a normally small non-negative whole number (11.6) choosing
//! an open type. Each branch is `map`ped into one enum, and the obligation
//! that the bit and the index agree with the variant falls out structurally,
//! as the CHOICE index already does.
//!
//! **Unknown alternatives.** A decoder meeting an extension index its schema
//! does not know keeps the index and the open type's raw content as
//! `Unknown(k, octets)`. That value is well formed and re-encodes to exactly
//! the bits it came from, so the decode is `SameVer` and a relay loses
//! nothing -- which is also what `is_format` forces: whatever a decoder
//! returns must be well formed (`weak_injective`), and a well-formed value's
//! encoding must decode back `SameVer` (`surjective`). VUPER does the same
//! (`ChoiceExt.v`, `unknown_ext`). Only an index above the schema's own
//! alternatives is `Unknown`; `Unknown(k, _)` with `k` naming a known
//! alternative is not well formed.
//!
//! **The index.** 11.6: `0` and six bits when the value is at most 63, else
//! `1` and a semi-constrained whole number: `vasn::uper::intx`'s `nsn`, in both
//! forms. (VUPER's `small_integer_format` has the short form only, and
//! rejects an index of 64 or more.)

use super::*;

pub(super) fn gen_choice_ext(
    name: &str,
    root_alts: &[(String, Type)],
    ext_alts: &[(String, Type)],
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    if root_alts.is_empty() {
        return Err(Pending::Unsupported("CHOICE with no root alternatives".into()));
    }
    let rn = rustify(name);
    let sn = format!("{rn}_S");
    let mut roots: Vec<(String, Compiled)> = Vec::new();
    for (n, t) in root_alts {
        roots.push((rustify(n), resolve(t, env, values)?));
    }
    let mut exts: Vec<(String, Compiled)> = Vec::new();
    for (n, t) in ext_alts {
        exts.push((rustify(n), resolve(t, env, values)?));
    }
    let n = roots.len();
    let m = exts.len();
    let (rw, u, ulen) = match super::aper_index(n as u64) {
        Some(x) => x,
        None => return Err(Pending::Unsupported("CHOICE has too many alternatives".into())),
    };
    let ulen = ulen.replace("{S}", "start");
    let rmax = (n - 1) as u64;
    let single = n == 1;

    let preamble = {
        let mut out = String::new();
        let mut seen = std::collections::HashSet::new();
        for (_, c) in roots.iter().chain(exts.iter()) {
            for p in &c.preamble {
                if seen.insert(p.clone()) {
                    out.push_str(&format!("    proof {{ {p} }}\n"));
                }
            }
        }
        out
    };
    let byref = |c: &Compiled| !(c.rust_ty == "bool" || c.rust_ty == "i64" || c.rust_ty == "Null");

    let mut s = String::new();
    s.push_str(&format!(
        "// ---------------------------------------------------------------- {name} (extensible)\n"
    ));

    // ------------------------------------------------------------ the types
    s.push_str(&format!("#[derive(PartialEq, Eq, Debug)]\npub enum {rn} {{\n"));
    for (an, c) in roots.iter().chain(exts.iter()) {
        s.push_str(&format!("    {an}({}),\n", c.rust_ty));
    }
    s.push_str(
        "    /// An extension alternative this schema does not know: its index,\n\
         \x20   /// and the open type's content as it came off the wire.\n\
         \x20   Unknown(u64, Vec<u8>),\n}\n\n",
    );
    s.push_str(&format!("pub enum {sn} {{\n"));
    for (an, c) in roots.iter().chain(exts.iter()) {
        s.push_str(&format!("    {an}({}),\n", c.sty()));
    }
    s.push_str("    Unknown(u64, Seq<bool>),\n}\n\n");
    s.push_str(&format!("pub open spec fn {rn}_view(v: {rn}) -> {sn} {{\n    match v {{\n"));
    for (an, c) in roots.iter().chain(exts.iter()) {
        s.push_str(&format!("        {rn}::{an}(x) => {sn}::{an}({}),\n", c.view_of("x")));
    }
    s.push_str(&format!("        {rn}::Unknown(k, b) => {sn}::Unknown(k, bits_of(b@)),\n    }}\n}}\n\n"));

    // ------------------------------------------- which half, and which index
    let spec_match = |fname: &str, ret: &str, arm: &dyn Fn(bool, usize, &str) -> String, unk: &str| -> String {
        let mut out = format!("pub open spec fn {rn}_{fname}(v: {sn}) -> {ret} {{\n    match v {{\n");
        for (i, (an, _)) in roots.iter().enumerate() {
            out.push_str(&format!("        {sn}::{an}(_) => {},\n", arm(false, i, an)));
        }
        for (j, (an, _)) in exts.iter().enumerate() {
            out.push_str(&format!("        {sn}::{an}(_) => {},\n", arm(true, j, an)));
        }
        out.push_str(&format!("        {sn}::Unknown(k, _) => {unk},\n    }}\n}}\n"));
        out
    };
    let exec_match = |fname: &str, ret: &str, arm: &dyn Fn(bool, usize, &str) -> String, unk: &str| -> String {
        let mut out = format!(
            "pub fn {rn}_{fname}_exec(v: &{rn}) -> (res: {ret})\n    ensures res == {rn}_{fname}({rn}_view(*v)),\n{{\n    match v {{\n"
        );
        for (i, (an, _)) in roots.iter().enumerate() {
            out.push_str(&format!("        {rn}::{an}(_) => {},\n", arm(false, i, an)));
        }
        for (j, (an, _)) in exts.iter().enumerate() {
            out.push_str(&format!("        {rn}::{an}(_) => {},\n", arm(true, j, an)));
        }
        out.push_str(&format!("        {rn}::Unknown(k, _) => {unk},\n    }}\n}}\n"));
        out
    };
    let isext = |e: bool, _: usize, _: &str| -> String { e.to_string() };
    let rtag = |e: bool, i: usize, _: &str| -> String { if e { "0".into() } else { i.to_string() } };
    let etag = |e: bool, j: usize, _: &str| -> String { if e { j.to_string() } else { "0".into() } };
    s.push_str(&spec_match("isext", "bool", &isext, "true"));
    s.push_str(&spec_match("rtag", "u64", &rtag, "0"));
    s.push_str(&spec_match("etag", "u64", &etag, "k"));
    s.push_str(&exec_match("isext", "bool", &isext, "true"));
    s.push_str(&exec_match("rtag", "u64", &rtag, "0"));
    s.push_str(&exec_match("etag", "u64", &etag, "*k"));
    s.push('\n');

    // ----------------------------------------------- injection / projection
    for (p, alts) in [("r", &roots), ("e", &exts)] {
        for (i, (an, c)) in alts.iter().enumerate() {
            let ty = c.sty();
            s.push_str(&format!(
                "pub open spec fn {rn}_{p}inj{i}() -> spec_fn({ty}) -> {sn} {{ |x: {ty}| {sn}::{an}(x) }}\n\
                 pub open spec fn {rn}_{p}prj{i}() -> spec_fn({sn}) -> {ty} {{\n\
                 \x20   |v: {sn}| match v {{ {sn}::{an}(x) => x, _ => vstd::pervasive::arbitrary() }}\n}}\n"
            ));
        }
    }
    s.push_str(&format!(
        "pub open spec fn {rn}_uinj(k: u64) -> spec_fn(Seq<bool>) -> {sn} {{ |c: Seq<bool>| {sn}::Unknown(k, c) }}\n\
         pub open spec fn {rn}_uprj() -> spec_fn({sn}) -> Seq<bool> {{\n\
         \x20   |v: {sn}| match v {{ {sn}::Unknown(_, c) => c, _ => vstd::pervasive::arbitrary() }}\n}}\n\n"
    ));

    // ------------------------------------------------------------ root half
    if single {
        s.push_str(&format!(
            "pub open spec fn {rn}_ridx_wf() -> Wf<u64> {{ unit_wf(0u64) }}\n\
             pub open spec fn {rn}_ridx_enc() -> Enc<u64> {{ unit_enc() }}\n\
             pub open spec fn {rn}_ridx_dec() -> Dec<u64> {{ unit_dec(0u64) }}\n\n"
        ));
    } else {
        s.push_str(&format!(
            "pub open spec fn {rn}_ridx_ok() -> spec_fn(u64) -> bool {{ |i: u64| i <= {rmax} }}\n\
             pub open spec fn {rn}_ridx_wf() -> Wf<u64> {{ restrict_wf({u}_wf({rw}), {rn}_ridx_ok()) }}\n\
             pub open spec fn {rn}_ridx_enc() -> Enc<u64> {{ {u}_enc({rw}) }}\n\
             pub open spec fn {rn}_ridx_dec() -> Dec<u64> {{ restrict_dec({u}_dec({rw}), {rn}_ridx_ok()) }}\n\n"
        ));
    }
    let rchain = |kind: &str| -> String {
        let one = |i: usize| -> String {
            let c = &roots[i].1;
            match kind {
                "wf" => format!("map_wf({}, {rn}_rinj{i}(), {rn}_rprj{i}())", wf_of(c)),
                "enc" => format!("map_enc({}, {rn}_rprj{i}())", enc_of(c)),
                _ => format!("map_dec({}, {rn}_rinj{i}())", dec_of(c)),
            }
        };
        let mut out = String::new();
        for i in 0..n - 1 {
            out.push_str(&format!("if i == {i} {{ {} }} else {{ ", one(i)));
        }
        out.push_str(&one(n - 1));
        for _ in 0..n - 1 {
            out.push_str(" }");
        }
        out
    };
    s.push_str(&format!(
        "pub open spec fn {rn}_ralt_wf() -> spec_fn(u64) -> Wf<{sn}> {{ |i: u64| {} }}\n\
         pub open spec fn {rn}_ralt_enc() -> spec_fn(u64) -> Enc<{sn}> {{ |i: u64| {} }}\n\
         pub open spec fn {rn}_ralt_dec() -> spec_fn(u64) -> Dec<{sn}> {{ |i: u64| {} }}\n\n",
        rchain("wf"), rchain("enc"), rchain("dec")
    ));

    // ------------------------------------------------------- extension half
    s.push_str(&format!(
        "pub open spec fn {rn}_eidx_ok() -> spec_fn(u64) -> bool {{ |k: u64| true }}\n\
         pub open spec fn {rn}_eidx_wf() -> Wf<u64> {{ restrict_wf(nsn_wf(), {rn}_eidx_ok()) }}\n\
         pub open spec fn {rn}_eidx_enc() -> Enc<u64> {{ nsn_enc() }}\n\
         pub open spec fn {rn}_eidx_dec() -> Dec<u64> {{ restrict_dec(nsn_dec(), {rn}_eidx_ok()) }}\n\n"
    ));
    let echain = |kind: &str| -> String {
        let one = |j: usize| -> String {
            let c = &exts[j].1;
            match kind {
                "wf" => format!("map_wf({}, {rn}_einj{j}(), {rn}_eprj{j}())", wf_of(c)),
                "enc" => format!("map_enc(open_enc({}), {rn}_eprj{j}())", enc_of(c)),
                _ => format!("map_dec(open_dec({}), {rn}_einj{j}())", dec_of(c)),
            }
        };
        let unk = match kind {
            "wf" => format!("map_wf(frag_wf(), {rn}_uinj(k), {rn}_uprj())"),
            "enc" => format!("map_enc(frag_enc(), {rn}_uprj())"),
            _ => format!("map_dec(frag_dec(), {rn}_uinj(k))"),
        };
        let mut out = String::new();
        for j in 0..m {
            out.push_str(&format!("if k == {j} {{ {} }} else {{ ", one(j)));
        }
        out.push_str(&unk);
        for _ in 0..m {
            out.push_str(" }");
        }
        out
    };
    s.push_str(&format!(
        "pub open spec fn {rn}_ealt_wf() -> spec_fn(u64) -> Wf<{sn}> {{ |k: u64| {} }}\n\
         pub open spec fn {rn}_ealt_enc() -> spec_fn(u64) -> Enc<{sn}> {{ |k: u64| {} }}\n\
         pub open spec fn {rn}_ealt_dec() -> spec_fn(u64) -> Dec<{sn}> {{ |k: u64| {} }}\n\n",
        echain("wf"), echain("enc"), echain("dec")
    ));

    // ------------------------------------------ each half as its own format
    for (h, idx, alt, tag) in [("root", "ridx", "ralt", "rtag"), ("ext", "eidx", "ealt", "etag")] {
        let p = &h[..1];
        s.push_str(&format!(
            "pub open spec fn {rn}_{p}to(t: (u64, {sn})) -> {sn} {{ t.1 }}\n\
             pub open spec fn {rn}_{p}from(v: {sn}) -> (u64, {sn}) {{ ({rn}_{tag}(v), v) }}\n\
             pub open spec fn {rn}_{p}to_f() -> spec_fn((u64, {sn})) -> {sn} {{ |t: (u64, {sn})| {rn}_{p}to(t) }}\n\
             pub open spec fn {rn}_{p}from_f() -> spec_fn({sn}) -> (u64, {sn}) {{ |v: {sn}| {rn}_{p}from(v) }}\n\
             pub open spec fn {rn}_{p}full_wf() -> Wf<(u64, {sn})> {{ dep_wf({rn}_{idx}_wf(), {rn}_{alt}_wf()) }}\n\
             pub open spec fn {rn}_{p}full_enc() -> Enc<(u64, {sn})> {{ dep_enc({rn}_{idx}_enc(), {rn}_{alt}_enc()) }}\n\
             pub open spec fn {rn}_{p}full_dec() -> Dec<(u64, {sn})> {{ dep_dec({rn}_{idx}_dec(), {rn}_{alt}_dec()) }}\n\
             pub open spec fn {rn}_{h}_wf() -> Wf<{sn}> {{ map_wf({rn}_{p}full_wf(), {rn}_{p}to_f(), {rn}_{p}from_f()) }}\n\
             pub open spec fn {rn}_{h}_enc() -> Enc<{sn}> {{ map_enc({rn}_{p}full_enc(), {rn}_{p}from_f()) }}\n\
             pub open spec fn {rn}_{h}_dec() -> Dec<{sn}> {{ map_dec({rn}_{p}full_dec(), {rn}_{p}to_f()) }}\n\n"
        ));
    }

    // ------------------------------------------------------------- the whole
    s.push_str(&format!(
        "pub open spec fn {rn}_fam_wf() -> spec_fn(bool) -> Wf<{sn}> {{ |e: bool| if e {{ {rn}_ext_wf() }} else {{ {rn}_root_wf() }} }}\n\
         pub open spec fn {rn}_fam_enc() -> spec_fn(bool) -> Enc<{sn}> {{ |e: bool| if e {{ {rn}_ext_enc() }} else {{ {rn}_root_enc() }} }}\n\
         pub open spec fn {rn}_fam_dec() -> spec_fn(bool) -> Dec<{sn}> {{ |e: bool| if e {{ {rn}_ext_dec() }} else {{ {rn}_root_dec() }} }}\n\
         pub open spec fn {rn}_to(t: (bool, {sn})) -> {sn} {{ t.1 }}\n\
         pub open spec fn {rn}_from(v: {sn}) -> (bool, {sn}) {{ ({rn}_isext(v), v) }}\n\
         pub open spec fn {rn}_to_f() -> spec_fn((bool, {sn})) -> {sn} {{ |t: (bool, {sn})| {rn}_to(t) }}\n\
         pub open spec fn {rn}_from_f() -> spec_fn({sn}) -> (bool, {sn}) {{ |v: {sn}| {rn}_from(v) }}\n\
         pub open spec fn {rn}_full_wf() -> Wf<(bool, {sn})> {{ dep_wf(bool_wf(), {rn}_fam_wf()) }}\n\
         pub open spec fn {rn}_full_enc() -> Enc<(bool, {sn})> {{ dep_enc(bool_enc(), {rn}_fam_enc()) }}\n\
         pub open spec fn {rn}_full_dec() -> Dec<(bool, {sn})> {{ dep_dec(bool_dec(), {rn}_fam_dec()) }}\n\
         pub open spec fn {rn}_wf() -> Wf<{sn}> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_enc() -> Enc<{sn}> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_dec() -> Dec<{sn}> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n"
    ));

    // ------------------------------------------------------------- proofs
    let mut seen = std::collections::HashSet::new();
    let mut calls = String::new();
    for (_, c) in roots.iter().chain(exts.iter()) {
        if seen.insert(c.proof_call.clone()) {
            calls.push_str(&format!("    {}\n", c.proof_call));
        }
    }
    // the root half
    s.push_str(&format!(
        "pub proof fn {rn}_root_is_format()\n    ensures is_format({rn}_root_wf(), {rn}_root_enc(), {rn}_root_dec()),\n{{\n"
    ));
    if single {
        s.push_str("    lemma_unit_format(0u64);\n");
    } else {
        s.push_str(&format!(
            "    {}\n    lemma_{u}_format({rw});\n\
             \x20   lemma_restrict_format({u}_wf({rw}), {u}_enc({rw}), {u}_dec({rw}), {rn}_ridx_ok());\n",
            p2_fact(rw)
        ));
    }
    s.push_str(&calls);
    for (i, (_, c)) in roots.iter().enumerate() {
        s.push_str(&format!(
            "    assert forall|x: {}| {}(x) implies\n\
             \x20       #[trigger] {rn}_rprj{i}()({rn}_rinj{i}()(x)) == x by {{ }}\n\
             \x20   lemma_map_format({}, {}, {}, {rn}_rinj{i}(), {rn}_rprj{i}());\n",
            c.sty(), wf_of(c), wf_of(c), enc_of(c), dec_of(c)
        ));
    }
    s.push_str(&format!(
        "    assert forall|i: u64| {rn}_ridx_wf()(i) implies\n\
         \x20       is_format(#[trigger] {rn}_ralt_wf()(i), {rn}_ralt_enc()(i), {rn}_ralt_dec()(i))\n\
         \x20   by {{ }}\n\
         \x20   lemma_dep_format({rn}_ridx_wf(), {rn}_ridx_enc(), {rn}_ridx_dec(),\n\
         \x20                    {rn}_ralt_wf(), {rn}_ralt_enc(), {rn}_ralt_dec());\n\
         \x20   assert forall|t: (u64, {sn})| {rn}_rfull_wf()(t) implies\n\
         \x20       #[trigger] {rn}_rfrom_f()({rn}_rto_f()(t)) == t by {{ }}\n\
         \x20   lemma_map_format({rn}_rfull_wf(), {rn}_rfull_enc(), {rn}_rfull_dec(),\n\
         \x20                    {rn}_rto_f(), {rn}_rfrom_f());\n}}\n\n"
    ));
    // the extension half
    s.push_str(&format!(
        "pub proof fn {rn}_ext_is_format()\n    ensures is_format({rn}_ext_wf(), {rn}_ext_enc(), {rn}_ext_dec()),\n{{\n\
         \x20   {}\n    lemma_nsn_format();\n\
         \x20   lemma_restrict_format(nsn_wf(), nsn_enc(), nsn_dec(), {rn}_eidx_ok());\n\
         \x20   lemma_frag_format();\n",
        p2_fact(7)
    ));
    s.push_str(&calls);
    for (j, (_, c)) in exts.iter().enumerate() {
        s.push_str(&format!(
            "    lemma_open_format({}, {}, {});\n\
             \x20   assert forall|x: {}| {}(x) implies\n\
             \x20       #[trigger] {rn}_eprj{j}()({rn}_einj{j}()(x)) == x by {{ }}\n\
             \x20   lemma_map_format({}, open_enc({}), open_dec({}), {rn}_einj{j}(), {rn}_eprj{j}());\n",
            wf_of(c), enc_of(c), dec_of(c),
            c.sty(), wf_of(c), wf_of(c), enc_of(c), dec_of(c)
        ));
    }
    s.push_str(&format!(
        "    assert forall|k: u64| {rn}_eidx_wf()(k) implies\n\
         \x20       is_format(#[trigger] {rn}_ealt_wf()(k), {rn}_ealt_enc()(k), {rn}_ealt_dec()(k))\n\
         \x20   by {{\n\
         \x20       if k >= {m} {{\n\
         \x20           assert forall|c: Seq<bool>| frag_wf()(c) implies\n\
         \x20               #[trigger] {rn}_uprj()({rn}_uinj(k)(c)) == c by {{ }}\n\
         \x20           lemma_map_format(frag_wf(), frag_enc(), frag_dec(), {rn}_uinj(k), {rn}_uprj());\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   lemma_dep_format({rn}_eidx_wf(), {rn}_eidx_enc(), {rn}_eidx_dec(),\n\
         \x20                    {rn}_ealt_wf(), {rn}_ealt_enc(), {rn}_ealt_dec());\n\
         \x20   assert forall|t: (u64, {sn})| {rn}_efull_wf()(t) implies\n\
         \x20       #[trigger] {rn}_efrom_f()({rn}_eto_f()(t)) == t by {{ }}\n\
         \x20   lemma_map_format({rn}_efull_wf(), {rn}_efull_enc(), {rn}_efull_dec(),\n\
         \x20                    {rn}_eto_f(), {rn}_efrom_f());\n}}\n\n"
    ));
    // each half accepts only its own variants
    s.push_str(&format!(
        "pub proof fn {rn}_root_only(v: {sn})\n\
         \x20   requires {rn}_root_wf()(v),\n\
         \x20   ensures !{rn}_isext(v), {rn}_ridx_wf()({rn}_rtag(v)), {rn}_ralt_wf()({rn}_rtag(v))(v),\n{{\n\
         \x20   assert({rn}_rfrom_f()({rn}_rto_f()({rn}_rfrom(v))) == {rn}_rfrom(v));\n}}\n\n\
         pub proof fn {rn}_ext_only(v: {sn})\n\
         \x20   requires {rn}_ext_wf()(v),\n\
         \x20   ensures {rn}_isext(v), {rn}_eidx_wf()({rn}_etag(v)), {rn}_ealt_wf()({rn}_etag(v))(v),\n\
         \x20   {{\n\
         \x20   assert({rn}_efrom_f()({rn}_eto_f()({rn}_efrom(v))) == {rn}_efrom(v));\n\
         \x20   lemma_restrict_wf_val(nsn_wf(), {rn}_eidx_ok(), {rn}_etag(v));\n}}\n\n"
    ));
    s.push_str(&format!(
        "pub proof fn {rn}_is_format()\n    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n{{\n\
         \x20   {rn}_root_is_format();\n\
         \x20   {rn}_ext_is_format();\n\
         \x20   lemma_bool_format();\n\
         \x20   assert forall|e: bool| bool_wf()(e) implies\n\
         \x20       is_format(#[trigger] {rn}_fam_wf()(e), {rn}_fam_enc()(e), {rn}_fam_dec()(e))\n\
         \x20   by {{ }}\n\
         \x20   lemma_dep_format(bool_wf(), bool_enc(), bool_dec(),\n\
         \x20                    {rn}_fam_wf(), {rn}_fam_enc(), {rn}_fam_dec());\n\
         \x20   assert forall|t: (bool, {sn})| {rn}_full_wf()(t) implies\n\
         \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t\n\
         \x20   by {{\n\
         \x20       if t.0 {{ {rn}_ext_only(t.1); }} else {{ {rn}_root_only(t.1); }}\n\
         \x20   }}\n\
         \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(),\n\
         \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n\
         pub proof fn {rn}_bounds(v: {sn})\n\
         \x20   requires {rn}_wf()(v),\n\
         \x20   ensures {rn}_fam_wf()({rn}_isext(v))(v),\n{{\n\
         \x20   assert({rn}_from_f()({rn}_to_f()({rn}_from(v))) == {rn}_from(v));\n}}\n\n"
    ));

    // ------------------------------------------------------ decode, root half
    let dec_head = |fname: &str, spec: &str| -> String {
        format!(
            "pub fn {rn}_{fname}(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
             \x20   requires old(r).wf(),\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v_, f_)) => {spec}(old(r).rem())\n\
             \x20               == Some::<({sn}, nat, Flg)>(({rn}_view(v_), (final(r).pos - old(r).pos) as nat, f_)),\n\
             \x20           None => {spec}(old(r).rem()).is_none(),\n\
             \x20       }},\n{{\n{preamble}\
             \x20   let ghost start = old(r).rem();\n\
             \x20   let ghost p0 = old(r).pos;\n"
        )
    };
    // One runner per alternative, stated against the alternative family at
    // the index it was given, and a dispatcher that only picks the runner.
    // Inline, every branch's `dep` lemma unfolded the whole `if i == 0 ..`
    // chain: O(n^2) in the alternatives, and a 37-alternative NR CHOICE went
    // over the rlimit.
    let alt_head = |fname: &str, req: &str, fam: &str| -> String {
        format!(
            "pub fn {rn}_{fname}(r: &mut BitReader, i_: u64) -> (res: Option<({rn}, Flg)>)\n\
             \x20   requires old(r).wf(), {req},\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v_, f_)) => {fam}(i_)(old(r).rem())\n\
             \x20               == Some::<({sn}, nat, Flg)>(({rn}_view(v_), (final(r).pos - old(r).pos) as nat, f_)),\n\
             \x20           None => {fam}(i_)(old(r).rem()).is_none(),\n\
             \x20       }},\n{{\n{preamble}\
             \x20   let ghost start = old(r).rem();\n\
             \x20   let ghost p0 = old(r).pos;\n"
        )
    };
    let ralt = format!("{rn}_ralt_dec()");
    for (i, (an, c)) in roots.iter().enumerate() {
        let dc = dec_of(c);
        let asn = &root_alts[i].0;
        s.push_str(&alt_head(&format!("ralt{i}_run"), &format!("i_ == {i}"), &ralt));
        s.push_str(&format!(
            "    let (v_, f_) = match {} {{\n\
             \x20       Some(xf_) => xf_,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_map_dec_none({dc}, {rn}_rinj{i}(), start); }}\n\
             \x20           {{ r.fail_in(\"{asn}\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_map_dec_some({dc}, {rn}_rinj{i}(), start, {}, (r.pos - p0) as nat, f_); }}\n\
             \x20   Some(({rn}::{an}(v_), f_))\n}}\n\n",
            c.decode.replace("{R}", "r"),
            c.view_of("v_"),
        ));
    }
    s.push_str(&dec_head("root_run", &format!("{rn}_root_dec()")));
    let rnone = format!(
        "lemma_dep_dec_none_fst({rn}_ridx_dec(), {rn}_ralt_dec(), start);\n\
         \x20               lemma_map_dec_none({rn}_rfull_dec(), {rn}_rto_f(), start);"
    );
    if single {
        s.push_str("    let i_: u64 = 0;\n    proof { lemma_unit_dec_val(0u64, start); }\n");
    } else {
        s.push_str(&format!(
            "    proof {{ {} }}\n\
             \x20   let i_ = match r.read_{u}({rw}) {{\n\
             \x20       Some(v_) => v_,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               lemma_restrict_dec_none({u}_dec({rw}), {rn}_ridx_ok(), start);\n\
             \x20               {rnone}\n\
             \x20           }}\n\
             \x20           {{ r.fail(\"CHOICE index (0..{rmax})\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   if i_ > {rmax} {{\n\
             \x20       proof {{\n\
             \x20           lemma_restrict_dec_none({u}_dec({rw}), {rn}_ridx_ok(), start);\n\
             \x20           {rnone}\n\
             \x20       }}\n\
             \x20       {{ r.fail(\"CHOICE index (0..{rmax})\"); return None; }}\n\
             \x20   }}\n\
             \x20   proof {{\n\
             \x20       lemma_restrict_dec_some({u}_dec({rw}), {rn}_ridx_ok(), start, i_, {ulen}, Flg::SameVer);\n\
             \x20       lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat);\n\
             \x20   }}\n",
            p2_fact(rw)
        ));
    }
    let mut pick = String::new();
    for i in 0..n {
        if n == 1 {
            pick.push_str(&format!("{rn}_ralt0_run(r, i_)"));
        } else if i == 0 {
            pick.push_str(&format!("if i_ == 0 {{ {rn}_ralt0_run(r, i_) }}"));
        } else if i + 1 == n {
            pick.push_str(&format!(" else {{ {rn}_ralt{i}_run(r, i_) }}"));
        } else {
            pick.push_str(&format!(" else if i_ == {i} {{ {rn}_ralt{i}_run(r, i_) }}"));
        }
    }
    let dispatch = |pick: &str, idx: &str, ivar: &str, alt: &str, full: &str, to: &str| -> String {
        format!(
            "    let ghost kidx = (r.pos - p0) as nat;\n\
             \x20   let ghost p1 = r.pos;\n\
             \x20   proof {{ assert(r.rem() {eq} {skip}); }}\n\
             \x20   let got = {pick};\n\
             \x20   match got {{\n\
             \x20       Some((v_, f_)) => {{\n\
             \x20           proof {{\n\
             \x20               lemma_dep_dec_some({idx}, {alt}, start, {ivar}, kidx, Flg::SameVer,\n\
             \x20                                  {rn}_view(v_), (r.pos - p1) as nat, f_);\n\
             \x20               lemma_map_dec_some({full}, {to}, start, ({ivar}, {rn}_view(v_)),\n\
             \x20                                  (r.pos - p0) as nat, f_);\n\
             \x20           }}\n\
             \x20           Some((v_, f_))\n\
             \x20       }}\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               lemma_dep_dec_none_snd({idx}, {alt}, start, {ivar}, kidx, Flg::SameVer);\n\
             \x20               lemma_map_dec_none({full}, {to}, start);\n\
             \x20           }}\n\
             \x20           None\n\
             \x20       }}\n\
             \x20   }}\n}}\n\n",
            eq = if aper() { "==" } else { "=~=" },
            skip = skip_in("start", "kidx"),
        )
    };
    s.push_str(&dispatch(&pick, &format!("{rn}_ridx_dec()"), "i_", &format!("{rn}_ralt_dec()"),
                         &format!("{rn}_rfull_dec()"), &format!("{rn}_rto_f()")));

    // ------------------------------------------------- decode, extension half
    let ealt = format!("{rn}_ealt_dec()");
    for (j, (an, c)) in exts.iter().enumerate() {
        let ed = dec_of(c);
        let asn = &ext_alts[j].0;
        // Its own solver process: an extension alternative's open-type
        // decoder is the same shape for every alternative, and verified in one
        // process with its siblings one of them could go over the rlimit
        // depending on what came before it (NR's posSIB-TypeAndInfo-r16, which
        // passes alone at the default).
        s.push_str("#[verifier::spinoff_prover]\n");
        s.push_str(&alt_head(&format!("ealt{j}_run"), &format!("i_ == {j}"), &ealt));
        let none = |inner: &str| -> String {
            format!("{inner}\n\x20                   lemma_map_dec_none(open_dec({ed}), {rn}_einj{j}(), start);")
        };
        // APER's content lies whole in the buffer, octet-aligned: borrowed
        // rather than copied (`read_afrag_ref`)
        let oref = if aper() { "_ref" } else { "" };
        s.push_str(&format!(
            "    let content = match r.read_{a}frag{oref}() {{\n\
             \x20       Some(cb) => cb,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               {}\n\
             \x20           }}\n\
             \x20           {{ r.fail(\"open type length\"); r.fail_in(\"{asn}\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   let ghost kf = (r.pos - p0) as nat;\n\
             \x20   let ghost cbits = bits_of(content@);\n\
             \x20   let mut r2 = BitReader::new(content.as_slice());\n\
             \x20   let r2 = &mut r2;\n{at0}\
             \x20   let (v_, f_) = match {} {{\n\
             \x20       Some(vf) => vf,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               {}\n\
             \x20           }}\n\
             \x20           {{ r.adopt(r2, content.len()); r.fail_in(\"{asn}\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   let ghost k2 = r2.pos as nat;\n\
             \x20   if !ot_octets_eq(r2.pos, content.len()) || !r2.check_zero_tail() {{\n\
             \x20       proof {{\n\
             \x20           {}\n\
             \x20       }}\n\
             \x20       {{ r.fail(\"open type padding\"); r.fail_in(\"{asn}\"); return None; }}\n\
             \x20   }}\n\
             \x20   let ghost sv_ = {};\n\
             \x20   proof {{\n\
             \x20       assert(cbits.len() / 8 == content@.len()) by (nonlinear_arith)\n\
             \x20           requires cbits.len() == 8 * content@.len();\n\
             \x20       assert(cbits.skip(k2 as int) =~= zeros((cbits.len() - k2) as nat));\n\
             \x20       lemma_open_dec_some({ed}, start, cbits, kf, sv_, k2, f_);\n\
             \x20       lemma_map_dec_some(open_dec({ed}), {rn}_einj{j}(), start, sv_, kf, f_);\n\
             \x20   }}\n\
             \x20   Some(({rn}::{an}(v_), f_))\n}}\n\n",
            none(&format!("lemma_open_dec_none_len({ed}, start);")),
            c.decode.replace("{R}", "r2"),
            none(&format!("lemma_open_dec_none_content({ed}, start, cbits, kf);")),
            none(&format!("lemma_open_dec_none_pad({ed}, start, cbits, kf);")),
            c.view_of("v_"),
            a = if aper() { "a" } else { "" },
            // an open type's content is a complete encoding: it starts at 0
            at0 = if aper() { "\x20   proof { assert(r2.at() == (0nat, cbits)); }\n" } else { "" },
        ));
    }
    // an index past everything this schema knows: kept, octets and all
    s.push_str(&alt_head("eunk_run", &format!("i_ >= {m}"), &ealt));
    s.push_str(&format!(
        "    let content = match r.read_{a}frag() {{\n\
         \x20       Some(cb) => cb,\n\
         \x20       None => {{\n\
         \x20           proof {{ lemma_map_dec_none(frag_dec(), {rn}_uinj(i_), start); }}\n\
         \x20           {{ r.fail(\"open type length, unknown alternative\"); return None; }}\n\
         \x20       }}\n\
         \x20   }};\n\
         \x20   proof {{\n\
         \x20       lemma_map_dec_some(frag_dec(), {rn}_uinj(i_), start, bits_of(content@),\n\
         \x20                          (r.pos - p0) as nat, Flg::SameVer);\n\
         \x20   }}\n\
         \x20   Some(({rn}::Unknown(i_, content), Flg::SameVer))\n}}\n\n",
        a = if aper() { "a" } else { "" },
    ));
    s.push_str(&dec_head("ext_run", &format!("{rn}_ext_dec()")));
    s.push_str(&format!(
        "    proof {{ {} }}\n\
         \x20   let k_ = match r.read_{a}nsn() {{\n\
         \x20       Some(v_) => v_,\n\
         \x20       None => {{\n\
         \x20           proof {{\n\
         \x20               lemma_restrict_dec_none(nsn_dec(), {rn}_eidx_ok(), start);\n\
         \x20               lemma_dep_dec_none_fst({rn}_eidx_dec(), {rn}_ealt_dec(), start);\n\
         \x20               lemma_map_dec_none({rn}_efull_dec(), {rn}_eto_f(), start);\n\
         \x20           }}\n\
         \x20           {{ r.fail(\"CHOICE extension index\"); return None; }}\n\
         \x20       }}\n\
         \x20   }};\n\
         \x20   proof {{\n\
         \x20       lemma_restrict_dec_some(nsn_dec(), {rn}_eidx_ok(), start, k_, (r.pos - p0) as nat, Flg::SameVer);\n\
         \x20       lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat);\n\
         \x20   }}\n",
        p2_fact(7),
        a = if aper() { "a" } else { "" },
    ));
    let mut epick = String::new();
    for j in 0..m {
        epick.push_str(&format!("{}if k_ == {j} {{ {rn}_ealt{j}_run(r, k_) }}", if j == 0 { "" } else { " else " }));
    }
    epick.push_str(&format!("{}{{ {rn}_eunk_run(r, k_) }}", if m == 0 { "" } else { " else " }));
    s.push_str(&dispatch(&epick, &format!("{rn}_eidx_dec()"), "k_", &format!("{rn}_ealt_dec()"),
                         &format!("{rn}_efull_dec()"), &format!("{rn}_eto_f()")));

    // ------------------------------------------------------ decode, the whole
    s.push_str(&dec_head("decode", &format!("{rn}_dec()")));
    s.push_str(&format!(
        "    let e_ = match r.read_bool() {{\n\
         \x20       Some(b) => b,\n\
         \x20       None => {{\n\
         \x20           proof {{\n\
         \x20               lemma_dep_dec_none_fst(bool_dec(), {rn}_fam_dec(), start);\n\
         \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           {{ r.fail(\"extension bit\"); return None; }}\n\
         \x20       }}\n\
         \x20   }};\n\
         \x20   proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n\
         \x20   let ghost kb = (r.pos - p0) as nat;\n\
         \x20   let ghost p1 = r.pos;\n\
         \x20   let got = if e_ {{ {rn}_ext_run(r) }} else {{ {rn}_root_run(r) }};\n\
         \x20   match got {{\n\
         \x20       Some((v_, f_)) => {{\n\
         \x20           proof {{\n\
         \x20               lemma_dep_dec_some(bool_dec(), {rn}_fam_dec(), start, e_, kb, Flg::SameVer,\n\
         \x20                                  {rn}_view(v_), (r.pos - p1) as nat, f_);\n\
         \x20               lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, (e_, {rn}_view(v_)),\n\
         \x20                                  (r.pos - p0) as nat, f_);\n\
         \x20           }}\n\
         \x20           Some((v_, f_))\n\
         \x20       }}\n\
         \x20       None => {{\n\
         \x20           proof {{\n\
         \x20               lemma_dep_dec_none_snd(bool_dec(), {rn}_fam_dec(), start, e_, kb, Flg::SameVer);\n\
         \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           None\n\
         \x20       }}\n\
         \x20   }}\n}}\n\n"
    ));

    // ------------------------------------------------------------- encode
    let enc_head = |fname: &str, wf: &str, enc: &str| -> String {
        format!(
            "pub fn {rn}_{fname}(w: &mut BitWriter, v: &{rn}) -> (ok: bool)\n\
             \x20   requires old(w).wf(), {wf}({rn}_view(*v)),\n\
             \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
             \x20       ok ==> final(w).written() =~= old(w).written() + {},\n\
             {{\n{preamble}",
            ea(enc, OLD_POS, &format!("{rn}_view(*v)"))
        )
    };
    // root half: an extension value cannot satisfy the precondition, and
    // `false` meets the postcondition anyway
    s.push_str(&enc_head("root_enc_run", &format!("{rn}_root_wf()"), &format!("{rn}_root_enc()")));
    s.push_str(&format!("    proof {{ {rn}_root_only({rn}_view(*v)); }}\n"));
    if !single {
        s.push_str(&format!(
            "    proof {{ {} }}\n\
             \x20   let i_ = {rn}_rtag_exec(v);\n\
             \x20   if !w.write_{u}({rw}, i_) {{ return false; }}\n",
            p2_fact(rw)
        ));
    }
    s.push_str("    match v {\n");
    for (an, c) in &roots {
        let inner = c.encode.replace("{W}", "w").replace("{V}", if byref(c) { "x_" } else { "*x_" });
        s.push_str(&format!("        {rn}::{an}(x_) => {inner},\n"));
    }
    s.push_str("        _ => false,\n    }\n}\n\n");

    // extension half: one runner per extension alternative, stated against
    // the alternative family at its own index, as the decoders are. Inline,
    // every branch's open-type proof shared one query with every other's,
    // and an NR CHOICE of eight open-type alternatives sat right at the
    // rlimit -- in once, over the next time.
    for (j, (an, c)) in exts.iter().enumerate() {
        let ee = enc_of(c);
        let sx = c.view_of("(*x_)");
        let inner = c.encode.replace("{W}", "sc").replace("{V}", if byref(c) { "x_" } else { "*x_" });
        s.push_str(&format!(
            "pub fn {rn}_ealt{j}_enc_run(w: &mut BitWriter, v: &{rn}) -> (ok: bool)\n\
             \x20   requires old(w).wf(), {rn}_ealt_wf()({j}u64)({rn}_view(*v)),\n\
             \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
             \x20       ok ==> final(w).written() =~= old(w).written() + {ealt},\n\
             {{\n{preamble}\
             \x20   match v {{\n\
             \x20       {rn}::{an}(x_) => {{\n\
             \x20           // the content is part of the output, so the output's own\n\
             \x20           // buffer is always large enough to measure it in\n\
             \x20           let mut sc_ = w.scratch();\n\
             \x20           let sc = &mut sc_;\n\
             \x20           if !{inner} {{ return false; }}\n\
             \x20           proof {{ lemma_ot_body_shape({ee}, {sx}); }}\n\
             \x20           if !sc.pad_open() {{ return false; }}\n\
             \x20           proof {{ assert(bits_of(sc.buf@).take(sc.pos as int) =~= ot_body({ee0}, {sx})); }}\n\
             \x20           let ok_ = w.write_{a}open(sc.buf.as_slice(), sc.pos, Ghost({ee}), Ghost({sx}));\n\
             \x20           w.give_back(sc_);\n\
             \x20           ok_\n\
             \x20       }}\n\
             \x20       _ => false,\n\
             \x20   }}\n}}\n\n",
            ealt = ea(&format!("{rn}_ealt_enc()({j}u64)"), OLD_POS, &format!("{rn}_view(*v)")),
            // APER: the content is the value encoded from position 0
            ee0 = if aper() { format!("at0_enc({ee})") } else { ee.clone() },
            a = if aper() { "a" } else { "" },
        ));
    }
    s.push_str(&enc_head("ext_enc_run", &format!("{rn}_ext_wf()"), &format!("{rn}_ext_enc()")));
    s.push_str(&format!(
        "    proof {{ {rn}_ext_only({rn}_view(*v)); {} }}\n\
         \x20   let k_ = {rn}_etag_exec(v);\n\
         \x20   if !w.write_{a}nsn(k_) {{ return false; }}\n\
         \x20   match v {{\n",
        p2_fact(7),
        a = if aper() { "a" } else { "" },
    ));
    for (j, (an, _)) in exts.iter().enumerate() {
        s.push_str(&format!("        {rn}::{an}(_) => {rn}_ealt{j}_enc_run(w, v),\n"));
    }
    s.push_str(&format!(
        "        {rn}::Unknown(_, b) => {{\n\
         \x20           if b.len() > usize::MAX / 8 {{ return false; }}\n\
         \x20           proof {{\n\
         {reveal}\
         \x20               assert(bits_of(b@).skip(0).take((8 * b.len()) as int) =~= bits_of(b@));\n\
         \x20           }}\n\
         \x20           w.write_{a}frag(b.as_slice(), 0, 8 * b.len())\n\
         \x20       }}\n\
         \x20       _ => false,\n\
         \x20   }}\n}}\n\n",
        a = if aper() { "a" } else { "" },
        reveal = if aper() { "" } else { "\x20               reveal(frag_enc);\n" },
    ));

    // the whole
    s.push_str(&enc_head("encode", &format!("{rn}_wf()"), &format!("{rn}_enc()")));
    s.push_str(&format!(
        "    proof {{ {rn}_bounds({rn}_view(*v)); }}\n\
         \x20   let e_ = {rn}_isext_exec(v);\n\
         \x20   if !w.write_bool(e_) {{ return false; }}\n\
         \x20   if e_ {{ {rn}_ext_enc_run(w, v) }} else {{ {rn}_root_enc_run(w, v) }}\n}}\n\n"
    ));

    let jalts: Vec<(String, String, Compiled)> = root_alts
        .iter()
        .chain(ext_alts.iter())
        .zip(roots.iter().chain(exts.iter()))
        .map(|((asn, _), (an, c))| (asn.clone(), an.clone(), c.clone()))
        .collect();
    // an alternative only a newer schema knows has no JER of its own; the
    // brace `jer_choice` opened is closed by `jer_unknown_alt`'s own object
    s.push_str(&jer_choice(
        &rn,
        &jalts,
        &format!("        {rn}::Unknown(k, b) => {{ jer_member(\"?unknown-extension\", &mut first, o); jer_unknown_alt(*k, b, o); }}\n"),
    ));
    s.push_str(&arb_choice(&rn, &jalts));
    Ok((
        s,
        Compiled {
            jer: format!("{rn}_jer({{V}}, {{O}})"),
            arb: format!("{rn}_arb({{G}})"),
            owner: None,
            // `Unknown` carries octets, so there is always a spec companion
            spec_ty: Some(sn.clone()),
            view: Some(format!("{rn}_view({{V}})")),
            rust_ty: rn.clone(),
            fmt: rn.clone(),
            proof_call: format!("{rn}_is_format();"),
            decode: format!("{rn}_decode({{R}})"),
            encode: format!("{rn}_encode({{W}}, {{V}})"),
            preamble: vec![],
        },
    ))
}
