//! The extensible ENUMERATED (X.691 14.2, 14.3).
//!
//! One bit, then either the root index as a constrained whole number, as a
//! non-extensible ENUMERATED would write it, or the index among the
//! extension values as a normally small non-negative whole number (11.6):
//!
//!     enc(v) = [0] + root_idx(i)      root value i
//!            | [1] + nsnnwn(j)        extension value j
//!
//! Like the extensible CHOICE this needs no new combinator: it is `dep` on
//! the bit, with the index format chosen by it, `map`ped into one Rust enum
//! holding root and extension values alike.
//!
//! An extension index past this schema's own values is rejected, not kept.
//! Unlike a CHOICE's unknown alternative there is nothing to keep -- an
//! enumerated value is its index, and one this schema cannot name has no
//! value in its type. VUPER does the same (`sum_format` over the root and
//! an extension format that is `empty_format` when there are no extension
//! values). So an `ENUMERATED { a, b, ... }` with no extension values at all
//! still reads its extension bit, and rejects a set one.
//!
//! The extension index is 11.6's normally small number in both forms
//! (`vuperx::intx::nsn`), as the CHOICE index is.
use super::*;

pub(super) fn gen_enum_ext(name: &str, root: &[String], ext: &[String]) -> Result<(String, Compiled), Pending> {
    if root.is_empty() {
        return Err(Pending::Unsupported("ENUMERATED with no root values".into()));
    }
    let rn = rustify(name);
    let n = root.len();
    let m = ext.len();
    let rw = width_for(n as u64);
    if rw > 56 {
        return Err(Pending::Unsupported("ENUMERATED is too wide".into()));
    }
    let rmax = (n - 1) as u64;
    let single = n == 1;
    let vals: Vec<(bool, usize, String)> = root
        .iter()
        .enumerate()
        .map(|(i, v)| (false, i, rustify(v)))
        .chain(ext.iter().enumerate().map(|(j, v)| (true, j, rustify(v))))
        .collect();

    let mut s = String::new();
    s.push_str(&format!("// ---------------------------------------------------------------- {name} (extensible)\n"));
    s.push_str(&format!("#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]\npub enum {rn} {{\n"));
    for (_, _, v) in &vals {
        s.push_str(&format!("    {v},\n"));
    }
    s.push_str("}\n\n");

    // --------------------------------------------- which half, which index
    let arms = |f: &dyn Fn(bool, usize) -> String| -> String {
        vals.iter().map(|(e, i, v)| format!("        {rn}::{v} => {},\n", f(*e, *i))).collect()
    };
    let isext = arms(&|e, _| e.to_string());
    let idx = arms(&|_, i| format!("{i}u64"));
    s.push_str(&format!(
        "pub open spec fn {rn}_isext(v: {rn}) -> bool {{\n    match v {{\n{isext}    }}\n}}\n\
         pub open spec fn {rn}_idx(v: {rn}) -> u64 {{\n    match v {{\n{idx}    }}\n}}\n\
         pub fn {rn}_isext_exec(v: &{rn}) -> (res: bool)\n    ensures res == {rn}_isext(*v),\n{{\n    match v {{\n{isext}    }}\n}}\n\
         pub fn {rn}_idx_exec(v: &{rn}) -> (res: u64)\n    ensures res == {rn}_idx(*v),\n{{\n    match v {{\n{idx}    }}\n}}\n\n"
    ));
    // index -> value, within each half
    let chain = |half: &[String], var: &str| -> String {
        let mut out = String::new();
        for (i, v) in half.iter().enumerate() {
            if i + 1 == half.len() {
                out.push_str(&format!("{rn}::{}", rustify(v)));
            } else {
                out.push_str(&format!("if {var} == {i} {{ {rn}::{} }} else {{ ", rustify(v)));
            }
        }
        for _ in 1..half.len() {
            out.push_str(" }");
        }
        out
    };
    let rto = chain(root, "i");
    // with no extension values there is no index to map, and the extension
    // half's format accepts nothing, so this is never reached
    let eto = if m == 0 { format!("{rn}::{}", rustify(&root[0])) } else { chain(ext, "i") };
    s.push_str(&format!(
        "pub open spec fn {rn}_to(t: (bool, u64)) -> {rn} {{\n\
         \x20   let i = t.1;\n\
         \x20   if t.0 {{ {eto} }} else {{ {rto} }}\n}}\n\
         pub open spec fn {rn}_from(v: {rn}) -> (bool, u64) {{ ({rn}_isext(v), {rn}_idx(v)) }}\n\
         pub open spec fn {rn}_to_f() -> spec_fn((bool, u64)) -> {rn} {{ |t: (bool, u64)| {rn}_to(t) }}\n\
         pub open spec fn {rn}_from_f() -> spec_fn({rn}) -> (bool, u64) {{ |v: {rn}| {rn}_from(v) }}\n\n"
    ));
    s.push_str(&format!(
        "pub fn {rn}_of(e: bool, i: u64) -> (v: {rn})\n\
         \x20   requires if e {{ i < {m} }} else {{ i <= {rmax} }},\n\
         \x20   ensures v == {rn}_to((e, i)),\n{{\n\
         \x20   if e {{ {} }} else {{ {} }}\n}}\n\n",
        if m == 0 { format!("{rn}::{}", rustify(&root[0])) } else { chain(ext, "i") },
        rto
    ));

    // ------------------------------------------------------ the two indices
    if single {
        s.push_str(&format!(
            "pub open spec fn {rn}_ridx_wf() -> Wf<u64> {{ unit_wf(0u64) }}\n\
             pub open spec fn {rn}_ridx_enc() -> Enc<u64> {{ unit_enc() }}\n\
             pub open spec fn {rn}_ridx_dec() -> Dec<u64> {{ unit_dec(0u64) }}\n"
        ));
    } else {
        s.push_str(&format!(
            "pub open spec fn {rn}_ridx_ok() -> spec_fn(u64) -> bool {{ |i: u64| i <= {rmax} }}\n\
             pub open spec fn {rn}_ridx_wf() -> Wf<u64> {{ restrict_wf(uint_wf({rw}), {rn}_ridx_ok()) }}\n\
             pub open spec fn {rn}_ridx_enc() -> Enc<u64> {{ uint_enc({rw}) }}\n\
             pub open spec fn {rn}_ridx_dec() -> Dec<u64> {{ restrict_dec(uint_dec({rw}), {rn}_ridx_ok()) }}\n"
        ));
    }
    s.push_str(&format!(
        "pub open spec fn {rn}_eidx_ok() -> spec_fn(u64) -> bool {{ |k: u64| k < {m} }}\n\
         pub open spec fn {rn}_eidx_wf() -> Wf<u64> {{ restrict_wf(nsn_wf(), {rn}_eidx_ok()) }}\n\
         pub open spec fn {rn}_eidx_enc() -> Enc<u64> {{ nsn_enc() }}\n\
         pub open spec fn {rn}_eidx_dec() -> Dec<u64> {{ restrict_dec(nsn_dec(), {rn}_eidx_ok()) }}\n\n\
         pub open spec fn {rn}_fam_wf() -> spec_fn(bool) -> Wf<u64> {{ |e: bool| if e {{ {rn}_eidx_wf() }} else {{ {rn}_ridx_wf() }} }}\n\
         pub open spec fn {rn}_fam_enc() -> spec_fn(bool) -> Enc<u64> {{ |e: bool| if e {{ {rn}_eidx_enc() }} else {{ {rn}_ridx_enc() }} }}\n\
         pub open spec fn {rn}_fam_dec() -> spec_fn(bool) -> Dec<u64> {{ |e: bool| if e {{ {rn}_eidx_dec() }} else {{ {rn}_ridx_dec() }} }}\n\
         pub open spec fn {rn}_full_wf() -> Wf<(bool, u64)> {{ dep_wf(bool_wf(), {rn}_fam_wf()) }}\n\
         pub open spec fn {rn}_full_enc() -> Enc<(bool, u64)> {{ dep_enc(bool_enc(), {rn}_fam_enc()) }}\n\
         pub open spec fn {rn}_full_dec() -> Dec<(bool, u64)> {{ dep_dec(bool_dec(), {rn}_fam_dec()) }}\n\
         pub open spec fn {rn}_wf() -> Wf<{rn}> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_enc() -> Enc<{rn}> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_dec() -> Dec<{rn}> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n"
    ));

    // ------------------------------------------------------------- proofs
    let ridx_format = if single {
        "    lemma_unit_format(0u64);\n".to_string()
    } else {
        format!(
            "    {}\n    lemma_uint_format({rw});\n\
             \x20   lemma_restrict_format(uint_wf({rw}), uint_enc({rw}), uint_dec({rw}), {rn}_ridx_ok());\n",
            p2_fact(rw)
        )
    };
    // the round trip, one half at a time: each is a case split over that
    // half's indices, and together they would be one split over both
    s.push_str(&format!(
        "pub proof fn {rn}_rt_root(i: u64)\n\
         \x20   requires {rn}_ridx_wf()(i),\n\
         \x20   ensures {rn}_from({rn}_to((false, i))) == (false, i),\n{{\n}}\n\n\
         pub proof fn {rn}_rt_ext(i: u64)\n\
         \x20   requires {rn}_eidx_wf()(i),\n\
         \x20   ensures {rn}_from({rn}_to((true, i))) == (true, i),\n{{\n}}\n\n\
         pub proof fn {rn}_is_format()\n    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n{{\n\
         {ridx_format}\
         \x20   {}\n    lemma_nsn_format();\n\
         \x20   lemma_restrict_format(nsn_wf(), nsn_enc(), nsn_dec(), {rn}_eidx_ok());\n\
         \x20   lemma_bool_format();\n\
         \x20   assert forall|e: bool| bool_wf()(e) implies\n\
         \x20       is_format(#[trigger] {rn}_fam_wf()(e), {rn}_fam_enc()(e), {rn}_fam_dec()(e))\n\
         \x20   by {{ }}\n\
         \x20   lemma_dep_format(bool_wf(), bool_enc(), bool_dec(),\n\
         \x20                    {rn}_fam_wf(), {rn}_fam_enc(), {rn}_fam_dec());\n\
         \x20   assert forall|t: (bool, u64)| {rn}_full_wf()(t) implies\n\
         \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t\n\
         \x20   by {{\n\
         \x20       if t.0 {{ {rn}_rt_ext(t.1); }} else {{ {rn}_rt_root(t.1); }}\n\
         \x20   }}\n\
         \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(),\n\
         \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n",
        p2_fact(7)
    ));

    // ------------------------------------------------------------- decode
    let eguard = if m == 0 { "false".to_string() } else { format!("k < {m}") };
    let none_all = format!(
        "lemma_dep_dec_none_snd(bool_dec(), {rn}_fam_dec(), start, e_, kb, Flg::SameVer);\n\
         \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);"
    );
    let root_read = if single {
        "        proof { lemma_unit_dec_val(0u64, r.rem()); }\n        0u64\n".to_string()
    } else {
        format!(
            "        proof {{ {} }}\n\
             \x20       let ghost st = r.rem();\n\
             \x20       match r.read_uint({rw}) {{\n\
             \x20           Some(i) if i <= {rmax} => {{\n\
             \x20               proof {{ lemma_restrict_dec_some(uint_dec({rw}), {rn}_ridx_ok(), st, i, {rw}, Flg::SameVer); }}\n\
             \x20               i\n\
             \x20           }}\n\
             \x20           _ => {{\n\
             \x20               proof {{\n\
             \x20                   lemma_restrict_dec_none(uint_dec({rw}), {rn}_ridx_ok(), st);\n\
             \x20                   {none_all}\n\
             \x20               }}\n\
             \x20               {{ r.fail(\"ENUMERATED index (0..{rmax})\"); return None; }}\n\
             \x20           }}\n\
             \x20       }}\n",
            p2_fact(rw)
        )
    };
    s.push_str(&format!(
        "pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v, f)) => {rn}_dec()(old(r).rem())\n\
         \x20               == Some::<({rn}, nat, Flg)>((v, (final(r).pos - old(r).pos) as nat, f)),\n\
         \x20           None => {rn}_dec()(old(r).rem()).is_none(),\n\
         \x20       }},\n{{\n\
         \x20   let ghost start = r.rem();\n\
         \x20   let ghost p0 = r.pos;\n\
         \x20   let e_ = match r.read_bool() {{\n\
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
         \x20   let i_ = if e_ {{\n\
         \x20       proof {{ {} }}\n\
         \x20       let ghost st = r.rem();\n\
         \x20       match r.read_nsn() {{\n\
         \x20           Some(k) if {eguard} => {{\n\
         \x20               proof {{ lemma_restrict_dec_some(nsn_dec(), {rn}_eidx_ok(), st, k, (r.pos - p1) as nat, Flg::SameVer); }}\n\
         \x20               k\n\
         \x20           }}\n\
         \x20           _ => {{\n\
         \x20               proof {{\n\
         \x20                   lemma_restrict_dec_none(nsn_dec(), {rn}_eidx_ok(), st);\n\
         \x20                   {none_all}\n\
         \x20               }}\n\
         \x20               {{ r.fail(\"ENUMERATED extension index\"); return None; }}\n\
         \x20           }}\n\
         \x20       }}\n\
         \x20   }} else {{\n\
         {root_read}\
         \x20   }};\n\
         \x20   proof {{\n\
         \x20       lemma_dep_dec_some(bool_dec(), {rn}_fam_dec(), start, e_, kb, Flg::SameVer,\n\
         \x20                          i_, (r.pos - p1) as nat, Flg::SameVer);\n\
         \x20       lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, (e_, i_),\n\
         \x20                          (r.pos - p0) as nat, Flg::SameVer);\n\
         \x20   }}\n\
         \x20   Some(({rn}_of(e_, i_), Flg::SameVer))\n}}\n\n",
        p2_fact(7)
    ));

    // ------------------------------------------------------------- encode
    let root_write = if single {
        format!("        proof {{ assert(w.written() + unit_enc::<u64>()(i_) =~= w.written()); }}\n        true\n")
    } else {
        format!("        proof {{ {} }}\n        w.write_uint({rw}, i_)\n", p2_fact(rw))
    };
    s.push_str(&format!(
        "pub fn {rn}_encode(w: &mut BitWriter, v: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {rn}_enc()(*v),\n{{\n\
         \x20   let e_ = {rn}_isext_exec(v);\n\
         \x20   let i_ = {rn}_idx_exec(v);\n\
         \x20   proof {{ lemma_bool_enc_seq(e_); }}\n\
         \x20   if !w.write_bool(e_) {{ return false; }}\n\
         \x20   if e_ {{\n\
         \x20       proof {{ {} }}\n\
         \x20       w.write_nsn(i_)\n\
         \x20   }} else {{\n\
         {root_write}\
         \x20   }}\n}}\n\n",
        p2_fact(7)
    ));

    let all: Vec<String> = root.iter().chain(ext.iter()).cloned().collect();
    s.push_str(&jer_enum(&rn, &all));
    s.push_str(&arb_enum(&rn, &all));
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
