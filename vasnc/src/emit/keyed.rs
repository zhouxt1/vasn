//! A SEQUENCE keyed by a component relation constraint (X.682 10), the
//! shape of every 3GPP application protocol container:
//!
//! ```text
//! ProtocolIE-Field ::= SEQUENCE { id, criticality, value ({IEs}{@id}) }
//! enc(v) = key(k) + rest_k(v)       k = the key, rest_k the SEQUENCE of the
//!                                   other components with the object's types
//! ```
//!
//! `ioc::elaborate` has made the rest, per key, an ordinary SEQUENCE whose
//! selected components are `Contains` of the object's type: an open type
//! (X.691 11.2), proved as any CONTAINING is. What is new here is only the
//! choice of rest by the key, and that is `choice_ext`'s extension half with
//! the key's own format in place of the normally small index: `dep` on the
//! key, each branch `map`ped into one enum.
//!
//! **A key no object has** is a newer peer's IE when every set involved is
//! extensible: its rest is kept with each selected component as octets,
//! `Unknown(k, rest)`, which re-encodes to the bits it came from, as an
//! unknown CHOICE alternative does. When a set is not extensible, such a key
//! does not decode. `Unknown(k, _)` with `k` an object's key is not well
//! formed, so each value has one encoding.

use super::*;

pub(super) fn gen_keyed(
    name: &str,
    key_name: &str,
    key: &Type,
    alt_types: &[(i64, String, String)],
    unknown: &str,
    ext: bool,
    env: &HashMap<String, Compiled>,
    values: &HashMap<String, i64>,
) -> Result<(String, Compiled), Pending> {
    let rn = rustify(name);
    let sn = format!("{rn}_S");
    let kc = resolve(key, env, values)?;
    if !alt_types.is_empty() && !(kc.rust_ty == "i64" && kc.plain()) {
        return Err(Pending::Unsupported(format!("a key of type {} selecting objects", kc.rust_ty)));
    }
    let kty = kc.rust_ty.clone();
    let ksty = kc.sty();
    let mut alts: Vec<(i64, String, Compiled)> = Vec::new();
    for (k, kn, tn) in alt_types {
        alts.push((*k, rustify(kn), resolve(&Type::Ref(tn.clone()), env, values)?));
    }
    let uc = resolve(&Type::Ref(unknown.to_string()), env, values)?;
    let m = alts.len();
    let (kwf, kenc, kdec) = (wf_of(&kc), enc_of(&kc), dec_of(&kc));
    let (uwf, uenc, udec) = (wf_of(&uc), enc_of(&uc), dec_of(&uc));
    // `k` is none of the objects' keys
    let not_known = |k: &str| -> String {
        if m == 0 {
            "true".into()
        } else {
            alts.iter().map(|(kv, _, _)| format!("{k} != {kv}i64")).collect::<Vec<_>>().join(" && ")
        }
    };

    let preamble = {
        let mut out = String::new();
        let mut seen = std::collections::HashSet::new();
        for c in alts.iter().map(|(_, _, c)| c).chain([&kc, &uc]) {
            for p in &c.preamble {
                if seen.insert(p.clone()) {
                    out.push_str(&format!("    proof {{ {p} }}\n"));
                }
            }
        }
        out
    };
    let byref = |c: &Compiled| !(c.rust_ty == "bool" || c.rust_ty == "i64" || c.rust_ty == "u64" || c.rust_ty == "Null");

    let mut s = String::new();
    s.push_str(&format!("// ---------------------------------------------------------------- {name} (keyed by {key_name})\n"));

    // ------------------------------------------------------------ the types
    s.push_str(&format!("#[derive(PartialEq, Eq, Debug)]\npub enum {rn} {{\n"));
    for (kv, an, c) in &alts {
        s.push_str(&format!("    /// {key_name} {kv}\n    {an}({}),\n", c.rust_ty));
    }
    s.push_str(&format!(
        "    /// A {key_name} no object of this schema has (a newer peer's), with\n\
         \x20   /// the open types it selects kept as octets.\n\
         \x20   Unknown({kty}, {}),\n}}\n\n",
        uc.rust_ty
    ));
    s.push_str(&format!("pub enum {sn} {{\n"));
    for (_, an, c) in &alts {
        s.push_str(&format!("    {an}({}),\n", c.sty()));
    }
    s.push_str(&format!("    Unknown({ksty}, {}),\n}}\n\n", uc.sty()));
    s.push_str(&format!("pub open spec fn {rn}_view(v: {rn}) -> {sn} {{\n    match v {{\n"));
    for (_, an, c) in &alts {
        s.push_str(&format!("        {rn}::{an}(x) => {sn}::{an}({}),\n", c.view_of("x")));
    }
    s.push_str(&format!(
        "        {rn}::Unknown(k, x) => {sn}::Unknown({}, {}),\n    }}\n}}\n\n",
        kc.view_of("k"),
        uc.view_of("x")
    ));

    // -------------------------------------------------------------- the key
    s.push_str(&format!("pub open spec fn {rn}_tag(v: {sn}) -> {ksty} {{\n    match v {{\n"));
    for (kv, an, _) in &alts {
        s.push_str(&format!("        {sn}::{an}(_) => {kv}i64,\n"));
    }
    s.push_str(&format!("        {sn}::Unknown(k, _) => k,\n    }}\n}}\n"));
    let kclone = if byref(&kc) { "k.clone()" } else { "*k" };
    // each arm unfolds the view's match and the tag's: the cost grows as the
    // square of the objects. F1AP's UEContextModificationRequest (97) took
    // 20 to 40; NGAP's InitialContextSetupRequest (56) passed under 10
    let n = alts.len() + 1;
    let tag_rl = if n > 48 { format!("#[verifier::rlimit({})]\n", 10 + n * n / 200) } else { String::new() };
    s.push_str(&format!(
        "{tag_rl}pub fn {rn}_tag_exec(v: &{rn}) -> (res: {kty})\n    ensures {} == {rn}_tag({rn}_view(*v)),\n{{\n    match v {{\n",
        kc.view_of("res")
    ));
    for (kv, an, _) in &alts {
        s.push_str(&format!("        {rn}::{an}(_) => {kv}i64,\n"));
    }
    s.push_str(&format!("        {rn}::Unknown(k, _) => {kclone},\n    }}\n}}\n\n"));

    // ----------------------------------------------- injection / projection
    for (j, (_, an, c)) in alts.iter().enumerate() {
        let ty = c.sty();
        s.push_str(&format!(
            "pub open spec fn {rn}_inj{j}() -> spec_fn({ty}) -> {sn} {{ |x: {ty}| {sn}::{an}(x) }}\n\
             pub open spec fn {rn}_prj{j}() -> spec_fn({sn}) -> {ty} {{\n\
             \x20   |v: {sn}| match v {{ {sn}::{an}(x) => x, _ => vstd::pervasive::arbitrary() }}\n}}\n"
        ));
    }
    let ust = uc.sty();
    s.push_str(&format!(
        "pub open spec fn {rn}_uinj(k: {ksty}) -> spec_fn({ust}) -> {sn} {{ |x: {ust}| {sn}::Unknown(k, x) }}\n\
         pub open spec fn {rn}_uprj() -> spec_fn({sn}) -> {ust} {{\n\
         \x20   |v: {sn}| match v {{ {sn}::Unknown(_, x) => x, _ => vstd::pervasive::arbitrary() }}\n}}\n"
    ));
    // the rest for a key no object has: octets when every set is
    // extensible, nothing at all otherwise
    let (unk_ok, unk_ok_pred) = if ext { ("true", "|x: ".to_string() + &ust + "| true") } else { ("false", "|x: ".to_string() + &ust + "| false") };
    s.push_str(&format!(
        "pub open spec fn {rn}_unk_ok() -> spec_fn({ust}) -> bool {{ {unk_ok_pred} }}\n\
         pub open spec fn {rn}_unk_wf(k: {ksty}) -> Wf<{sn}> {{ map_wf(restrict_wf({uwf}, {rn}_unk_ok()), {rn}_uinj(k), {rn}_uprj()) }}\n\
         pub open spec fn {rn}_unk_enc() -> Enc<{sn}> {{ map_enc({uenc}, {rn}_uprj()) }}\n\
         pub open spec fn {rn}_unk_dec(k: {ksty}) -> Dec<{sn}> {{ map_dec(restrict_dec({udec}, {rn}_unk_ok()), {rn}_uinj(k)) }}\n\n"
    ));
    let _ = unk_ok;

    // ------------------------------------------------- the rest, by the key
    let chain = |kind: &str| -> String {
        let one = |j: usize| -> String {
            let c = &alts[j].2;
            match kind {
                "wf" => format!("map_wf({}, {rn}_inj{j}(), {rn}_prj{j}())", wf_of(c)),
                "enc" => format!("map_enc({}, {rn}_prj{j}())", enc_of(c)),
                _ => format!("map_dec({}, {rn}_inj{j}())", dec_of(c)),
            }
        };
        let unk = match kind {
            "wf" => format!("{rn}_unk_wf(k)"),
            "enc" => format!("{rn}_unk_enc()"),
            _ => format!("{rn}_unk_dec(k)"),
        };
        let mut out = String::new();
        for (j, (kv, _, _)) in alts.iter().enumerate() {
            out.push_str(&format!("if k == {kv}i64 {{ {} }} else {{ ", one(j)));
        }
        out.push_str(&unk);
        for _ in 0..m {
            out.push_str(" }");
        }
        out
    };
    s.push_str(&format!(
        "pub open spec fn {rn}_alt_wf() -> spec_fn({ksty}) -> Wf<{sn}> {{ |k: {ksty}| {} }}\n\
         pub open spec fn {rn}_alt_enc() -> spec_fn({ksty}) -> Enc<{sn}> {{ |k: {ksty}| {} }}\n\
         pub open spec fn {rn}_alt_dec() -> spec_fn({ksty}) -> Dec<{sn}> {{ |k: {ksty}| {} }}\n\n",
        chain("wf"), chain("enc"), chain("dec")
    ));

    // ------------------------------------------------------------- the whole
    s.push_str(&format!(
        "pub open spec fn {rn}_to(t: ({ksty}, {sn})) -> {sn} {{ t.1 }}\n\
         pub open spec fn {rn}_from(v: {sn}) -> ({ksty}, {sn}) {{ ({rn}_tag(v), v) }}\n\
         pub open spec fn {rn}_to_f() -> spec_fn(({ksty}, {sn})) -> {sn} {{ |t: ({ksty}, {sn})| {rn}_to(t) }}\n\
         pub open spec fn {rn}_from_f() -> spec_fn({sn}) -> ({ksty}, {sn}) {{ |v: {sn}| {rn}_from(v) }}\n\
         pub open spec fn {rn}_full_wf() -> Wf<({ksty}, {sn})> {{ dep_wf({kwf}, {rn}_alt_wf()) }}\n\
         pub open spec fn {rn}_full_enc() -> Enc<({ksty}, {sn})> {{ dep_enc({kenc}, {rn}_alt_enc()) }}\n\
         pub open spec fn {rn}_full_dec() -> Dec<({ksty}, {sn})> {{ dep_dec({kdec}, {rn}_alt_dec()) }}\n\
         pub open spec fn {rn}_wf() -> Wf<{sn}> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_enc() -> Enc<{sn}> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
         pub open spec fn {rn}_dec() -> Dec<{sn}> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n"
    ));

    // ------------------------------------------------------------- proofs
    let mut seen = std::collections::HashSet::new();
    let mut calls = String::new();
    for c in alts.iter().map(|(_, _, c)| c).chain([&kc, &uc]) {
        if seen.insert(c.proof_call.clone()) {
            calls.push_str(&format!("    {}\n", c.proof_call));
        }
    }
    // the unknown rest, at any key
    s.push_str(&format!(
        "pub proof fn {rn}_unk_is_format(k: {ksty})\n\
         \x20   ensures is_format({rn}_unk_wf(k), {rn}_unk_enc(), {rn}_unk_dec(k)),\n{{\n\
         \x20   {}\n\
         \x20   lemma_restrict_format({uwf}, {uenc}, {udec}, {rn}_unk_ok());\n\
         \x20   assert forall|x: {ust}| restrict_wf({uwf}, {rn}_unk_ok())(x) implies\n\
         \x20       #[trigger] {rn}_uprj()({rn}_uinj(k)(x)) == x by {{ }}\n\
         \x20   lemma_map_format(restrict_wf({uwf}, {rn}_unk_ok()), {uenc}, restrict_dec({udec}, {rn}_unk_ok()),\n\
         \x20                    {rn}_uinj(k), {rn}_uprj());\n}}\n\n",
        uc.proof_call
    ));
    // each object's rest
    for (j, (_, _, c)) in alts.iter().enumerate() {
        s.push_str(&format!(
            "pub proof fn {rn}_alt{j}_is_format()\n\
             \x20   ensures is_format(map_wf({w}, {rn}_inj{j}(), {rn}_prj{j}()), map_enc({e}, {rn}_prj{j}()),\n\
             \x20                     map_dec({d}, {rn}_inj{j}())),\n{{\n\
             \x20   {}\n\
             \x20   assert forall|x: {t}| {w}(x) implies #[trigger] {rn}_prj{j}()({rn}_inj{j}()(x)) == x by {{ }}\n\
             \x20   lemma_map_format({w}, {e}, {d}, {rn}_inj{j}(), {rn}_prj{j}());\n}}\n\n",
            c.proof_call,
            w = wf_of(c), e = enc_of(c), d = dec_of(c), t = c.sty(),
        ));
    }
    // the family is a format at every key, and a well-formed (key, value)
    // has the key as its tag: each a case split over the objects, written
    // out and proved in a solver process of its own. Left to the solver,
    // NGAP's InitiatingMessage (87 procedures) went over the rlimit.
    let mut at = format!(
        "#[verifier::spinoff_prover]\n\
         pub proof fn {rn}_alt_is_format_at(k: {ksty})\n\
         \x20   ensures is_format({rn}_alt_wf()(k), {rn}_alt_enc()(k), {rn}_alt_dec()(k)),\n{{\n"
    );
    let mut tag = format!(
        "#[verifier::spinoff_prover]\n\
         pub proof fn {rn}_tag_ok(t: ({ksty}, {sn}))\n\
         \x20   requires {rn}_full_wf()(t),\n\
         \x20   ensures {rn}_from_f()({rn}_to_f()(t)) == t,\n{{\n\
         \x20   lemma_dep_wf_val({kwf}, {rn}_alt_wf(), t.0, t.1);\n\
         \x20   assert({kwf}(t.0) && {rn}_alt_wf()(t.0)(t.1));\n"
    );
    for (j, (kv, _, c)) in alts.iter().enumerate() {
        let els = if j == 0 { "    " } else { "    } else " };
        at.push_str(&format!("{els}if k == {kv}i64 {{\n        {rn}_alt{j}_is_format();\n"));
        tag.push_str(&format!(
            "{els}if t.0 == {kv}i64 {{\n\
             \x20       assert({rn}_alt_wf()(t.0) == map_wf({w}, {rn}_inj{j}(), {rn}_prj{j}()));\n\
             \x20       assert({rn}_inj{j}()({rn}_prj{j}()(t.1)) == t.1);\n",
            w = wf_of(c)
        ));
    }
    let open = if m == 0 { "    {\n" } else { "    } else {\n" };
    at.push_str(&format!("{open}        {rn}_unk_is_format(k);\n    }}\n}}\n\n"));
    tag.push_str(&format!(
        "{open}        assert({rn}_alt_wf()(t.0) == {rn}_unk_wf(t.0));\n\
         \x20       assert({rn}_uinj(t.0)({rn}_uprj()(t.1)) == t.1);\n    }}\n}}\n\n"
    ));
    s.push_str(&at);
    s.push_str(&tag);
    s.push_str(&format!(
        "pub proof fn {rn}_is_format()\n    ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n{{\n\
         \x20   {}\n\
         \x20   assert forall|k: {ksty}| {kwf}(k) implies\n\
         \x20       is_format(#[trigger] {rn}_alt_wf()(k), {rn}_alt_enc()(k), {rn}_alt_dec()(k))\n\
         \x20   by {{ {rn}_alt_is_format_at(k); }}\n\
         \x20   lemma_dep_format({kwf}, {kenc}, {kdec}, {rn}_alt_wf(), {rn}_alt_enc(), {rn}_alt_dec());\n\
         \x20   assert forall|t: ({ksty}, {sn})| {rn}_full_wf()(t) implies\n\
         \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t by {{ {rn}_tag_ok(t); }}\n\
         \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(), {rn}_to_f(), {rn}_from_f());\n}}\n\n\
         pub proof fn {rn}_bounds(v: {sn})\n\
         \x20   requires {rn}_wf()(v),\n\
         \x20   ensures {kwf}({rn}_tag(v)), {rn}_alt_wf()({rn}_tag(v))(v),\n{{\n\
         \x20   assert({rn}_from_f()({rn}_to_f()({rn}_from(v))) == {rn}_from(v));\n}}\n\n",
        kc.proof_call
    ));

    // ------------------------------------------------------------- decode
    // one runner per object, stated against the family at its own key, and
    // a dispatcher that only picks the runner (as `choice_ext`'s are)
    let alt_head = |fname: &str, req: &str| -> String {
        format!(
            "pub fn {rn}_{fname}(r: &mut BitReader, k_: {kty}) -> (res: Option<({rn}, Flg)>)\n\
             \x20   requires old(r).wf(), {req},\n\
             \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
             \x20       match res {{\n\
             \x20           Some((v_, f_)) => {rn}_alt_dec()({kv})(old(r).{rem}())\n\
             \x20               == Some::<({sn}, nat, Flg)>(({rn}_view(v_), (final(r).pos - old(r).pos) as nat, f_)),\n\
             \x20           None => {rn}_alt_dec()({kv})(old(r).{rem}()).is_none(),\n\
             \x20       }},\n{{\n{preamble}\
             \x20   let ghost start = old(r).{rem}();\n\
             \x20   let ghost p0 = old(r).pos;\n",
            kv = kc.view_of("k_"),
            rem = if aper() { "at" } else { "rem" },
        )
    };
    for (j, (kv, an, c)) in alts.iter().enumerate() {
        let dc = dec_of(c);
        s.push_str("#[verifier::spinoff_prover]\n");
        s.push_str(&alt_head(&format!("alt{j}_run"), &format!("k_ == {kv}i64")));
        s.push_str(&format!(
            "    let (v_, f_) = match {} {{\n\
             \x20       Some(xf_) => xf_,\n\
             \x20       None => {{\n\
             \x20           proof {{ lemma_map_dec_none({dc}, {rn}_inj{j}(), start); }}\n\
             \x20           {{ r.fail_in(\"{key_name} {kv}\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_map_dec_some({dc}, {rn}_inj{j}(), start, {}, (r.pos - p0) as nat, f_); }}\n\
             \x20   Some(({rn}::{an}(v_), f_))\n}}\n\n",
            c.decode.replace("{R}", "r"),
            c.view_of("v_"),
        ));
    }
    s.push_str("#[verifier::spinoff_prover]\n");
    s.push_str(&alt_head("unk_run", &not_known("k_")));
    if ext {
        s.push_str(&format!(
            "    let (v_, f_) = match {} {{\n\
             \x20       Some(xf_) => xf_,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               lemma_restrict_dec_none({udec}, {rn}_unk_ok(), start);\n\
             \x20               lemma_map_dec_none(restrict_dec({udec}, {rn}_unk_ok()), {rn}_uinj({kv}), start);\n\
             \x20           }}\n\
             \x20           {{ r.fail_in(\"{key_name}, unknown\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{\n\
             \x20       lemma_restrict_dec_some({udec}, {rn}_unk_ok(), start, {uv}, (r.pos - p0) as nat, f_);\n\
             \x20       lemma_map_dec_some(restrict_dec({udec}, {rn}_unk_ok()), {rn}_uinj({kv}), start, {uv},\n\
             \x20                          (r.pos - p0) as nat, f_);\n\
             \x20   }}\n\
             \x20   Some(({rn}::Unknown(k_, v_), f_))\n}}\n\n",
            uc.decode.replace("{R}", "r"),
            kv = kc.view_of("k_"),
            uv = uc.view_of("v_"),
        ));
    } else {
        s.push_str(&format!(
            "    proof {{\n\
             \x20       lemma_restrict_dec_none({udec}, {rn}_unk_ok(), start);\n\
             \x20       lemma_map_dec_none(restrict_dec({udec}, {rn}_unk_ok()), {rn}_uinj({kv}), start);\n\
             \x20   }}\n\
             \x20   {{ r.fail(\"{key_name}: no object of a set that is not extensible\"); return None; }}\n}}\n\n",
            kv = kc.view_of("k_"),
        ));
    }
    // the dispatcher, at twice the rlimit NGAP's DownlinkRANConfiguration-
    // Transfer container's needed once its module held the case-split
    // lemmas (in a process of its own, spinoff_prover, it went over at 20)
    s.push_str(&format!(
        "#[verifier::rlimit(40)]\n\
         pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v_, f_)) => {rn}_dec()(old(r).{rem}())\n\
         \x20               == Some::<({sn}, nat, Flg)>(({rn}_view(v_), (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => {rn}_dec()(old(r).{rem}()).is_none(),\n\
         \x20       }},\n{{\n{preamble}\
         \x20   let ghost start = old(r).{rem}();\n\
         \x20   let ghost p0 = old(r).pos;\n\
         \x20   let (k_, fk_) = match {} {{\n\
         \x20       Some(kf_) => kf_,\n\
         \x20       None => {{\n\
         \x20           proof {{\n\
         \x20               lemma_dep_dec_none_fst({kdec}, {rn}_alt_dec(), start);\n\
         \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           {{ r.fail_in(\"{key_name}\"); return None; }}\n\
         \x20       }}\n\
         \x20   }};\n\
         \x20   let ghost kidx = (r.pos - p0) as nat;\n\
         \x20   let ghost p1 = r.pos;\n\
         \x20   proof {{ assert(r.{rem}() {eq} {skip}); }}\n",
        kc.decode.replace("{R}", "r"),
        rem = if aper() { "at" } else { "rem" },
        eq = if aper() { "==" } else { "=~=" },
        skip = skip_in("start", "kidx"),
    ));
    let mut pick = String::new();
    for (j, (kv, _, _)) in alts.iter().enumerate() {
        pick.push_str(&format!("{}if k_ == {kv}i64 {{ {rn}_alt{j}_run(r, k_) }}", if j == 0 { "" } else { " else " }));
    }
    pick.push_str(&format!("{}{{ {rn}_unk_run(r, k_) }}", if m == 0 { "" } else { " else " }));
    let kv = kc.view_of("k_");
    s.push_str(&format!(
        "    let got = {pick};\n\
         \x20   match got {{\n\
         \x20       Some((v_, f_)) => {{\n\
         \x20           proof {{\n\
         \x20               lemma_dep_dec_some({kdec}, {rn}_alt_dec(), start, {kv}, kidx, fk_,\n\
         \x20                                  {rn}_view(v_), (r.pos - p1) as nat, f_);\n\
         \x20               lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, ({kv}, {rn}_view(v_)),\n\
         \x20                                  (r.pos - p0) as nat, flg_add(fk_, f_));\n\
         \x20           }}\n\
         \x20           Some((v_, flg_join(fk_, f_)))\n\
         \x20       }}\n\
         \x20       None => {{\n\
         \x20           proof {{\n\
         \x20               lemma_dep_dec_none_snd({kdec}, {rn}_alt_dec(), start, {kv}, kidx, fk_);\n\
         \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
         \x20           }}\n\
         \x20           None\n\
         \x20       }}\n\
         \x20   }}\n}}\n\n"
    ));

    // ------------------------------------------------------------- encode
    // One runner per object, which writes the key and the rest and proves
    // the whole encoding, each in a solver process of its own; the encoder
    // only picks the runner. In one function, every arm unfolded the key's
    // `dep` and the family's chain, and NGAP's InitialContextSetupRequest
    // (56 objects) went over the rlimit. Each at twice the default: the
    // whole type's well-formedness is in its precondition, and XnAP's
    // HandoverRequest's IAB Node Indication runner took 10 to 15.
    let kenc_call = kc.encode.replace("{W}", "w").replace("{V}", if byref(&kc) { "&k_" } else { "k_" });
    let full_head = |fname: &str, which: &str| -> String {
        format!(
            "#[verifier::spinoff_prover]\n\
             #[verifier::rlimit(20)]\n\
             pub fn {rn}_{fname}(w: &mut BitWriter, v: &{rn}) -> (ok: bool)\n\
             \x20   requires old(w).wf(), {rn}_wf()({rn}_view(*v)), {rn}_view(*v) is {which},\n\
             \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
             \x20       ok ==> final(w).written() =~= old(w).written() + {},\n\
             {{\n{preamble}\
             \x20   proof {{ {rn}_bounds({rn}_view(*v)); }}\n",
            ea(&format!("{rn}_enc()"), OLD_POS, &format!("{rn}_view(*v)"))
        )
    };
    for (j, (kv, an, c)) in alts.iter().enumerate() {
        let inner = c.encode.replace("{W}", "w").replace("{V}", if byref(c) { "x_" } else { "*x_" });
        s.push_str(&full_head(&format!("alt{j}_enc_run"), an));
        s.push_str(&format!(
            "    let k_: {kty} = {kv}i64;\n\
             \x20   if !{kenc_call} {{ return false; }}\n\
             \x20   match v {{\n        {rn}::{an}(x_) => {inner},\n        _ => false,\n    }}\n}}\n\n"
        ));
    }
    {
        let inner = uc.encode.replace("{W}", "w").replace("{V}", if byref(&uc) { "x_" } else { "*x_" });
        s.push_str(&full_head("unk_enc_run", "Unknown"));
        s.push_str(&format!(
            "    let k_ = {rn}_tag_exec(v);\n\
             \x20   if !{kenc_call} {{ return false; }}\n\
             \x20   match v {{\n        {rn}::Unknown(_, x_) => {inner},\n        _ => false,\n    }}\n}}\n\n"
        ));
    }
    s.push_str(&format!(
        "#[verifier::rlimit(40)]\n\
         pub fn {rn}_encode(w: &mut BitWriter, v: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({rn}_view(*v)),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {},\n\
         {{\n\
         \x20   match v {{\n",
        ea(&format!("{rn}_enc()"), OLD_POS, &format!("{rn}_view(*v)"))
    ));
    for (j, (_, an, _)) in alts.iter().enumerate() {
        s.push_str(&format!("        {rn}::{an}(_) => {rn}_alt{j}_enc_run(w, v),\n"));
    }
    s.push_str(&format!("        {rn}::Unknown(_, _) => {rn}_unk_enc_run(w, v),\n    }}\n}}\n\n"));

    // --------------------------------------------------------- JER, values
    // the SEQUENCE it came from: the key, then the rest's members
    let kjer = kc.jer.replace("{V}", if byref(&kc) { "k" } else { "&k" }).replace("{O}", "o");
    let mut jbody = format!(
        "    let (k, mut t) = match v {{\n"
    );
    for (kv, an, c) in &alts {
        jbody.push_str(&format!(
            "        {rn}::{an}(x) => {{ let mut t = String::new(); {}; ({kv}i64, t) }}\n",
            c.jer.replace("{V}", "x").replace("{O}", "&mut t")
        ));
    }
    jbody.push_str(&format!(
        "        {rn}::Unknown(k, x) => {{ let mut t = String::new(); {}; ({kclone}, t) }}\n    }};\n",
        uc.jer.replace("{V}", "x").replace("{O}", "&mut t")
    ));
    jbody.push_str(&format!(
        "    o.push_str(\"{{\\\"{key_name}\\\":\");\n\
         \x20   {kjer};\n\
         \x20   if t.len() > 2 {{ o.push(','); o.push_str(&t[1..]); }} else {{ o.push('}}'); }}\n\
         \x20   let _ = &mut t;\n"
    ));
    s.push_str(&jer_fn(&rn, &jbody));
    let mut abody = format!("    match g.pick({}) {{\n", m + if ext { 1 } else { 0 });
    for (j, (_, an, c)) in alts.iter().enumerate() {
        let arm = if j + 1 == m && !ext { "_".to_string() } else { j.to_string() };
        abody.push_str(&format!("        {arm} => {rn}::{an}({}),\n", c.arb.replace("{G}", "g")));
    }
    if ext {
        // a key no object has, if the key's type leaves one
        let fallback = if m > 0 {
            format!("{rn}::{}({})", alts[0].1, alts[0].2.arb.replace("{G}", "g"))
        } else {
            "unreachable!()".into()
        };
        let known = if m == 0 {
            "false".to_string()
        } else {
            alts.iter().map(|(kv, _, _)| format!("k == {kv}i64")).collect::<Vec<_>>().join(" || ")
        };
        abody.push_str(&format!(
            "        _ => {{\n\
             \x20           let mut i = 0;\n\
             \x20           loop {{\n\
             \x20               let k = {};\n\
             \x20               if !({known}) {{ break {rn}::Unknown(k, {}); }}\n\
             \x20               i += 1;\n\
             \x20               if i == 16 {{ break {fallback}; }}\n\
             \x20           }}\n\
             \x20       }}\n",
            kc.arb.replace("{G}", "g"),
            uc.arb.replace("{G}", "g"),
        ));
    }
    abody.push_str("    }\n");
    s.push_str(&arb_fn(&rn, &abody));
    Ok((
        s,
        Compiled {
            jer: format!("{rn}_jer({{V}}, {{O}})"),
            arb: format!("{rn}_arb({{G}})"),
            owner: None,
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
