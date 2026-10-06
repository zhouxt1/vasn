//! A list with a SIZE whose upper bound is below 64K, in the ALIGNED variant:
//! SEQUENCE OF, BIT STRING, OCTET STRING, and a known-multiplier character
//! string's characters (`vasn::aper::list`).
//!
//! The shape is `gen_list_type`'s, with two additions X.691 makes:
//!
//!   * the length, when there is one, is a constrained whole number (11.9.3.3,
//!     11.5.7): UPER's bit-field for a range up to 255, one or two octets,
//!     octet-aligned, above;
//!   * the elements of a string are an octet-aligned field when the string is
//!     wide enough (16.9 to 16.11, 17.6 to 17.8, 30.5.6, 30.5.7), and only
//!     when there is at least one (11.9.3.3). A SEQUENCE OF's never are (20).
use super::*;

/// Whether the elements are an octet-aligned field, by X.691's rule for the
/// kind of list.
pub(super) fn contents_aligned(kind: ListKind, lb: u64, ub: u64) -> bool {
    let fixed = lb == ub;
    match kind {
        // 16.9: a fixed size up to 16 bits is a plain bit-field; 16.10, 16.11
        // otherwise
        ListKind::Bits => !(fixed && ub <= 16),
        // 17.6: a fixed size up to two octets; 17.7, 17.8 otherwise
        ListKind::Octets => !(fixed && ub <= 2),
        // 30.5.6: fixed, aligned above 16 bits; 30.5.7: variable, from 16 on
        ListKind::Chars(b) => {
            let bits = (ub as u128) * (b as u128);
            if fixed { bits > 16 } else { bits >= 16 }
        }
        // 20.5, 20.6: the elements' own fields, never padded as a whole
        ListKind::Of => false,
    }
}

/// The constrained whole number a length `lb..ub` is (11.5.7): its bits, and
/// whether it is octet-aligned.
pub(super) fn length_field(lb: u64, ub: u64) -> (u32, bool) {
    let range = (ub - lb + 1) as u128;
    if range <= 255 {
        (width_for(ub - lb + 1), false)
    } else if range == 256 {
        (8, true)
    } else {
        (16, true)
    }
}

pub(super) fn gen_sized(
    name: &str,
    lb: u64,
    ub: u64,
    elem: Compiled,
    kind: ListKind,
) -> Result<(String, Compiled), Pending> {
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
        .replace("{V}", if ety == "bool" || ety == "u8" || ety == "u16" || ety == "u32" || ety == "i64" || ety == "u64" || ety == "Null" {
            "*x_"
        } else {
            "x_"
        });
    let mut eprefix = String::new();
    for p in &elem.preamble {
        eprefix.push_str(&format!("    proof {{ {p} }}\n"));
    }

    let fixed = lb == ub;
    let al = contents_aligned(kind, lb, ub);
    let (w, a) = length_field(lb, ub);
    let pf = p2_fact(w.max(1));
    // the list, after its length: `alist(al, c, _)`
    let (lwf, lenc, ldec) = if fixed {
        (format!("alist_wf({al}, {lb}, {ewf})"), format!("alist_enc({al}, {lb}, {eenc})"),
         format!("alist_dec({al}, {lb}, {edec})"))
    } else {
        (String::new(), String::new(), String::new())
    };
    let alen_d = format!("alen_dec({lb}, {ub}, {w}, {a})");

    let mut s = String::new();
    s.push_str(&format!("// ---------------------------------------------------------------- {name}\n"));
    s.push_str(&format!("pub type {rn} = Vec<{ety}>;\n\n"));
    if !eplain {
        s.push_str(&format!(
            "pub open spec fn {rn}_lview(s: Seq<{ety}>) -> Seq<{sty}> {{ s.map_values(|x_: {ety}| {xv}) }}\n\n"
        ));
    }

    if fixed {
        s.push_str(&format!(
            "pub open spec fn {rn}_wf() -> Wf<Seq<{sty}>> {{ {lwf} }}\n\
             pub open spec fn {rn}_enc() -> Enc<Seq<{sty}>> {{ {lenc} }}\n\
             pub open spec fn {rn}_dec() -> Dec<Seq<{sty}>> {{ {ldec} }}\n\n\
             pub proof fn {rn}_is_format()\n\
             \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
             {{\n    {}\n    lemma_alist_format({al}, {lb}, {ewf}, {eenc}, {edec});\n}}\n\n",
            elem.proof_call
        ));
    } else {
        s.push_str(&format!(
            "pub open spec fn {rn}_to(t: (u64, Seq<{sty}>)) -> Seq<{sty}> {{ t.1 }}\n\
             pub open spec fn {rn}_from(l: Seq<{sty}>) -> (u64, Seq<{sty}>) {{ (l.len() as u64, l) }}\n\
             pub open spec fn {rn}_to_f() -> spec_fn((u64, Seq<{sty}>)) -> Seq<{sty}> {{ |t: (u64, Seq<{sty}>)| {rn}_to(t) }}\n\
             pub open spec fn {rn}_from_f() -> spec_fn(Seq<{sty}>) -> (u64, Seq<{sty}>) {{ |l: Seq<{sty}>| {rn}_from(l) }}\n\
             pub open spec fn {rn}_full_wf() -> Wf<(u64, Seq<{sty}>)> {{ sized_wf({lb}, {ub}, {w}, {a}, {al}, {ewf}) }}\n\
             pub open spec fn {rn}_full_enc() -> Enc<(u64, Seq<{sty}>)> {{ sized_enc({lb}, {ub}, {w}, {a}, {al}, {eenc}) }}\n\
             pub open spec fn {rn}_full_dec() -> Dec<(u64, Seq<{sty}>)> {{ sized_dec({lb}, {ub}, {w}, {a}, {al}, {edec}) }}\n\
             pub open spec fn {rn}_wf() -> Wf<Seq<{sty}>> {{ map_wf({rn}_full_wf(), {rn}_to_f(), {rn}_from_f()) }}\n\
             pub open spec fn {rn}_enc() -> Enc<Seq<{sty}>> {{ map_enc({rn}_full_enc(), {rn}_from_f()) }}\n\
             pub open spec fn {rn}_dec() -> Dec<Seq<{sty}>> {{ map_dec({rn}_full_dec(), {rn}_to_f()) }}\n\n\
             pub proof fn {rn}_is_format()\n\
             \x20   ensures is_format({rn}_wf(), {rn}_enc(), {rn}_dec()),\n\
             {{\n    {}\n    {pf}\n    vasn::bits::prim_read::lemma_p2_56();\n\
             \x20   lemma_sized_format({lb}, {ub}, {w}, {a}, {al}, {ewf}, {eenc}, {edec});\n\
             \x20   assert forall|t: (u64, Seq<{sty}>)| {rn}_full_wf()(t) implies\n\
             \x20       #[trigger] {rn}_from_f()({rn}_to_f()(t)) == t by {{\n\
             \x20       lemma_dep_wf_val(alen_wf({lb}, {ub}, {w}, {a}), list_wf_f({al}, {ewf}), t.0, t.1);\n\
             \x20       lemma_alist_wf_val({al}, t.0 as nat, {ewf}, t.1);\n\
             \x20   }}\n\
             \x20   lemma_map_format({rn}_full_wf(), {rn}_full_enc(), {rn}_full_dec(),\n\
             \x20                    {rn}_to_f(), {rn}_from_f());\n}}\n\n",
            elem.proof_call
        ));
    }

    // ------------------------------------------------------------ decode
    // What a failure after the length is, up to the whole type's decoder.
    let fail_tail = |what: &str| -> String {
        if fixed {
            String::new()
        } else {
            format!(
                "                   lemma_dep_dec_none_snd({alen_d}, list_dec_f({al}, {edec}),\n\
                 \x20                                         start, c_, klen, Flg::SameVer);\n\
                 \x20                  lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n{what}"
            )
        }
    };
    // a BIT or OCTET STRING's (the bulk read): twice the default rlimit;
    // once its module's encoder took the bulk write, `tests/aper`'s
    // `alignment` `E1.s` decoder went over, its own text unchanged
    let dec_rl = match (elem.fmt.as_str(), eplain) {
        ("bool", true) | ("byte", true) => "#[verifier::rlimit(20)]\n",
        _ => "",
    };
    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         {dec_rl}pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v_, f_)) => {rn}_dec()(old(r).at())\n\
         \x20               == Some::<(Seq<{sty}>, nat, Flg)>(({},\n\
         \x20                                                 (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => {rn}_dec()(old(r).at()).is_none(),\n\
         \x20       }},\n\
         {{\n{eprefix}\
         \x20   let ghost start = old(r).at();\n\
         \x20   let ghost p0 = old(r).pos;\n",
        lv("v_@")
    ));
    if fixed {
        s.push_str(&format!("    let c_: u64 = {lb};\n"));
    } else {
        s.push_str(&format!(
            "    proof {{ {pf} vasn::bits::prim_read::lemma_p2_56(); }}\n\
             \x20   let c_ = match r.read_alen({lb}, {ub}, {w}, {a}) {{\n\
             \x20       Some(v_) => v_,\n\
             \x20       None => {{\n\
             \x20           proof {{\n\
             \x20               lemma_dep_dec_none_fst({alen_d}, list_dec_f({al}, {edec}), start);\n\
             \x20               lemma_map_dec_none({rn}_full_dec(), {rn}_to_f(), start);\n\
             \x20           }}\n\
             \x20           {{ r.fail(\"SIZE ({lb}..{ub}) length\"); return None; }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   proof {{ lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat); }}\n"
        ));
    }
    // `i1`: where the elements' field starts, before any padding; `body`:
    // where the first element does
    s.push_str(&format!(
        "    let ghost klen = {};\n\
         \x20   let ghost i1 = r.at();\n\
         \x20   let ghost p1 = r.pos;\n\
         \x20   proof {{ assert(i1 == adv(start, klen)); }}\n",
        if fixed { "0nat" } else { "(r.pos - p0) as nat" }
    ));
    if al {
        s.push_str(&format!(
            "    if c_ > 0 {{\n\
             \x20       if !r.read_align() {{\n\
             \x20           proof {{\n\
             \x20               lemma_alist_dec_misaligned({al}, c_ as nat, {edec}, i1);\n{}\
             \x20           }}\n\
             \x20           {{ r.fail(\"padding\"); return None; }}\n\
             \x20       }}\n\
             \x20   }}\n\
             \x20   proof {{ lemma_rem_skip(r.buf@, p1 as nat, (r.pos - p1) as nat); }}\n",
            fail_tail("")
        ));
    }
    // a BIT STRING's bits or an OCTET STRING's octets, all there: one bulk
    // read (vasn::aper::fast); otherwise element by element, which says
    // where the input ran out
    let bulk = match (elem.fmt.as_str(), eplain) {
        ("bool", true) | ("byte", true) => {
            let (rd, need) = if elem.fmt == "bool" {
                ("read_abit_list", "(c_ as usize) <= left_")
            } else {
                ("read_aoctet_list", "8 * (c_ as usize) <= left_")
            };
            format!(
                "    let bulk_: bool = {need};\n\
                 \x20   let mut out_: Vec<{ety}> = if bulk_ {{ r.{rd}(c_ as usize) }} else {{\n\
                 \x20       Vec::with_capacity(if (c_ as usize) < left_ {{ c_ as usize }} else {{ left_ }})\n\
                 \x20   }};\n\
                 \x20   let mut i_: u64 = if bulk_ {{ c_ }} else {{ 0 }};\n\
                 \x20   proof {{\n\
                 \x20       if bulk_ {{\n\
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
        "    let ghost kal = (r.pos - p1) as nat;\n\
         \x20   let ghost body = r.at();\n\
         \x20   let ghost p2 = r.pos;\n\
         \x20   proof {{\n\
         \x20       assert(body == adv(i1, kal));\n\
         \x20       lemma_alist_dec_val({al}, c_ as nat, {edec}, i1, kal);\n\
         \x20   }}\n\
         \x20   // sized from the count, but never past one element per bit left,\n\
         \x20   // so a hostile count cannot make a short input allocate much\n\
         \x20   let left_: usize = r.buf.len() * 8 - r.pos;\n\
         {bulk}\
         \x20   let mut fa_: Flg = Flg::SameVer;\n\
         \x20   while i_ < c_\n\
         \x20       invariant\n\
         \x20           r.wf(), r.buf == old(r).buf, r.pos >= p2, p2 >= p1, p1 >= p0,\n\
         \x20           p0 == old(r).pos, start == old(r).at(),\n\
         \x20           i1 == adv(start, klen), body == adv(i1, kal), p0 + klen == p1, p1 + kal == p2,\n\
         \x20           alist_dec({al}, c_ as nat, {edec})(i1) == (match list_dec_rec(c_ as nat, {edec}, body) {{\n\
         \x20               Some((l, k, f)) => Some((l, (kal + k) as nat, f)),\n\
         \x20               None => None,\n\
         \x20           }}),\n\
         \x20           out_@.len() == i_, i_ <= c_,\n\
         \x20           list_dec_rec(c_ as nat, {edec}, body)\n\
         \x20               == list_cont({ov}, (r.pos - p2) as nat, fa_,\n\
         \x20                            list_dec_rec((c_ - i_) as nat, {edec}, r.at())),\n\
         \x20       decreases c_ - i_,\n\
         \x20   {{\n\
         \x20       let ghost bi = r.at();\n\
         \x20       let ghost pi = r.pos;\n\
         \x20       let (x_, fx_) = match {edecode} {{\n\
         \x20           Some(vf_) => vf_,\n\
         \x20           None => {{\n\
         \x20               proof {{\n\
         \x20                   lemma_list_loop_fail(c_ as nat, {edec}, body, {ov},\n\
         \x20                                        (pi - p2) as nat, fa_, (c_ - i_) as nat, bi);\n\
         {}\
         \x20               }}\n\
         \x20               {{ r.fail_at(i_); return None; }}\n\
         \x20           }}\n\
         \x20       }};\n\
         \x20       let ghost sx_ = {xv};\n\
         \x20       let ghost ov_ = {ov};\n\
         \x20       proof {{\n\
         \x20           lemma_rem_skip(r.buf@, pi as nat, (r.pos - pi) as nat);\n\
         \x20           lemma_list_loop_step(c_ as nat, {edec}, body, ov_, (pi - p2) as nat, fa_,\n\
         \x20                                (c_ - i_) as nat, bi, sx_, (r.pos - pi) as nat, fx_);\n\
         \x20       }}\n\
         \x20       out_.push(x_);\n\
         \x20       proof {{ assert({ov} =~= ov_.push(sx_)); }}\n\
         \x20       fa_ = flg_join(fa_, fx_);\n\
         \x20       i_ = i_ + 1;\n\
         \x20   }}\n\
         \x20   proof {{\n\
         \x20       lemma_list_loop_done(c_ as nat, {edec}, body, {ov}, (r.pos - p2) as nat, fa_,\n\
         \x20                            r.at());\n",
        fail_tail(""),
        ov = lv("out_@")
    ));
    if !fixed {
        s.push_str(&format!(
            "        lemma_dep_dec_some({alen_d}, list_dec_f({al}, {edec}),\n\
             \x20                       start, c_, klen, Flg::SameVer, {ov}, (r.pos - p1) as nat, fa_);\n\
             \x20   lemma_map_dec_some({rn}_full_dec(), {rn}_to_f(), start, (c_, {ov}),\n\
             \x20                      (r.pos - p0) as nat, fa_);\n",
            ov = lv("out_@")
        ));
    }
    s.push_str("    }\n    Some((out_, fa_))\n}\n\n");

    // ------------------------------------------------------------ encode
    // Twice the default rlimit: these run close to it. Once the decoder took
    // the bulk read and the sized `Vec`, NR's
    // `AvailabilityIndicator-r16.availableCombToAddModList-r16` encoder went
    // over though its text had not changed, and in a solver of its own
    // (`spinoff_prover`) `RF-Parameters.supportedBandListNR`'s did. And the
    // loop's `take`/`push` equality is proved apart (below): inline,
    // `IAB-IP-AddressAndTraffic-r16`'s went over at 100 after its module's
    // other queries, though alone it took a second. 40: NGAP's
    // ProtocolExtensionContainer {PDUSessionResourceModifyIndicationTransfer-ExtIEs}'s
    // went over at 20, and at 100 after its module's other queries, though
    // alone it took a second: its loop's invariant is an `==`, each step
    // proved by `lemma_list_enc_step`, and it then took under 3.
    let lvl = lv("l@");
    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         #[verifier::rlimit(40)]\n\
         pub fn {rn}_encode(w: &mut BitWriter, l: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({lvl}),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {rn}_enc()(old(w).pos as nat, {lvl}),\n\
         {{\n{eprefix}\
         \x20   let ghost p0 = w.pos as nat;\n"
    ));
    if !fixed {
        s.push_str(&format!(
            "    proof {{\n\
             \x20       {pf}\n\
             \x20       vasn::bits::prim_read::lemma_p2_56();\n\
             \x20       lemma_dep_wf_val(alen_wf({lb}, {ub}, {w}, {a}), list_wf_f({al}, {ewf}), {lvl}.len() as u64, {lvl});\n\
             \x20       lemma_alen_wf_bound({lb}, {ub}, {w}, {a}, {lvl}.len() as u64);\n\
             \x20       lemma_alist_wf_val({al}, {lvl}.len(), {ewf}, {lvl});\n\
             \x20   }}\n\
             \x20   if !w.write_alen({lb}, {ub}, {w}, {a}, l.len() as u64) {{ return false; }}\n"
        ));
    } else {
        s.push_str(&format!("    proof {{ lemma_alist_wf_val({al}, {lb}, {ewf}, {lvl}); }}\n"));
    }
    s.push_str("    let ghost w1 = w.written();\n    let ghost pa = w.pos as nat;\n");
    if al {
        s.push_str("    if l.len() > 0 {\n        if !w.write_align() { return false; }\n    }\n");
    }
    // a BIT STRING's bits or an OCTET STRING's octets: one bulk write
    // (vasn::aper::fast) rather than one per element
    let bulk_wr = match (elem.fmt.as_str(), eplain) {
        ("bool", true) => Some("write_abit_list"),
        ("byte", true) => Some("write_aoctet_list"),
        _ => None,
    };
    if let Some(wr) = bulk_wr {
        s.push_str(&format!(
            "    proof {{ lemma_alist_enc_val({al}, {lvl}.len(), {eenc}, pa, {lvl}); }}\n\
             \x20   if !w.{wr}(l) {{ return false; }}\n\
             \x20   true\n}}\n\n"
        ));
    } else {
    s.push_str(&format!(
        "    let ghost mid = w.written();\n\
         \x20   let ghost pm = w.pos as nat;\n\
         \x20   proof {{ lemma_alist_enc_val({al}, {lvl}.len(), {eenc}, pa, {lvl}); }}\n\
         \x20   let mut j_: usize = 0;\n\
         \x20   while j_ < l.len()\n\
         \x20       invariant\n\
         \x20           w.wf(), j_ <= l@.len(), w.buf@.len() == old(w).buf@.len(),\n\
         \x20           w.written() == mid + list_enc_rec(pm, {lvl}.take(j_ as int), {eenc}),\n\
         \x20           pm == mid.len(),\n\
         \x20       decreases l@.len() - j_,\n\
         \x20   {{\n\
         \x20       let ghost pre = {lvl}.take(j_ as int);\n\
         \x20       let x_ = &l[j_];\n\
         {xfact}\
         \x20       let ghost wo = w.written();\n\
         \x20       if !{eencode} {{ return false; }}\n\
         \x20       proof {{\n\
         \x20           lemma_list_enc_step(mid, pm, pre, {eenc}, {lvl}[j_ as int], wo, w.written());\n\
         \x20           // proved apart: inline, the extensionality could take the\n\
         \x20           // whole rlimit, depending on the queries before it\n\
         \x20           assert({lvl}.take(j_ as int + 1) == pre.push({lvl}[j_ as int])) by {{\n\
         \x20               assert({lvl}.take(j_ as int + 1) =~= pre.push({lvl}[j_ as int]));\n\
         \x20           }}\n\
         \x20       }}\n\
         \x20       j_ = j_ + 1;\n\
         \x20   }}\n\
         \x20   proof {{ assert({lvl}.take({lvl}.len() as int) =~= {lvl}); }}\n\
         \x20   true\n}}\n\n",
        xfact = if eplain { String::new() } else {
            format!("\x20       proof {{ assert({xvr} == {}[j_ as int]); }}\n", lv("l@"))
        }
    ));
    }

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

/// A list with no upper bound, or one of 64K or more (11.9.3.5 to 11.9.3.8):
/// `gen_list_frag` over `vasn::aper::fraglist`, every head octet-aligned.
pub(super) fn gen_frag(name: &str, lb: u64, ub: u64, elem: Compiled, kind: ListKind) -> (String, Compiled) {
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
        .replace("{V}", if ety == "bool" || ety == "u8" || ety == "u16" || ety == "u32" || ety == "i64" || ety == "u64" || ety == "Null" {
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
    s.push_str(&format!("// ---------------------------------------------------------------- {name}\n"));
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
         \x20           Some(f_) => list_dec_rec(c_ as nat, {edec}, old(r).at())\n\
         \x20               == Some::<(Seq<{sty}>, nat, Flg)>(({lout}.skip(old(out_)@.len() as int),\n\
         \x20                                                 (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => list_dec_rec(c_ as nat, {edec}, old(r).at()).is_none(),\n\
         \x20       }},\n\
         {{\n{eprefix}\
         \x20   let ghost body = old(r).at();\n\
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
         \x20           body == old(r).at(), o0 == {lold}, n0 == o0.len(),\n\
         \x20           out_@.len() == n0 + i_, i_ <= c_,\n\
         \x20           {lho}.take(n0 as int) == o0,\n\
         \x20           list_dec_rec(c_ as nat, {edec}, body)\n\
         \x20               == list_cont({lho}.skip(n0 as int), (r.pos - p1) as nat, fa_,\n\
         \x20                            list_dec_rec((c_ - i_) as nat, {edec}, r.at())),\n\
         \x20       decreases c_ - i_,\n\
         \x20   {{\n\
         \x20       let ghost bi = r.at();\n\
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
         \x20                            (r.pos - p1) as nat, fa_, r.at());\n\
         \x20   }}\n\
         \x20   Some(fa_)\n\
         }}\n\n"
    ));

    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         pub fn {rn}_decode(r: &mut BitReader) -> (res: Option<({rn}, Flg)>)\n\
         \x20   requires old(r).wf(),\n\
         \x20   ensures final(r).wf(), final(r).buf == old(r).buf, final(r).pos >= old(r).pos,\n\
         \x20       match res {{\n\
         \x20           Some((v_, f_)) => {rn}_dec()(old(r).at())\n\
         \x20               == Some::<(Seq<{sty}>, nat, Flg)>(({v},\n\
         \x20                                                 (final(r).pos - old(r).pos) as nat, f_)),\n\
         \x20           None => {rn}_dec()(old(r).at()).is_none(),\n\
         \x20       }},\n\
         {{\n{eprefix}\
         \x20   let ghost start = old(r).at();\n\
         \x20   let ghost p0 = old(r).pos;\n\
         \x20   let mut out_: Vec<{ety}> = Vec::new();\n\
         \x20   let mut fa_: Flg = Flg::SameVer;\n\
         \x20   let mut pending_: bool = false;\n\
         \x20   proof {{\n\
         \x20       lemma_flist_loop_start({edec}, start);\n\
         \x20       assert({lho} =~= Seq::<{sty}>::empty());\n\
         \x20       lemma_flist_dec_val({edec}, start);\n\
         \x20       assert(adv(start, 0) =~= start);\n\
         \x20   }}\n\
         \x20   loop\n\
         \x20       invariant\n\
         \x20           r.wf(), r.buf == old(r).buf, p0 == old(r).pos, start == old(r).at(),\n\
         \x20           r.pos >= p0,\n\
         \x20           r.at() == adv(start, (r.pos - p0) as nat),\n\
         \x20           (r.pos - p0) + r.at().1.len() == start.1.len(),\n\
         \x20           flist_dec({edec})(start) == flist_dec_rec({edec}, start),\n\
         \x20           flist_dec_rec({edec}, start)\n\
         \x20               == flist_cont({lho}, (r.pos - p0) as nat, fa_, pending_,\n\
         \x20                             flist_dec_rec({edec}, r.at())),\n\
         \x20       decreases 8 * r.buf@.len() - r.pos,\n\
         \x20   {{\n\
         \x20       let ghost cur = r.at();\n\
         \x20       let ghost consumed = (r.pos - p0) as nat;\n\
         \x20       let ghost acc = {lho};\n\
         \x20       let ph = r.pos;\n\
         \x20       let h = match r.read_alh() {{\n\
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
         \x20           lemma_lha_dec_facts(cur);\n\
         \x20           lemma_lh_wf_iff(h);\n\
         \x20           lemma_rem_skip(r.buf@, ph as nat, (r.pos - ph) as nat);\n\
         \x20       }}\n\
         \x20       let ghost k = (r.pos - ph) as nat;\n\
         \x20       let (c_, last_) = match h {{\n\
         \x20           LenHead::Final(n) => (n, true),\n\
         \x20           LenHead::Frag(m) => {{\n\
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
         \x20       let ghost atc = r.at();\n\
         \x20       proof {{ assert(atc == adv(cur, k)); }}\n\
         \x20       let fx_ = match {rn}_frag_dec(r, &mut out_, c_) {{\n\
         \x20           Some(f) => f,\n\
         \x20           None => {{\n\
         \x20               proof {{\n\
         \x20                   lemma_flist_loop_fail({edec}, start, cur, acc, consumed, fa_, pending_);\n\
         \x20                   lemma_restrict_dec_none(flist_dec({edec}), flist_ok({lb}, {ub}), start);\n\
         \x20               }}\n\
         \x20               return None;\n\
         \x20           }}\n\
         \x20       }};\n\
         \x20       let ghost l1 = {lho}.skip(acc.len() as int);\n\
         \x20       let ghost k1 = (r.pos - pc) as nat;\n\
         \x20       proof {{\n\
         \x20           assert({lho} =~= acc + l1);\n\
         \x20           lemma_rem_skip(r.buf@, p0 as nat, (r.pos - p0) as nat);\n\
         \x20           assert(k + k1 <= cur.1.len());\n\
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

    s.push_str(&format!(
        "#[verifier::loop_isolation(false)]\n\
         pub fn {rn}_frag_enc(w: &mut BitWriter, l: &{rn}, from: usize, cnt: usize) -> (ok: bool)\n\
         \x20   requires old(w).wf(), from + cnt <= l@.len(),\n\
         \x20       forall|i: int| 0 <= i < {lo}.len() ==> #[trigger] {ewf}({lo}[i]),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written()\n\
         \x20           =~= old(w).written() + list_enc_rec(old(w).pos as nat, {lo}.subrange(from as int, (from + cnt) as int), {eenc}),\n\
         {{\n{eprefix}\
         \x20   let ghost mid = w.written();\n\
         \x20   let ghost pm = w.pos as nat;\n\
         \x20   let n_ = l.len();\n\
         \x20   let end_ = from + cnt;\n\
         \x20   let mut j_: usize = from;\n\
         \x20   proof {{ assert({lo}.subrange(from as int, from as int) =~= Seq::<{sty}>::empty()); }}\n\
         \x20   while j_ < end_\n\
         \x20       invariant\n\
         \x20           w.wf(), from <= j_ <= end_, end_ == from + cnt, from + cnt <= l@.len(),\n\
         \x20           w.buf@.len() == old(w).buf@.len(), pm == mid.len(),\n\
         \x20           w.written() =~= mid + list_enc_rec(pm, {lo}.subrange(from as int, j_ as int), {eenc}),\n\
         \x20       decreases end_ - j_,\n\
         \x20   {{\n\
         \x20       let ghost pre = {lo}.subrange(from as int, j_ as int);\n\
         \x20       let x_ = &l[j_];\n\
         {xfact}\
         \x20       proof {{ assert({ewf}({lo}[j_ as int])); }}\n\
         \x20       if !{eencode} {{ return false; }}\n\
         \x20       proof {{\n\
         \x20           lemma_list_enc_push(pm, pre, {eenc}, {lo}[j_ as int]);\n\
         \x20           assert({lo}.subrange(from as int, j_ as int + 1) =~= pre.push({lo}[j_ as int]));\n\
         \x20       }}\n\
         \x20       j_ = j_ + 1;\n\
         \x20   }}\n\
         \x20   true\n\
         }}\n\n\
         // The loop isolated (Verus's default), unlike the other loops here:\n\
         // its invariant carries all the rest needs, and as one query with\n\
         // what follows it ETSI ITS's ReferenceDenms went over the rlimit even\n\
         // at 10x; isolated it takes 3M.\n\
         pub fn {rn}_encode(w: &mut BitWriter, l: &{rn}) -> (ok: bool)\n\
         \x20   requires old(w).wf(), {rn}_wf()({lo}),\n\
         \x20   ensures final(w).wf(), final(w).buf@.len() == old(w).buf@.len(),\n\
         \x20       ok ==> final(w).written() =~= old(w).written() + {rn}_enc()(old(w).pos as nat, {lo}),\n\
         {{\n{eprefix}\
         \x20   let ghost s = {lo};\n\
         \x20   let ghost w0 = w.written();\n\
         \x20   let ghost p0 = w.pos as nat;\n\
         \x20   proof {{\n\
         \x20       lemma_restrict_wf_val(flist_wf({ewf}), flist_ok({lb}, {ub}), s);\n\
         \x20       lemma_flist_wf_val({ewf}, s);\n\
         \x20       lemma_flist_enc_val({eenc}, p0, s);\n\
         \x20       assert(s.skip(0) =~= s);\n\
         \x20   }}\n\
         \x20   let n = l.len();\n\
         \x20   let mut off: usize = 0;\n\
         \x20   while n - off >= 16384\n\
         \x20       invariant\n\
         \x20           w.wf(), w.buf@.len() == old(w).buf@.len(),\n\
         \x20           off <= n, n == l@.len(), s == {lo}, s.len() == n,\n\
         \x20           w0.len() == p0, w.written().len() >= w0.len(),\n\
         \x20           forall|i: int| 0 <= i < s.len() ==> #[trigger] {ewf}(s[i]),\n\
         \x20           w.written() + flist_enc_rec(w.pos as nat, s.skip(off as int), {eenc}) =~= w0 + flist_enc_rec(p0, s, {eenc}),\n\
         \x20       decreases n - off,\n\
         \x20   {{\n\
         \x20       let left = n - off;\n\
         \x20       let m: usize = if left / 16384 >= 4 {{ 4 }} else {{ left / 16384 }};\n\
         \x20       let ghost before = w.written();\n\
         \x20       let ghost pb = w.pos as nat;\n\
         \x20       // only the arithmetic: the equation is `lemma_flist_enc_loop_step`'s\n\
         \x20       proof {{\n\
         \x20           lemma_written_len(*w);\n\
         \x20           lemma_frag_len_ge(left as nat);\n\
         \x20           lemma_lh_wf_iff(LenHead::Frag(m as u64));\n\
         \x20       }}\n\
         \x20       if !w.write_alh(LenHead::Frag(m as u64)) {{ return false; }}\n\
         \x20       if !{rn}_frag_enc(w, l, off, m * 16384) {{ return false; }}\n\
         \x20       proof {{\n\
         \x20           lemma_flist_enc_loop_step(before, w.written(), w0, p0, pb, s, {eenc}, off as nat, m as nat);\n\
         \x20       }}\n\
         \x20       off = off + m * 16384;\n\
         \x20   }}\n\
         \x20   let ghost before = w.written();\n\
         \x20   let ghost pb = w.pos as nat;\n\
         \x20   proof {{\n\
         \x20       lemma_written_len(*w);\n\
         \x20       lemma_lh_wf_iff(LenHead::Final((n - off) as u64));\n\
         \x20   }}\n\
         \x20   if !w.write_alh(LenHead::Final((n - off) as u64)) {{ return false; }}\n\
         \x20   if !{rn}_frag_enc(w, l, off, n - off) {{ return false; }}\n\
         \x20   proof {{\n\
         \x20       lemma_flist_enc_loop_last(before, w.written(), w0, p0, pb, s, {eenc}, off as nat);\n\
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
