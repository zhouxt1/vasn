//! `vasnc --stats schema.asn1` — what actually appears where, measured on the
//! real schemas instead of guessed at.
use crate::ast::*;
use std::collections::BTreeMap;

#[derive(Default)]
pub struct Stats {
    pub field_kind: BTreeMap<String, usize>,
    pub presence: BTreeMap<String, usize>,
    pub top_kind: BTreeMap<String, usize>,
    pub seq_width: BTreeMap<usize, usize>,
    pub opt_count: BTreeMap<usize, usize>,
    pub choice_width: BTreeMap<usize, usize>,
    pub int_width: BTreeMap<String, usize>,
    pub size_cons: BTreeMap<String, usize>,
    /// extension additions by kind: one component or a group, and presence
    pub additions: BTreeMap<String, usize>,
    /// the mandatory single additions, `Type.component`
    pub mandatory_adds: Vec<String>,
}

fn bucket(n: usize) -> usize {
    match n {
        0..=1 => n,
        2..=4 => 4,
        5..=8 => 8,
        9..=16 => 16,
        17..=32 => 32,
        _ => 64,
    }
}

fn size_label(sc: &SizeCons) -> String {
    match sc {
        SizeCons::None => "unconstrained".into(),
        SizeCons::Fixed(Num::Lit(_)) => "SIZE (n) literal".into(),
        SizeCons::Fixed(Num::Ref(_)) => "SIZE (n) value ref".into(),
        SizeCons::Fixed(Num::Big(_)) => "SIZE (n) beyond 64 bits".into(),
        SizeCons::Range(Num::Lit(_), Num::Lit(_)) => "SIZE (lb..ub) literal".into(),
        SizeCons::Range(_, _) => "SIZE (lb..ub) value ref".into(),
        SizeCons::RangeExt(_, _) => "SIZE (lb..ub, ...) extensible".into(),
        SizeCons::Semi(_) => "SIZE (lb..MAX)".into(),
        SizeCons::SemiExt(_) => "SIZE (lb..MAX, ...) extensible".into(),
    }
}

fn kind(t: &Type) -> String {
    match t {
        Type::Boolean => "BOOLEAN".into(),
        Type::Null => "NULL".into(),
        Type::Never => "(recursion cut off)".into(),
        Type::ObjectId => "OBJECT IDENTIFIER".into(),
        Type::RelativeOid => "RELATIVE-OID".into(),
        Type::Real => "REAL".into(),
        Type::Integer(IntCons::Range(_, _)) => "INTEGER (lb..ub)".into(),
        Type::Integer(IntCons::RangeExt(_, _)) => "INTEGER (lb..ub, ...)".into(),
        Type::Integer(IntCons::Fixed(_)) => "INTEGER (n)".into(),
        Type::Integer(IntCons::None) => "INTEGER unconstrained".into(),
        Type::Integer(IntCons::Semi(_)) => "INTEGER (lb..MAX)".into(),
        Type::Integer(IntCons::SemiExt(_) | IntCons::NoneExt) => "INTEGER, extensible, semi- or unconstrained".into(),
        Type::Integer(IntCons::U64) => "INTEGER (0..18446744073709551615)".into(),
        Type::Enumerated(_, None) => "ENUMERATED inline".into(),
        Type::Enumerated(_, _) => "ENUMERATED inline, extensible".into(),
        Type::BitString(_) => "BIT STRING".into(),
        Type::NamedBitString(_) => "BIT STRING, named bits".into(),
        Type::OctetString(_) => "OCTET STRING".into(),
        Type::Str(..) => "character string".into(),
        Type::Sequence(_, None) => "SEQUENCE inline".into(),
        // groups are counted apart: `[[ ... ]]` is one extension addition, not
        // one per field, so it needs its own handling in the backend
        Type::Sequence(_, Some(e)) if e.iter().any(|x| matches!(x, ExtAdd::Group(_))) => {
            "SEQUENCE inline, extensible with [[ group ]]".into()
        }
        Type::Sequence(_, Some(_)) => "SEQUENCE inline, extensible".into(),
        Type::Choice(_, None) => "CHOICE inline".into(),
        Type::Choice(_, Some(_)) => "CHOICE inline, extensible".into(),
        Type::SequenceOf(_, _) => "SEQUENCE OF inline".into(),
        Type::Ref(_) => "reference to a named type".into(),
        Type::ParamRef(_, _) => "parameterised reference".into(),
        Type::ClassField { .. } => "information object class field (unresolved)".into(),
        Type::Dispatch { .. } => "open type, by a component relation constraint".into(),
        Type::Keyed { .. } => "SEQUENCE keyed by a component relation constraint".into(),
        Type::Constrained(..) => "constrained (unresolved)".into(),
        Type::Invalid(_) => "invalid".into(),
        Type::EnumeratedNum(..) => "ENUMERATED, numbered".into(),
        Type::Tagged(..) => "tagged".into(),
        Type::Set(..) | Type::SetOf(..) => "SET (unresolved)".into(),
        Type::Contains(_) => "OCTET STRING (CONTAINING T), decoded".into(),
        Type::Open(_) => "open type, of a known type".into(),
    }
}

fn walk_in(owner: &str, t: &Type, st: &mut Stats) {
    let walk = |t: &Type, st: &mut Stats| walk_in(owner, t, st);
    match t {
        Type::Sequence(root, ext) => {
            for a in ext.iter().flatten() {
                let k = match a {
                    ExtAdd::Group(g) if g.iter().any(|f| f.presence == Presence::Mandatory) => {
                        let m: Vec<&str> = g.iter().filter(|f| f.presence == Presence::Mandatory).map(|f| f.name.as_str()).collect();
                        st.mandatory_adds.push(format!("{owner}: [[ ]] with {}", m.join(", ")));
                        "[[ group ]] with a mandatory component"
                    }
                    ExtAdd::Group(_) => "[[ group ]], every component OPTIONAL or DEFAULT",
                    ExtAdd::One(f) => match &f.presence {
                        Presence::Mandatory => {
                            st.mandatory_adds.push(format!("{owner}.{}", f.name));
                            "one component, mandatory"
                        }
                        Presence::Optional => "one component, OPTIONAL",
                        Presence::Default(_) => "one component, DEFAULT",
                    },
                };
                *st.additions.entry(k.into()).or_default() += 1;
            }
            let all: Vec<&Field> =
                root.iter().chain(ext.iter().flatten().flat_map(ExtAdd::fields)).collect();
            *st.seq_width.entry(bucket(all.len())).or_default() += 1;
            let mut nopt = 0;
            for f in &all {
                *st.field_kind.entry(kind(&f.ty)).or_default() += 1;
                let p = match &f.presence {
                    Presence::Mandatory => "mandatory",
                    Presence::Optional => "OPTIONAL",
                    Presence::Default(_) => "DEFAULT",
                };
                if p != "mandatory" {
                    nopt += 1;
                }
                *st.presence.entry(p.into()).or_default() += 1;
                walk(&f.ty, st);
            }
            *st.opt_count.entry(bucket(nopt)).or_default() += 1;
        }
        Type::Choice(root, ext) => {
            let all: Vec<&(String, Type)> = root.iter().chain(ext.iter().flatten()).collect();
            *st.choice_width.entry(bucket(all.len())).or_default() += 1;
            for (_, a) in all {
                walk(a, st);
            }
        }
        Type::SequenceOf(sc, inner) => {
            *st.size_cons.entry(format!("SEQUENCE OF {}", size_label(sc))).or_default() += 1;
            walk(inner, st);
        }
        Type::BitString(sc) => {
            *st.size_cons.entry(format!("BIT STRING {}", size_label(sc))).or_default() += 1;
        }
        Type::OctetString(sc) => {
            *st.size_cons.entry(format!("OCTET STRING {}", size_label(sc))).or_default() += 1;
        }
        Type::Integer(IntCons::Range(a, b)) => {
            if let (Num::Lit(a), Num::Lit(b)) = (a, b) {
                let span = (*b as i128) - (*a as i128) + 1;
                let mut w = 0u32;
                while (1i128 << w) < span {
                    w += 1;
                }
                let label = match w {
                    0..=8 => "<= 8 bits",
                    9..=16 => "9..16 bits",
                    17..=32 => "17..32 bits",
                    33..=56 => "33..56 bits",
                    _ => "> 56 bits (unsupported width)",
                };
                *st.int_width.entry(label.into()).or_default() += 1;
            } else {
                *st.int_width.entry("bound is a value reference".into()).or_default() += 1;
            }
        }
        _ => {}
    }
}

fn show(title: &str, m: &BTreeMap<String, usize>) {
    let total: usize = m.values().sum();
    println!("\n{title}  (total {total})");
    let mut v: Vec<(&String, &usize)> = m.iter().collect();
    v.sort_by(|a, b| b.1.cmp(a.1));
    for (k, n) in v {
        println!("  {n:6}  {k}");
    }
}

fn show_n(title: &str, m: &BTreeMap<usize, usize>) {
    println!("\n{title}");
    for (k, n) in m {
        println!("  {n:6}  <= {k}");
    }
}

pub fn report(module: &Module) {
    let mut st = Stats::default();
    for a in &module.assignments {
        if let Assignment::Type { name, ty } = a {
            *st.top_kind.entry(kind(ty)).or_default() += 1;
            walk_in(name, ty, &mut st);
        }
    }
    show("top-level type assignments", &st.top_kind);
    show("types appearing as a SEQUENCE field", &st.field_kind);
    show("field presence markers", &st.presence);
    show("constrained INTEGER widths", &st.int_width);
    show("size constraints on list-like types", &st.size_cons);
    show_n("SEQUENCE field counts", &st.seq_width);
    show_n("OPTIONAL+DEFAULT fields per SEQUENCE", &st.opt_count);
    show_n("CHOICE alternative counts", &st.choice_width);
    show("SEQUENCE extension additions", &st.additions);
    if !module.dispatch.is_empty() {
        let mut by: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        let mut biggest: Vec<(usize, String)> = Vec::new();
        for ((set, field), t) in &module.dispatch {
            let k = match (t.alts.len(), t.ext) {
                (0, true) => "no objects, extensible (every key kept as octets)".to_string(),
                (0, false) => "no objects, not extensible (nothing decodes)".to_string(),
                (_, true) => "objects, extensible".to_string(),
                (_, false) => "objects, not extensible".to_string(),
            };
            *by.entry(k).or_default() += 1;
            biggest.push((t.alts.len(), format!("{set}.&{field}")));
        }
        println!("\nopen types selected by a component relation constraint  (total {})", module.dispatch.len());
        for (k, n) in &by {
            println!("  {n:6}  {k}");
        }
        biggest.sort();
        for (n, s) in biggest.iter().rev().take(5) {
            println!("  largest: {s}, {n} objects");
        }
    }
    if !st.mandatory_adds.is_empty() {
        println!("\nmandatory additions, alone or in a group:");
        for m in &st.mandatory_adds {
            println!("  {m}");
        }
    }
}
