//! Information object classes (X.681), the object sets built from them, and
//! the table and component relation constraints that use them (X.682 10),
//! elaborated away before anything else looks at the types.
//!
//! The 3GPP application protocols (NGAP, F1AP, E1AP, XnAP, S1AP, X2AP) all
//! use one pattern:
//!
//! ```asn1
//! ProtocolIE-Field {NGAP-PROTOCOL-IES : IEsSetParam} ::= SEQUENCE {
//!     id          NGAP-PROTOCOL-IES.&id          ({IEsSetParam}),
//!     criticality NGAP-PROTOCOL-IES.&criticality ({IEsSetParam}{@id}),
//!     value       NGAP-PROTOCOL-IES.&Value       ({IEsSetParam}{@id})
//! }
//! ```
//!
//! After `normalize::expand_params` has substituted an object set for
//! `IEsSetParam`, this pass replaces each `CLASS.&field`:
//!
//! * a fixed-type value field (`&id`, `&criticality`) by its type. A table
//!   constraint on one is never PER-visible (X.691 10.3.4, 10.3.5), so the
//!   value is not checked against the set: an `id` no object has is a newer
//!   peer's, and a `criticality` other than the object's is the receiver's
//!   business (TS 38.413 10.3.4), not the decoder's;
//! * a type field (`&Value`) under `({Set}{@key})` by a `Type::Dispatch`:
//!   an open type (X.691 11.2) whose content is a value of the type the
//!   object with that key gives. The table it selects from is in
//!   `Module::dispatch`;
//! * a type field under no component relation constraint by an open type,
//!   which PER encodes as an unconstrained OCTET STRING is (11.2).
use crate::ast::*;
use crate::lexer::Tok;
use crate::parser::Parser;
use std::collections::HashMap;

/// A field's setting in one object (X.681 11.7).
#[derive(Debug, Clone)]
enum Setting {
    Type(Type),
    /// a value, as written: an integer or a reference
    Value(Tok),
}

type Object = HashMap<String, Setting>;

struct Class {
    fields: Vec<ClassField>,
    syntax: Option<Vec<SynItem>>,
}

struct Ctx<'a> {
    classes: HashMap<String, Class>,
    objects: HashMap<String, (&'a str, &'a [Tok])>,
    sets: HashMap<String, (&'a str, &'a [Tok])>,
    values: HashMap<String, i64>,
}

/// Elaborate every class field away (see the module comment). Returns how
/// many dispatch tables were built.
pub fn elaborate(module: &mut Module) -> Result<usize, String> {
    let mut classes = HashMap::new();
    for a in &module.assignments {
        if let Assignment::Class { name, fields, syntax } = a {
            classes.insert(name.clone(), Class { fields: fields.clone(), syntax: syntax.clone() });
        }
    }
    if classes.is_empty() {
        return Ok(0);
    }
    let assignments = std::mem::take(&mut module.assignments);
    let mut objects = HashMap::new();
    let mut sets = HashMap::new();
    let mut values = HashMap::new();
    for a in &assignments {
        match a {
            Assignment::Object { name, class, body } if classes.contains_key(class) => {
                objects.insert(name.clone(), (class.as_str(), body.as_slice()));
            }
            Assignment::ObjectSet { name, class, body } if classes.contains_key(class) => {
                sets.insert(name.clone(), (class.as_str(), body.as_slice()));
            }
            Assignment::Value { name, value } => {
                values.insert(name.clone(), *value);
            }
            _ => {}
        }
    }
    let ctx = Ctx { classes, objects, sets, values };
    let mut taken: std::collections::HashSet<String> =
        assignments.iter().map(|a| assignment_name(a).to_string()).collect();
    let mut tables: HashMap<(String, String), DispatchTable> = HashMap::new();
    let mut hoisted: Vec<Assignment> = Vec::new();
    let mut out = Vec::new();
    for mut a in assignments.iter().cloned() {
        if let Assignment::Type { name, ty } = &mut a {
            let n = name.clone();
            replace(ty, &ctx, &mut tables, &mut taken, &mut hoisted)
                .map_err(|e| format!("{n}: {e}"))?;
        }
        // the class machinery itself has served its purpose
        if !matches!(a, Assignment::Class { .. } | Assignment::ObjectSet { .. })
            && !matches!(&a, Assignment::Object { class, .. } if ctx.classes.contains_key(class))
        {
            out.push(a);
        }
    }
    out.extend(hoisted);
    // each SEQUENCE with a selected open type in it becomes a keyed one
    let mut rests = Vec::new();
    let mut same: HashMap<String, String> = HashMap::new();
    for a in out.iter_mut() {
        if let Assignment::Type { name, ty } = a {
            if has_dispatch(ty) {
                let n = name.clone();
                *ty = keyed(&n, ty, &tables, &mut taken, &mut rests, &mut same).map_err(|e| format!("{n}: {e}"))?;
            }
        }
    }
    out.extend(rests);
    module.assignments = out;
    let n = tables.len();
    module.dispatch.extend(tables);
    Ok(n)
}

fn has_dispatch(t: &Type) -> bool {
    match t {
        Type::Sequence(root, ext) => root
            .iter()
            .chain(ext.iter().flatten().flat_map(ExtAdd::fields))
            .any(|f| matches!(f.ty, Type::Dispatch { .. })),
        _ => false,
    }
}

/// `SEQUENCE { key K, f1 T1, ..., fn Tn }`, some `Ti` selected by `key`,
/// as a `Type::Keyed`: for each key value an object gives, a SEQUENCE of
/// `f1..fn` with each selected open type a `Contains` of that object's
/// type; for a key no object gives, the same with octets. The components
/// keep their order and their encodings, so the encoding is unchanged.
fn keyed(
    name: &str,
    t: &Type,
    tables: &HashMap<(String, String), DispatchTable>,
    taken: &mut std::collections::HashSet<String>,
    rests: &mut Vec<Assignment>,
    // a rest that another keyed SEQUENCE already has, by its components:
    // the same IE in many messages is one type, not one per message
    same: &mut HashMap<String, String>,
) -> Result<Type, String> {
    let Type::Sequence(root, ext) = t else { unreachable!() };
    if ext.is_some() {
        return Err("an extensible SEQUENCE with a selected open type is not supported".into());
    }
    let key_name = match root.iter().find_map(|f| match &f.ty {
        Type::Dispatch { key, .. } => Some(key.clone()),
        _ => None,
    }) {
        Some(k) => k,
        None => unreachable!(),
    };
    let Some(kf) = root.first() else { unreachable!() };
    if kf.name != key_name {
        return Err(format!("the selecting component {key_name} is not the first"));
    }
    for f in root {
        if f.presence != Presence::Mandatory {
            return Err(format!("component {} is not mandatory", f.name));
        }
        if let Type::Dispatch { key, .. } = &f.ty {
            if key != &key_name {
                return Err(format!("components selected by both {key_name} and {key}"));
            }
        }
    }
    // every key some selected component knows, in the order first seen
    let mut keys: Vec<(i64, String)> = Vec::new();
    let mut ext_all = true;
    for f in &root[1..] {
        if let Type::Dispatch { set, field, .. } = &f.ty {
            let tab = &tables[&(set.clone(), field.clone())];
            ext_all &= tab.ext;
            for (k, kn, _) in &tab.alts {
                if !keys.iter().any(|(x, _)| x == k) {
                    keys.push((*k, kn.clone()));
                }
            }
        }
    }
    // no object anywhere: nothing to select, every selected component is
    // an open type of octets (11.2), which is how an unconstrained OCTET
    // STRING is encoded -- the SEQUENCE as it is, with octets for those
    if keys.is_empty() && ext_all {
        let fields = root
            .iter()
            .map(|f| Field {
                name: f.name.clone(),
                ty: match &f.ty {
                    Type::Dispatch { .. } => Type::OctetString(SizeCons::None),
                    other => other.clone(),
                },
                presence: f.presence.clone(),
            })
            .collect();
        return Ok(Type::Sequence(fields, None));
    }
    let mut fresh = |base: String| -> String {
        let mut cand = base.clone();
        let mut i = 2;
        while !taken.insert(cand.clone()) {
            cand = format!("{base}-{i}");
            i += 1;
        }
        cand
    };
    // the rest for a key: Some(type) per selected component that knows it
    let rest = |k: Option<i64>| -> Vec<Field> {
        root[1..]
            .iter()
            .map(|f| {
                let ty = match &f.ty {
                    Type::Dispatch { set, field, .. } => {
                        let tab = &tables[&(set.clone(), field.clone())];
                        match k.and_then(|k| tab.alts.iter().find(|(x, _, _)| *x == k)) {
                            Some((_, _, tn)) => Type::Open(Box::new(Type::Ref(tn.clone()))),
                            None => Type::OctetString(SizeCons::None),
                        }
                    }
                    other => other.clone(),
                };
                Field { name: f.name.clone(), ty, presence: Presence::Mandatory }
            })
            .collect()
    };
    let mut make = |fields: Vec<Field>, base: String| -> String {
        let sig = format!("{fields:?}");
        if let Some(n) = same.get(&sig) {
            return n.clone();
        }
        let rn = fresh(base);
        rests.push(Assignment::Type { name: rn.clone(), ty: Type::Sequence(fields, None) });
        same.insert(sig, rn.clone());
        rn
    };
    let mut alts = Vec::new();
    for (k, kn) in &keys {
        let rn = make(rest(Some(*k)), format!("{name}-{kn}"));
        alts.push((*k, kn.clone(), rn));
    }
    let unknown = make(rest(None), format!("{name}-unknown"));
    Ok(Type::Keyed { key_name, key: Box::new(kf.ty.clone()), alts, unknown, ext: ext_all })
}

fn replace(
    t: &mut Type,
    ctx: &Ctx,
    tables: &mut HashMap<(String, String), DispatchTable>,
    taken: &mut std::collections::HashSet<String>,
    hoisted: &mut Vec<Assignment>,
) -> Result<(), String> {
    match t {
        Type::ClassField { class, field, set, key } => {
            let c = ctx.classes.get(class.as_str()).ok_or_else(|| format!("{class} is not a class"))?;
            let f = c.fields.iter().find(|f| &f.name == field)
                .ok_or_else(|| format!("{class} has no field &{field}"))?;
            *t = match (&f.ty, set, key) {
                (Some(ty), _, _) => ty.clone(),
                (None, Some(s), Some(k)) => {
                    let tk = (s.clone(), field.clone());
                    if !tables.contains_key(&tk) {
                        let tab = table(ctx, s, field, taken, hoisted)?;
                        tables.insert(tk, tab);
                    }
                    Type::Dispatch { set: s.clone(), field: field.clone(), key: k.clone() }
                }
                (None, _, _) => Type::OctetString(SizeCons::None),
            };
            Ok(())
        }
        Type::Sequence(root, ext) | Type::Set(root, ext) => {
            for f in root.iter_mut().chain(ext.iter_mut().flatten().flat_map(ExtAdd::fields_mut)) {
                replace(&mut f.ty, ctx, tables, taken, hoisted)?;
            }
            Ok(())
        }
        Type::Choice(root, ext) => {
            for (_, a) in root.iter_mut().chain(ext.iter_mut().flatten()) {
                replace(a, ctx, tables, taken, hoisted)?;
            }
            Ok(())
        }
        Type::SequenceOf(_, inner) | Type::SetOf(_, inner) | Type::Constrained(inner, _)
        | Type::Tagged(_, inner) | Type::Contains(inner) => replace(inner, ctx, tables, taken, hoisted),
        _ => Ok(()),
    }
}

/// The objects of set `s` that define type field `field`, by key.
fn table(
    ctx: &Ctx,
    s: &str,
    field: &str,
    taken: &mut std::collections::HashSet<String>,
    hoisted: &mut Vec<Assignment>,
) -> Result<DispatchTable, String> {
    let (objs, ext) = resolve_set(ctx, s, 0)?;
    let class = ctx.sets.get(s).map(|(c, _)| *c).ok_or_else(|| format!("{s} is not an object set"))?;
    let c = &ctx.classes[class];
    // the key is the class's UNIQUE field (X.681 9.5.5); 3GPP's have one
    let uniq = c.fields.iter().find(|f| f.unique).map(|f| f.name.clone());
    let mut alts: Vec<(i64, String, String)> = Vec::new();
    for o in objs {
        let Some(Setting::Type(ty)) = o.get(field) else { continue };
        let Some(u) = &uniq else { return Err(format!("class {class} has no UNIQUE field to select by")) };
        let (kv, kname) = match o.get(u) {
            Some(Setting::Value(Tok::Int(n))) => (*n, n.to_string()),
            Some(Setting::Value(Tok::Word(w))) => match ctx.values.get(w) {
                Some(n) => (*n, w.clone()),
                None => return Err(format!("{s}: key {w} is not an integer value")),
            },
            _ => return Err(format!("{s}: an object without its key &{u}")),
        };
        if let Some((_, other, _)) = alts.iter().find(|(k, _, _)| *k == kv) {
            // X.681 9.5.5 makes a UNIQUE field's values distinct in a set
            if other != &kname {
                return Err(format!("{s}: key {kv} twice ({other}, {kname})"));
            }
            continue;
        }
        let tname = match ty {
            Type::Ref(n) => n.clone(),
            other => {
                // an inline type gets a name of its own, as a hoisted field's
                let base = format!("{s}-{kname}");
                let mut cand = base.clone();
                let mut i = 2;
                while !taken.insert(cand.clone()) {
                    cand = format!("{base}-{i}");
                    i += 1;
                }
                hoisted.push(Assignment::Type { name: cand.clone(), ty: other.clone() });
                cand
            }
        };
        alts.push((kv, kname, tname));
    }
    Ok(DispatchTable { alts, ext })
}

/// The objects of a set, in order, and whether it is extensible.
fn resolve_set(ctx: &Ctx, s: &str, depth: usize) -> Result<(Vec<Object>, bool), String> {
    if depth > 16 {
        return Err(format!("{s}: object sets nested too deep"));
    }
    let (class, body) = ctx.sets.get(s).copied().ok_or_else(|| format!("{s} is not an object set"))?;
    let mut p = Parser::from_tokens(body, 0);
    let mut objs = Vec::new();
    let mut ext = false;
    while !p.at_end() {
        match p.peek_tok().clone() {
            Tok::Ellipsis => {
                p.next_tok();
                ext = true;
            }
            Tok::Pipe | Tok::Comma => {
                p.next_tok();
            }
            Tok::Word(w) if w == "UNION" => {
                p.next_tok();
            }
            Tok::LBrace => {
                let toks = p.braced_tokens()?;
                objs.push(read_object(ctx, class, &toks)?);
            }
            Tok::Word(w) => {
                p.next_tok();
                if let Some((oc, toks)) = ctx.objects.get(&w) {
                    if *oc != class {
                        return Err(format!("{s}: object {w} is of class {oc}, not {class}"));
                    }
                    objs.push(read_object(ctx, class, toks)?);
                } else if ctx.sets.contains_key(&w) {
                    let (o, e) = resolve_set(ctx, &w, depth + 1)?;
                    objs.extend(o);
                    ext |= e;
                } else {
                    return Err(format!("{s}: {w} is neither an object nor an object set"));
                }
            }
            other => return Err(format!("{s}: unexpected {other:?}")),
        }
    }
    Ok((objs, ext))
}

/// One object of `class`, from the tokens between its braces.
fn read_object(ctx: &Ctx, class: &str, toks: &[Tok]) -> Result<Object, String> {
    let c = &ctx.classes[class];
    let mut p = Parser::from_tokens(toks, 0);
    let mut out = Object::new();
    match &c.syntax {
        Some(items) => {
            match_items(c, items, &mut p, &mut out, false)?;
        }
        None => {
            // the default syntax: `&field setting, ...` (X.681 11.4)
            while !p.at_end() {
                let Tok::Field(f) = p.next_tok() else { return Err(format!("{class}: expected a field setting")) };
                let s = setting(c, &f, &mut p)?;
                out.insert(f, s);
                if p.peek_tok() == &Tok::Comma {
                    p.next_tok();
                }
            }
        }
    }
    if !p.at_end() {
        return Err(format!("{class}: unexpected {:?} in an object", p.peek_tok()));
    }
    for f in &c.fields {
        if !out.contains_key(&f.name) && !f.optional && f.default.is_none() {
            return Err(format!("{class}: an object without &{}", f.name));
        }
    }
    Ok(out)
}

/// Match `items` of a WITH SYNTAX. In an optional group (`opt`), a first
/// literal that is not there means the group is absent: `Ok(false)`.
fn match_items(c: &Class, items: &[SynItem], p: &mut Parser, out: &mut Object, opt: bool) -> Result<bool, String> {
    for (i, it) in items.iter().enumerate() {
        match it {
            SynItem::Word(w) if w == "," => {
                if p.peek_tok() == &Tok::Comma {
                    p.next_tok();
                } else if opt && i == 0 {
                    return Ok(false);
                } else {
                    return Err("expected `,` in an object".into());
                }
            }
            SynItem::Word(w) => {
                if matches!(p.peek_tok(), Tok::Word(x) if x == w) {
                    p.next_tok();
                } else if opt && i == 0 {
                    return Ok(false);
                } else {
                    return Err(format!("expected {w} in an object, found {:?}", p.peek_tok()));
                }
            }
            SynItem::Field(f) => {
                let s = setting(c, f, p)?;
                out.insert(f.clone(), s);
            }
            SynItem::Opt(inner) => {
                match_items(c, inner, p, out, true)?;
            }
        }
    }
    Ok(true)
}

fn setting(c: &Class, f: &str, p: &mut Parser) -> Result<Setting, String> {
    let def = c.fields.iter().find(|x| x.name == f).ok_or_else(|| format!("no field &{f}"))?;
    if def.ty.is_none() {
        return Ok(Setting::Type(p.parse_type()?));
    }
    match p.next_tok() {
        t @ (Tok::Int(_) | Tok::Word(_)) => Ok(Setting::Value(t)),
        other => Err(format!("&{f}: unexpected {other:?} as a value")),
    }
}
