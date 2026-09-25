//! Hoisting anonymous inline types out of fields.
//!
//! ASN.1 lets a SEQUENCE field carry a whole type inline:
//!
//! ```asn1
//! PDSCH-Config ::= SEQUENCE {
//!     resourceAllocation  ENUMERATED { resourceAllocationType0, ... },
//!     ...
//! }
//! ```
//!
//! Nothing about the encoding depends on whether the type was written inline or
//! given a name, so the compiler gives each one a name and lifts it to the top
//! level, exactly as VUPER's Rocq backend does. The name is derived from the
//! path that reached it, so `PDSCH-Config` above yields
//! `PDSCH-Config-resourceAllocation`.
//!
//! This is a pure source-to-source pass: it adds assignments and replaces
//! inline types with references, and never changes what any type encodes to.
use crate::ast::*;
use std::collections::HashSet;

pub struct Hoister {
    taken: HashSet<String>,
    new_defs: Vec<Assignment>,
    pub hoisted: usize,
}

/// Inline types worth naming. Terminal types stay where they are -- naming a
/// `BOOLEAN` or an `INTEGER (0..7)` would add noise without adding anything.
/// BIT and OCTET STRING count as constructed: the backend generates them as
/// list types, which only exist at the top level.
fn is_constructed(t: &Type) -> bool {
    matches!(
        t,
        Type::Enumerated(_, _)
            | Type::Sequence(_, _)
            | Type::Choice(_, _)
            | Type::SequenceOf(_, _)
            | Type::BitString(_)
            | Type::NamedBitString(_)
            | Type::Str(..)
            | Type::OctetString(_)
            | Type::Contains(_)
    ) || is_single_int(t)
}

/// `INTEGER (5)` or `INTEGER (5..5)`: one value, no bits. Hoisted so that the
/// backend can give it a named 0-bit format, which a terminal cannot carry.
pub fn is_single_int(t: &Type) -> bool {
    match t {
        Type::Integer(IntCons::Fixed(_)) => true,
        Type::Integer(IntCons::Range(a, b)) => a == b,
        _ => false,
    }
}

/// The names the backend gives a type's own hidden parts: an extensible
/// SEQUENCE's root and its groups, and a named-bit BIT STRING's plain list. A
/// field called `root` or `ext0` holding an inline type is hoisted to the
/// next free name instead of onto one of these.
fn reserve_hidden(taken: &mut HashSet<String>, name: &str, ty: &Type) {
    match ty {
        Type::Sequence(_, Some(adds)) => {
            taken.insert(format!("{name}-root"));
            for i in 0..adds.len() {
                taken.insert(format!("{name}-ext{i}"));
            }
        }
        Type::NamedBitString(_) => {
            taken.insert(format!("{name}-bits"));
        }
        _ => {}
    }
    // an extensible SIZE's root and extension lists
    if let Type::Str(StringKind::Utf8, ..) = ty {
        taken.insert(format!("{name}-octets"));
    }
    if let Type::BitString(sc) | Type::NamedBitString(sc) | Type::OctetString(sc) | Type::SequenceOf(sc, _) | Type::Str(_, sc, _) = ty {
        if matches!(sc, SizeCons::RangeExt(..) | SizeCons::SemiExt(_)) {
            taken.insert(format!("{name}-sroot"));
            taken.insert(format!("{name}-sext"));
            taken.insert(format!("{name}-bits-sroot"));
            taken.insert(format!("{name}-bits-sext"));
        }
    }
}

impl Hoister {
    pub fn new(module: &Module) -> Self {
        let mut taken = HashSet::new();
        for a in &module.assignments {
            match a {
                Assignment::Type { name, ty } => {
                    taken.insert(name.clone());
                    reserve_hidden(&mut taken, name, ty);
                }
                Assignment::ParamType { name, .. } | Assignment::Value { name, .. } => {
                    taken.insert(name.clone());
                }
            }
        }
        Hoister { taken, new_defs: Vec::new(), hoisted: 0 }
    }

    fn fresh(&mut self, base: &str) -> String {
        if self.taken.insert(base.to_string()) {
            return base.to_string();
        }
        let mut i = 2;
        loop {
            let cand = format!("{base}-{i}");
            if self.taken.insert(cand.clone()) {
                return cand;
            }
            i += 1;
        }
    }

    /// Replace `t` by a reference to a freshly named top-level type, after
    /// hoisting anything nested inside it first.
    fn lift(&mut self, path: &str, t: &mut Type) {
        // before its fields are hoisted, so that none lands on these
        reserve_hidden(&mut self.taken, path, t);
        self.descend(path, t);
        let mut owned = Type::Null;
        std::mem::swap(&mut owned, t);
        let name = self.fresh(path);
        self.new_defs.push(Assignment::Type { name: name.clone(), ty: owned });
        self.hoisted += 1;
        *t = Type::Ref(name);
    }

    /// Walk into `t`, lifting any constructed type found in a field,
    /// alternative, or element position.
    fn descend(&mut self, path: &str, t: &mut Type) {
        match t {
            Type::Sequence(root, ext) => {
                for f in root
                    .iter_mut()
                    .chain(ext.iter_mut().flatten().flat_map(ExtAdd::fields_mut))
                {
                    let p = format!("{path}-{}", f.name);
                    if is_constructed(&f.ty) {
                        self.lift(&p, &mut f.ty);
                    } else {
                        self.descend(&p, &mut f.ty);
                    }
                }
            }
            Type::Choice(root, ext) => {
                for (n, a) in root.iter_mut().chain(ext.iter_mut().flatten()) {
                    let p = format!("{path}-{n}");
                    if is_constructed(a) {
                        self.lift(&p, a);
                    } else {
                        self.descend(&p, a);
                    }
                }
            }
            Type::SequenceOf(_, inner) => {
                let p = format!("{path}-item");
                if is_constructed(inner) {
                    self.lift(&p, inner);
                } else {
                    self.descend(&p, inner);
                }
            }
            Type::Contains(inner) => {
                let p = format!("{path}-contained");
                if is_constructed(inner) {
                    self.lift(&p, inner);
                } else {
                    self.descend(&p, inner);
                }
            }
            _ => {}
        }
    }

    pub fn run(mut self, module: &mut Module) -> usize {
        let mut assignments = std::mem::take(&mut module.assignments);
        for a in assignments.iter_mut() {
            if let Assignment::Type { name, ty } = a {
                let n = name.clone();
                self.descend(&n, ty);
            }
        }
        assignments.append(&mut self.new_defs);
        module.assignments = assignments;
        self.hoisted
    }
}

pub fn hoist(module: &mut Module) -> usize {
    Hoister::new(module).run(module)
}

/// Expand every use of a parameterised type into a named instance.
///
/// `SetupRelease { PDSCH-Config }` becomes a reference to a new top-level
/// `SetupRelease-PDSCH-Config`, whose body is `SetupRelease`'s with the
/// parameter replaced by the argument. One instance per distinct argument
/// list, however many fields use it. Like hoisting, this changes no encoding:
/// X.683 instantiation is textual substitution. Only type parameters are
/// handled, which is all 3GPP and ETSI use; a parameterised type whose own
/// body is parameterised is expanded to a fixed point.
pub fn expand_params(module: &mut Module) -> usize {
    let defs: std::collections::HashMap<String, (Vec<String>, Type)> = module
        .assignments
        .iter()
        .filter_map(|a| match a {
            Assignment::ParamType { name, params, ty } => {
                Some((name.clone(), (params.clone(), ty.clone())))
            }
            _ => None,
        })
        .collect();
    if defs.is_empty() {
        return 0;
    }
    let mut taken: HashSet<String> = module
        .assignments
        .iter()
        .map(|a| match a {
            Assignment::Type { name, .. }
            | Assignment::ParamType { name, .. }
            | Assignment::Value { name, .. } => name.clone(),
        })
        .collect();
    let mut instances: std::collections::HashMap<(String, Vec<String>), String> =
        std::collections::HashMap::new();
    let mut new_defs: Vec<Assignment> = Vec::new();

    fn subst(t: &mut Type, map: &std::collections::HashMap<String, String>) {
        match t {
            Type::Ref(n) => {
                if let Some(a) = map.get(n) {
                    *n = a.clone();
                }
            }
            Type::ParamRef(_, args) => {
                for a in args.iter_mut() {
                    if let Some(b) = map.get(a) {
                        *a = b.clone();
                    }
                }
            }
            Type::Sequence(root, ext) => {
                for f in root
                    .iter_mut()
                    .chain(ext.iter_mut().flatten().flat_map(ExtAdd::fields_mut))
                {
                    subst(&mut f.ty, map);
                }
            }
            Type::Choice(root, ext) => {
                for (_, a) in root.iter_mut().chain(ext.iter_mut().flatten()) {
                    subst(a, map);
                }
            }
            Type::SequenceOf(_, inner) => subst(inner, map),
            Type::Constrained(inner, _) | Type::Tagged(_, inner) | Type::SetOf(_, inner) => subst(inner, map),
            Type::Set(root, ext) => {
                for f in root.iter_mut().chain(ext.iter_mut().flatten().flat_map(ExtAdd::fields_mut)) {
                    subst(&mut f.ty, map);
                }
            }
            _ => {}
        }
    }

    // Replace every ParamRef inside `t` by a Ref to its instance, creating the
    // instance the first time. Returns the instances created, still to visit.
    fn visit(
        t: &mut Type,
        defs: &std::collections::HashMap<String, (Vec<String>, Type)>,
        instances: &mut std::collections::HashMap<(String, Vec<String>), String>,
        taken: &mut HashSet<String>,
        pending: &mut Vec<(String, Type)>,
    ) {
        match t {
            Type::ParamRef(name, args) => {
                let Some((params, body)) = defs.get(name.as_str()) else { return };
                if params.len() != args.len() {
                    return;
                }
                let key = (name.clone(), args.clone());
                let inst = match instances.get(&key) {
                    Some(n) => n.clone(),
                    None => {
                        let base = format!("{name}-{}", args.join("-"));
                        let mut cand = base.clone();
                        let mut i = 2;
                        while !taken.insert(cand.clone()) {
                            cand = format!("{base}-{i}");
                            i += 1;
                        }
                        let map = params.iter().cloned().zip(args.iter().cloned()).collect();
                        let mut b = body.clone();
                        subst(&mut b, &map);
                        instances.insert(key, cand.clone());
                        pending.push((cand.clone(), b));
                        cand
                    }
                };
                *t = Type::Ref(inst);
            }
            Type::Sequence(root, ext) => {
                for f in root
                    .iter_mut()
                    .chain(ext.iter_mut().flatten().flat_map(ExtAdd::fields_mut))
                {
                    visit(&mut f.ty, defs, instances, taken, pending);
                }
            }
            Type::Choice(root, ext) => {
                for (_, a) in root.iter_mut().chain(ext.iter_mut().flatten()) {
                    visit(a, defs, instances, taken, pending);
                }
            }
            Type::SequenceOf(_, inner) => visit(inner, defs, instances, taken, pending),
            Type::Constrained(inner, _) | Type::Tagged(_, inner) | Type::SetOf(_, inner) => {
                visit(inner, defs, instances, taken, pending)
            }
            Type::Set(root, ext) => {
                for f in root.iter_mut().chain(ext.iter_mut().flatten().flat_map(ExtAdd::fields_mut)) {
                    visit(&mut f.ty, defs, instances, taken, pending);
                }
            }
            _ => {}
        }
    }

    let mut pending: Vec<(String, Type)> = Vec::new();
    for a in module.assignments.iter_mut() {
        if let Assignment::Type { ty, .. } = a {
            visit(ty, &defs, &mut instances, &mut taken, &mut pending);
        }
    }
    // an instance's own body may use another parameterised type
    while let Some((name, mut ty)) = pending.pop() {
        visit(&mut ty, &defs, &mut instances, &mut taken, &mut pending);
        new_defs.push(Assignment::Type { name, ty });
    }
    // an instance is the parameterised body, so it is in that body's module
    for ((pname, _), inst) in &instances {
        if let Some(e) = module.envs.get(pname).copied() {
            module.envs.insert(inst.clone(), e);
        }
    }
    let n = new_defs.len();
    module.assignments.append(&mut new_defs);
    n
}

/// Under `--containing decode`, a CONTAINING whose contained type leads back
/// to it is kept as octets, and its name returned. NR has such cycles:
/// `RRCReconfiguration-v1530-IEs` carries `nr-SCG OCTET STRING (CONTAINING
/// RRCReconfiguration)`, and `RRCReconfiguration` reaches
/// `RRCReconfiguration-v1530-IEs`. Decoding one would make the Rust type and
/// the format recursive, which vuperc does not build: every other type is
/// generated after the ones it uses. Every cycle in NR passes through a
/// CONTAINING, so this leaves none.
pub fn break_containing_cycles(module: &mut Module) -> Vec<String> {
    use std::collections::HashMap;
    let graph: HashMap<String, Vec<String>> = module
        .assignments
        .iter()
        .filter_map(|a| match a {
            Assignment::Type { name, ty } => {
                let mut r = Vec::new();
                crate::emit::collect_refs(ty, &mut r);
                Some((name.clone(), r))
            }
            _ => None,
        })
        .collect();
    let reaches = |from: &str, to: &str| -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![from.to_string()];
        while let Some(n) = stack.pop() {
            if n == to {
                return true;
            }
            if seen.insert(n.clone()) {
                if let Some(next) = graph.get(&n) {
                    stack.extend(next.iter().cloned());
                }
            }
        }
        false
    };
    let mut broken = Vec::new();
    for a in module.assignments.iter_mut() {
        if let Assignment::Type { name, ty } = a {
            if let Type::Contains(inner) = ty {
                let mut r = Vec::new();
                crate::emit::collect_refs(inner, &mut r);
                if r.iter().any(|x| reaches(x, name)) {
                    *ty = Type::OctetString(SizeCons::None);
                    broken.push(name.clone());
                }
            }
        }
    }
    broken
}
