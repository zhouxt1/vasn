//! Effective PER-visible constraints (X.691 10.3), from constraints as written.
//!
//! The parser keeps every constraint as written, applied serially, in a
//! `Type::Constrained`. This pass replaces each one with the effective
//! constraint X.691 encodes by, which is all the backend reads:
//!
//! * INTEGER: the bounds of the root of the effective value set, and whether
//!   it is extensible (13). `(0..7 | 9)` is `0..9`; `(0..7 ^ 2..3)` is `2..3`;
//!   `(5, ...)` is `5..5` and extensible.
//! * BIT STRING, OCTET STRING, SEQUENCE OF: the effective size constraint
//!   (10.3.10), from the SIZE constraints alone (10.3.9, 10.3.18).
//! * known-multiplier character strings: the effective size constraint and the
//!   effective permitted alphabet (10.3.11, 10.3.12). UTF8String is not
//!   known-multiplier, so nothing constrains it for PER (10.3.7).
//! * everything else: no constraint is PER-visible (10.3.18), and it is
//!   dropped. That includes a reference to such a type, `y Seq (WITH ...)`.
//!
//! Set arithmetic follows X.680 50.4 and 50.5: a union or intersection is
//! extensible if any part is, and the root is the arithmetic on the roots
//! alone. Visibility follows X.691 10.3.21: a part that is not PER-visible is
//! ignored in an intersection and makes a union invisible; EXCEPT is ignored.
//! Serial application follows X.680 50.11 and X.691 10.3.20: a later
//! constraint applies to the parent without its extension marker, and one
//! that is not PER-visible removes the earlier extensibility.
//!
//! A reference to a constrained INTEGER, string or list, constrained again
//! (`Sub ::= Base (0..7)`), becomes a copy of `Base`'s type with the combined
//! constraint.
use crate::ast::*;
use std::collections::HashMap;

type I = i128;
const NEG: I = i128::MIN;
const POS: I = i128::MAX;

/// A set of integers: sorted, disjoint, inclusive intervals. `NEG` and `POS`
/// stand for no bound.
#[derive(Clone, Debug, PartialEq)]
struct Ints(Vec<(I, I)>);

impl Ints {
    fn all() -> Self { Ints(vec![(NEG, POS)]) }
    fn empty() -> Self { Ints(vec![]) }
    fn range(a: I, b: I) -> Self { if a <= b { Ints(vec![(a, b)]) } else { Ints::empty() } }
    fn is_empty(&self) -> bool { self.0.is_empty() }
    fn min(&self) -> Option<I> { self.0.first().map(|r| r.0) }
    fn max(&self) -> Option<I> { self.0.last().map(|r| r.1) }

    fn union(&self, o: &Ints) -> Ints {
        let mut v: Vec<(I, I)> = self.0.iter().chain(o.0.iter()).cloned().collect();
        v.sort();
        let mut out: Vec<(I, I)> = Vec::new();
        for (a, b) in v {
            match out.last_mut() {
                Some(l) if a <= l.1.saturating_add(1) => l.1 = l.1.max(b),
                _ => out.push((a, b)),
            }
        }
        Ints(out)
    }

    fn inter(&self, o: &Ints) -> Ints {
        let mut out = Vec::new();
        for &(a, b) in &self.0 {
            for &(c, d) in &o.0 {
                let (lo, hi) = (a.max(c), b.min(d));
                if lo <= hi {
                    out.push((lo, hi));
                }
            }
        }
        Ints(out).union(&Ints::empty())
    }

    fn contains_all(&self, o: &Ints) -> bool { self.inter(o) == *o }
}

/// A set of character-string values, as a union of boxes: a value is in a
/// box when its length is in `size` and each of its characters in `alpha`.
/// `None` is no restriction in that dimension.
#[derive(Clone, Debug, PartialEq)]
struct SBox {
    size: Option<Ints>,
    alpha: Option<Ints>,
}

fn opt_inter(a: &Option<Ints>, b: &Option<Ints>) -> Option<Ints> {
    match (a, b) {
        (None, x) | (x, None) => x.clone(),
        (Some(x), Some(y)) => Some(x.inter(y)),
    }
}

fn opt_union(a: &Option<Ints>, b: &Option<Ints>) -> Option<Ints> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.union(y)),
        _ => None,
    }
}

/// What a constraint constrains, which decides what is PER-visible.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Dom {
    Int,
    /// BIT STRING, OCTET STRING, SEQUENCE OF: only SIZE is visible
    Sized,
    /// a known-multiplier character string: SIZE and FROM
    Str,
    /// the characters inside FROM
    Alpha,
}

#[derive(Clone, Debug, PartialEq)]
enum VS {
    Int(Ints),
    Sized(Ints),
    Str(Vec<SBox>),
}

impl VS {
    fn all(d: Dom) -> VS {
        match d {
            Dom::Int | Dom::Alpha => VS::Int(Ints::all()),
            Dom::Sized => VS::Sized(Ints::range(0, POS)),
            Dom::Str => VS::Str(vec![SBox { size: None, alpha: None }]),
        }
    }

    fn union(&self, o: &VS) -> VS {
        match (self, o) {
            (VS::Int(a), VS::Int(b)) => VS::Int(a.union(b)),
            (VS::Sized(a), VS::Sized(b)) => VS::Sized(a.union(b)),
            (VS::Str(a), VS::Str(b)) => VS::Str(a.iter().chain(b.iter()).cloned().collect()),
            _ => unreachable!("set arithmetic across domains"),
        }
    }

    fn inter(&self, o: &VS) -> VS {
        match (self, o) {
            (VS::Int(a), VS::Int(b)) => VS::Int(a.inter(b)),
            (VS::Sized(a), VS::Sized(b)) => VS::Sized(a.inter(b)),
            (VS::Str(a), VS::Str(b)) => {
                let mut out = Vec::new();
                for x in a {
                    for y in b {
                        out.push(SBox { size: opt_inter(&x.size, &y.size), alpha: opt_inter(&x.alpha, &y.alpha) });
                    }
                }
                VS::Str(out)
            }
            _ => unreachable!("set arithmetic across domains"),
        }
    }
}

/// The effective constraint so far: its root, and whether it is extensible.
/// `None` from `eval` is "not PER-visible".
type Eff = (VS, bool);

/// The whole alphabet of a known-multiplier string type (X.680 41, Table 7
/// and 41.2-41.4), as code points.
pub fn alphabet(k: &StringKind) -> Option<Vec<char>> {
    Some(match k {
        StringKind::Ia5 => (0u8..=127).map(char::from).collect(),
        StringKind::Visible => (32u8..=126).map(char::from).collect(),
        StringKind::Numeric => " 0123456789".chars().collect(),
        StringKind::Printable => {
            let mut v: Vec<char> = ('A'..='Z').chain('a'..='z').chain('0'..='9').collect();
            v.extend(" '()+,-./:=?".chars());
            v.sort();
            v
        }
        StringKind::Utf8 => return None,
    })
}

fn chars_to_ints(v: &[char]) -> Ints {
    v.iter().fold(Ints::empty(), |acc, &c| acc.union(&Ints::range(c as I, c as I)))
}

pub struct Resolver<'a> {
    values: &'a HashMap<String, i64>,
    tag_default: TagDefault,
    ext_implied: bool,
    containing: ContainingMode,
    /// each assignment's module environment; the current one is above
    envs: &'a HashMap<String, ModEnv>,
    env0: ModEnv,
    /// every type as written, tags included
    types: HashMap<String, Type>,
    done: HashMap<String, Type>,
    busy: Vec<String>,
}

impl<'a> Resolver<'a> {
    fn num(&self, n: &Num) -> Result<I, String> {
        match n {
            Num::Lit(v) => Ok(*v as I),
            Num::Ref(r) => self.values.get(r).map(|v| *v as I).ok_or_else(|| format!("unknown value `{r}`")),
        }
    }

    fn bound(&self, b: &Bound) -> Result<I, String> {
        match b {
            Bound::Val(n) => self.num(n),
            Bound::Min => Ok(NEG),
            Bound::Max => Ok(POS),
        }
    }

    /// A type by name, resolved (memoised).
    fn named(&mut self, name: &str) -> Result<Type, String> {
        if let Some(t) = self.done.get(name) {
            return Ok(t.clone());
        }
        if self.busy.iter().any(|b| b == name) {
            // a recursive type: it is not a constrainable one, so leave it be
            return Ok(Type::Ref(name.to_string()));
        }
        let t = self.types.get(name).cloned().ok_or_else(|| format!("unknown type `{name}`"))?;
        self.busy.push(name.to_string());
        // a type is resolved in the environment of the module it is written in
        let saved = (self.tag_default, self.ext_implied);
        let env = self.env_of(name);
        (self.tag_default, self.ext_implied) = (env.tag_default, env.ext_implied);
        let r = self.resolve(&t);
        (self.tag_default, self.ext_implied) = saved;
        self.busy.pop();
        let r = r?;
        self.done.insert(name.to_string(), r.clone());
        Ok(r)
    }

    /// Follow references to the type that decides the domain.
    fn base_of(&mut self, t: &Type) -> Result<Type, String> {
        match t {
            Type::Ref(n) => {
                let r = self.named(n)?;
                match r {
                    Type::Invalid(e) => Err(format!("depends on `{n}`: {e}")),
                    Type::Ref(_) if &r == t => Ok(r),
                    Type::Ref(_) => self.base_of(&r),
                    other => Ok(other),
                }
            }
            Type::Tagged(_, inner) => self.base_of(inner),
            other => self.resolve(other),
        }
    }

    // ---------------------------------------------------------- tags

    fn universal(n: i64) -> Option<(TagClass, I)> { Some((TagClass::Universal, n as I)) }

    /// Automatic tagging is in effect for a CHOICE when the module selects it
    /// and no alternative is textually tagged (X.680 29.2, 25.2).
    fn automatic(&self, td: TagDefault, root: &[(String, Type)], ext: &Option<Vec<(String, Type)>>) -> bool {
        td == TagDefault::Automatic
            && !root.iter().chain(ext.iter().flatten()).any(|(_, t)| Self::textually_tagged(t))
    }

    fn textually_tagged(t: &Type) -> bool {
        match t {
            Type::Tagged(..) => true,
            Type::Constrained(b, _) => Self::textually_tagged(b),
            _ => false,
        }
    }

    /// The outermost tag of a type, as written (X.680 8.6), following
    /// references. An untagged CHOICE takes the smallest tag in its root
    /// (X.691 23.3); an automatically tagged one, `[0]`.
    fn env_of(&self, name: &str) -> ModEnv {
        self.envs.get(name).copied().unwrap_or(self.env0)
    }

    /// `td` is the tag default of the module `t` is written in.
    fn tag_of(&self, t: &Type, td: TagDefault, depth: usize) -> Result<Option<(TagClass, I)>, String> {
        if depth > 64 {
            return Ok(None);
        }
        Ok(match t {
            Type::Tagged(tag, _) => Some((tag.class, self.num(&tag.num)?)),
            Type::Constrained(b, _) => self.tag_of(b, td, depth + 1)?,
            Type::Ref(n) => match self.types.get(n) {
                Some(d) => self.tag_of(d, self.env_of(n).tag_default, depth + 1)?,
                None => None,
            },
            Type::Boolean => Self::universal(1),
            Type::Integer(_) => Self::universal(2),
            Type::BitString(_) | Type::NamedBitString(_) => Self::universal(3),
            Type::OctetString(_) => Self::universal(4),
            Type::Null => Self::universal(5),
            Type::Enumerated(..) | Type::EnumeratedNum(..) => Self::universal(10),
            Type::Sequence(..) | Type::SequenceOf(..) => Self::universal(16),
            Type::Set(..) | Type::SetOf(..) => Self::universal(17),
            Type::Contains(_) => Self::universal(4),
            Type::Str(k, ..) => Self::universal(match k {
                StringKind::Utf8 => 12,
                StringKind::Numeric => 18,
                StringKind::Printable => 19,
                StringKind::Ia5 => 22,
                StringKind::Visible => 26,
            }),
            Type::Choice(root, ext) => {
                if self.automatic(td, root, ext) {
                    if root.is_empty() { None } else { Some((TagClass::Context, 0)) }
                } else {
                    let mut best = None;
                    for (_, a) in root {
                        if let Some(tg) = self.tag_of(a, td, depth + 1)? {
                            if best.map_or(true, |b| tg < b) {
                                best = Some(tg);
                            }
                        }
                    }
                    best
                }
            }
            Type::ParamRef(..) | Type::Invalid(_) => None,
        })
    }

    /// A SET's root components in X.691 21's order: canonical tag order unless
    /// automatic tagging applies (X.680 25.3, as for a SEQUENCE: no component
    /// textually tagged), which makes it the textual order.
    fn set_order(&self, root: &[Field], ext: &Option<Vec<ExtAdd>>) -> Result<Vec<Field>, String> {
        let auto = self.tag_default == TagDefault::Automatic
            && !root.iter().chain(ext.iter().flatten().flat_map(|a| a.fields().iter())).any(|f| Self::textually_tagged(&f.ty));
        if auto {
            return Ok(root.to_vec());
        }
        let mut keyed = Vec::new();
        for f in root {
            let tag = self.tag_of(&f.ty, self.tag_default, 0)?.ok_or_else(|| format!("SET component {}: its tag cannot be determined", f.name))?;
            keyed.push((tag, f.clone()));
        }
        for (i, x) in keyed.iter().enumerate() {
            if let Some(y) = keyed[..i].iter().find(|y| y.0 == x.0) {
                return Err(format!("SET components {} and {} have the same tag {:?} (X.680 27.3)", y.1.name, x.1.name, x.0));
            }
        }
        keyed.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(keyed.into_iter().map(|(_, f)| f).collect())
    }

    /// The root of a CHOICE in X.691 23.2's index order: canonical tag order
    /// (X.680 8.6) unless automatic tagging makes it the textual order.
    fn choice_order(&self, root: &[(String, Type)], ext: &Option<Vec<(String, Type)>>) -> Result<Vec<(String, Type)>, String> {
        let auto = self.automatic(self.tag_default, root, ext);
        let mut keyed = Vec::new();
        for (i, (n, a)) in root.iter().enumerate() {
            let tag = if auto {
                (TagClass::Context, i as I)
            } else {
                self.tag_of(a, self.tag_default, 0)?.ok_or_else(|| format!("CHOICE alternative {n}: its tag cannot be determined"))?
            };
            keyed.push((tag, n.clone(), a.clone()));
        }
        // X.680 29.3: the alternatives' tags are distinct
        for (i, x) in keyed.iter().enumerate() {
            if let Some(y) = keyed[..i].iter().find(|y| y.0 == x.0) {
                return Err(format!("CHOICE alternatives {} and {} have the same tag {:?} (X.680 29.3)", y.1, x.1, x.0));
            }
        }
        keyed.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(keyed.into_iter().map(|(_, n, a)| (n, a)).collect())
    }

    /// The effective constraint a resolved type already carries.
    fn eff_of(&self, t: &Type) -> Result<Option<(Dom, Eff)>, String> {
        let sz = |s: &SizeCons| -> Result<Eff, String> {
            Ok(match s {
                SizeCons::None => (VS::Sized(Ints::range(0, POS)), false),
                SizeCons::Fixed(n) => { let v = self.num(n)?; (VS::Sized(Ints::range(v, v)), false) }
                SizeCons::Range(a, b) => (VS::Sized(Ints::range(self.num(a)?, self.num(b)?)), false),
                SizeCons::RangeExt(a, b) => (VS::Sized(Ints::range(self.num(a)?, self.num(b)?)), true),
                SizeCons::Semi(a) => (VS::Sized(Ints::range(self.num(a)?, POS)), false),
                SizeCons::SemiExt(a) => (VS::Sized(Ints::range(self.num(a)?, POS)), true),
            })
        };
        Ok(Some(match t {
            Type::Integer(c) => (Dom::Int, match c {
                IntCons::None => (VS::Int(Ints::all()), false),
                IntCons::NoneExt => (VS::Int(Ints::all()), true),
                IntCons::Fixed(n) => { let v = self.num(n)?; (VS::Int(Ints::range(v, v)), false) }
                IntCons::Range(a, b) => (VS::Int(Ints::range(self.num(a)?, self.num(b)?)), false),
                IntCons::RangeExt(a, b) => (VS::Int(Ints::range(self.num(a)?, self.num(b)?)), true),
                IntCons::Semi(a) => (VS::Int(Ints::range(self.num(a)?, POS)), false),
                IntCons::SemiExt(a) => (VS::Int(Ints::range(self.num(a)?, POS)), true),
            }),
            Type::BitString(s) | Type::NamedBitString(s) | Type::OctetString(s) | Type::SequenceOf(s, _) => {
                (Dom::Sized, sz(s)?)
            }
            Type::Str(k, s, alpha) if alphabet(k).is_some() => {
                let (VS::Sized(size), ext) = sz(s)? else { unreachable!() };
                let size = if size == Ints::range(0, POS) { None } else { Some(size) };
                let alpha = alpha.as_ref().map(|a| chars_to_ints(a));
                (Dom::Str, (VS::Str(vec![SBox { size, alpha }]), ext))
            }
            _ => return Ok(None),
        }))
    }

    /// X.680 49.6 `ElementSetSpecs`: the root, and extensible if marked.
    fn eval_spec(&mut self, c: &ConsSpec, d: Dom) -> Result<Option<Eff>, String> {
        Ok(self.eval(&c.root, d)?.map(|(v, e)| (v, e || c.ext)))
    }

    fn eval(&mut self, s: &SetExpr, d: Dom) -> Result<Option<Eff>, String> {
        Ok(match s {
            SetExpr::Elem(e) => self.elem(e, d)?,
            SetExpr::Union(us) => {
                let mut acc: Option<Eff> = None;
                for u in us {
                    match self.eval(u, d)? {
                        // 10.3.21: a union with an invisible part is invisible
                        None => return Ok(None),
                        Some((v, e)) => {
                            acc = Some(match acc {
                                None => (v, e),
                                Some((w, f)) => (w.union(&v), e || f),
                            })
                        }
                    }
                }
                acc
            }
            SetExpr::Inter(is) => {
                let mut acc: Option<Eff> = None;
                for i in is {
                    // 10.3.21: invisible parts of an intersection are ignored
                    if let Some((v, e)) = self.eval(i, d)? {
                        acc = Some(match acc {
                            None => (v, e),
                            Some((w, f)) => (w.inter(&v), e || f),
                        })
                    }
                }
                acc
            }
            // 10.3.21: "the EXCEPT and the following value set is completely ignored"
            SetExpr::Except(a, _) => self.eval(a, d)?,
            SetExpr::AllExcept(_) => Some((VS::all(d), false)),
        })
    }

    fn elem(&mut self, e: &Elem, d: Dom) -> Result<Option<Eff>, String> {
        Ok(match (e, d) {
            (Elem::NotVisible, _) => None,
            (Elem::Nested(c), _) => self.eval_spec(c, d)?,
            (Elem::Value(CValue::Int(n)), Dom::Int) => { let v = self.num(n)?; Some((VS::Int(Ints::range(v, v)), false)) }
            (Elem::Range(a, ao, b, bo), Dom::Int) => {
                let mut lo = self.bound(a)?;
                let mut hi = self.bound(b)?;
                if *ao { lo = lo.saturating_add(1); }
                if *bo { hi = hi.saturating_sub(1); }
                Some((VS::Int(Ints::range(lo, hi)), false))
            }
            // inside FROM: characters (X.680 51.7)
            (Elem::Value(CValue::Chars(s)), Dom::Alpha) => {
                Some((VS::Int(s.chars().fold(Ints::empty(), |a, c| a.union(&Ints::range(c as I, c as I)))), false))
            }
            (Elem::CharRange(a, b), Dom::Alpha) => Some((VS::Int(Ints::range(*a as I, *b as I)), false)),
            (Elem::Size(c), Dom::Sized) => match self.eval_spec(c, Dom::Int)? {
                None => None,
                Some((VS::Int(v), e)) => Some((VS::Sized(v.inter(&Ints::range(0, POS))), e)),
                Some(_) => unreachable!(),
            },
            (Elem::Size(c), Dom::Str) => match self.eval_spec(c, Dom::Int)? {
                None => None,
                Some((VS::Int(v), e)) => Some((VS::Str(vec![SBox { size: Some(v.inter(&Ints::range(0, POS))), alpha: None }]), e)),
                Some(_) => unreachable!(),
            },
            (Elem::From(c), Dom::Str) => match self.eval_spec(c, Dom::Alpha)? {
                // 10.3.11: an extensible permitted alphabet is not PER-visible
                None | Some((_, true)) => None,
                Some((VS::Int(v), false)) => Some((VS::Str(vec![SBox { size: None, alpha: Some(v) }]), false)),
                Some(_) => unreachable!(),
            },
            // 51.3: the root of another type's values; its extensibility is
            // not inherited (51.3.3)
            (Elem::Contained(n), _) => {
                let t = self.named(n)?;
                let t = self.base_of(&t)?;
                match self.eff_of(&t)? {
                    Some((td, (v, _))) if td == d => Some((v, false)),
                    Some((Dom::Int, (v, _))) if d == Dom::Alpha => Some((v, false)),
                    _ => None,
                }
            }
            // 10.3.17 single values on strings, a BIT STRING value, TRUE: not
            // PER-visible; nor anything on a type whose constraints never are
            (Elem::Value(_), _) => None,
            (Elem::Containing(..), _) => None,
            (Elem::Range(..), _) | (Elem::CharRange(..), _) | (Elem::Size(_), _) | (Elem::From(_), _) => {
                return Err(format!("a constraint that cannot apply here ({d:?})"));
            }
        })
    }

    /// `base` with `specs` applied serially: the resolved type.
    fn constrain(&mut self, base: &Type, specs: &[ConsSpec]) -> Result<Type, String> {
        // a reference to a constrainable type is replaced by that type
        let b = self.base_of(base)?;
        let Some((dom, mut cur)) = self.eff_of(&b)? else {
            // 10.3.18: no constraint on this type is PER-visible. CONTAINING on
            // an OCTET STRING is handled with the strings, below.
            return self.resolve(base);
        };
        for c in specs {
            match self.eval_spec(c, dom)? {
                // 10.3.20: an invisible serial constraint keeps the root and
                // removes the extensibility
                None => cur.1 = false,
                // X.680 50.11: applied to the parent without its extension marker
                Some((v, e)) => cur = (cur.0.inter(&v), e),
            }
        }
        self.rebuild(&b, cur)
    }

    fn lit(v: I) -> Result<Num, String> {
        i64::try_from(v).map(Num::Lit).map_err(|_| format!("bound {v} is outside 64 bits"))
    }

    /// The resolved type with effective constraint `eff`.
    fn rebuild(&self, b: &Type, (v, ext): Eff) -> Result<Type, String> {
        let sizes = |s: &Ints| -> Result<SizeCons, String> {
            let (Some(lo), Some(hi)) = (s.min(), s.max()) else {
                return Err("the SIZE constraint permits no size".into());
            };
            Ok(match (hi == POS, ext) {
                (true, false) if lo == 0 => SizeCons::None,
                (true, false) => SizeCons::Semi(Self::lit(lo)?),
                (true, true) => SizeCons::SemiExt(Self::lit(lo)?),
                (false, false) if lo == hi => SizeCons::Fixed(Self::lit(lo)?),
                (false, false) => SizeCons::Range(Self::lit(lo)?, Self::lit(hi)?),
                (false, true) => SizeCons::RangeExt(Self::lit(lo)?, Self::lit(hi)?),
            })
        };
        Ok(match (b, v) {
            (Type::Integer(_), VS::Int(s)) => {
                let (Some(lo), Some(hi)) = (s.min(), s.max()) else {
                    return Err("the constraint permits no value".into());
                };
                Type::Integer(match (lo == NEG, hi == POS, ext) {
                    (true, _, false) => IntCons::None,
                    (true, _, true) => IntCons::NoneExt,
                    (false, true, false) => IntCons::Semi(Self::lit(lo)?),
                    (false, true, true) => IntCons::SemiExt(Self::lit(lo)?),
                    (false, false, false) if lo == hi => IntCons::Fixed(Self::lit(lo)?),
                    (false, false, false) => IntCons::Range(Self::lit(lo)?, Self::lit(hi)?),
                    (false, false, true) => IntCons::RangeExt(Self::lit(lo)?, Self::lit(hi)?),
                })
            }
            (Type::BitString(_), VS::Sized(s)) => Type::BitString(sizes(&s)?),
            (Type::NamedBitString(_), VS::Sized(s)) => Type::NamedBitString(sizes(&s)?),
            (Type::OctetString(_), VS::Sized(s)) => Type::OctetString(sizes(&s)?),
            (Type::SequenceOf(_, e), VS::Sized(s)) => Type::SequenceOf(sizes(&s)?, e.clone()),
            (Type::Str(k, _, _), VS::Str(boxes)) => {
                // 10.3.10 and 10.3.12: a size, or a character, is permitted if
                // some value of the constrained type has it
                let boxes: Vec<SBox> = boxes
                    .into_iter()
                    .filter(|b| !b.size.as_ref().is_some_and(Ints::is_empty) && !b.alpha.as_ref().is_some_and(Ints::is_empty))
                    .collect();
                if boxes.is_empty() {
                    return Err("the constraint permits no value".into());
                }
                let size = boxes.iter().skip(1).fold(boxes[0].size.clone(), |a, b| opt_union(&a, &b.size));
                let alpha = boxes.iter().skip(1).fold(boxes[0].alpha.clone(), |a, b| opt_union(&a, &b.alpha));
                let full = chars_to_ints(&alphabet(k).unwrap());
                let alpha = match alpha {
                    None => None,
                    Some(a) => {
                        let a = a.inter(&full);
                        if a.contains_all(&full) {
                            None
                        } else {
                            Some(a.0.iter().flat_map(|&(x, y)| (x..=y).filter_map(|c| char::from_u32(c as u32))).collect())
                        }
                    }
                };
                let s = size.unwrap_or_else(|| Ints::range(0, POS));
                Type::Str(k.clone(), sizes(&s)?, alpha)
            }
            _ => unreachable!("rebuild across domains"),
        })
    }

    /// X.680 20.3-20.6 assign every item a value; X.691 14.1 indexes the root
    /// in ascending order of value, and the additions as written (which X.680
    /// 20.4 requires to be ascending already).
    fn enumerated(&self, root: &[(String, Option<Num>)], ext: &Option<Vec<(String, Option<Num>)>>) -> Result<Type, String> {
        let mut used: Vec<I> = Vec::new();
        for (n, v) in root.iter().chain(ext.iter().flatten()) {
            if let Some(v) = v {
                let v = self.num(v)?;
                if used.contains(&v) {
                    return Err(format!("ENUMERATED: {n}'s value {v} is used twice (X.680 20.2)"));
                }
                used.push(v);
            }
        }
        // 20.3: the root's identifiers take 0, 1, 2, ... skipping the numbers
        // the root's NamedNumbers use
        let root_nums: Vec<I> = root.iter().filter_map(|(_, v)| v.as_ref().map(|v| self.num(v))).collect::<Result<_, _>>()?;
        let mut next: I = 0;
        let mut rv: Vec<(I, String)> = Vec::new();
        for (n, v) in root {
            let val = match v {
                Some(v) => self.num(v)?,
                None => {
                    while root_nums.contains(&next) || rv.iter().any(|(x, _)| *x == next) {
                        next += 1;
                    }
                    next
                }
            };
            if rv.iter().any(|(x, _)| *x == val) {
                return Err(format!("ENUMERATED: two items have the value {val} (X.680 20.2)"));
            }
            rv.push((val, n.clone()));
        }
        let ext_names = match ext {
            None => None,
            Some(adds) => {
                let mut names = Vec::new();
                let mut last: Option<I> = None;
                let mut all: Vec<I> = rv.iter().map(|(v, _)| *v).collect();
                for (n, v) in adds {
                    let val = match v {
                        Some(v) => self.num(v)?,
                        // 20.6: the smallest value above the additions so far
                        // that the root does not use
                        None => {
                            let mut c = last.map_or(0, |l| l + 1);
                            while all.contains(&c) {
                                c += 1;
                            }
                            c
                        }
                    };
                    if all.contains(&val) {
                        return Err(format!("ENUMERATED: {n}'s value {val} is already used (X.680 20.5)"));
                    }
                    if last.is_some_and(|l| val <= l) {
                        return Err(format!("ENUMERATED: addition {n} is not above the ones before it (X.680 20.4)"));
                    }
                    last = Some(val);
                    all.push(val);
                    names.push(n.clone());
                }
                Some(names)
            }
        };
        rv.sort();
        let ext_names = if self.ext_implied { Some(ext_names.unwrap_or_default()) } else { ext_names };
        Ok(Type::Enumerated(rv.into_iter().map(|(_, n)| n).collect(), ext_names))
    }

    /// A component with its type resolved, and a DEFAULT that names an
    /// INTEGER value reference (`DEFAULT defaultValidity`) replaced by the value.
    fn field(&mut self, f: &Field) -> Result<Field, String> {
        let ty = self.resolve(&f.ty)?;
        let presence = match &f.presence {
            Presence::Default(DefaultVal::Name(n)) if self.values.contains_key(n) => {
                match self.base_of(&ty)? {
                    Type::Integer(_) => Presence::Default(DefaultVal::Int(self.values[n])),
                    _ => f.presence.clone(),
                }
            }
            p => p.clone(),
        };
        Ok(Field { name: f.name.clone(), ty, presence })
    }

    /// `t` with every constraint in it resolved.
    pub fn resolve(&mut self, t: &Type) -> Result<Type, String> {
        Ok(match t {
            Type::EnumeratedNum(root, ext) => self.enumerated(root, ext)?,
            Type::Tagged(_, inner) => self.resolve(inner)?,
            // X.691 21: a SET is a SEQUENCE of its root in canonical order,
            // then its extension additions as written
            Type::Set(root, ext) => {
                let root = self.set_order(root, ext)?;
                let ext = if self.ext_implied && ext.is_none() { Some(vec![]) } else { ext.clone() };
                self.resolve(&Type::Sequence(root, ext))?
            }
            // 22.2: in BASIC-PER a SET OF is a SEQUENCE OF
            Type::SetOf(s, inner) => self.resolve(&Type::SequenceOf(s.clone(), inner.clone()))?,
            // X.680 13.4: EXTENSIBILITY IMPLIED puts `...` in every type that may have one
            Type::Enumerated(r, None) if self.ext_implied => Type::Enumerated(r.clone(), Some(vec![])),
            Type::Sequence(r, None) if self.ext_implied => self.resolve(&Type::Sequence(r.clone(), Some(vec![])))?,
            Type::Choice(r, None) if self.ext_implied => self.resolve(&Type::Choice(r.clone(), Some(vec![])))?,
            Type::Constrained(base, specs) => {
                let containing = specs.iter().find_map(|c| match &c.root {
                    SetExpr::Elem(Elem::Containing(t, by)) => Some((t.clone(), *by)),
                    _ => None,
                });
                if let Some((inner, by)) = containing {
                    let rest: Vec<ConsSpec> = specs
                        .iter()
                        .filter(|c| !matches!(c.root, SetExpr::Elem(Elem::Containing(..))))
                        .cloned()
                        .collect();
                    let b = self.base_of(base)?;
                    let bare = matches!(b, Type::OctetString(SizeCons::None));
                    // X.682 11.3: without ENCODED BY the octets are the complete
                    // encoding (X.691 11.1) of a `T`; with it, of something else
                    if self.containing == ContainingMode::Decode && !by {
                        if !bare || !rest.is_empty() {
                            return Err("CONTAINING on a BIT STRING, or with a size constraint too: \
                                        not built under --containing decode".into());
                        }
                        return Ok(Type::Contains(Box::new(self.resolve(&inner)?)));
                    }
                    // otherwise the contents are carried as octets, undecoded
                    return if rest.is_empty() { self.resolve(base) } else { self.constrain(base, &rest) };
                }
                self.constrain(base, specs)?
            }
            Type::Sequence(root, ext) => {
                let mut r2 = Vec::new();
                for f in root {
                    r2.push(self.field(f)?);
                }
                let e2 = match ext {
                    None => None,
                    Some(adds) => {
                        let mut v = Vec::new();
                        for a in adds {
                            v.push(match a {
                                ExtAdd::One(f) => ExtAdd::One(self.field(f)?),
                                ExtAdd::Group(g) => {
                                    let mut gg = Vec::new();
                                    for f in g {
                                        gg.push(self.field(f)?);
                                    }
                                    ExtAdd::Group(gg)
                                }
                            });
                        }
                        Some(v)
                    }
                };
                Type::Sequence(r2, e2)
            }
            Type::Choice(root, ext) => {
                let root = self.choice_order(root, ext)?;
                let mut r2 = Vec::new();
                for (n, a) in &root {
                    r2.push((n.clone(), self.resolve(a)?));
                }
                let e2 = match ext {
                    None => None,
                    Some(v) => {
                        let mut out = Vec::new();
                        for (n, a) in v {
                            out.push((n.clone(), self.resolve(a)?));
                        }
                        Some(out)
                    }
                };
                Type::Choice(r2, e2)
            }
            Type::SequenceOf(s, inner) => Type::SequenceOf(s.clone(), Box::new(self.resolve(inner)?)),
            other => other.clone(),
        })
    }
}

/// Resolve every constraint in the module. A type whose constraint cannot be
/// resolved -- an unknown value reference, an empty value set -- becomes
/// `Type::Invalid`, which the backend reports as skipped.
pub fn resolve(module: &mut Module, containing: ContainingMode) {
    let values: HashMap<String, i64> = module
        .assignments
        .iter()
        .filter_map(|a| match a {
            Assignment::Value { name, value } => Some((name.clone(), *value)),
            _ => None,
        })
        .collect();
    let types: HashMap<String, Type> = module
        .assignments
        .iter()
        .filter_map(|a| match a {
            Assignment::Type { name, ty } => Some((name.clone(), ty.clone())),
            _ => None,
        })
        .collect();
    let mut r = Resolver {
        values: &values,
        tag_default: module.env.tag_default,
        ext_implied: module.env.ext_implied,
        containing,
        envs: &module.envs,
        env0: module.env,
        types,
        done: HashMap::new(),
        busy: Vec::new(),
    };
    for a in module.assignments.iter_mut() {
        if let Assignment::Type { name, ty } = a {
            *ty = match r.named(name) {
                Ok(t) => t,
                Err(e) => Type::Invalid(e),
            };
        }
    }
}
