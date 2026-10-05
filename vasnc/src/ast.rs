#![allow(dead_code)] // the AST covers more than the backend consumes yet

//! ASN.1 abstract syntax. Modelled on VUPER's `Compile/src/ASN1Format.ml`,
//! which is already validated against the full 3GPP NR-RRC grammar.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Num {
    Lit(i64),
    /// A reference to a value assignment (`maxNrofCells` etc).
    Ref(String),
}

/// The effective PER-visible constraint on an INTEGER (X.691 10.3), after
/// `constraints::resolve`: only the bounds of the root matter to PER (13), and
/// whether the constraint is extensible (13.1). The parser only ever produces
/// `None`, with the written constraint in a `Type::Constrained` around it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntCons {
    None,
    /// `(n)`
    Fixed(Num),
    /// `(lb..ub)`
    Range(Num, Num),
    /// `(lb..ub, ...)`, and `(n, ...)` as `RangeExt(n, n)`
    RangeExt(Num, Num),
    /// `(lb..MAX)`: semi-constrained (13.2.3)
    Semi(Num),
    /// `(lb..MAX, ...)`
    SemiExt(Num),
    /// an extensible constraint whose root has no lower bound, `(MIN..5, ...)`
    NoneExt,
}

/// The effective size constraint (X.691 10.3.10), in the same shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SizeCons {
    None,
    Fixed(Num),
    Range(Num, Num),
    RangeExt(Num, Num),
    /// `SIZE (lb..MAX)`
    Semi(Num),
    /// `SIZE (lb..MAX, ...)`
    SemiExt(Num),
}

// ------------------------------------------------------------ constraints
//
// As written (X.680 49-51), before `constraints::resolve` turns them into the
// effective PER-visible constraint of X.691 10.3.

/// An end of a value range (X.680 51.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bound {
    Val(Num),
    Min,
    Max,
}

/// A single value in a constraint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CValue {
    Int(Num),
    /// `"abc"`, and a character in `FROM ("a".."z")`
    Chars(String),
    /// `'0101'B` or `'5A'H`, as written (the letter says which)
    Bits(String, char),
    Bool(bool),
    /// an identifier that is not a known value reference, e.g. an enumeration
    Name(String),
}

/// One `SubtypeElements` (X.680 51).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elem {
    Value(CValue),
    /// `lb..ub`, each end possibly open (`lb<..<ub`)
    Range(Bound, bool, Bound, bool),
    /// character range in a permitted alphabet, `"a".."z"`
    CharRange(char, char),
    Size(Box<ConsSpec>),
    From(Box<ConsSpec>),
    /// a contained subtype: `INCLUDES T`, or `T` by name (51.3)
    Contained(String),
    /// `CONTAINING T` on a BIT or OCTET STRING (X.682 11), and whether an
    /// `ENCODED BY` follows it. Not a value set.
    Containing(Box<Type>, bool),
    /// a parenthesised element set
    Nested(Box<ConsSpec>),
    /// never PER-visible: WITH COMPONENT(S), PATTERN, CONSTRAINED BY, a table
    /// constraint, and anything else X.691 10.3.1-10.3.8 names
    NotVisible,
}

/// Set arithmetic over elements (X.680 50).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SetExpr {
    Elem(Elem),
    Union(Vec<SetExpr>),
    Inter(Vec<SetExpr>),
    /// `a EXCEPT b`
    Except(Box<SetExpr>, Box<SetExpr>),
    /// `ALL EXCEPT b`
    AllExcept(Box<SetExpr>),
}

/// `( root [, ... [, additions]] )` (X.680 49.6 `ElementSetSpecs`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsSpec {
    pub root: SetExpr,
    pub ext: bool,
    pub adds: Option<SetExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringKind {
    Ia5,
    Numeric,
    Printable,
    Visible,
    Utf8,
    /// the known-multiplier strings of 16- and 32-bit characters (X.691 30.1)
    Bmp,
    Universal,
    /// the strings that are not known-multiplier (X.691 30.6): their X.690
    /// 8.23.5 octets, with a length in octets
    General,
    Graphic,
    /// TeletexString, and T61String, its other name (X.680 41.1)
    Teletex,
    Videotex,
    /// the useful types (X.680 46 to 48, X.691 10.6.5): a VisibleString in
    /// the forms X.690 11.7 and 11.8 allow, and a GraphicString
    GeneralizedTime,
    UtcTime,
    ObjectDescriptor,
}

impl StringKind {
    /// Encoded as octets with an unconstrained length (X.691 30.6), rather
    /// than character by character.
    pub fn octets(&self) -> bool {
        matches!(self, StringKind::Utf8 | StringKind::General | StringKind::Graphic
                 | StringKind::Teletex | StringKind::Videotex | StringKind::ObjectDescriptor)
    }
    /// A useful type: no constraint on it is PER-visible (X.691 10.3.16).
    pub fn useful(&self) -> bool {
        matches!(self, StringKind::GeneralizedTime | StringKind::UtcTime | StringKind::ObjectDescriptor)
    }
    /// The UNIVERSAL tag number (X.680 8.4, Table 1).
    pub fn tag(&self) -> u32 {
        match self {
            StringKind::ObjectDescriptor => 7,
            StringKind::Utf8 => 12,
            StringKind::Numeric => 18,
            StringKind::Printable => 19,
            StringKind::Teletex => 20,
            StringKind::Videotex => 21,
            StringKind::Ia5 => 22,
            StringKind::UtcTime => 23,
            StringKind::GeneralizedTime => 24,
            StringKind::Graphic => 25,
            StringKind::Visible => 26,
            StringKind::General => 27,
            StringKind::Universal => 28,
            StringKind::Bmp => 30,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Boolean,
    Null,
    Integer(IntCons),
    /// Root values, then -- if there is a `...` -- the extension values after
    /// it. `Some(vec![])` is extensible with no extension values yet, which
    /// still costs an extension bit (X.691 14.2), so it must not be `None`.
    Enumerated(Vec<String>, Option<Vec<String>>),
    /// An ENUMERATED with numbers written on some items, `a(2), b, c(0)`, as
    /// the parser saw it. `constraints::resolve` assigns the values (X.680
    /// 20.3, 20.6) and makes it an `Enumerated` whose root is in X.691 14.1's
    /// index order: ascending by value.
    EnumeratedNum(Vec<(String, Option<Num>)>, Option<Vec<(String, Option<Num>)>>),
    BitString(SizeCons),
    /// `BIT STRING { a(0), b(1) }`: X.680 22.7 applies, so trailing 0 bits
    /// are not significant and X.691 16.2/16.3 send the shortest size
    /// that carries the value and satisfies the effective size constraint.
    NamedBitString(SizeCons),
    OctetString(SizeCons),
    /// OBJECT IDENTIFIER and RELATIVE-OID (X.680 32, 33): the contents octets
    /// of their BER encoding (X.690 8.19, 8.20) with a length (X.691 24, 25).
    /// Constraints on them are not PER-visible.
    ObjectId,
    RelativeOid,
    /// REAL (X.680 21): the contents octets of its CER/DER encoding (X.690
    /// 8.5, 11.3) with a length (X.691 15). Constraints on it are not
    /// PER-visible (X.691 10.3.14).
    Real,
    /// A character string, with its effective size constraint and effective
    /// permitted alphabet (X.691 10.3.12) as sorted disjoint ranges of code
    /// points, `None` for the whole alphabet.
    Str(StringKind, SizeCons, Option<Vec<(u32, u32)>>),
    /// Root fields, then the extension additions after `...`.
    Sequence(Vec<Field>, Option<Vec<ExtAdd>>),
    Choice(Vec<(String, Type)>, Option<Vec<(String, Type)>>),
    SequenceOf(SizeCons, Box<Type>),
    /// SET, as written. `constraints::resolve` sorts its root into canonical
    /// tag order (X.691 21) and makes it a `Sequence`.
    Set(Vec<Field>, Option<Vec<ExtAdd>>),
    /// SET OF: in BASIC-PER a SEQUENCE OF (X.691 22.2), which
    /// `constraints::resolve` makes it; its tag is UNIVERSAL 17 until then.
    SetOf(SizeCons, Box<Type>),
    Ref(String),
    /// `SetupRelease { PDSCH-Config }` and friends.
    ParamRef(String, Vec<String>),
    /// A type with constraints applied to it, serially, as written: `T (C1)
    /// (C2)`. Only the parser makes these, and `constraints::resolve` removes
    /// every one, so the backend never sees it.
    Constrained(Box<Type>, Vec<ConsSpec>),
    /// A type `constraints::resolve` could not make sense of, and why. The
    /// backend skips it with that reason.
    Invalid(String),
    /// `[class n] T`, IMPLICIT or EXPLICIT. Tags do not affect PER encodings
    /// (X.691 10.6.3) except through canonical order (10.2), which
    /// `constraints::resolve` settles before removing them.
    Tagged(Tag, Box<Type>),
    /// `OCTET STRING (CONTAINING T)` under `--containing decode`: a `T`,
    /// carried as its complete encoding (X.691 11.1) in an unconstrained
    /// OCTET STRING, which is an open type's encoding (11.2). Under the
    /// default, `--containing octets`, it stays an OCTET STRING.
    Contains(Box<Type>),
}

/// What `OCTET STRING (CONTAINING T)` compiles to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContainingMode {
    /// the octets, undecoded, as asn1c and VUPER do
    Octets,
    /// the `T` they encode, as pycrate does
    Decode,
}

/// X.680 8.1's tag classes, in X.680 8.6's canonical order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TagClass {
    Universal,
    Application,
    Context,
    Private,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tag {
    pub class: TagClass,
    pub num: Num,
}

/// The module's `TagDefault` (X.680 13.1): EXPLICIT when none is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TagDefault {
    Explicit,
    Implicit,
    Automatic,
}

/// One extension addition of a SEQUENCE. Each one costs a single bit in the
/// extension bitmap and is carried as a single open type, so a `[[ ... ]]`
/// group is **one** addition whose content is an implicit SEQUENCE -- not one
/// addition per field. Flattening a group changes the encoding, so the two
/// cases are kept apart here rather than merged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtAdd {
    One(Field),
    Group(Vec<Field>),
}

impl ExtAdd {
    pub fn fields(&self) -> &[Field] {
        match self {
            ExtAdd::One(f) => std::slice::from_ref(f),
            ExtAdd::Group(g) => g,
        }
    }
    pub fn fields_mut(&mut self) -> &mut [Field] {
        match self {
            ExtAdd::One(f) => std::slice::from_mut(f),
            ExtAdd::Group(g) => g,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Presence {
    Mandatory,
    Optional,
    Default(DefaultVal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefaultVal {
    Int(i64),
    Name(String),
    Bits(String),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    pub name: String,
    pub ty: Type,
    pub presence: Presence,
}

#[derive(Debug, Clone)]
pub enum Assignment {
    Type { name: String, ty: Type },
    Value { name: String, value: i64 },
    /// `Name { Param } ::= ...` — recorded but not expanded yet.
    ParamType { name: String, params: Vec<String>, ty: Type },
}

/// What a module's header says about the types written in it (X.680 13.1):
/// its `TagDefault`, and `EXTENSIBILITY IMPLIED` (13.4). Both apply to the
/// types textually in that module, wherever they are used from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModEnv {
    pub tag_default: TagDefault,
    pub ext_implied: bool,
}

/// One module as parsed, or several merged into one namespace (`merge`).
#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    /// the environment of an assignment not in `envs`
    pub env: ModEnv,
    /// per assignment name, where the modules merged had different headers
    pub envs: std::collections::HashMap<String, ModEnv>,
    /// names each module imports, and from where (X.680 13.16)
    pub imports: Vec<(String, String)>,
    pub assignments: Vec<Assignment>,
}

impl Module {
    pub fn env_of(&self, name: &str) -> ModEnv {
        self.envs.get(name).copied().unwrap_or(self.env)
    }
}

fn assignment_name(a: &Assignment) -> &str {
    match a {
        Assignment::Type { name, .. } | Assignment::Value { name, .. } | Assignment::ParamType { name, .. } => name,
    }
}

/// Every module of the input as one namespace. ASN.1 names are per module,
/// but the ones vasnc is given (NR's six, ETSI ITS's three) share one: a
/// name defined in two modules is an error unless both define it alike. Each
/// assignment keeps its own module's environment. An import that no module
/// defines is returned, for the caller to report.
pub fn merge(mods: Vec<Module>) -> Result<(Module, Vec<(String, String)>), String> {
    let mut out = Module {
        name: mods.iter().map(|m| m.name.as_str()).collect::<Vec<_>>().join(", "),
        env: mods.first().map_or(ModEnv { tag_default: TagDefault::Explicit, ext_implied: false }, |m| m.env),
        envs: std::collections::HashMap::new(),
        imports: Vec::new(),
        assignments: Vec::new(),
    };
    let mut seen: std::collections::HashMap<String, (String, usize)> = std::collections::HashMap::new();
    for m in mods {
        for a in m.assignments {
            let n = assignment_name(&a).to_string();
            if let Some((from, i)) = seen.get(&n) {
                let same = format!("{:?}", out.assignments[*i]) == format!("{a:?}")
                    && out.env_of(&n) == m.env;
                if same {
                    continue;
                }
                return Err(format!("`{n}` is defined in both {from} and {}, differently", m.name));
            }
            if m.env != out.env {
                out.envs.insert(n.clone(), m.env);
            }
            seen.insert(n, (m.name.clone(), out.assignments.len()));
            out.assignments.push(a);
        }
        out.imports.extend(m.imports);
    }
    let missing = out.imports.iter().filter(|(n, _)| !seen.contains_key(n)).cloned().collect();
    Ok((out, missing))
}

/// Reserved words that an ASN.1 identifier may legally be. 3GPP uses several
/// of them -- `ENUMERATED { true }` is a common presence flag, and `type`,
/// `ref` and `match` all turn up as field names.
const RUST_KEYWORDS: &[&str] = &[
    "as", "async", "await", "box", "break", "const", "continue", "crate", "do", "dyn", "else",
    "enum", "extern", "false", "final", "fn", "for", "if", "impl", "in", "let", "loop", "macro",
    "match", "mod", "move", "mut", "override", "priv", "pub", "ref", "return", "self", "Self",
    "static", "struct", "super", "trait", "true", "try", "type", "typeof", "unsafe", "unsized",
    "use", "virtual", "where", "while", "yield", "abstract", "become", "gen",
    // Verus keywords, which are equally unusable as identifiers here
    "spec", "proof", "exec", "ghost", "tracked", "requires", "ensures", "decreases", "invariant",
    "assert", "assume", "forall", "exists", "choose", "old", "closed", "open",
    // names every generated crate has in scope, from the Rust and vstd
    // preludes and vasn's glob imports: an ASN.1 type `Seq` or `Gen` would
    // shadow them
    "Seq", "Set", "Map", "Multiset", "Vec", "Option", "Some", "None", "Result", "Ok", "Err",
    "String", "Box", "Ghost", "Tracked", "Flg", "Wf", "Enc", "Dec", "Gen", "BitReader",
    "BitWriter", "LenHead", "Null", "DecodeError",
];

/// Hyphens are legal in ASN.1 identifiers and illegal in Rust ones; reserved
/// words get a trailing underscore.
pub fn rustify(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 1);
    for c in s.chars() {
        out.push(if c == '-' { '_' } else { c });
    }
    if RUST_KEYWORDS.contains(&out.as_str()) {
        out.push('_');
    }
    out
}
