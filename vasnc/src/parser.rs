//! Recursive-descent parser for the ASN.1 subset VUPER targets.
use crate::ast::*;
use crate::lexer::{Lexer, Tok};

pub struct Parser {
    toks: Vec<(Tok, usize)>,
    i: usize,
}

type P<T> = Result<T, String>;

impl Parser {
    pub fn new(src: &str) -> P<Self> {
        Ok(Parser { toks: Lexer::tokenize(src)?, i: 0 })
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.i].0
    }
    fn peek_at(&self, k: usize) -> &Tok {
        self.toks.get(self.i + k).map(|t| &t.0).unwrap_or(&Tok::Eof)
    }
    fn line(&self) -> usize {
        self.toks[self.i].1
    }
    fn bump(&mut self) -> Tok {
        let t = self.toks[self.i].0.clone();
        if self.i + 1 < self.toks.len() {
            self.i += 1;
        }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == t {
            self.bump();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, t: &Tok) -> P<()> {
        if self.eat(t) {
            Ok(())
        } else {
            Err(format!("line {}: expected {:?}, found {:?}", self.line(), t, self.peek()))
        }
    }
    fn word(&mut self) -> P<String> {
        match self.bump() {
            Tok::Word(w) => Ok(w),
            other => Err(format!("line {}: expected a name, found {other:?}", self.line())),
        }
    }
    fn is_word(&self, w: &str) -> bool {
        matches!(self.peek(), Tok::Word(x) if x == w)
    }
    fn eat_word(&mut self, w: &str) -> bool {
        if self.is_word(w) {
            self.bump();
            true
        } else {
            false
        }
    }

    // ------------------------------------------------------------ module

    pub fn parse_module(&mut self) -> P<Module> {
        let name = self.word()?;
        // skip an OID after the module name
        if self.eat(&Tok::LBrace) {
            let mut depth = 1;
            while depth > 0 {
                match self.bump() {
                    Tok::LBrace => depth += 1,
                    Tok::RBrace => depth -= 1,
                    Tok::Eof => return Err("unterminated module identifier".into()),
                    _ => {}
                }
            }
        }
        if !self.eat_word("DEFINITIONS") {
            return Err(format!("line {}: expected DEFINITIONS", self.line()));
        }
        // X.680 13.1: [EncodingReferenceDefault] [TagDefault] [ExtensionDefault]
        let mut tag_default = TagDefault::Explicit;
        let mut ext_implied = false;
        while !self.eat(&Tok::Assign) {
            match self.bump() {
                Tok::Word(w) if w == "AUTOMATIC" => tag_default = TagDefault::Automatic,
                Tok::Word(w) if w == "IMPLICIT" => tag_default = TagDefault::Implicit,
                Tok::Word(w) if w == "EXPLICIT" => tag_default = TagDefault::Explicit,
                Tok::Word(w) if w == "IMPLIED" => ext_implied = true,
                Tok::Eof => return Err("expected ::= after DEFINITIONS".into()),
                _ => {}
            }
        }
        if !self.eat_word("BEGIN") {
            return Err(format!("line {}: expected BEGIN", self.line()));
        }
        // EXPORTS runs to the next `;`; IMPORTS is kept, to check against what
        // the other modules define
        let mut imports = Vec::new();
        loop {
            if self.eat_word("EXPORTS") {
                while !self.eat(&Tok::Semi) {
                    if matches!(self.peek(), Tok::Eof) {
                        return Err("unterminated EXPORTS".into());
                    }
                    self.bump();
                }
            } else if self.eat_word("IMPORTS") {
                imports = self.parse_imports()?;
            } else {
                break;
            }
        }
        let mut assignments = Vec::new();
        while !self.is_word("END") && !matches!(self.peek(), Tok::Eof) {
            if let Some(a) = self.parse_assignment()? {
                assignments.push(a);
            }
        }
        if !self.eat_word("END") {
            return Err(format!("module {name}: expected END"));
        }
        Ok(Module {
            name,
            env: ModEnv { tag_default, ext_implied },
            envs: std::collections::HashMap::new(),
            imports,
            assignments,
        })
    }

    /// Every module in the input, in order.
    pub fn parse_modules(&mut self) -> P<Vec<Module>> {
        let mut mods = Vec::new();
        while !matches!(self.peek(), Tok::Eof) {
            mods.push(self.parse_module()?);
        }
        if mods.is_empty() {
            return Err("no module in the input".into());
        }
        Ok(mods)
    }

    /// X.680 13.16: `SymbolList FROM ModuleReference [AssignedIdentifier]`,
    /// repeated, to `;`. A symbol may be written `Name{}` (a parameterised
    /// type). The AssignedIdentifier is an OID in braces or a value reference;
    /// a lower-case word after the module name is the first symbol of the
    /// next list instead when a `,` or `FROM` follows it (13.17).
    fn parse_imports(&mut self) -> P<Vec<(String, String)>> {
        let mut out = Vec::new();
        let mut syms: Vec<String> = Vec::new();
        loop {
            match self.bump() {
                Tok::Semi => break,
                Tok::Eof => return Err("unterminated IMPORTS".into()),
                Tok::Word(w) if w == "FROM" => {
                    let m = self.word()?;
                    for s in syms.drain(..) {
                        out.push((s, m.clone()));
                    }
                    if self.eat(&Tok::LBrace) {
                        let mut depth = 1;
                        while depth > 0 {
                            match self.bump() {
                                Tok::LBrace => depth += 1,
                                Tok::RBrace => depth -= 1,
                                Tok::Eof => return Err("unterminated IMPORTS".into()),
                                _ => {}
                            }
                        }
                    } else if let Tok::Word(v) = self.peek().clone() {
                        let lower = v.chars().next().is_some_and(|c| c.is_lowercase());
                        let is_sym = matches!(self.peek_at(1), Tok::Comma)
                            || matches!(self.peek_at(1), Tok::Word(x) if x == "FROM");
                        if lower && !is_sym {
                            self.bump();
                        }
                    }
                }
                Tok::Word(w) => {
                    // `Name{}`
                    if self.peek() == &Tok::LBrace && self.peek_at(1) == &Tok::RBrace {
                        self.bump();
                        self.bump();
                    }
                    syms.push(w);
                }
                Tok::Comma => {}
                other => return Err(format!("line {}: unexpected {other:?} in IMPORTS", self.line())),
            }
        }
        if !syms.is_empty() {
            return Err(format!("IMPORTS: {} without FROM", syms.join(", ")));
        }
        Ok(out)
    }

    /// A type or value assignment. A value of a type other than INTEGER --
    /// an OBJECT IDENTIFIER's `{ iso 3 }`, a string -- is read and dropped:
    /// no encoding depends on one.
    fn parse_assignment(&mut self) -> P<Option<Assignment>> {
        let name = self.word()?;
        // parameterised type: Name { P1, P2 } ::= ...
        if self.peek() == &Tok::LBrace && self.looks_like_params() {
            self.expect(&Tok::LBrace)?;
            let mut params = Vec::new();
            loop {
                params.push(self.word()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::RBrace)?;
            self.expect(&Tok::Assign)?;
            let ty = self.parse_type()?;
            return Ok(Some(Assignment::ParamType { name, params, ty }));
        }
        // value assignment: name INTEGER ::= 42
        if self.is_word("INTEGER") && self.peek_at(1) == &Tok::Assign {
            self.bump();
            self.expect(&Tok::Assign)?;
            let v = match self.bump() {
                Tok::Int(n) => n,
                other => return Err(format!("line {}: expected an integer, found {other:?}",
                                            self.line(), )),
            };
            return Ok(Some(Assignment::Value { name, value: v }));
        }
        // any other value assignment (X.680 16.2): a value reference begins
        // with a lower-case letter
        if name.starts_with(|c: char| c.is_ascii_lowercase()) && self.peek() != &Tok::Assign {
            self.parse_type()?;
            self.expect(&Tok::Assign)?;
            if self.peek() == &Tok::LBrace {
                self.skip_braced();
            } else {
                self.bump();
            }
            return Ok(None);
        }
        self.expect(&Tok::Assign)?;
        let ty = self.parse_type()?;
        Ok(Some(Assignment::Type { name, ty }))
    }

    /// `X { A } ::=` is a parameter list; `X ::= SEQUENCE { ... }` is not.
    fn looks_like_params(&self) -> bool {
        let mut k = 1;
        let mut depth = 1;
        while depth > 0 {
            match self.peek_at(k) {
                Tok::LBrace => depth += 1,
                Tok::RBrace => depth -= 1,
                Tok::Eof => return false,
                _ => {}
            }
            k += 1;
        }
        self.peek_at(k) == &Tok::Assign
    }

    // -------------------------------------------------------------- types

    /// A type and whatever constraints follow it, applied serially
    /// (X.680 49.1: `Type Constraint Constraint ...`).
    pub fn parse_type(&mut self) -> P<Type> {
        let ty = self.parse_type_inner()?;
        let mut specs = Vec::new();
        while self.peek() == &Tok::LParen {
            specs.push(self.parse_constraint()?);
        }
        Ok(if specs.is_empty() { ty } else { Type::Constrained(Box::new(ty), specs) })
    }

    fn parse_type_inner(&mut self) -> P<Type> {
        // a tag, `[n]`, `[APPLICATION n]`, then IMPLICIT or EXPLICIT (X.680 31)
        if self.eat(&Tok::LBracket) {
            let class = if self.eat_word("UNIVERSAL") {
                TagClass::Universal
            } else if self.eat_word("APPLICATION") {
                TagClass::Application
            } else if self.eat_word("PRIVATE") {
                TagClass::Private
            } else {
                TagClass::Context
            };
            let num = self.parse_num()?;
            self.expect(&Tok::RBracket)?;
            let _ = self.eat_word("IMPLICIT") || self.eat_word("EXPLICIT");
            let inner = self.parse_type()?;
            return Ok(Type::Tagged(Tag { class, num }, Box::new(inner)));
        }
        if self.eat_word("BOOLEAN") {
            return Ok(Type::Boolean);
        }
        if self.eat_word("NULL") {
            return Ok(Type::Null);
        }
        if self.eat_word("INTEGER") {
            // a named-number list `INTEGER { unavailable(0), ... }` does not
            // affect the encoding
            if self.peek() == &Tok::LBrace {
                self.skip_braced();
            }
            return Ok(Type::Integer(IntCons::None));
        }
        if self.eat_word("ENUMERATED") {
            return self.parse_enumerated();
        }
        if self.is_word("BIT") && matches!(self.peek_at(1), Tok::Word(w) if w == "STRING") {
            self.bump();
            self.bump();
            // a named bit list: the names do not affect the encoding, but
            // having one does (X.691 16.2, 16.3)
            if self.peek() == &Tok::LBrace {
                self.skip_braced();
                return Ok(Type::NamedBitString(SizeCons::None));
            }
            return Ok(Type::BitString(SizeCons::None));
        }
        if self.is_word("OBJECT") && matches!(self.peek_at(1), Tok::Word(w) if w == "IDENTIFIER") {
            self.bump();
            self.bump();
            return Ok(Type::ObjectId);
        }
        if self.eat_word("RELATIVE-OID") {
            return Ok(Type::RelativeOid);
        }
        if self.eat_word("REAL") {
            return Ok(Type::Real);
        }
        if self.is_word("OCTET") && matches!(self.peek_at(1), Tok::Word(w) if w == "STRING") {
            self.bump();
            self.bump();
            return Ok(Type::OctetString(SizeCons::None));
        }
        for (kw, kind) in [
            ("IA5String", StringKind::Ia5),
            ("NumericString", StringKind::Numeric),
            ("PrintableString", StringKind::Printable),
            ("VisibleString", StringKind::Visible),
            ("UTF8String", StringKind::Utf8),
            ("ISO646String", StringKind::Visible),
            ("BMPString", StringKind::Bmp),
            ("UniversalString", StringKind::Universal),
            ("GeneralString", StringKind::General),
            ("GraphicString", StringKind::Graphic),
            ("TeletexString", StringKind::Teletex),
            ("T61String", StringKind::Teletex),
            ("VideotexString", StringKind::Videotex),
            ("GeneralizedTime", StringKind::GeneralizedTime),
            ("UTCTime", StringKind::UtcTime),
            ("ObjectDescriptor", StringKind::ObjectDescriptor),
        ] {
            if self.eat_word(kw) {
                return Ok(Type::Str(kind, SizeCons::None, None));
            }
        }
        if self.is_word("SEQUENCE") {
            self.bump();
            // SEQUENCE OF, SEQUENCE (SIZE (..)) OF, SEQUENCE SIZE (..) OF:
            // a constraint on the SEQUENCE OF type itself (X.680 49.4)
            let spec = if self.peek() == &Tok::LParen {
                Some(self.parse_constraint()?)
            } else if self.is_word("SIZE") {
                self.bump();
                let inner = self.parse_constraint()?;
                Some(ConsSpec { root: SetExpr::Elem(Elem::Size(Box::new(inner))), ext: false, adds: None })
            } else {
                None
            };
            if self.eat_word("OF") {
                // an optional element name is allowed before the type
                if matches!(self.peek(), Tok::Word(_)) && self.element_name_ahead() {
                    self.bump();
                }
                let inner = self.parse_type()?;
                let t = Type::SequenceOf(SizeCons::None, Box::new(inner));
                return Ok(match spec {
                    Some(c) => Type::Constrained(Box::new(t), vec![c]),
                    None => t,
                });
            }
            if spec.is_some() {
                return Err(format!("line {}: expected OF after SEQUENCE and a constraint", self.line()));
            }
            let (root, ext) = self.parse_fields()?;
            return Ok(Type::Sequence(root, ext));
        }
        if self.is_word("SET") {
            self.bump();
            let spec = if self.peek() == &Tok::LParen {
                Some(self.parse_constraint()?)
            } else if self.is_word("SIZE") {
                self.bump();
                let inner = self.parse_constraint()?;
                Some(ConsSpec { root: SetExpr::Elem(Elem::Size(Box::new(inner))), ext: false, adds: None })
            } else {
                None
            };
            if self.eat_word("OF") {
                if matches!(self.peek(), Tok::Word(_)) && self.element_name_ahead() {
                    self.bump();
                }
                let inner = self.parse_type()?;
                let t = Type::SetOf(SizeCons::None, Box::new(inner));
                return Ok(match spec {
                    Some(c) => Type::Constrained(Box::new(t), vec![c]),
                    None => t,
                });
            }
            if spec.is_some() {
                return Err(format!("line {}: expected OF after SET and a constraint", self.line()));
            }
            let (root, ext) = self.parse_fields()?;
            return Ok(Type::Set(root, ext));
        }
        if self.eat_word("CHOICE") {
            let (root, ext) = self.parse_alternatives()?;
            return Ok(Type::Choice(root, ext));
        }
        // a type reference, possibly parameterised
        let name = self.word()?;
        if self.peek() == &Tok::LBrace {
            self.expect(&Tok::LBrace)?;
            let mut args = Vec::new();
            loop {
                args.push(self.word()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::RBrace)?;
            return Ok(Type::ParamRef(name, args));
        }
        Ok(Type::Ref(name))
    }

    /// In `SEQUENCE OF elemName ElemType`, the lowercase word is a label.
    fn element_name_ahead(&self) -> bool {
        matches!(self.peek(), Tok::Word(w) if w.chars().next().is_some_and(|c| c.is_lowercase()))
            && matches!(self.peek_at(1), Tok::Word(_))
    }

    fn parse_enumerated(&mut self) -> P<Type> {
        self.expect(&Tok::LBrace)?;
        let mut root: Vec<(String, Option<Num>)> = Vec::new();
        let mut ext: Option<Vec<(String, Option<Num>)>> = None;
        loop {
            if self.peek() == &Tok::RBrace {
                break;
            }
            if self.eat(&Tok::Ellipsis) {
                ext = Some(Vec::new());
                // an exception specification, `...!value`, affects no encoding
                if self.eat(&Tok::Bang) {
                    self.bump();
                }
            } else {
                let n = self.word()?;
                // `name(3)` or `name(someValue)`: a NamedNumber (X.680 20.1)
                let num = if self.eat(&Tok::LParen) {
                    let v = self.parse_num()?;
                    self.expect(&Tok::RParen)?;
                    Some(v)
                } else {
                    None
                };
                match ext.as_mut() {
                    Some(e) => e.push((n, num)),
                    None => root.push((n, num)),
                }
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RBrace)?;
        let numbered = root.iter().chain(ext.iter().flatten()).any(|(_, v)| v.is_some());
        if numbered {
            return Ok(Type::EnumeratedNum(root, ext));
        }
        let names = |v: Vec<(String, Option<Num>)>| v.into_iter().map(|(n, _)| n).collect::<Vec<_>>();
        Ok(Type::Enumerated(names(root), ext.map(names)))
    }

    fn parse_fields(&mut self) -> P<(Vec<Field>, Option<Vec<ExtAdd>>)> {
        self.expect(&Tok::LBrace)?;
        let mut root = Vec::new();
        let mut ext: Option<Vec<ExtAdd>> = None;
        // X.680 25.1: `root, ..., additions, ..., root`: components after a
        // second extension marker are root components again, after the first
        // root list (the whole root is both lists, in order)
        let mut after_end = false;
        loop {
            if self.peek() == &Tok::RBrace {
                break;
            }
            if self.eat(&Tok::Ellipsis) {
                if ext.is_none() {
                    ext = Some(Vec::new());
                } else if after_end {
                    return Err(format!("line {}: a third extension marker (X.680 25.1)", self.line()));
                } else {
                    after_end = true;
                }
                // an exception spec, `...!value`, affects no encoding
                if self.eat(&Tok::Bang) {
                    self.bump();
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
                continue;
            }
            // extension addition group `[[ ... ]]` -- one addition, not one per
            // field, so it is kept whole
            if self.peek() == &Tok::LBracket2 && after_end {
                return Err(format!("line {}: an extension addition group after the extension end marker", self.line()));
            }
            if self.eat(&Tok::LBracket2) {
                // an optional version number precedes the fields
                // an extension-group version number, `[[ 3: field Type ]]`
                if matches!(self.peek(), Tok::Int(_)) && self.peek_at(1) == &Tok::Colon {
                    self.bump();
                    self.bump();
                }
                let mut group = Vec::new();
                loop {
                    if self.peek() == &Tok::RBracket2 {
                        break;
                    }
                    group.push(self.parse_field()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(&Tok::RBracket2)?;
                ext.get_or_insert_with(Vec::new).push(ExtAdd::Group(group));
                if !self.eat(&Tok::Comma) {
                    break;
                }
                continue;
            }
            let f = self.parse_field()?;
            match ext.as_mut() {
                Some(e) if !after_end => e.push(ExtAdd::One(f)),
                _ => root.push(f),
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RBrace)?;
        Ok((root, ext))
    }

    fn parse_field(&mut self) -> P<Field> {
        let name = self.word()?;
        let ty = self.parse_type()?;
        let presence = if self.eat_word("OPTIONAL") {
            Presence::Optional
        } else if self.eat_word("DEFAULT") {
            Presence::Default(self.parse_default()?)
        } else {
            Presence::Mandatory
        };
        Ok(Field { name, ty, presence })
    }

    fn parse_default(&mut self) -> P<DefaultVal> {
        Ok(match self.bump() {
            Tok::Int(n) => DefaultVal::Int(n),
            Tok::BString(b) => DefaultVal::Bits(b),
            Tok::HString(h) => DefaultVal::Bits(h),
            Tok::Word(w) if w == "TRUE" => DefaultVal::Bool(true),
            Tok::Word(w) if w == "FALSE" => DefaultVal::Bool(false),
            Tok::Word(w) => DefaultVal::Name(w),
            other => return Err(format!("line {}: bad DEFAULT value {other:?}", self.line())),
        })
    }

    fn parse_alternatives(&mut self) -> P<(Vec<(String, Type)>, Option<Vec<(String, Type)>>)> {
        self.expect(&Tok::LBrace)?;
        let mut root = Vec::new();
        let mut ext: Option<Vec<(String, Type)>> = None;
        loop {
            if self.peek() == &Tok::RBrace {
                break;
            }
            if self.eat(&Tok::Ellipsis) {
                if ext.is_none() {
                    ext = Some(Vec::new());
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
                continue;
            }
            if self.eat(&Tok::LBracket2) {
                let mut group = Vec::new();
                loop {
                    if self.peek() == &Tok::RBracket2 {
                        break;
                    }
                    let n = self.word()?;
                    let t = self.parse_type()?;
                    group.push((n, t));
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(&Tok::RBracket2)?;
                ext.get_or_insert_with(Vec::new).extend(group);
                if !self.eat(&Tok::Comma) {
                    break;
                }
                continue;
            }
            let n = self.word()?;
            let t = self.parse_type()?;
            match ext.as_mut() {
                Some(e) => e.push((n, t)),
                None => root.push((n, t)),
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RBrace)?;
        Ok((root, ext))
    }

    // -------------------------------------------------------- constraints
    //
    // The grammar of X.680 49-51, as written. What it means for PER is
    // `constraints::resolve`'s business, not the parser's.

    fn parse_num(&mut self) -> P<Num> {
        match self.bump() {
            Tok::Int(n) => Ok(Num::Lit(n)),
            Tok::Word(w) => Ok(Num::Ref(w)),
            other => Err(format!("line {}: expected a bound, found {other:?}", self.line())),
        }
    }

    /// `( ConstraintSpec ExceptionSpec )` (X.680 49.6).
    fn parse_constraint(&mut self) -> P<ConsSpec> {
        self.expect(&Tok::LParen)?;
        let spec = self.parse_constraint_spec()?;
        // an exception specification, `! value`, affects no encoding
        if self.eat(&Tok::Bang) {
            self.skip_to_close()?;
        }
        self.expect(&Tok::RParen)?;
        Ok(spec)
    }

    fn not_visible() -> ConsSpec {
        ConsSpec { root: SetExpr::Elem(Elem::NotVisible), ext: false, adds: None }
    }

    /// Everything up to the `)` that closes the current constraint.
    fn skip_to_close(&mut self) -> P<()> {
        let mut depth = 0i32;
        loop {
            match self.peek() {
                Tok::RParen if depth == 0 => return Ok(()),
                Tok::LParen | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBrace => depth -= 1,
                Tok::Eof => return Err("unterminated constraint".into()),
                _ => {}
            }
            self.bump();
        }
    }

    /// `SubtypeConstraint` (an `ElementSetSpecs`) or a `GeneralConstraint`
    /// (X.682: user-defined, table, contents constraints).
    fn parse_constraint_spec(&mut self) -> P<ConsSpec> {
        // X.682 9: user-defined constraints are never PER-visible (10.3.3)
        if self.is_word("CONSTRAINED") {
            self.skip_to_close()?;
            return Ok(Self::not_visible());
        }
        // X.682 10: a table or component relation constraint, `({Set})` or
        // `({Set}{@id})` -- never PER-visible (10.3.4, 10.3.5). A brace
        // before a number is a value instead: a character's `{ group, plane,
        // row, cell }` (X.680 41.8), as in `({0,0,0,65}..{0,0,0,70})`
        if self.peek() == &Tok::LBrace && !matches!(self.peek_at(1), Tok::Int(_)) {
            self.skip_to_close()?;
            return Ok(Self::not_visible());
        }
        // X.682 11: a contents constraint, CONTAINING T [ENCODED BY v]
        if self.eat_word("CONTAINING") {
            let t = self.parse_type()?;
            let by = self.eat_word("ENCODED");
            if by {
                self.skip_to_close()?;
            }
            return Ok(ConsSpec { root: SetExpr::Elem(Elem::Containing(Box::new(t), by)), ext: false, adds: None });
        }
        if self.is_word("ENCODED") {
            self.skip_to_close()?;
            return Ok(Self::not_visible());
        }
        // `( ... )`: an extensible constraint with nothing in its root
        if self.eat(&Tok::Ellipsis) {
            let adds = if self.eat(&Tok::Comma) { Some(self.parse_set()?) } else { None };
            return Ok(ConsSpec { root: SetExpr::AllExcept(Box::new(SetExpr::Union(vec![]))), ext: true, adds });
        }
        let root = self.parse_set()?;
        let mut ext = false;
        let mut adds = None;
        if self.peek() == &Tok::Comma && self.peek_at(1) == &Tok::Ellipsis {
            self.bump();
            self.bump();
            ext = true;
            if self.eat(&Tok::Comma) {
                adds = Some(self.parse_set()?);
            }
        }
        Ok(ConsSpec { root, ext, adds })
    }

    /// `ElementSetSpec ::= Unions | ALL Exclusions` (X.680 50.1).
    fn parse_set(&mut self) -> P<SetExpr> {
        if self.eat_word("ALL") {
            if !self.eat_word("EXCEPT") {
                return Err(format!("line {}: expected EXCEPT after ALL", self.line()));
            }
            let e = self.parse_elements()?;
            return Ok(SetExpr::AllExcept(Box::new(e)));
        }
        let mut us = vec![self.parse_intersections()?];
        while self.eat(&Tok::Pipe) || self.eat_word("UNION") {
            us.push(self.parse_intersections()?);
        }
        Ok(if us.len() == 1 { us.pop().unwrap() } else { SetExpr::Union(us) })
    }

    fn parse_intersections(&mut self) -> P<SetExpr> {
        let mut is = vec![self.parse_intersection_elements()?];
        while self.eat(&Tok::Caret) || self.eat_word("INTERSECTION") {
            is.push(self.parse_intersection_elements()?);
        }
        Ok(if is.len() == 1 { is.pop().unwrap() } else { SetExpr::Inter(is) })
    }

    fn parse_intersection_elements(&mut self) -> P<SetExpr> {
        let e = self.parse_elements()?;
        if self.eat_word("EXCEPT") {
            let x = self.parse_elements()?;
            return Ok(SetExpr::Except(Box::new(e), Box::new(x)));
        }
        Ok(e)
    }

    /// `Elements ::= SubtypeElements | "(" ElementSetSpec ")"` (X.680 50.6).
    fn parse_elements(&mut self) -> P<SetExpr> {
        if self.peek() == &Tok::LParen {
            // a nested `ElementSetSpec`, which may itself be extensible
            self.bump();
            let spec = self.parse_constraint_spec()?;
            self.expect(&Tok::RParen)?;
            return Ok(SetExpr::Elem(Elem::Nested(Box::new(spec))));
        }
        Ok(SetExpr::Elem(self.parse_subtype_element()?))
    }

    /// X.680 51.
    fn parse_subtype_element(&mut self) -> P<Elem> {
        if self.eat_word("SIZE") {
            return Ok(Elem::Size(Box::new(self.parse_constraint()?)));
        }
        if self.eat_word("FROM") {
            return Ok(Elem::From(Box::new(self.parse_constraint()?)));
        }
        if self.eat_word("INCLUDES") {
            return Ok(Elem::Contained(self.word()?));
        }
        // inner subtyping (51.8), a pattern (51.9), property settings (51.10):
        // none is PER-visible for anything vasnc compiles
        if self.eat_word("WITH") {
            self.bump(); // COMPONENT or COMPONENTS
            if self.peek() == &Tok::LBrace {
                self.skip_braced();
            } else {
                self.parse_constraint()?;
            }
            return Ok(Elem::NotVisible);
        }
        if self.eat_word("PATTERN") || self.eat_word("SETTINGS") {
            self.bump();
            return Ok(Elem::NotVisible);
        }
        // a value range, or a single value
        let lo = self.parse_bound_or_value()?;
        let lo_open = self.eat(&Tok::Less);
        if self.eat(&Tok::Range) {
            let hi_open = self.eat(&Tok::Less);
            let hi = self.parse_bound_or_value()?;
            return match (lo, hi) {
                (Ok(a), Ok(b)) => Ok(Elem::Range(a, lo_open, b, hi_open)),
                (Err(CValue::Chars(a)), Err(CValue::Chars(b))) if a.chars().count() == 1 && b.chars().count() == 1 => {
                    if lo_open || hi_open {
                        return Err(format!("line {}: open ends on a character range", self.line()));
                    }
                    Ok(Elem::CharRange(a.chars().next().unwrap(), b.chars().next().unwrap()))
                }
                _ => Err(format!("line {}: a range needs integer or single-character ends", self.line())),
            };
        }
        if lo_open {
            return Err(format!("line {}: `<` outside a range", self.line()));
        }
        Ok(match lo {
            Ok(Bound::Val(n)) => Elem::Value(CValue::Int(n)),
            Ok(_) => return Err(format!("line {}: MIN or MAX outside a range", self.line())),
            // an upper-case name in value position is a type: a contained
            // subtype (51.3); value references begin with a lower-case letter
            Err(CValue::Name(n)) if n.starts_with(|c: char| c.is_ascii_uppercase()) => Elem::Contained(n),
            Err(v) => Elem::Value(v),
        })
    }

    /// A range end (`Ok`), or a value that cannot be one (`Err`).
    fn parse_bound_or_value(&mut self) -> P<Result<Bound, CValue>> {
        Ok(match self.bump() {
            Tok::Int(n) => Ok(Bound::Val(Num::Lit(n))),
            Tok::Word(w) if w == "MIN" => Ok(Bound::Min),
            Tok::Word(w) if w == "MAX" => Ok(Bound::Max),
            Tok::Word(w) if w == "TRUE" => Err(CValue::Bool(true)),
            Tok::Word(w) if w == "FALSE" => Err(CValue::Bool(false)),
            // a lower-case name may be a value reference, resolved later
            Tok::Word(w) if w.starts_with(|c: char| c.is_ascii_lowercase()) => Ok(Bound::Val(Num::Ref(w))),
            Tok::Word(w) => Err(CValue::Name(w)),
            Tok::CString(c) => Err(CValue::Chars(c)),
            Tok::BString(b) => Err(CValue::Bits(b, 'B')),
            Tok::HString(h) => Err(CValue::Bits(h, 'H')),
            // `{ col, row }` or `{ group, plane, row, cell }`: one character,
            // by its position in the character table (X.680 41.8)
            Tok::LBrace => {
                let mut parts = Vec::new();
                loop {
                    match self.bump() {
                        Tok::Int(n) => parts.push(n),
                        other => return Err(format!("line {}: bad character tuple {other:?}", self.line())),
                    }
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(&Tok::RBrace)?;
                let code = match parts.as_slice() {
                    [col, row] => col * 16 + row,
                    [g, p, r, c] => ((g * 256 + p) * 256 + r) * 256 + c,
                    _ => return Err(format!("line {}: a character tuple has 2 or 4 numbers", self.line())),
                };
                let ch = char::from_u32(code as u32)
                    .ok_or_else(|| format!("line {}: character {code} out of range", self.line()))?;
                Err(CValue::Chars(ch.to_string()))
            }
            other => return Err(format!("line {}: expected a value, found {other:?}", self.line())),
        })
    }

    fn skip_braced(&mut self) {
        let mut depth = 0;
        loop {
            match self.bump() {
                Tok::LBrace => depth += 1,
                Tok::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return;
                    }
                }
                Tok::Eof => return,
                _ => {}
            }
        }
    }
}
