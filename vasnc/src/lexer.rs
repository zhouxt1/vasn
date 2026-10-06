//! Hand-rolled ASN.1 lexer. No dependencies, so the compiler builds offline.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tok {
    /// Identifier or keyword; hyphens are kept as written.
    Word(String),
    Int(i64),
    /// an integer outside `i64`, as a bound may be: the 3GPP protocols'
    /// counters are `INTEGER (0..18446744073709551615)`
    BigInt(i128),
    BString(String),
    HString(String),
    Assign,     // ::=
    Range,      // ..
    Ellipsis,   // ...
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket2,  // [[
    RBracket2,  // ]]
    LBracket,
    RBracket,
    Comma,
    Pipe,
    Semi,
    Colon,
    /// `^`, INTERSECTION
    Caret,
    /// `<` in an open range end, `lb<..ub`
    Less,
    /// `!`, before an exception identifier
    Bang,
    /// `@`, in a component relation constraint
    At,
    /// `.`, in a dotted value or component reference
    Dot,
    /// `"..."`, a character string literal (X.680 12.14; `""` is a quote)
    CString(String),
    /// `&name`, a field of an information object class (X.681 7.5, 7.6):
    /// `&id` a value field, `&Value` a type field. The name is without `&`.
    Field(String),
    Eof,
}

pub struct Lexer {
    src: Vec<char>,
    i: usize,
    pub line: usize,
}

impl Lexer {
    pub fn new(src: &str) -> Self {
        Lexer { src: src.chars().collect(), i: 0, line: 1 }
    }

    fn peek(&self, k: usize) -> Option<char> {
        self.src.get(self.i + k).copied()
    }

    fn skip_trivia(&mut self) {
        loop {
            match self.peek(0) {
                Some(c) if c.is_whitespace() => {
                    if c == '\n' {
                        self.line += 1;
                    }
                    self.i += 1;
                }
                // `-- comment` runs to end of line or to a closing `--`
                Some('-') if self.peek(1) == Some('-') => {
                    self.i += 2;
                    loop {
                        match self.peek(0) {
                            None | Some('\n') => break,
                            Some('-') if self.peek(1) == Some('-') => {
                                self.i += 2;
                                break;
                            }
                            _ => self.i += 1,
                        }
                    }
                }
                // `/* ... */`, which 3GPP files do use
                Some('/') if self.peek(1) == Some('*') => {
                    self.i += 2;
                    let mut depth = 1;
                    while depth > 0 && self.peek(0).is_some() {
                        if self.peek(0) == Some('*') && self.peek(1) == Some('/') {
                            depth -= 1;
                            self.i += 2;
                        } else if self.peek(0) == Some('/') && self.peek(1) == Some('*') {
                            depth += 1;
                            self.i += 2;
                        } else {
                            if self.peek(0) == Some('\n') {
                                self.line += 1;
                            }
                            self.i += 1;
                        }
                    }
                }
                _ => return,
            }
        }
    }

    pub fn next(&mut self) -> Result<Tok, String> {
        self.skip_trivia();
        let c = match self.peek(0) {
            None => return Ok(Tok::Eof),
            Some(c) => c,
        };
        // multi-character punctuation first
        if c == ':' && self.peek(1) == Some(':') && self.peek(2) == Some('=') {
            self.i += 3;
            return Ok(Tok::Assign);
        }
        if c == '.' && self.peek(1) == Some('.') {
            if self.peek(2) == Some('.') {
                self.i += 3;
                return Ok(Tok::Ellipsis);
            }
            self.i += 2;
            return Ok(Tok::Range);
        }
        if c == '[' && self.peek(1) == Some('[') {
            self.i += 2;
            return Ok(Tok::LBracket2);
        }
        if c == ']' && self.peek(1) == Some(']') {
            self.i += 2;
            return Ok(Tok::RBracket2);
        }
        let single = match c {
            '{' => Some(Tok::LBrace),
            '}' => Some(Tok::RBrace),
            '(' => Some(Tok::LParen),
            ')' => Some(Tok::RParen),
            '[' => Some(Tok::LBracket),
            ']' => Some(Tok::RBracket),
            ',' => Some(Tok::Comma),
            '|' => Some(Tok::Pipe),
            ';' => Some(Tok::Semi),
            ':' => Some(Tok::Colon),
            '^' => Some(Tok::Caret),
            '<' => Some(Tok::Less),
            '!' => Some(Tok::Bang),
            '@' => Some(Tok::At),
            '.' => Some(Tok::Dot),
            _ => None,
        };
        if let Some(t) = single {
            self.i += 1;
            return Ok(t);
        }
        if c == '&' && self.peek(1).is_some_and(|d| d.is_ascii_alphabetic()) {
            self.i += 1;
            let mut s = String::new();
            while let Some(ch) = self.peek(0) {
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    s.push(ch);
                    self.i += 1;
                } else if ch == '-' && self.peek(1).map_or(false, |d| d.is_ascii_alphanumeric()) {
                    s.push(ch);
                    self.i += 1;
                } else {
                    break;
                }
            }
            return Ok(Tok::Field(s));
        }
        if c == '"' {
            let mut body = String::new();
            self.i += 1;
            loop {
                match self.peek(0) {
                    None => return Err(format!("line {}: unterminated character string", self.line)),
                    Some('"') if self.peek(1) == Some('"') => {
                        body.push('"');
                        self.i += 2;
                    }
                    Some('"') => {
                        self.i += 1;
                        break;
                    }
                    Some(ch) => {
                        if ch == '\n' {
                            self.line += 1;
                        }
                        body.push(ch);
                        self.i += 1;
                    }
                }
            }
            return Ok(Tok::CString(body));
        }
        // bit/hex string literals
        if c == '\'' {
            let mut body = String::new();
            self.i += 1;
            while let Some(ch) = self.peek(0) {
                if ch == '\'' {
                    break;
                }
                body.push(ch);
                self.i += 1;
            }
            if self.peek(0) != Some('\'') {
                return Err(format!("line {}: unterminated quoted string", self.line));
            }
            self.i += 1;
            return match self.peek(0) {
                Some('B') => {
                    self.i += 1;
                    Ok(Tok::BString(body))
                }
                Some('H') => {
                    self.i += 1;
                    Ok(Tok::HString(body))
                }
                _ => Err(format!("line {}: quoted string needs a B or H suffix", self.line)),
            };
        }
        if c.is_ascii_digit() || (c == '-' && self.peek(1).map_or(false, |d| d.is_ascii_digit())) {
            let mut s = String::new();
            if c == '-' {
                s.push('-');
                self.i += 1;
            }
            while let Some(ch) = self.peek(0) {
                if ch.is_ascii_digit() {
                    s.push(ch);
                    self.i += 1;
                } else {
                    break;
                }
            }
            if let Ok(v) = s.parse::<i64>() {
                return Ok(Tok::Int(v));
            }
            return s
                .parse::<i128>()
                .map(Tok::BigInt)
                .map_err(|_| format!("line {}: bad integer {s}", self.line));
        }
        if c.is_ascii_alphabetic() {
            let mut s = String::new();
            while let Some(ch) = self.peek(0) {
                // a hyphen is part of the name only if a name character follows
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    s.push(ch);
                    self.i += 1;
                } else if ch == '-' && self.peek(1).map_or(false, |d| d.is_ascii_alphanumeric()) {
                    s.push(ch);
                    self.i += 1;
                } else {
                    break;
                }
            }
            return Ok(Tok::Word(s));
        }
        Err(format!("line {}: unexpected character {c:?}", self.line))
    }

    pub fn tokenize(src: &str) -> Result<Vec<(Tok, usize)>, String> {
        let mut lx = Lexer::new(src);
        let mut out = Vec::new();
        loop {
            let line = lx.line;
            let t = lx.next()?;
            let done = t == Tok::Eof;
            out.push((t, line));
            if done {
                return Ok(out);
            }
        }
    }
}
