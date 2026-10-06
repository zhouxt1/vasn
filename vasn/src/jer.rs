//! JER (ITU-T X.697 (02/2021)) printing of decoded values.
//!
//! Not verified, and not part of any format: this is how a decoded value is
//! shown to a person or compared against another decoder. Generated code
//! calls these for the terminal types and composes them for the rest; the
//! clause each follows is named on it. Nothing here is inside `verus!`, so
//! Verus treats the module as external.

/// X.697 20: `true` or `false`.
#[inline]
pub fn jer_bool(v: bool, o: &mut String) {
    o.push_str(if v { "true" } else { "false" });
}

/// X.697 21: a JSON number, no fraction, no exponent.
#[inline]
pub fn jer_int(v: i64, o: &mut String) {
    o.push_str(&v.to_string());
}

/// X.697 21, for an INTEGER whose values are all of `u64`'s.
#[inline]
pub fn jer_uint(v: u64, o: &mut String) {
    o.push_str(&v.to_string());
}

/// X.697 26.
#[inline]
pub fn jer_null(o: &mut String) {
    o.push_str("null");
}

/// A JSON string of an ASN.1 identifier -- an enumeration item (X.697 22),
/// or a member name (27.3.2, 31.3.2). Identifiers are letters, digits and
/// hyphens, so nothing needs escaping.
#[inline]
pub fn jer_ident(s: &str, o: &mut String) {
    o.push('"');
    o.push_str(s);
    o.push('"');
}

const HEX: &[u8; 16] = b"0123456789ABCDEF";

/// X.697 25.3: an OCTET STRING as a JSON string of hex digit pairs.
#[inline]
pub fn jer_octets(b: &[u8], o: &mut String) {
    o.push('"');
    for x in b {
        o.push(HEX[(x >> 4) as usize] as char);
        o.push(HEX[(x & 15) as usize] as char);
    }
    o.push('"');
}

/// X.697 24.2.1: a BIT STRING as hex digit pairs, padded with zero bits up to
/// a multiple of 8; empty if the value is.
#[inline]
fn hex_bits(b: &[bool], o: &mut String) {
    o.push('"');
    for chunk in b.chunks(8) {
        let mut x = 0u8;
        for (i, bit) in chunk.iter().enumerate() {
            if *bit {
                x |= 0x80 >> i;
            }
        }
        o.push(HEX[(x >> 4) as usize] as char);
        o.push(HEX[(x & 15) as usize] as char);
    }
    o.push('"');
}

/// X.697 24.2: a BIT STRING whose effective size constraint is one size.
#[inline]
pub fn jer_bits_fixed(b: &[bool], o: &mut String) {
    hex_bits(b, o);
}

/// X.697 24.3: any other BIT STRING, `{"value": hex, "length": bits}`.
#[inline]
pub fn jer_bits_var(b: &[bool], o: &mut String) {
    o.push_str("{\"value\":");
    hex_bits(b, o);
    o.push_str(",\"length\":");
    o.push_str(&b.len().to_string());
    o.push('}');
}

/// Opens a member of a JSON object: a comma unless it is the first, then
/// the name and the colon.
#[inline]
pub fn jer_member(name: &str, first: &mut bool, o: &mut String) {
    if !*first {
        o.push(',');
    }
    *first = false;
    jer_ident(name, o);
    o.push(':');
}

/// The value of an extension alternative this schema does not know. X.697
/// has no encoding for it -- JER encodes abstract values, and the decoder does
/// not know this one's type -- so the generated code puts it under a member
/// name no ASN.1 identifier can have, `?unknown-extension`, and this writes
/// the index and the open type's octets.
#[inline]
pub fn jer_unknown_alt(k: u64, b: &[u8], o: &mut String) {
    o.push_str("{\"index\":");
    o.push_str(&k.to_string());
    o.push_str(",\"octets\":");
    jer_octets(b, o);
    o.push('}');
}

/// One character of a JSON string, with the escapes RFC 8259 7 requires.
fn json_char(c: char, o: &mut String) {
    match c {
        '"' => o.push_str("\\\""),
        '\\' => o.push_str("\\\\"),
        c if (c as u32) < 0x20 || c as u32 == 0x7f => o.push_str(&format!("\\u{:04x}", c as u32)),
        c => o.push(c),
    }
}

/// A JSON string of `s`, with the escapes RFC 8259 7 requires.
fn json_str(s: &str, o: &mut String) {
    o.push('"');
    for c in s.chars() {
        json_char(c, o);
    }
    o.push('"');
}

/// X.697 38 (restricted character strings): a JSON string of the
/// characters, each given by its code (X.691 30.5.3: ISO 646 for the
/// octet-wide types, the ISO/IEC 10646 cell for BMPString and
/// UniversalString). A code that is not a Unicode scalar value -- a BMP
/// surrogate, or a UniversalString cell past U+10FFFF -- has no JSON
/// character; it is written `\uXXXX` (and past the BMP, as `\u{X}`, which is
/// not JSON), so that it at least shows.
#[inline]
pub fn jer_chars<T: Copy + Into<u32>>(v: &[T], o: &mut String) {
    o.push('"');
    for c in v {
        let c: u32 = (*c).into();
        match char::from_u32(c) {
            Some(ch) => json_char(ch, o),
            None if c <= 0xffff => o.push_str(&format!("\\u{c:04x}")),
            None => o.push_str(&format!("\\u{{{c:x}}}")),
        }
    }
    o.push('"');
}

/// X.697 38 for a string that is not known-multiplier (X.691 30.6), held as
/// its octets: each octet as the character of that code, which is right for
/// the ISO 646 (G0) characters every such type starts with.
#[inline]
pub fn jer_octet_chars(v: &[u8], o: &mut String) {
    o.push('"');
    for b in v {
        json_char(*b as char, o);
    }
    o.push('"');
}

/// X.697 38 for a UTF8String, whose octets the decoder has checked are UTF-8.
#[inline]
pub fn jer_utf8(v: &[u8], o: &mut String) {
    json_str(&String::from_utf8_lossy(v), o);
}

/// The subidentifiers of OID contents (X.690 8.19.2), each as decimal
/// digits, of any size.
fn subids(v: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    // little-endian base-10^9 limbs of the subidentifier being read
    let mut limbs: Vec<u64> = vec![0];
    for &b in v {
        let mut carry = (b & 0x7f) as u64;
        for l in limbs.iter_mut() {
            let x = *l * 128 + carry;
            *l = x % 1_000_000_000;
            carry = x / 1_000_000_000;
        }
        if carry > 0 {
            limbs.push(carry);
        }
        if b & 0x80 == 0 {
            let mut s = limbs.last().unwrap().to_string();
            for l in limbs.iter().rev().skip(1) {
                s.push_str(&format!("{l:09}"));
            }
            out.push(s.into_bytes());
            limbs = vec![0];
        }
    }
    out
}

/// X.697 29: an OBJECT IDENTIFIER as a JSON string of its arcs, dotted. The
/// first subidentifier is 40 X + Y (X.690 8.19.4).
pub fn jer_oid(v: &[u8], o: &mut String) {
    let ids = subids(v);
    o.push('"');
    for (i, d) in ids.iter().enumerate() {
        let s = String::from_utf8_lossy(d).into_owned();
        if i == 0 {
            // X = 0 or 1 below 80, else 2 and Y whatever is left
            let (x, y) = if s.len() <= 2 && s.parse::<u64>().unwrap() < 80 {
                let n: u64 = s.parse().unwrap();
                (n / 40, (n % 40).to_string())
            } else {
                (2, dec_sub(&s, 80))
            };
            o.push_str(&format!("{x}.{y}"));
        } else {
            o.push('.');
            o.push_str(&s);
        }
    }
    o.push('"');
}

/// X.697 30: a RELATIVE-OID as a JSON string of its arcs, dotted.
pub fn jer_roid(v: &[u8], o: &mut String) {
    let ids: Vec<String> = subids(v).into_iter().map(|d| String::from_utf8_lossy(&d).into_owned()).collect();
    o.push('"');
    o.push_str(&ids.join("."));
    o.push('"');
}

/// `s - k`, `s` a decimal at least `k`.
fn dec_sub(s: &str, k: u64) -> String {
    if s.len() <= 18 {
        return (s.parse::<u64>().unwrap() - k).to_string();
    }
    let mut d: Vec<u8> = s.bytes().map(|c| c - b'0').collect();
    let mut borrow = k;
    for x in d.iter_mut().rev() {
        let sub = (borrow % 10) as u8;
        borrow /= 10;
        if *x >= sub {
            *x -= sub;
        } else {
            *x = *x + 10 - sub;
            borrow += 1;
        }
        if borrow == 0 {
            break;
        }
    }
    let t: String = d.iter().map(|x| (x + b'0') as char).collect();
    t.trim_start_matches('0').to_string()
}

/// A non-negative integer as little-endian base-10^9 limbs, for printing
/// values past `u128`.
struct Dec(Vec<u64>);

impl Dec {
    fn from_be(b: &[u8]) -> Dec {
        let mut d = Dec(vec![0]);
        for &x in b {
            d.mul_add(256, x as u64);
        }
        d
    }
    fn mul_add(&mut self, m: u64, a: u64) {
        let mut carry = a;
        for l in self.0.iter_mut() {
            let x = *l * m + carry;
            *l = x % 1_000_000_000;
            carry = x / 1_000_000_000;
        }
        while carry > 0 {
            self.0.push(carry % 1_000_000_000);
            carry /= 1_000_000_000;
        }
    }
    fn digits(&self) -> String {
        let mut s = self.0.last().unwrap().to_string();
        for l in self.0.iter().rev().skip(1) {
            s.push_str(&format!("{l:09}"));
        }
        s
    }
}

/// X.697 23: a REAL, from its CER/DER contents octets (X.690 8.5, 11.3; the
/// decoder has checked they are in that form). A base-2 value is a JSON
/// number, written exactly; a base-10 one `{"base10Value": number}` (23.4,
/// for a REAL whose base is not constrained); the special values strings
/// (23.2).
pub fn jer_real(v: &[u8], o: &mut String) {
    if v.is_empty() {
        o.push('0');
        return;
    }
    match v[0] {
        0x40 => return o.push_str("\"INF\""),
        0x41 => return o.push_str("\"-INF\""),
        0x42 => return o.push_str("\"NaN\""),
        0x43 => return o.push_str("\"-0\""),
        _ => {}
    }
    if v[0] == 3 {
        // NR3, `[-]M.E[-]X` or `M.E+0`: a JSON number `[-]MEX`
        let t = String::from_utf8_lossy(&v[1..]).into_owned();
        let t = t.replacen(".E", "E", 1).replace("E+0", "E0");
        o.push_str("{\"base10Value\":");
        o.push_str(&t);
        o.push('}');
        return;
    }
    // binary: 1 S 00 00 FF, the exponent, N
    let neg = v[0] & 0x40 != 0;
    let (at, ne) = if v[0] & 3 < 3 { (1, (v[0] & 3) as usize + 1) } else { (2, v[1] as usize) };
    let eb = &v[at..at + ne];
    let n = &v[at + ne..];
    if neg {
        o.push('-');
    }
    if ne > 2 {
        // an exponent past 16 bits: no exact decimal worth writing
        let mut m = 0f64;
        for &x in n {
            m = m * 256.0 + x as f64;
        }
        let e = eb.iter().fold(if eb[0] & 0x80 != 0 { -1i128 } else { 0 }, |a, &x| (a << 8) | x as i128);
        let f = m * 2f64.powf(e as f64);
        o.push_str(&format!("{f:e}"));
        return;
    }
    let e: i64 = eb.iter().fold(if eb[0] & 0x80 != 0 { -1i64 } else { 0 }, |a, &x| (a << 8) | x as i64);
    let mut d = Dec::from_be(n);
    if e >= 0 {
        for _ in 0..e {
            d.mul_add(2, 0);
        }
        o.push_str(&d.digits());
    } else {
        // N 2^-k = N 5^k / 10^k
        let k = (-e) as usize;
        for _ in 0..k {
            d.mul_add(5, 0);
        }
        let s = d.digits();
        let (int, frac) = if s.len() > k {
            (s[..s.len() - k].to_string(), s[s.len() - k..].to_string())
        } else {
            ("0".to_string(), format!("{}{s}", "0".repeat(k - s.len())))
        };
        o.push_str(&int);
        o.push('.');
        o.push_str(&frac);
    }
}
