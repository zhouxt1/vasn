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

/// A JSON string of `s`, with the escapes RFC 8259 7 requires.
fn json_str(s: &str, o: &mut String) {
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
}

/// X.697 38 (restricted character strings): a JSON string of the
/// characters. For the known-multiplier types here every character is
/// ISO 646, one octet.
#[inline]
pub fn jer_chars(v: &[u8], o: &mut String) {
    let s: String = v.iter().map(|b| *b as char).collect();
    json_str(&s, o);
}

/// X.697 38 for a UTF8String, whose octets the decoder has checked are UTF-8.
#[inline]
pub fn jer_utf8(v: &[u8], o: &mut String) {
    json_str(&String::from_utf8_lossy(v), o);
}
