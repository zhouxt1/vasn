# X.691 test modules

Each `NAME.asn1` exercises a group of ASN.1 constructs, and `NAME.vec` holds
encodings of them derived by hand from ITU-T X.691 (02/2021) and X.680, the
clause given on each line. X.691 is the judge. pycrate 0.7.11, asn1c
(mouse07410, `tools/get-asn1c.sh`) and rasn 0.28.14 (with rasn-compiler
0.16.0's bindings, `bench/decode/build.sh` installs it) are the reference
implementations that the results are checked against, and each disagreement
with X.691 found in them is recorded below.

```sh
tests/x691/run.sh            # every module, 40 random values each
tools/xcheck.py tests/x691/enumerated.asn1 --vectors tests/x691/enumerated.vec -n 200 --verify
```

`tools/xcheck.py` builds ours (vasnc and its `--driver`), pycrate's module
asn1c's converter and a rasn driver for the schema, then:

* checks each vector against all three decoders, and that ours re-encodes it
  to the same bytes, same version;
* draws random values from our generator, encodes them with our verified
  encoder, and checks that pycrate, asn1c and rasn decode each to the same value
  (compared as JER, X.697) and re-encode it to the same bytes;
* with `--verify`, verifies the generated module with Verus.

A reference that cannot parse a construct is left out for that module, and
xcheck says so. Where neither can, the vectors are the whole check: pycrate
has no `^`, `INTERSECTION`, `INCLUDES` or size unions, asn1c no open range
ends, which is why the constraint tests are in three modules.

`oid`, `real`, `strings2`, `strings2q`, `objdesc` and `wide` (OBJECT
IDENTIFIER and RELATIVE-OID, REAL, the character strings beyond ISO 646 and
the time types, ObjectDescriptor, an ENUMERATED of 256 values and more) have
no hand-derived vectors yet: they are checked with random values only, and
their `.vec` files hold only the references' deviations. `strings2q` (a
permitted alphabet of character quadruples, which asn1c and pycrate do not
parse) is only verified.

## Vector format

```
accept TYPE HEX JER     every decoder gives this value; ours re-encodes it to HEX
reject TYPE HEX         every decoder rejects it
accept! / reject!       the same, where a reference is known to deviate (see below)
deviates TOOL TYPE      TOOL deviates from X.691 on TYPE: its random-value checks
                        are left out for TYPE
deviates-encode TOOL TYPE   TOOL decodes TYPE as X.691 does but encodes it
                        otherwise: only its re-encodings are left out
```

HEX is the complete encoding, padded to octets (X.691 11.1.3). Comments
start with `#`.

`containing` has two vector files: `containing.vec` under `--containing
decode`, checked against pycrate, which decodes the contents, and
`containing.octets.vec` under the default, checked against asn1c and rasn,
which keep the octets. A `# xcheck: FLAGS` line in a vector file is what run.sh passes
to xcheck.

JER is compared as a value. Hex digits in either case are equal (X.697 24,
25). A member equal to its DEFAULT and an absent member are equal (X.697
lets a printer do either), which xcheck works out from pycrate's compiled
schema. asn1c prints an extension addition group as an object of its own,
`"ext1": {..}`, where X.697 27.2.1 makes its components members of the
enclosing SEQUENCE, and xcheck merges them back. Random values come from the
effective, PER-visible constraint (X.691 10.3), which may allow values the
full constraint does not (`INTEGER (0..7 | 9)` is encoded as 0..9); a
reference that rejects one of those for its full constraint is counted
separately, not as a failure.

## Deviations of the reference implementations

(One difference that is not a deviation: asn1c re-encodes a SET OF with its
elements sorted, CANONICAL-PER's order (X.691 22.1). In BASIC-PER (22.2) a
SET OF is encoded as a SEQUENCE OF, and a SET OF value is unordered, so any
order is an encoding of it. Ours keeps the order it decoded. Its decoding
agrees with ours; `set_*.vec` leave its re-encoding out.)

| module | tool | what X.691 / X.680 says | what the tool does |
| --- | --- | --- | --- |
| `enumerated` | pycrate | an unnumbered addition after `c(7)` is 8 (X.680 20.6), so `{..., c(7), d}` indexes c, d | orders them d, c |
| `tags_implicit`, `tags_auto` | pycrate | CHOICE alternatives are indexed in canonical tag order unless automatic tagging applies (X.691 23.2, X.680 8.6, 29.2) | textual order always |
| `tags_implicit`, `tags_auto` | asn1c | the same | its tables list the canonical order correctly, but `asn_MAP_*_to_canonical` and `_from_canonical` are swapped, so a reordering that is not its own inverse (a 3-cycle) comes out wrong |
| `tags_implied` | asn1c | EXTENSIBILITY IMPLIED puts `...` in every type that may have one (X.680 13.4) | not in ENUMERATED |
| `sequence` | pycrate, asn1c | components after a second extension marker are root components (X.680 25.1; X.691 19.9 NOTE 2) | drop them |
| `integer` | asn1c | an extensible INTEGER's value outside the root is sent as an unconstrained, 2's-complement integer (X.691 13.1, 11.8) | for `(0..MAX, ...)`, decodes it as the root's unsigned form (`80ff80` as 255, not -1); and `-c` rejects every value outside an extensible root |
| `sizes` | asn1c | an extensible SIZE's bit is 1 for a size outside the root (X.691 16.6, 17.3, 20.4) | for `OCTET STRING (SIZE (2..MAX, ...))` its encoder writes 0 for size 1 (its decoder reads it right); `-c` rejects every size outside an extensible root; it accepts no items for `SIZE (1..MAX)` |
| `sizes` | pycrate | an extensible size constraint is not JER-visible, so a BIT STRING prints as `{"value", "length"}` (X.697 7.2.2 g, 24.3) | prints the fixed-size form, and loses the length of a 3-bit value |
| `strings` | asn1c | no constraint on a UTF8String is PER-visible (X.691 10.3.7, 30.6), so its length is the unconstrained one, in octets | applies `SIZE (1..4)` as a constrained length |
| `strings` | pycrate | a one-character alphabet takes 0 bits a character (X.691 30.5.2) | fails with `NameError: name 'V' is not defined` |
| `containing` | pycrate | `OCTET STRING (CONTAINING T)` holds the complete encoding of one T (X.682 11.3, X.691 11.1): no nonzero padding bit, no extra octet | accepts both, and prints the value as `{"T": value}`, not X.697 25.4's `{"containing": value}` |
| `containing` | asn1c | (no deviation in the encoding: it keeps the octets, as `--containing octets` does) | `-c` segfaults on a top-level contents-constrained type |
| `sequence`, `additions`, `namedbits`, `integer`, `sizes`, `strings` | pycrate, asn1c | a group with every value missing, a DEFAULT sent at its default, a named-bit string with a trailing 0, an integer in more octets than needed, a root value or size sent as an extension, octets that are not UTF-8 in a UTF8String are not encodings (X.691 19.9, 19.5, 16.3, 11.3.6, 11.4.6, 10.4.3) | accept them |
| `integer` | asn1c | a semi-constrained INTEGER's offset is a non-negative binary integer in the fewest octets (X.691 11.7.4) | re-encodes 123 as `00 80`, two's complement (reached by the generator's octet-boundary values) |
| `sizes` | pycrate | a BIT STRING of 16K bits or more is fragmented (X.691 11.9.3.8) | its encoder is X.691's, its decoder cannot read one back, its own included |
| `sizes` | asn1c | `SEQUENCE (SIZE (1..MAX)) OF INTEGER (0..3)` of 16K elements or more is fragmented | rejects it; pycrate reads ours |
| `constraints` | rasn | a contained subtype, `INTEGER (Sub)`, is Sub's range (X.680 51.3); a constraint on a type reference applies serially (X.680 50.11, X.691 10.3.18) | rasn-compiler drops the first, and reads `Octets8 (SIZE (4))` with Octets8's own `SIZE (1..8)` length |
| `constraints_inter` | rasn | `INCLUDES Sub \| 12` is 0..12, `SIZE (1..4) \| SIZE (8)` a size constraint 1..8 | the single value 12, and a *value* constraint on the OCTET STRING (so no size constraint at all) |
| `sizes` | rasn | a size outside an extensible SIZE's root: bit 1, then the length as if unconstrained (X.691 20.4, 11.9) | its encoder writes something else (`8260` as `98`), its decoder is right; it misreads a fragmented length after the extension bit; prints ExtBits in JER's fixed form, as pycrate |
| `strings` | rasn | UTF8String's SIZE is not PER-visible (X.691 30.6) | applies it, as asn1c |
| `tags_implicit`, `tags_auto` | rasn | CHOICE alternatives in canonical tag order (X.691 23.2) | textual order, as pycrate |
| `strings2` | asn1c | GeneralizedTime and UTCTime are encoded as the VisibleString they are (X.691 10.6.5), 7 bits a character in UNALIGNED | 8 bits a character, so it reads past the end of ours |
| `containing` | rasn | (no deviation: it keeps the octets, as asn1c) | |

Beyond the table (the random checks of `oid`, `real`, `strings2`, and
`tests/protocols/its.vec`): rasn
0.28 corrupts a fragmented character string whose length is not a multiple
of 16K when it encodes one (the last fragment repeats the first's
characters), holds an OBJECT IDENTIFIER's arcs in 32 bits and keeps the low
32 bits of a wider one, makes a RELATIVE-OID an OBJECT IDENTIFIER, has no
BMPString, TeletexString or REAL in PER, and rejects a SEQUENCE whose
mandatory extension addition is absent (a valid message from an older
sender, X.691 19.7). asn1c rejects a 201-element `SEQUENCE (SIZE (1..256))
OF` in UNALIGNED (ETSI ITS's DigitalMap). Its REAL is a C double. pycrate
decodes a binary REAL to twice its value.
