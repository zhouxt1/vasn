#!/usr/bin/env python3
"""Extract the ASN.1 of a 3GPP spec (.docx): every paragraph between a
`-- ASN1START` and an `-- ASN1STOP` line, split into one file per module.
  extract_asn1.py SPEC.docx OUTDIR"""
import re, sys, zipfile, pathlib
import xml.etree.ElementTree as ET
W = '{http://schemas.openxmlformats.org/wordprocessingml/2006/main}'
doc = ET.fromstring(zipfile.ZipFile(sys.argv[1]).read('word/document.xml'))
lines = []
for p in doc.iter(W + 'p'):
    s = []
    for el in p.iter():
        if el.tag == W + 't':
            s.append(el.text or '')
        elif el.tag == W + 'tab':
            s.append('\t')
        elif el.tag in (W + 'br', W + 'cr'):
            s.append('\n')
    lines.append(''.join(s).replace(' ', ' ').replace('‑', '-').replace('–', '-'))
text = '\n'.join(lines)
# a block runs to its ASN1STOP; one that has none (37.483 V19.4.0's
# Container Definitions) to its module's END
chunks = []
for part in re.split(r'--\s*ASN1START[^\n]*\n', text)[1:]:
    m = re.search(r'\n\s*--\s*ASN1STOP', part)
    if m:
        chunks.append(part[:m.start()])
    else:
        e = re.search(r'(?m)^\s*END\s*$', part)
        chunks.append(part[:e.end()] if e else part)
body = '\n'.join(chunks)
out = pathlib.Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)
# split at module headers: `Name {` ... `DEFINITIONS` ... `END`, indented
# or not (38.455 V19.3.0 has NRPPA-IEs's tab-indented)
mods = re.split(r'(?m)^(?=[ \t]*[A-Z][A-Za-z0-9-]*\s*(?:\{[^}]*\}\s*)?\n?\s*DEFINITIONS)', body)
n = 0
for m in mods:
    m = m.strip()
    if not m or 'DEFINITIONS' not in m:
        continue
    name = re.match(r'([A-Z][A-Za-z0-9-]*)', m).group(1)
    # a module ends at its END: 36.455 V19.0.0's last block has no ASN1STOP
    # before the change history
    e = re.search(r'(?m)^\s*END\s*$', m)
    if e:
        m = m[:e.end()]
    (out / f'{name}.asn').write_text(m + '\n')
    n += 1
print(f'{sys.argv[1]}: {len(chunks)} ASN.1 blocks, {n} modules, {body.count(chr(10))} lines')
