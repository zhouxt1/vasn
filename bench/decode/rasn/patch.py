#!/usr/bin/env python3
"""The two fixes rasn-compiler 0.16.0's NR output needs before it compiles.

Both are naming bugs in the compiler, not changes to what is decoded:

* A DEFAULT component's default is written as a function, and the call site
  spells its name differently from the definition (`filter_config_cli_r16_...`
  called, `filter_config_clir16_...` defined). Each undefined call is pointed
  at the one defined function whose name is the same up to underscores.
* PC5-RRC-Definitions imports `SetupRelease` from NR-RRC-Definitions, where
  that parameterised type exists only as its instances, and never uses it.
  The import is dropped.

    patch.py FILE      FILE is the compiler's output after rustfmt
"""
import re
import sys

path = sys.argv[1]
s = open(path).read()

defined = set(re.findall(r'fn (\w+_default)\(\)', s))
by_key = {}
for d in defined:
    by_key.setdefault(d.replace('_', ''), []).append(d)
for m in sorted(set(re.findall(r'\b(\w+_default)\(\)', s)) - defined):
    [fix] = [d for d in by_key[m.replace('_', '')] if d != m]
    s = re.sub(r'\b' + m + r'\(\)', fix + '()', s)
    print(f'{m} -> {fix}')

pc5 = s.index('pub mod pc5_rrc_definitions {')
imp = re.compile(r'(use super::nr_rrc_definitions::\{[^}]*?)\bSetupRelease,\s*')
s = s[:pc5] + imp.sub(r'\1', s[pc5:], count=1)
assert not re.search(r'[^_\w]SetupRelease[^_\w]', s[pc5:]), 'SetupRelease is used after all'

open(path, 'w').write(s)
