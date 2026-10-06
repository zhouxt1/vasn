#!/usr/bin/env python3
"""Mutants of a corpus of captured messages, one per file, for differential
testing of what decoders accept: truncations, single-bit flips, an octet
changed, an octet inserted, a tail appended.
  mutate.py IN_DIR OUT_DIR PER_MESSAGE [SEED]"""
import os, random, sys, pathlib
src, out, k = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), int(sys.argv[3])
rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
out.mkdir(parents=True, exist_ok=True)
files = sorted(src.iterdir())
n = 0
seen = set()
for f in files:
    b = f.read_bytes()
    if not b:
        continue
    for i in range(k):
        m = bytearray(b)
        op = rng.choice(['trunc', 'flip', 'flip', 'flip', 'byte', 'insert', 'tail'])
        if op == 'trunc':
            m = m[:rng.randrange(1, len(m))] if len(m) > 1 else m
        elif op == 'flip':
            p = rng.randrange(8 * len(m))
            m[p // 8] ^= 0x80 >> (p % 8)
        elif op == 'byte':
            m[rng.randrange(len(m))] = rng.randrange(256)
        elif op == 'insert':
            m.insert(rng.randrange(len(m) + 1), rng.randrange(256))
        else:
            m += bytes(rng.randrange(256) for _ in range(rng.randrange(1, 4)))
        m = bytes(m)
        if m == b or m in seen:
            continue
        seen.add(m)
        (out / f'{n:06d}-{op}.aper').write_bytes(m)
        n += 1
print(f'{n} mutants of {len(files)} messages')
