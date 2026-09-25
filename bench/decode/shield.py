#!/usr/bin/env python3
"""A benchmark corpus from the 5G Shield dataset's over-the-air traces.

    shield.py RAW_DATA_DIR [OUT_DIR]     default OUT_DIR corpus/shield

RAW_DATA_DIR is the dataset's `raw_data/` (real_commercial, real_attacks,
real_attract), whose CSVs are QXDM-style logs: one row per message, with the
RRC decode and, after a `[HEX]` line, the message's UPER octets. Each RRC
message goes to OUT_DIR/<channel>/, e.g. corpus/shield/DL-DCCH-Message/,
once per distinct octet string. Rows that carry no RRC channel message
(NAS, and the SIBs logged on their own outside a SystemInformation) are
skipped. A summary of the counts goes to OUT_DIR/summary.txt.
"""
import collections
import csv
import hashlib
import pathlib
import re
import sys

csv.field_size_limit(1 << 30)
CHANNEL = re.compile(r"\n\n([A-Z][A-Za-z0-9-]+-Message)\n")
HEX = re.compile(r"\[HEX\]\s*([0-9A-Fa-f\s]+)$")


def main():
    raw = pathlib.Path(sys.argv[1])
    out = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else "corpus/shield")
    seen = collections.defaultdict(set)
    total = collections.Counter()
    for f in sorted(raw.glob("*/*.CSV")):
        with open(f, newline="", errors="replace") as fh:
            for row in csv.DictReader(fh):
                d = row["DETAILED"]
                m, h = CHANNEL.search(d), HEX.search(d)
                if not (m and h):
                    continue
                ch = m.group(1)
                b = bytes.fromhex("".join(h.group(1).split()))
                total[ch] += 1
                key = hashlib.sha1(b).hexdigest()[:16]
                if key in seen[ch]:
                    continue
                seen[ch].add(key)
                (out / ch).mkdir(parents=True, exist_ok=True)
                (out / ch / f"{key}.uper").write_bytes(b)
    lines = [f"{ch:24} {total[ch]:9} messages, {len(seen[ch]):7} distinct"
             for ch in sorted(total, key=lambda c: -total[c])]
    (out / "summary.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
