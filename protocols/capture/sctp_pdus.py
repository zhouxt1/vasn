#!/usr/bin/env python3
"""The application PDUs in a pcap's SCTP DATA chunks, one file each.
  sctp_pdus.py PCAP OUTDIR [PPID]   (60 NGAP, 62 F1AP, 64 E1AP, 61 XnAP,
                                     18 S1AP, 27 X2AP; default 60)
  sctp_pdus.py PCAP OUTDIR port:N   (those to or from SCTP port N: FlexRIC
                                     sends E2AP, 36421, with PPID 0)
Fragmented user messages (B/E flags) are reassembled per stream."""
import struct, sys, pathlib, collections
pcap, out = sys.argv[1], pathlib.Path(sys.argv[2])
sel = sys.argv[3] if len(sys.argv) > 3 else '60'
port = int(sel[5:]) if sel.startswith('port:') else None
want = None if port else int(sel)
out.mkdir(parents=True, exist_ok=True)
data = open(pcap, 'rb').read()
magic = struct.unpack('<I', data[:4])[0]
le = magic in (0xa1b2c3d4, 0xa1b23c4d)
E = '<' if le else '>'
linktype = struct.unpack(E + 'I', data[20:24])[0]
off = 24
n = 0
partial = collections.defaultdict(bytes)
seen = set()
while off + 16 <= len(data):
    ts, tu, incl, orig = struct.unpack(E + 'IIII', data[off:off + 16])
    pkt = data[off + 16: off + 16 + incl]
    off += 16 + incl
    if linktype == 1:            # Ethernet
        if len(pkt) < 14 or pkt[12:14] != b'\x08\x00':
            continue
        ip = pkt[14:]
    elif linktype == 113:        # Linux cooked
        ip = pkt[16:]
    elif linktype == 276:        # Linux cooked v2
        ip = pkt[20:]
    elif linktype in (0, 108):   # BSD loopback
        ip = pkt[4:]
    else:
        ip = pkt
    if not ip or ip[0] >> 4 != 4:
        continue
    ihl = (ip[0] & 15) * 4
    if ip[9] != 132:
        continue
    sctp = ip[ihl:]
    src, dst = struct.unpack('>HH', sctp[:4])
    p = 12
    while p + 4 <= len(sctp):
        ctype, flags, clen = sctp[p], sctp[p + 1], struct.unpack('>H', sctp[p + 2:p + 4])[0]
        if clen < 4:
            break
        if ctype == 0 and clen >= 16:
            tsn, sid, ssn, ppid = struct.unpack('>IHHI', sctp[p + 4:p + 16])
            payload = sctp[p + 16:p + clen]
            key = (src, dst, sid)
            if (key, tsn) not in seen:   # a retransmission is the same chunk
                seen.add((key, tsn))
                b, e = flags & 2, flags & 1
                if b:
                    partial[key] = payload
                else:
                    partial[key] += payload
                if e and (ppid == want if port is None else port in (src, dst)):
                    (out / f'{n:06d}.aper').write_bytes(partial[key])
                    n += 1
                if e:
                    partial[key] = b''
        p += (clen + 3) & ~3
print(f'{pcap}: {n} PDUs with ' + (f'PPID {want}' if port is None else f'port {port}'))
