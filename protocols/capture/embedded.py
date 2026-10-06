#!/usr/bin/env python3
"""The PDUs one protocol carries as octets in another's, one file each, from
our decoder's JER of the outer messages.

  embedded.py DRIVER TYPE INDIR OUTDIR nrppa
      NGAP's NRPPa-PDU (IE id 46): NRPPa
  embedded.py DRIVER TYPE INDIR OUTDIR e2sm FUNC=NAME...
      E2AP's E2SM octets, by the RAN function they are for (FUNC=NAME, e.g.
      2=kpm): RANfunctionDefinition, RICeventTriggerDefinition,
      RICactionDefinition, RICindicationHeader/Message, RICcontrolHeader/
      Message, to OUTDIR/NAME-<what>/

Only messages our decoder accepts are looked into; it says how many."""
import json, pathlib, subprocess, sys, collections

drv, ty, indir, outdir, mode = sys.argv[1:6]
files = sorted(pathlib.Path(indir).glob('*.aper'))
inp = ''.join(f.read_bytes().hex() + '\n' for f in files)
res = subprocess.run([drv, 'dec', ty], input=inp, capture_output=True, text=True).stdout.splitlines()
assert len(res) == len(files)
out = pathlib.Path(outdir)
count = collections.Counter()


def put(kind, h):
    d = out / kind
    d.mkdir(parents=True, exist_ok=True)
    (d / f'{count[kind]:06d}.aper').write_bytes(bytes.fromhex(h))
    count[kind] += 1


def walk(v, f):
    if isinstance(v, dict):
        f(v)
        for x in v.values():
            walk(x, f)
    elif isinstance(v, list):
        for x in v:
            walk(x, f)


funcs = dict(a.split('=') for a in sys.argv[6:])
bad = 0
for line in res:
    if not line.startswith('ok '):
        bad += 1
        continue
    j = json.loads(line.split(' ', 4)[4])
    if mode == 'nrppa':
        walk(j, lambda d: put('nrppa', d['value']) if d.get('id') == 46 and 'value' in d else None)
    elif mode == 'e2sm':
        # the message's RANfunctionID IE (id 5), for the octets at its level
        fid = []
        walk(j, lambda d: fid.append(d['value']) if d.get('id') == 5 and isinstance(d.get('value'), int) else None)
        msg_f = funcs.get(str(fid[0])) if fid else None

        def f(d):
            # E2 Setup's and RIC Service Update's RANfunction-Item
            if 'ranFunctionDefinition' in d and str(d.get('ranFunctionID')) in funcs:
                put(funcs[str(d['ranFunctionID'])] + '-RANfunctionDefinition', d['ranFunctionDefinition'])
            if msg_f is None:
                return
            for k, what in (('ricEventTriggerDefinition', 'EventTriggerDefinition'),
                            ('ricActionDefinition', 'ActionDefinition')):
                if k in d:
                    put(f'{msg_f}-{what}', d[k])
            ie = {25: 'IndicationHeader', 26: 'IndicationMessage', 22: 'ControlHeader', 23: 'ControlMessage'}
            if d.get('id') in ie and isinstance(d.get('value'), str):
                put(f'{msg_f}-{ie[d["id"]]}', d['value'])
        walk(j, f)
print(f'{indir}: {len(files)} messages, {bad} not decoded; ' +
      ', '.join(f'{k} {v}' for k, v in sorted(count.items())))
