#!/usr/bin/env python3
"""Verify kit bytes. This is not mathematical or release acceptance."""
from pathlib import Path
import argparse,hashlib,json,sys

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(4*1024*1024),b''):h.update(b)
 return h.hexdigest()
def verify(root,quick=False):
 root=root.resolve();m=json.loads((root/'MANIFEST.json').read_text());rows=m['files'];expected={r['path']:r for r in rows}
 if len(rows)!=len(expected):raise ValueError('Duplicate manifest path')
 actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
 if actual!=set(expected)|{'MANIFEST.json'}:raise ValueError('Payload inventory mismatch')
 n=0
 for name,r in expected.items():
  p=root/name
  if p.is_symlink() or not p.resolve().is_relative_to(root):raise ValueError('Escaping payload '+name)
  if p.stat().st_size!=r['bytes']:raise ValueError('Size mismatch '+name)
  if quick and name.startswith('runtime/'):continue
  if digest(p)!=r['sha256']:raise ValueError('Hash mismatch '+name)
  n+=1
 return {'status':'PASS_QUICK_EXCLUDES_RUNTIME_HASHES' if quick else 'PASS_ALL_PAYLOAD_HASHES','files_checked':n,'total_files':len(rows),'authority':'BYTE_INTEGRITY_ONLY','full_release_accepted':False}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--quick',action='store_true');a=p.parse_args()
 try:print(json.dumps(verify(Path(__file__).resolve().parents[1],a.quick),indent=2))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(2)
