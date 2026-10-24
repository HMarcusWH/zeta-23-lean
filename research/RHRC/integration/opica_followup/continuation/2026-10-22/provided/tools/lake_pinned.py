#!/usr/bin/env python3
"""Pinned offline Lake wrapper. Package path overrides prevent unwanted re-cloning."""
from pathlib import Path
import argparse,json,os,subprocess,sys
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--restored',type=Path,required=True);p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args()
try:
 d=a.restored.resolve();r=d/'repo';cmd=a.command
 if cmd and cmd[0]=='--':cmd=cmd[1:]
 if not cmd or cmd[0] in ['update','clean'] or any(x in ['--update','--try-cache'] or x.startswith('--packages') for x in cmd):raise ValueError('Unsafe or missing command')
 if (r/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.33.0-rc2':raise ValueError('Wrong Lean pin')
 packages=json.loads((r/'lake-manifest.json').read_text())['packages']
 if next(x for x in packages if x['name']=='mathlib')['rev']!='51e6992efd06126df61a496bebf8f49482a4e129':raise ValueError('Wrong Mathlib pin')
 entries=[]
 for x in packages:
  loc=r/'.lake/packages'/x['name']
  if not loc.is_dir():raise ValueError('Missing package '+x['name'])
  entries.append({j:x[j] for j in ['name','scope','inherited','configFile','manifestFile'] if j in x}|{'type':'path','dir':str(loc)})
 overrides=d/'packages-local.json';overrides.write_text(json.dumps({'version':'1.2.0','packages':entries},indent=2)+'\n')
 env=os.environ.copy();env['PATH']=str(d/'toolchain/bin')+os.pathsep+env.get('PATH','');env.setdefault('LEAN_NUM_THREADS','2')
 raise SystemExit(subprocess.run([str(d/'toolchain/bin/lake'),'--packages='+str(overrides),'--no-cache',*cmd],cwd=r,env=env).returncode)
except (OSError,ValueError,KeyError) as e:print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(2)
