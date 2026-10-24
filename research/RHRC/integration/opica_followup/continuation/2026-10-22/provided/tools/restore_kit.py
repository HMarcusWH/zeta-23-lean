#!/usr/bin/env python3
"""Restore this source snapshot offline to a fresh directory. No commits or pushes."""
from pathlib import Path
import argparse,json,platform,shutil,subprocess,sys
sys.dont_write_bytecode=True
from verify_kit import verify,digest
BASE='9b6a9a3a2badb4cff62a56c1158d9cef8759d30d'
TREE='545ea182910db9c8d05c4c7e8ee229d119a9aa28'
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--dest',type=Path,required=True);p.add_argument('--mode',choices=['current','baseline'],default='current');p.add_argument('--runtime',action='store_true');a=p.parse_args()
 k=Path(__file__).resolve().parents[1];d=a.dest.resolve()
 if d==k or d.is_relative_to(k) or k.is_relative_to(d):raise ValueError('Use an external destination')
 if d.exists() and any(d.iterdir()):raise ValueError('Destination not empty; refusing overwrite')
 if not shutil.which('git'):raise ValueError('Git is required')
 if a.runtime and (platform.system()!='Linux' or platform.machine().lower() not in ['x86_64','amd64']):raise ValueError('Bundled runtime requires Linux x86_64')
 if a.runtime and (not shutil.which('tar') or not shutil.which('zstd')):raise ValueError('tar and zstd are required')
 print(json.dumps(verify(k)),flush=True);d.mkdir(parents=True,exist_ok=True);r=d/'repo';r.mkdir();e=d/'restore-evidence';e.mkdir();records=[]
 def run(label,cmd,cwd=None,stdin=None):
  print('RUN '+label,flush=True);q=subprocess.run(cmd,cwd=cwd,stdin=stdin,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);f=e/(label+'.log');f.write_bytes(q.stdout)
  records.append({'label':label,'command':cmd,'exit_code':q.returncode,'log':f.name,'sha256':digest(f)});(e/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
  if q.returncode:raise RuntimeError(label+' failed: '+str(f))
  return q.stdout.decode(errors='replace').strip()
 run('git-init',['git','init','-q',str(r)]);run('git-autocrlf',['git','config','core.autocrlf','false'],r)
 with (k/'baseline/source/source-objects.pack').open('rb') as f:run('git-objects',['git','index-pack','--stdin'],r,f)
 b=json.loads((k/'state/GIT_ARCHIVE_BOUNDARIES.json').read_text())['shallow_boundaries']
 (r/'.git/shallow').write_text(''.join(x['commit']+'\n' for x in b))
 run('base-ref',['git','update-ref','refs/heads/ssot-base',BASE],r);run('head',['git','symbolic-ref','HEAD','refs/heads/ssot-base'],r);run('checkout',['git','reset','--hard','HEAD'],r)
 if run('tree',['git','rev-parse','HEAD^{tree}'],r)!=TREE:raise ValueError('Wrong base tree')
 receipt=json.loads((k/'evidence/cold41/subset/compiler-receipt.json').read_text())
 for row in receipt['source_manifest']:
  if digest(r/row['path'])!=row['sha256']:raise ValueError('Baseline source mismatch: '+row['path'])
 changes=json.loads((k/'state/WORKSPACE_CHANGES.json').read_text())['files']
 if a.mode=='current':
  for row in changes:
   dest=r/row['path'];old=digest(dest) if dest.is_file() else None
   if old!=row['base_sha256']:raise ValueError('Changed target '+row['path'])
  for row in changes:
   dest=r/row['path'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(k/'workspace'/row['path'],dest)
   if digest(dest)!=row['current_sha256']:raise ValueError('Installed source mismatch')
 if a.runtime:
  t=d/'toolchain';t.mkdir();lake=r/'.lake';lake.mkdir(exist_ok=True)
  run('extract-compiler',['tar','--zstd','-xf',str(k/'runtime/toolchain-linux-x86_64.tar.zst'),'-C',str(t),'--no-same-owner'])
  run('extract-cache',['tar','--zstd','-xf',str(k/'runtime/lake-pinned-linux-x86_64.tar.zst'),'-C',str(lake),'--no-same-owner'])
  version=run('compiler-version',[str(t/'bin/lean'),'--version'])
  if '4.33.0-rc2' not in version or 'd8b18978322de05a8f3dba51ef03cf5461676c17' not in version:raise ValueError('Compiler pin mismatch')
  m=json.loads((r/'lake-manifest.json').read_text())['packages']
  if next(x for x in m if x['name']=='mathlib')['rev']!='51e6992efd06126df61a496bebf8f49482a4e129':raise ValueError('Declared Mathlib pin mismatch')
  if (lake/'packages/mathlib/lean-toolchain').read_text().strip()!='leanprover/lean4:v4.33.0-rc2':raise ValueError('Exported Mathlib toolchain mismatch')
  # Package .git metadata was deliberately omitted: never use an upward Git HEAD lookup.
  entries=[]
  for x in m:
   loc=lake/'packages'/x['name']
   if not loc.is_dir():raise ValueError('Missing exported package '+x['name'])
   entries.append({j:x[j] for j in ['name','scope','inherited','configFile','manifestFile'] if j in x}|{'type':'path','dir':str(loc)})
  (d/'packages-local.json').write_text(json.dumps({'version':'1.2.0','packages':entries},indent=2)+'\n')
 report={'status':'RESTORED_NOT_PROOF_ACCEPTANCE','mode':a.mode,'base_commit':BASE,'base_tree':TREE,'runtime_restored':a.runtime,'working_tree_dirty':bool(run('status',['git','status','--porcelain'],r)),'package_provenance':'Exact SHA256-bound pinned CI export; dependency Git metadata intentionally omitted','commands':records,'RH':'OPEN','Step4':'OPEN','full_release_accepted':False}
 (e/'RESTORE.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({j:v for j,v in report.items() if j!='commands'},indent=2))
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(2)
