#!/usr/bin/env python3
"""Apply the exact snapshot only at its base, after a guarded dry run. Never pushes."""
from pathlib import Path
import argparse,json,shutil,subprocess,sys
sys.dont_write_bytecode=True
from verify_kit import digest
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--apply',action='store_true');p.add_argument('--backup',type=Path);a=p.parse_args()
try:
 k=Path(__file__).resolve().parents[1];r=a.repo.resolve();m=json.loads((k/'state/WORKSPACE_CHANGES.json').read_text())
 def git(*args):return subprocess.check_output(['git',*args],cwd=r,text=True).strip()
 if git('rev-parse','HEAD')!=m['base_commit'] or git('rev-parse','HEAD^{tree}')!=m['base_tree']:raise ValueError('Wrong base; reconcile newer work')
 if git('diff','--name-only') or git('diff','--cached','--name-only'):raise ValueError('Tracked/staged changes present')
 backup=a.backup.resolve() if a.backup else None
 if a.apply and (backup is None or backup==r or backup.is_relative_to(r) or backup.is_relative_to(k)):raise ValueError('External backup required')
 for row in m['files']:
  q=r/row['path']
  if not q.resolve().is_relative_to(r) or q.is_symlink():raise ValueError('Escaping target')
  old=digest(q) if q.is_file() else None
  if old!=row['base_sha256'] or digest(k/'workspace'/row['path'])!=row['current_sha256']:raise ValueError('Hash precondition failed: '+row['path'])
 patch=k/'patches/current_from_9b.patch';git('apply','--check',str(patch))
 if a.apply:
  for row in m['files']:
   q=r/row['path']
   if q.is_file():
    b=backup/row['path'];b.parent.mkdir(parents=True,exist_ok=True)
    if b.exists() and digest(b)!=digest(q):raise ValueError('Backup conflict')
    shutil.copyfile(q,b)
  git('apply',str(patch))
  for row in m['files']:
   if digest(r/row['path'])!=row['current_sha256']:raise ValueError('Post-apply hash mismatch')
 print(json.dumps({'status':'APPLIED_UNACCEPTED_SNAPSHOT' if a.apply else 'PASS_DRY_RUN','paths':len(m['files']),'committed':False,'pushed':False,'full_release_accepted':False},indent=2))
except Exception as e:print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(2)
