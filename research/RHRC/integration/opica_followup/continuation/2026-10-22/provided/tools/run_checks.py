#!/usr/bin/env python3
"""Narrow reproducibility replay. No root registration or full release promotion."""
from pathlib import Path
import argparse,json,os,re,subprocess,sys,time
sys.dont_write_bytecode=True
from verify_kit import digest
MODS=['ComplexLocalMeasures','AuxiliaryCompletions','MaskedNativeRate']
CONS={'ExpectedComplex':'ComplexLocalMeasures','ExpectedAuxiliary':'AuxiliaryCompletions','ExpectedMasks':'MaskedNativeRate'}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--restored',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--lane',choices=['lean','python','all'],default='all');p.add_argument('--timeout',type=int,default=1800);a=p.parse_args()
 k=Path(__file__).resolve().parents[1];d=a.restored.resolve();r=d/'repo';out=a.out.resolve()
 if out.is_relative_to(r) or out.is_relative_to(k):raise ValueError('Use external evidence directory')
 if out.exists() and any(out.iterdir()):raise ValueError('Fresh evidence directory required')
 out.mkdir(parents=True,exist_ok=True)
 if (r/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.33.0-rc2':raise ValueError('Wrong Lean pin')
 if next(x for x in json.loads((r/'lake-manifest.json').read_text())['packages'] if x['name']=='mathlib')['rev']!='51e6992efd06126df61a496bebf8f49482a4e129':raise ValueError('Wrong Mathlib pin')
 def sources():return {p.relative_to(r).as_posix():digest(p) for p in sorted((r/'Zeta23').rglob('*.lean'))}
 before=sources();(out/'source-before.json').write_text(json.dumps(before,indent=2)+'\n')
 env=os.environ.copy();env.update(LEAN_NUM_THREADS='2',PYTHONDONTWRITEBYTECODE='1');records=[];failures=[]
 def run(label,cmd):
  start=time.monotonic();log=out/(label+'.log')
  with log.open('wb') as f:
   try:q=subprocess.run(cmd,cwd=r,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=a.timeout);code=q.returncode
   except subprocess.TimeoutExpired:code=124
  row={'label':label,'command':cmd,'exit_code':code,'seconds':time.monotonic()-start,'log':log.name,'log_sha256':digest(log)};records.append(row)
  (out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(row),flush=True)
  return row,log.read_text(errors='replace')
 if a.lane in ['lean','all']:
  lean=str(d/'toolchain/bin/lean');v,t=run('version',[lean,'--version'])
  if v['exit_code'] or '4.33.0-rc2' not in t or 'd8b18978322de05a8f3dba51ef03cf5461676c17' not in t:raise ValueError('Actual compiler pin mismatch')
  fresh=out/'olean';fresh.mkdir();inherited=r/'.lake/build/lib/lean'
  excluded={'Zeta23/OPICAFollowup/'+n for n in MODS}|{'Zeta23/OPICA/WeightedLaplace'}
  # Lean resolves the whole leading namespace root. Mirror its unchanged files,
  # not a sparse directory which would hide all the inherited Zeta23 imports.
  for src in inherited.rglob('*'):
   if src.is_file():
    rel=src.relative_to(inherited)
    if any(rel.as_posix().startswith(x+'.') for x in excluded):continue
    target=fresh/rel;target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(src.resolve())
  env['LEAN_PATH']=os.pathsep.join(str(x) for x in [fresh,*sorted((r/'.lake/packages').glob('*/.lake/build/lib/lean'))])
  env['PATH']=str(d/'toolchain/bin')+os.pathsep+env.get('PATH','')
  (out/'environment.json').write_text(json.dumps({'LEAN_PATH':env['LEAN_PATH'],'policy':'Warm pinned CI cache, fresh candidate objects; not cold CI; package .git metadata absent'},indent=2)+'\n')
  visiting=set()
  def prepare(module):
   rel=Path(module.replace('.','/')+'.lean');obj=fresh/rel.with_suffix('.olean')
   if obj.is_file():return True
   src=r/rel
   if module in visiting or not src.is_file():raise ValueError('Missing/cyclic prerequisite '+module)
   visiting.add(module)
   for imp in re.findall(r'^(?:(?:public|private)\s+)?import\s+(\S+)',src.read_text(),re.M):
    if imp.startswith('Zeta23.') and not prepare(imp):visiting.remove(module);return False
   obj.parent.mkdir(parents=True,exist_ok=True)
   row,t=run('prerequisite_'+module.replace('.','_'),[lean,'-DmaxHeartbeats=800000','-DrelaxedAutoImplicit=false','-o',str(obj),str(rel)]);row['source_sha256']=digest(src);visiting.remove(module)
   return row['exit_code']==0 and 'sorryAx' not in t
  if not prepare('Zeta23.OPICA.WeightedLaplace'):failures.append('WeightedLaplace prerequisite closure')
  passed={}
  for name in MODS:
   rel=Path('Zeta23/OPICAFollowup')/(name+'.lean');obj=fresh/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
   row,t=run('module_'+name,[lean,'-DmaxHeartbeats=800000','-DrelaxedAutoImplicit=false','-o',str(obj),str(rel)]);row['source_sha256']=digest(r/rel)
   passed[name]=row['exit_code']==0 and 'sorryAx' not in t
   if not passed[name]:failures.append(name)
  for name,dep in CONS.items():
   if not passed[dep]:records.append({'label':name,'status':'BLOCKED_DEPENDENCY','dependency':dep});failures.append(name);continue
   src=k/'consumers'/(name+'.lean');row,t=run(name,[lean,'-DmaxHeartbeats=800000','-DrelaxedAutoImplicit=false',str(src)]);row['source_sha256']=digest(src)
   lists=[sorted({v.strip() for v in x.split(',') if v.strip()}) for x in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',t,re.S)]
   n=len(re.findall(r'^#print axioms ',src.read_text(),re.M));ok=len(lists)+len(re.findall('does not depend on any axioms',t))==n and all(not(set(x)-{'propext','Classical.choice','Quot.sound'}) for x in lists) and 'sorryAx' not in t
   row.update(axiom_lists=lists,requested_axiom_checks=n,axiom_output_valid=ok)
   if row['exit_code'] or not ok:failures.append(name)
 if a.lane in ['python','all']:
  for mode in ['normal','optimized']:
   for label,folder,pattern in [('parent','research/RHRC/integration/opica/tests','test_contract.py'),('child','research/RHRC/integration/opica_followup/tests','test_parent_extension.py')]:
    cmd=[sys.executable,*(['-O'] if mode=='optimized' else []),'-B','-m','unittest','discover','-v','-s',folder,'-p',pattern];row,_=run(label+'_'+mode,cmd)
    if row['exit_code']:failures.append(label+'_'+mode)
 unchanged=before==sources()
 if not unchanged:failures.append('SOURCE_CHANGED')
 result={'status':'PASS_NARROW_ONLY' if not failures else 'FAILED_OR_BLOCKED','commands':records,'failures':failures,'source_unchanged':unchanged,'cache_policy':'WARM_PINNED_CACHE_FRESH_CANDIDATES','full_release_accepted':False,'RH':'OPEN','Step4':'OPEN'}
 (out/'CHECK_RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({j:v for j,v in result.items() if j!='commands'},indent=2));return 1 if failures else 0
if __name__=='__main__':
 try:raise SystemExit(main())
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(2)
