from pathlib import Path
import subprocess, json, sys, time, os
R=Path('/mnt/data/rh_audit/snapshot/zeta-23-lean-main');O=Path('/mnt/data/rh_audit');res=[]
env=dict(os.environ,OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1')
paths=sorted(R.glob('research/RHRC/**/check*.py'))
cmds=[(p.stem,[sys.executable,str(p)]) for p in paths]
cmds += [('r004_exact_displacement',[sys.executable,'research/RHRC/routes/R004_prolate_v2/derive_exact_displacement.py'])]
for name,cmd in cmds:
 t=time.monotonic();p=O/'logs'/('extra_'+name+'.log');print('START',name,flush=True)
 try:
  with p.open('w') as f:
   f.write('$ '+' '.join(cmd)+'\n');f.flush();cp=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=80)
  rc=cp.returncode; txt=p.read_text();status='PASS' if rc==0 else ('ENVIRONMENT_BLOCKED' if "No module named 'flint'" in txt else 'FAIL_OR_MISSING_INPUT')
 except subprocess.TimeoutExpired:rc=None;status='TIMEOUT';txt=p.read_text()
 row={'name':name,'command':cmd,'returncode':rc,'disposition':status,'elapsed_seconds':round(time.monotonic()-t,3),'log':str(p.relative_to(O)),'tail':txt[-4000:]};res.append(row)
 (O/'results/extra_test_results.json').write_text(json.dumps(res,indent=2)+'\n');print('END',name,status,flush=True)
print('COMPLETE',flush=True)
