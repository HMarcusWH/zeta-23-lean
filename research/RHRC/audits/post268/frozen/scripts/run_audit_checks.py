from pathlib import Path
import subprocess,time,json,sys,os,re
A=Path('/mnt/data/rh_audit'); R=A/'snapshot/zeta-23-lean-main'; results=[]
cmds=[('original_rhrc_suite',[sys.executable,'research/RHRC/tools/run_suite.py'],600),('graph_build_check',[sys.executable,'research/RHRC/graph/build.py','--check'],300),('graph_validate',[sys.executable,'research/RHRC/graph/validate.py'],300)]
for d in ['graph','ffbbp','ool','runner','control_v2','integration']:
 cmds.append((d+'_unittests',[sys.executable,'-m','unittest','discover','-s',f'research/RHRC/{d}/tests','-p','test_*.py','-v'],300))
for name,path,args in [('ffbbp_assurance','research/RHRC/ffbbp/rhkg_assurance.py',['--check']),('ool_phase_atlas','research/RHRC/ool/rhkg_phase_atlas.py',['--check']),('integration_lint','research/RHRC/integration/integration_lint.py',[])]: cmds.append((name,[sys.executable,path,*args],300))
for name in ['claim_lint','registry_lint','promoted_binding_lint','registered_theorem_binding_lint','lean_imports','arithmetic_firewall_lint','million_dollar_firewall_lint']: cmds.append((name,[sys.executable,f'research/RHRC/tools/{name}.py'],120))
for name,path in [('post155_countermodel','research/RHRC/countermodels/check_post155_riesz_pointwise_sign.py'),('r002_ccm_compare','research/RHRC/routes/R002_multi_probe/compare_r002_ccm_probe_families.py')]: cmds.append((name,[sys.executable,path],180))
env=dict(os.environ); env.update(OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',PYTHONHASHSEED='0')
for name,cmd,timeout in cmds:
 print('START',name,flush=True); t=time.monotonic(); p=A/'logs'/(name+'.log'); rc=None
 try:
  with p.open('w') as f:
   f.write('$ '+' '.join(cmd)+'\n'); f.flush(); res=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
  rc=res.returncode; disposition='PASS' if rc==0 else 'FAIL'
 except subprocess.TimeoutExpired: disposition='TIMEOUT'
 text=p.read_text(errors='replace'); m=re.findall(r'Ran (\d+) tests? in ([\d.]+)s',text)
 row={'name':name,'command':cmd,'returncode':rc,'disposition':disposition,'elapsed_seconds':round(time.monotonic()-t,3),'log':str(p.relative_to(A)),'unittest_summaries':[{'tests':int(n),'seconds':float(s)} for n,s in m],'tail':text[-3000:]}
 results.append(row); (A/'results/test_results.json').write_text(json.dumps(results,indent=2)+'\n'); print('END',name,disposition,row['elapsed_seconds'],flush=True)
print('COMPLETE',flush=True)
