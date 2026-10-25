from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time

S=Path(__file__).resolve().parent;W=S.parent;R=W/'opica-followup-repo'
O=S/'clean-controls';O.mkdir(exist_ok=False)
L='C:/Users/macka/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lake.exe'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True).strip()
head,tree=git('rev-parse','HEAD'),git('rev-parse','HEAD^{tree}')
assert head=='9a8b2a4baee49f2056c7945b1544a7bc2893735b' and not git('status','--porcelain')
paths=list((R/'Zeta23').rglob('*.lean'))+[R/'lean-toolchain',R/'lake-manifest.json']
before={p.relative_to(R).as_posix():sha(p) for p in sorted(paths)}
(O/'source-before.json').write_text(json.dumps(before,indent=2)+'\n',encoding='utf-8')
jobs=[]
for p in sorted((W/'opica-stage19/negative-controls').glob('*.lean')):
    q=O/p.name;q.write_bytes(p.read_bytes());jobs.append((q,False,'Stage19 force/sampling contract mutation'))
for p in sorted((W/'audit-rate/staged').glob('Negative*.lean')):
    q=O/p.name;q.write_bytes(p.read_bytes());jobs.append((q,False,'Rate/physical consumer contract mutation'))
for name in ['NegativeConfluentProfilesDistinctness','NegativeConfluentProfilesDeterminantSign','NegativeConfluentProfilesUnnormalized']:
    p=W/'audit-math-grouped'/(name+'.lean');q=O/p.name
    b=p.read_bytes();assert b.count(b'import ConfluentProfilesCandidate')==1
    q.write_bytes(b.replace(b'import ConfluentProfilesCandidate',b'import Zeta23.OPICAFollowup.ConfluentProfiles'))
    jobs.append((q,False,'H2a full statement mutation'))
for name in ['ConfluentProfilesFactorialControls','ConfluentProfilesReflectionControl']:
    p=W/'audit-math-grouped'/(name+'.lean');q=O/p.name
    b=p.read_bytes();assert b.count(b'import ConfluentProfilesCandidate')==1
    b=b.replace(b'import ConfluentProfilesCandidate',b'import Zeta23.OPICAFollowup.ConfluentProfiles')
    text=b.decode('utf-8')
    ns='OPICARightCellTaylor' if name.endswith('FactorialControls') else 'OPICAConfluentReflectionControl'
    # Resolve namespace exactly from the supplied positive source, then qualify every print.
    ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
    text=re.sub(r'^#print axioms (\S+)\s*$',lambda m:'#print axioms '+(m.group(1) if '.' in m.group(1) else ns+'.'+m.group(1)),text,flags=re.M)
    q.write_text(text,encoding='utf-8',newline='\n');jobs.append((q,True,'Actual-kernel normalization/degeneracy falsification'))
    if name.endswith('FactorialControls'):
        neg=O/'NegativeParameterFactorial.lean'
        neg.write_text(text+'\nexample : OPICARightCellTaylor.oddJetCoefficient (1 / 4) 2 1 = (-1 / 3 : ℂ) := by\n  exact OPICARightCellTaylor.second_parameter_jet_cubic_coefficient\n',encoding='utf-8',newline='\n')
        jobs.append((neg,False,'Wrong 1/2! normalization against proved actual coefficient'))
assert len(jobs)==17 and len({p.name for p,_,_ in jobs})==17
env=dict(os.environ,LEAN_NUM_THREADS='2')
version=subprocess.check_output([L,'env','lean','--version'],cwd=R,env=env,text=True).strip()
assert 'd8b18978322de05a8f3dba51ef03cf5461676c17' in version
def run(job):
    p,positive,scope=job;cmd=[L,'env','lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxHeartbeats=800000',str(p)]
    start=time.monotonic();r=subprocess.run(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=1200)
    log=O/(p.stem+'.log');log.write_bytes(r.stdout);text=r.stdout.decode('utf-8',errors='replace')
    axioms={n:[a.strip() for a in xs.split(',') if a.strip()] for n,xs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)}
    bad=any(x in text for x in ['unknown module','unknown identifier','invalid import','object file','sorryAx'])
    if positive:
        requested=re.findall(r'^#print axioms (\S+)\s*$',p.read_text(encoding='utf-8'),re.M)
        passed=r.returncode==0 and not bad and requested and set(requested)<=set(axioms) and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
        observed='PASS_ACTUAL_FALSIFICATION_CONTROL' if passed else 'FAILED_CONTROL'
    else:
        passed=r.returncode!=0 and 'error:' in text and not bad
        observed='REJECTED_INTENDED_MUTATION' if passed else 'FAILED_CONTROL'
    return {'name':p.stem,'file':p.name,'source_sha256':sha(p),'log':log.name,'log_sha256':sha(log),'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start,'scope':scope,'expected':'PASS' if positive else 'REJECTED','observed':observed,'passed':bool(passed),'axioms':axioms}
with ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(run,jobs))
after={p.relative_to(R).as_posix():sha(p) for p in sorted(paths)}
assert before==after and not git('status','--porcelain') and git('rev-parse','HEAD')==head
report={'schema':'OPICA_STAGE20_CLEAN_CONTROLS_V1','status':'PASS_CONTROLS_ONLY' if all(r['passed'] for r in rows) else 'FAIL','checked_commit':head,'checked_tree':tree,'dirty_status_during_checks':'','compiler':version,'source_unchanged':True,'source_snapshot':'source-before.json','source_snapshot_sha256':sha(O/'source-before.json'),'controls':rows,'finished_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'aggregate_accepted':False,'RH':'OPEN','Step4':'OPEN'}
(O/'CHECK_RESULT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k!='controls'},indent=2))
raise SystemExit(0 if report['status']=='PASS_CONTROLS_ONLY' else 1)
