from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import datetime,hashlib,json,os,re,subprocess,time
S=Path(__file__).resolve().parent;W=S.parent;R=W/'opica-followup-repo';O=S/'clean-controls';O.mkdir(exist_ok=False)
L='C:/Users/macka/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lake.exe'
HEAD='139c1a0d88cc0fb2d8a0d8ea71e152b25b14c36e';TREE='3e63b0c72fc04da7bab45388d6096e82e95c4acb'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True).strip()
assert git('rev-parse','HEAD')==HEAD and git('rev-parse','HEAD^{tree}')==TREE and not git('status','--porcelain')
paths=sorted((R/'Zeta23').rglob('*.lean'))+[R/'lean-toolchain',R/'lake-manifest.json'];before={p.relative_to(R).as_posix():sha(p) for p in paths}
(O/'source-before.json').write_text(json.dumps(before,indent=2)+'\n',encoding='utf-8')
prior=json.loads((W/'opica-stage20/clean-controls/CHECK_RESULT.json').read_bytes());assert prior['status']=='PASS_CONTROLS_ONLY'
jobs=[]
helper_names=['OPICAConfluentAudit','OPICAActualFirstCellAudit','OPICARightCellTaylor','OPICAShCoefficientExtraction','OPICAActualMeasureCell','OPICAGroupedConfluent']
for row in prior['controls']:
    p=W/'opica-stage20/clean-controls'/row['file'];assert sha(p)==row['source_sha256']
    text=p.read_text(encoding='utf-8')
    for ns in helper_names:text=re.sub(r'(?<![\w.])'+re.escape(ns)+r'\b','Zeta23.OPICAFollowup.'+ns,text)
    q=O/p.name;q.write_text(text,encoding='utf-8',newline='\n');jobs.append((q,row['expected']=='PASS',row['scope']))
F=W/'audit-finite-span/SEALED_FINITE_SPAN_2026-10-24'
for name,positive in [('NegativeFullFiniteSpanFinal',False),('NegativeBudgetIndependenceFinal',False),('DuplicateBasisControlFinal',True),('WeightedControlsFinal',True)]:
    raw=(F/(name+'.lean')).read_bytes();needle=b'import FiniteSpanSeparationFullCandidate';assert raw.count(needle)==1
    q=O/(name+'.lean');q.write_bytes(raw.replace(needle,b'import Zeta23.OPICAFollowup.FiniteSpanSeparation'))
    jobs.append((q,positive,'Actual finite-span clause / independent-basis / reflection / selfduality falsification'))
assert len(jobs)==21
env=dict(os.environ,LEAN_NUM_THREADS='2');version=subprocess.check_output([L,'env','lean','--version'],cwd=R,env=env,text=True).strip();assert 'd8b18978322de05a8f3dba51ef03cf5461676c17' in version
def run(job):
    p,positive,scope=job;cmd=[L,'env','lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxHeartbeats=800000',str(p)]
    start=time.monotonic();r=subprocess.run(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=1200);log=O/(p.stem+'.log');log.write_bytes(r.stdout);text=r.stdout.decode('utf-8',errors='replace')
    axioms={a:[x.strip() for x in xs.split(',') if x.strip()] for a,xs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)}
    bad=any(x in text for x in ['unknown module','unknown identifier','invalid import','object file','sorryAx'])
    if positive:
        requested=re.findall(r'^#print axioms (\S+)\s*$',p.read_text(encoding='utf-8'),re.M)
        passed=r.returncode==0 and not bad and requested and set(requested)<=set(axioms) and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
        observed='PASS_ACTUAL_FALSIFICATION_CONTROL' if passed else 'FAILED_CONTROL'
    else:
        passed=r.returncode!=0 and 'error:' in text and not bad;observed='REJECTED_INTENDED_MUTATION' if passed else 'FAILED_CONTROL'
    return {'name':p.stem,'file':p.name,'source_sha256':sha(p),'log':log.name,'log_sha256':sha(log),'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start,'expected':'PASS' if positive else 'REJECTED','observed':observed,'passed':bool(passed),'scope':scope,'axioms':axioms}
with ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(run,jobs))
after={p.relative_to(R).as_posix():sha(p) for p in paths};assert before==after and git('rev-parse','HEAD')==HEAD and not git('status','--porcelain')
report={'schema':'OPICA_STAGE21_CLEAN_CONTROLS_V1','status':'PASS_CONTROLS_ONLY' if all(r['passed'] for r in rows) else 'FAIL','checked_commit':HEAD,'checked_tree':TREE,'dirty_status_during_checks':'','compiler':version,'source_unchanged':True,'source_snapshot':'source-before.json','source_snapshot_sha256':sha(O/'source-before.json'),'controls':rows,'negative_source_files':17,'positive_source_files':4,'new_finite_span_mutations':4,'finished_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'aggregate_accepted':False,'RH':'OPEN','Step4':'OPEN'}
(O/'CHECK_RESULT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print(report['status'],[(r['name'],r['observed']) for r in rows])
raise SystemExit(0 if report['status']=='PASS_CONTROLS_ONLY' else 1)
