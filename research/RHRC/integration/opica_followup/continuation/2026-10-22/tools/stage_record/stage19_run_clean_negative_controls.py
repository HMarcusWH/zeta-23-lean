from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time

HERE=Path(__file__).resolve().parent
REPO=HERE.parent/'opica-followup-repo'
OUT=HERE/'clean-negative-controls'
OUT.mkdir(exist_ok=False)
LAKE='C:/Users/macka/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lake.exe'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=REPO,text=True).strip()
head,tree,dirty=git('rev-parse','HEAD'),git('rev-parse','HEAD^{tree}'),git('status','--porcelain')
if dirty:raise RuntimeError('Clean checked code tree required')
sources=['Zeta23/OPICAFollowup/Consumers.lean','lean-toolchain','lake-manifest.json',
 'research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedForceSampling.lean',
 'research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedSampleSign.lean',
 'research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedWordJet.lean']
before={p:sha(REPO/p) for p in sources}
for p in sources:
    if hashlib.sha256(subprocess.check_output(['git','show',head+':'+p],cwd=REPO)).hexdigest()!=before[p]:
        raise RuntimeError('Source does not match checked commit: '+p)
env=dict(os.environ,LEAN_NUM_THREADS='2')
version=subprocess.check_output([LAKE,'env','lean','--version'],cwd=REPO,env=env,text=True)
if '4.33.0-rc2' not in version or 'd8b18978322de05a8f3dba51ef03cf5461676c17' not in version:
    raise RuntimeError('Wrong compiler')
def check(p):
    path=OUT/(p.stem+'.log')
    argv=[LAKE,'env','lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxHeartbeats=800000',str(p)]
    start=time.monotonic()
    with path.open('wb') as f:
        proc=subprocess.run(argv,cwd=REPO,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=900)
    text=path.read_text(encoding='utf-8',errors='replace')
    reject=proc.returncode!=0 and 'error:' in text and not any(x in text for x in
          ('unknown module','object file','unknown identifier','invalid import'))
    return {'name':p.stem,'file':'negative-controls/'+p.name,'source_sha256':sha(p),
       'log':'negative-controls/'+path.name,'log_sha256':sha(path),'command':argv,
       'exit_code':proc.returncode,'seconds':time.monotonic()-start,
       'expected':'REJECTED','observed':'REJECTED_INTENDED_MUTATION' if reject else 'FAILED_CONTROL'}
paths=sorted((HERE/'negative-controls').glob('*.lean'))
with ThreadPoolExecutor(max_workers=2) as pool:
    rows=list(pool.map(check,paths))
after={p:sha(REPO/p) for p in sources}
ok=(len(rows)==6 and all(r['observed']=='REJECTED_INTENDED_MUTATION' for r in rows)
    and before==after and git('status','--porcelain')=='' and git('rev-parse','HEAD')==head)
report={'schema':'OPICA_STAGE19_CLEAN_NEGATIVE_REPLAY_V1',
 'status':'PASS_NEGATIVE_REPLAY_ONLY' if ok else 'FAIL',
 'checked_commit':head,'checked_tree':tree,'dirty_status_during_checks':dirty,
 'compiler':version.strip(),'source_before':before,'source_after':after,
 'source_unchanged':before==after,'negative_controls':rows,
 'finished_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'RH':'OPEN','Step4':'OPEN','full_release_accepted':False}
(OUT/'CHECK_RESULT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k not in ('source_before','source_after','negative_controls')},indent=2))
raise SystemExit(0 if ok else 1)
