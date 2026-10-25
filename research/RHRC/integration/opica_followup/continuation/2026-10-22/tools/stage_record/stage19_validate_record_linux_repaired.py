from pathlib import Path
import concurrent.futures,datetime,hashlib,json,os,platform,subprocess,sys,tempfile
R=Path('/mnt/c/Users/macka/.codex/.chatgpt-projects/g-p-6a353c7268b08191b685956e466d73e4/work/opica-followup-repo')
O=R.parent/'opica-stage19/record-validation-repaired/linux';O.mkdir(parents=True,exist_ok=False)
def state():
    rows={n:subprocess.check_output(['git',*a],cwd=R,text=True).strip() for n,a in [('head',['rev-parse','HEAD']),('tree',['rev-parse','HEAD^{tree}']),('dirty',['status','--porcelain'])]}
    paths=['research/RHRC/integration/opica/validate_contract.py','research/RHRC/integration/opica/tests/test_contract.py','research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md','research/RHRC/integration/opica_followup/validate_contract.py','research/RHRC/integration/opica_followup/CONTINUATION_MANIFEST.json']
    rows['files']={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths};return rows
before=state()
def run(pair):
    name,flags=pair;env=os.environ.copy();env['TMPDIR']=tempfile.mkdtemp(prefix='opica-stage19-repaired-'+name+'-',dir='/tmp');env['PYTHONDONTWRITEBYTECODE']='1'
    cmd=[sys.executable,'-B',*flags,'-m','unittest','discover','-s','research/RHRC/integration/opica/tests','-p','test_contract.py']
    start=datetime.datetime.now(datetime.timezone.utc).isoformat();p=subprocess.run(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=900)
    log=name+'.log';(O/log).write_bytes(p.stdout)
    row=dict(name=name,command=cmd,started_at=start,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=p.returncode,log=log,log_sha256=hashlib.sha256(p.stdout).hexdigest(),tmpdir=env['TMPDIR'])
    print(json.dumps(row),flush=True);return row
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(run,[('normal',[]),('optimized',['-O'])]))
after=state()
summary=dict(status='PASS_FOCUSED_PARENT_TESTS_ONLY' if all(r['exit_code']==0 for r in rows) else 'FAIL',source_before=before,source_after=after,source_hashes_unchanged=before['files']==after['files'],commands=rows,python=sys.version,platform=platform.platform(),RH='OPEN',Step4='OPEN',release_accepted=False)
(O/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8');print(summary['status'],flush=True)
