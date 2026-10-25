from pathlib import Path
import datetime, hashlib, json, os, platform, subprocess, sys, tempfile
R=Path('/mnt/c/Users/macka/.codex/.chatgpt-projects/g-p-6a353c7268b08191b685956e466d73e4/work/opica-followup-repo')
O=R.parent/'opica-stage19/record-validation/linux'
O.mkdir(parents=True,exist_ok=False)
os.environ['TMPDIR']=tempfile.mkdtemp(prefix='opica-stage19-record-',dir='/tmp')
tempfile.tempdir=os.environ['TMPDIR'];os.environ['PYTHONDONTWRITEBYTECODE']='1'
def state():
    return {n:subprocess.check_output(['git',*a],cwd=R,text=True).strip() for n,a in
            [('head',['rev-parse','HEAD']),('tree',['rev-parse','HEAD^{tree}']),('dirty',['status','--porcelain'])]}
before=state();rows=[]
for name,flags in [('normal',[]),('optimized',['-O'])]:
    cmd=[sys.executable,'-B',*flags,'-m','unittest','discover','-s','research/RHRC/integration/opica/tests','-p','test_contract.py']
    start=datetime.datetime.now(datetime.timezone.utc).isoformat()
    p=subprocess.run(cmd,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=900)
    log=name+'.log';(O/log).write_bytes(p.stdout)
    rows.append(dict(name=name,command=cmd,started_at=start,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=p.returncode,log=log,log_sha256=hashlib.sha256(p.stdout).hexdigest()))
    print(json.dumps(rows[-1]),flush=True)
after=state()
summary=dict(status='PASS_FOCUSED_PARENT_TESTS_ONLY' if all(r['exit_code']==0 for r in rows) else 'FAIL',source_before=before,source_after=after,commands=rows,python=sys.version,platform=platform.platform(),tmpdir=os.environ['TMPDIR'],RH='OPEN',Step4='OPEN',release_accepted=False)
(O/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(summary['status'])
