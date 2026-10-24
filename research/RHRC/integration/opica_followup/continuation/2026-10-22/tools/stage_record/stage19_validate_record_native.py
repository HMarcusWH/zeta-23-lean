from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys
S=Path(__file__).resolve().parent
R=S.parent/'opica-followup-repo'
O=S/'record-validation/native'
O.mkdir(parents=True,exist_ok=False)
env=os.environ.copy();env['TEMP']=str(O/'temp');env['TMP']=env['TEMP'];(O/'temp').mkdir()
def state():
    return {n:subprocess.check_output(['git',*a],cwd=R,text=True).strip() for n,a in
            [('head',['rev-parse','HEAD']),('tree',['rev-parse','HEAD^{tree}']),('dirty',['status','--porcelain'])]}
rows=[];before=state()
jobs=[('child-normal',['-B','-m','unittest','discover','-s','research/RHRC/integration/opica_followup/tests','-p','test_*.py']),
      ('child-optimized',['-B','-O','-m','unittest','discover','-s','research/RHRC/integration/opica_followup/tests','-p','test_*.py']),
      ('frozen-replay',['-B','research/RHRC/integration/opica_followup/replay_controls.py','--modes','normal','optimized','--include-numerical','--output-dir',str(O/'frozen')])]
for name,args in jobs:
    start=datetime.datetime.now(datetime.timezone.utc).isoformat()
    p=subprocess.run([sys.executable,*args],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=900)
    (O/(name+'.log')).write_bytes(p.stdout)
    rows.append(dict(name=name,command=[sys.executable,*args],exit_code=p.returncode,started_at=start,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),log=name+'.log',log_sha256=hashlib.sha256(p.stdout).hexdigest()))
    print(json.dumps(rows[-1]),flush=True)
after=state()
summary=dict(status='PASS_TESTS_AND_FROZEN_REPLAY_ONLY' if all(r['exit_code']==0 for r in rows) else 'FAIL',source_before=before,source_after=after,commands=rows,RH='OPEN',Step4='OPEN',release_accepted=False)
(O/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(summary['status'])
