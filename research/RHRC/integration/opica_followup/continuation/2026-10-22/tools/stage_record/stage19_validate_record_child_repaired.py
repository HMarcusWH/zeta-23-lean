from pathlib import Path
import concurrent.futures,datetime,hashlib,json,os,subprocess,sys
S=Path(__file__).resolve().parent;R=S.parent/'opica-followup-repo';O=S/'record-validation-repaired/native';O.mkdir(parents=True,exist_ok=False)
manifest=R/'research/RHRC/integration/opica_followup/CONTINUATION_MANIFEST.json';before=hashlib.sha256(manifest.read_bytes()).hexdigest()
def run(pair):
    name,flags=pair;env=os.environ.copy();folder=O/('temp-'+name);folder.mkdir();env['TEMP']=str(folder);env['TMP']=str(folder)
    cmd=[sys.executable,'-B',*flags,'-m','unittest','discover','-s','research/RHRC/integration/opica_followup/tests','-p','test_*.py']
    start=datetime.datetime.now(datetime.timezone.utc).isoformat();p=subprocess.run(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=900)
    log=name+'.log';(O/log).write_bytes(p.stdout)
    row=dict(name=name,command=cmd,started_at=start,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=p.returncode,log=log,log_sha256=hashlib.sha256(p.stdout).hexdigest());print(json.dumps(row),flush=True);return row
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(run,[('normal',[]),('optimized',['-O'])]))
summary=dict(status='PASS_CHILD_TESTS_ONLY' if all(r['exit_code']==0 for r in rows) else 'FAIL',commands=rows,manifest_before=before,manifest_after=hashlib.sha256(manifest.read_bytes()).hexdigest(),RH='OPEN',Step4='OPEN',release_accepted=False)
(O/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8');print(summary['status'])
