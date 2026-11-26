import hashlib,json,os,pathlib,subprocess,tempfile,zipfile
def need(ok,msg):
    if not ok: raise RuntimeError(msg)
def run(*args,cwd=None):
    return subprocess.check_output(args,cwd=cwd,text=True,timeout=180).strip()
def sha(path):
    with pathlib.Path(path).open("rb") as f:return hashlib.file_digest(f,"sha256").hexdigest()
def api(path):
    return json.loads(run("gh","api",path))
repo="HMarcusWH/zeta-23-lean"
s={'head': 'eae5672cbbb18c4d53f50eccb664efb0421b877a', 'tree': '4efb4851013134e01742c230f64c256e0046375c', 'run': 45497774256, 'artifact': 14986188748, 'archive': '0e4c361f39691ec3ec61ee2fe61e0c5b588e656846d7bf69a9a61f1cde12fcc8', 'patch': '7781a97fc2bf1b43b6f8c378f6596e5f07cd0d6cbb5939fb2cb51e6fd1059a0d', 'count': 10, 'workflow': '.github/workflows/opica-dispatch-registration-review.yml', 'stage': 'ops/opica-canonical-staged-314-eae5672', 'target': 'ops/opica-dispatch-registration-20261123', 'message': 'Stage exact dispatch-registration canonical products for review'}
key="314"
root=pathlib.Path.cwd()
r=api(f"repos/{repo}/actions/runs/{s['run']}")
need(r["head_sha"]==s["head"] and r["repository"]["full_name"]==repo and r["path"].split("@")[0]==s["workflow"] and r["run_attempt"]==1,"Producer identity")
jobs=api(f"repos/{repo}/actions/runs/{s['run']}/attempts/1/jobs?per_page=100")["jobs"]
need(sum(j["name"]=="canonical-candidate" and j["conclusion"]=="success" for j in jobs)==1,"Canonical producer not successful")
a=api(f"repos/{repo}/actions/artifacts/{s['artifact']}")
need(a["id"]==s["artifact"] and a["workflow_run"]["id"]==s["run"] and a["digest"]=="sha256:"+s["archive"] and not a["expired"],"Artifact identity")
with tempfile.TemporaryDirectory() as d:
    td=pathlib.Path(d);archive=td/"candidate.zip"
    with archive.open("wb") as f:subprocess.run(["gh","api",f"repos/{repo}/actions/artifacts/{s['artifact']}/zip"],stdout=f,check=True,timeout=300)
    need(sha(archive)==s["archive"],"Artifact digest")
    with zipfile.ZipFile(archive) as z:
        def member(leaf):
            names=[n for n in z.namelist() if pathlib.PurePosixPath(n).name==leaf]
            need(len(names)==1,"Ambiguous member: "+leaf)
            return z.read(names[0])
        receipt=json.loads(member("receipt.json"));patch=td/"generated-state.patch";patch.write_bytes(member("generated-state.patch"))
        need(sha(patch)==receipt["patch_sha256"]==s["patch"],"Patch digest")
        need(receipt["schema"]=="OPICA_CANONICAL_CANDIDATE_V3" and receipt["status"]=="REVIEW_ONLY_GENERATED_STATE" and receipt["source_head"]==s["head"] and receipt["source_tree"]==s["tree"] and receipt["proof_acceptance"] is False and all(receipt[k]=="OPEN" for k in ("RH","C1","Step4")),"Receipt scope")
        for name,digest in receipt["logs_sha256"].items():
            need(hashlib.sha256(member(pathlib.PurePosixPath(name).name)).hexdigest()==digest,"Log digest "+name)
    need(run("git","rev-parse","HEAD")==s["head"] and run("git","rev-parse","HEAD^{tree}")==s["tree"] and not run("git","status","--porcelain","--untracked-files=all"),"Source checkout")
    # Actual approved inventory is read from the checked-out project manifest.
    before=receipt["before_sha256"];after=receipt["after_write_sha256"];frozen=receipt["frozen_git_oids"];changed=set(receipt["changed_paths"])
    need(len(before)==len(after)==81 and set(before)==set(after) and after==receipt["after_check_sha256"],"81-product boundary")
    need(len(frozen)==4 and set(frozen)<=set(before) and len(changed)==receipt["changed_count"]==s["count"] and not (changed&set(frozen)),"Frozen/active boundary")
    need(changed=={p for p in before if before[p]!=after[p]},"Changed paths")
    for p in before:
        rel=pathlib.PurePosixPath(p);need(not rel.is_absolute() and ".." not in rel.parts and not pathlib.Path(p).is_symlink(),"Unsafe path")
    if key=="312":
        policy=json.loads(pathlib.Path("research/RHRC/integration/opica_next_acceptance/SOURCE_POLICY.json").read_text())
        need(set(policy["allowed_generated"])==set(before)-set(frozen),"Successor generated whitelist")
        need(set(policy["unchanged_frozen_products"])==set(frozen),"Successor frozen whitelist")
    else:
        import sys
        sys.path.insert(0,str(root))
        from research.RHRC.integration.opica_dispatch_registration.gate import check
        inspected=check(root)
        need(inspected["checked_commit"]==s["head"] and inspected["checked_tree"]==s["tree"],"Registration admission")
    need({p:sha(p) for p in before}==before,"Before bytes")
    for p,oid in frozen.items():need(run("git","rev-parse",s["head"]+":"+p)==oid,"Frozen Git object")
    run("git","apply","--check",str(patch));run("git","apply",str(patch))
    rows=run("git","diff","--name-status","--no-renames","HEAD").splitlines()
    need(all(x.startswith("M\t") for x in rows) and {x[2:] for x in rows}==changed and not run("git","ls-files","--others","--exclude-standard"),"Unexpected patch delta")
    need({p:sha(p) for p in after}==after,"After bytes")
    run("git","add","--",*sorted(changed))
    run("git","config","user.name","OPICA canonical patch review")
    run("git","config","user.email","opica-review@invalid.example")
    run("git","commit","-m",s["message"],"-m",f"Reviewed artifact {s['artifact']} from run {s['run']}; archive {s['archive']}; exact before/write/check hashes. RH, C1, Step4 OPEN.")
    commit=run("git","rev-parse","HEAD");tree=run("git","rev-parse","HEAD^{tree}")
    need(tree=="7ab96c28f455d0bfdd280856b6d9e0bcf7015e5c","Result tree differs from independently checked candidate")
    need(run("git","rev-parse","HEAD^")==s["head"] and not run("git","status","--porcelain","--untracked-files=all"),"Staged commit")
    need(run("git","ls-remote","--heads","origin","refs/heads/"+s["target"]).split()[0]==s["head"],"Target changed during staging")
    need(not run("git","ls-remote","--heads","origin","refs/heads/"+s["stage"]),"Staging ref already exists; review instead of overwrite")
    run("git","push","origin","HEAD:refs/heads/"+s["stage"])
    result={"status":"STAGED_REVIEWED_CANONICAL_COMMIT_ONLY","source_head":s["head"],"source_tree":s["tree"],"commit":commit,"tree":tree,"staging_ref":s["stage"],"target_ref":s["target"],"changed_count":len(changed),"archive_sha256":s["archive"],"patch_sha256":s["patch"],"proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    out=pathlib.Path(os.environ["RUNNER_TEMP"])/"canonical-stage.json";out.write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result),flush=True)
