#!/usr/bin/env python3
"""Approved, single-use resource extension for exactly460 previously UNRUN SECOND children."""
from __future__ import annotations
import argparse, copy, hashlib, json, math, os, signal, subprocess, sys, time, zipfile
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from k3_resume_partition import HERE, current_identity, digest, rational, LAYERS, validate_layer
import k3_source_revalidation as legacy_review

REPO=HERE.parents[4]
INTEGRATION=REPO/"research/RHRC/integration/post290"
PROTOCOL=INTEGRATION/"D2_UNRUN460_APPROVED_PROTOCOL.json"
CHILDREN=INTEGRATION/"D2_UNRUN460_CHILDREN.json"
RESOURCE={"precision_bits":512,"max_depth":48,"max_nodes":8192,"seconds":1800}
PROTOCOL_ID="SECOND_UNRUN_CAP_CONTINUATION_2026_10_14_v1"
ARCHIVE_SHA="0077e514187a0cb326170b7b13e9e699d898a2ba10d8b4b20fa75a5cd6072b92"
PARTITION_SHA="247bef79c15993061022868e0449356c0e5e35a506497154538ab06b6888ad1c"
CANDIDATE_SHA="041c4aa68b1140c4d11826277eb2e588509424077aff49c9297f35ddb516eb0c"
SEARCH_SHA="0a736f4a6b96c759f387c87b9602c7356b88b2d129ab8569b1212bf872fc68d9"
CONTROL_PATHS=["research/RHRC/routes/R003_ccm_bridge/post290/k3_continue_unrun460.py",
"research/RHRC/routes/R003_ccm_bridge/post290/k3_checkpoint_upload.cjs",
"research/RHRC/routes/R003_ccm_bridge/post290/test_k3_unrun460.py",
"research/RHRC/integration/post290/D2_UNRUN460_APPROVED_PROTOCOL.json",
"research/RHRC/integration/post290/D2_UNRUN460_CHILDREN.json",
".github/workflows/rhrc_post290_unrun460.yml",
".github/workflows/rhrc_post290_unrun460_check_batch.yml"]

def read(p):return json.loads(Path(p).read_text(encoding="utf-8"))
def write(p,v):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
    q=p.with_name(p.name+".atomic");q.write_text(json.dumps(v,indent=2,sort_keys=True,allow_nan=False)+"\n",encoding="utf-8");q.replace(p)
def exclusive(p,v):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
    with p.open("x",encoding="utf-8") as f:json.dump(v,f,sort_keys=True,allow_nan=False)
def identity():
    return {"source":current_identity(),"control_sha256":{n:digest(REPO/n) for n in CONTROL_PATHS}}
def approval():
    d=read(PROTOCOL)
    if d["protocol_id"]!=PROTOCOL_ID or d["approval"]["text"]!="Approve the 460-child continuation and its stated resource limit" or d["status"]!="APPROVED" or d["resources"]!=RESOURCE or d["children"]!=460 or d["max_concurrency"]!=8 or d["max_search_runner_seconds"]!=828000:
        raise ValueError("resource approval or frozen limits changed")
    if d["children_sha256"]!=digest(CHILDREN):raise ValueError("approved child manifest changed")
    return d

def guard_single_use(run_id,attempt,runs):
    if type(attempt) is not int or attempt!=1:raise ValueError("reruns forbidden: each child has one execution budget")
    rows=[r for page in runs for r in page.get("workflow_runs",[])] if isinstance(runs,list) else runs["workflow_runs"]
    if any(int(r["id"])<run_id for r in rows):raise ValueError("earlier run requires a complete no-consumption or remaining-approved-budget audit; no silent retry or automatic new authorization requirement")
    if not any(int(r["id"])==run_id for r in rows):raise ValueError("current workflow run missing from complete single-use audit")

def extract(archive,dest):
    if digest(archive)!=ARCHIVE_SHA:raise ValueError("wrong original archive")
    dest=Path(dest);dest.mkdir(parents=True,exist_ok=False)
    with zipfile.ZipFile(archive) as z:
        for i in z.infolist():
            if not (dest/i.filename).resolve().is_relative_to(dest.resolve()) or (i.external_attr>>16)&0o170000==0o120000:raise ValueError("unsafe archive")
        z.extractall(dest)

def archive_review(raw):
    raw=Path(raw)
    if digest(raw/"partition.json")!=PARTITION_SHA or digest(raw/"candidate/manifest.json")!=CANDIDATE_SHA or digest(raw/"search/campaign.json")!=SEARCH_SHA:raise ValueError("original producer bytes changed")
    p=read(raw/"partition.json");c=read(raw/"search/campaign.json")
    if p["current_source"]["commit"]!="4789c93f6dd60817936793935211522a0b8100e1" or c["first_jobs"]!=32 or c["second_jobs"]!=256 or c["unresolved_count"]!=0 or c["negative_investigation_stop"]:raise ValueError("wrong exhausted original campaign")
    if len(c["results"])!=288 or len({x["file"] for x in c["results"]})!=288:raise ValueError("missing or duplicate original search receipt")
    first=[];finished=[]
    for spec in c["results"]:
        if Path(spec["file"]).name!=spec["file"] or digest(raw/"search"/spec["file"])!=spec["sha256"]:raise ValueError("original288 receipt hash mismatch")
        v=read(raw/"search"/spec["file"])
        if v["partition_sha256"]!=PARTITION_SHA:raise ValueError("stale original receipt")
        if v["job"]["pass"]==1:first.append(v)
        else:
            if v["resources"]!=RESOURCE or v["unresolved"] or v.get("certified_negative_stop"):raise ValueError("original selected child unfinished")
            finished.append(v)
    if len(first)!=32 or len(finished)!=256:raise ValueError("wrong original pass counts")
    ordered=sorted(((v["job"],t,i) for v in first for i,t in enumerate(v["unresolved"])),key=lambda x:(x[0]["Q"],x[0]["component"],rational(x[1]["left"])))
    allchildren=[]
    for parent,tile,index in ordered:
        lo,hi=rational(tile["left"]),rational(tile["right"])
        for n in range(4):
            a,b=lo+(hi-lo)*n/4,lo+(hi-lo)*(n+1)/4
            allchildren.append({**parent,"id":parent["id"]+f"_R{index:05d}_P{n}","left":[a.numerator,a.denominator],"right":[b.numerator,b.denominator],"pass":2,"parent_job":parent["id"],"parent_leaf":index})
    second=read(raw/"search/second-partition.json")
    if len(allchildren)!=716 or allchildren[:256]!=second["jobs"] or [{**j,"reason":"SECOND_CHILD_CAP"} for j in allchildren[256:]]!=c["unrun"] or c["unrun"]!=second["unrun"]:raise ValueError("remaining child geometry not the original deterministic460")
    expected=read(CHILDREN)
    simple=lambda j:{k:j[k] for k in ("id","Q","parity","left","right","pass","parent_job","parent_leaf","component")}
    if expected["children"]!=[simple(j) for j in allchildren[256:]]:raise ValueError("approved460 ID/endpoint manifest differs")
    # Keep the old source guard unchanged. The one new approved resource runner is
    # checked in the new plan; historical mathematical equality uses the old guard.
    now=current_identity();review=copy.deepcopy(now)
    review["continuation_source_digests"].pop("k3_continue_unrun460.py",None)
    changes=legacy_review.compare(p["current_source"],review)
    for spec in read(raw/"candidate/manifest.json")["records"]:
        import k3_replay_shards as R
        v=R.target(raw/"candidate",spec);validate_layer(spec,v,"SECOND")
    return allchildren[256:],changes

def freeze(archive,dest,run_id,attempt,runs):
    approved=approval();guard_single_use(run_id,attempt,read(runs))
    dest=Path(dest)
    if dest.exists():raise ValueError("freeze directory already exists")
    dest.mkdir(parents=True)
    extract(archive,dest/"producer");jobs,changes=archive_review(dest/"producer")
    d={"schema":"post290.k3-unrun460-plan.v1","protocol":PROTOCOL_ID,"run_id":run_id,"run_attempt":1,"approval_sha256":digest(PROTOCOL),"children_sha256":digest(CHILDREN),"current_source":current_identity(),"validation_identity":identity(),"original_archive_sha256":ARCHIVE_SHA,"original_partition_sha256":PARTITION_SHA,"original_candidate_manifest_sha256":CANDIDATE_SHA,"original_search_campaign_sha256":SEARCH_SHA,"original_source":read(dest/"producer/partition.json")["current_source"],"source_integrity_changes":changes,"resources":RESOURCE,"max_concurrency":8,"jobs":[{"index":i,"wave":1 if i<256 else 2,"job":j} for i,j in enumerate(jobs)],"terminal_claim":"RH_OPEN","budget_policy":"ONE_EXECUTION_PER_CHILD_NO_RERUN_NO_RETRY"}
    write(dest/"plan.json",d);return d

def validate(plan):
    d=read(plan);approval()
    if d["schema"]!="post290.k3-unrun460-plan.v1" or d["protocol"]!=PROTOCOL_ID or d["resources"]!=RESOURCE or d["approval_sha256"]!=digest(PROTOCOL) or d["children_sha256"]!=digest(CHILDREN) or d["validation_identity"]!=identity() or d["current_source"]!=current_identity():raise ValueError("frozen plan/source/approval changed")
    if d["run_attempt"]!=1 or len(d["jobs"])!=460 or [j["index"] for j in d["jobs"]]!=list(range(460)):raise ValueError("wrong child inventory")
    if os.environ.get("GITHUB_RUN_ID") and (int(os.environ["GITHUB_RUN_ID"])!=d["run_id"] or int(os.environ["GITHUB_RUN_ATTEMPT"])!=1):raise ValueError("cross-run use or retry forbidden")
    simple=lambda j:{k:j[k] for k in ("id","Q","parity","left","right","pass","parent_job","parent_leaf","component")}
    if [simple(x["job"]) for x in d["jobs"]]!=read(CHILDREN)["children"]:raise ValueError("frozen child IDs/endpoints differ")
    if [x["wave"] for x in d["jobs"]]!=[1]*256+[2]*204:raise ValueError("wave boundaries changed")
    return d

def pending(job,planhash,reason):
    return {"schema":"post290.k3-search-job.v1","job":job,"partition_sha256":planhash,"resources":RESOURCE,"accepted":[],"unresolved":[{"left":job["left"],"right":job["right"],"reason":reason,"unrun":True}],"tested_nodes":0,"elapsed_seconds":0,"certified_negative_stop":False,"status":"UNRESOLVED","terminal_claim":"RH_OPEN"}

def validate_result(v,job,planhash):
    if v.get("job")!=job or v.get("partition_sha256")!=planhash or v.get("resources")!=RESOURCE or type(v.get("certified_negative_stop"))is not bool or type(v.get("tested_nodes"))is not int or not 0<=v["tested_nodes"]<=8192:raise ValueError("wrong child result identity/resources")
    if v.get("terminal_claim")!="RH_OPEN" or v.get("status")!=("UNRESOLVED" if v["unresolved"] else "PASS"):raise ValueError("contradictory child disposition")
    def finite(x):
        if isinstance(x,float) and not math.isfinite(x):raise ValueError("nonfinite child output")
        if isinstance(x,dict):
            for k,y in x.items():
                if k in ("lower","upper") and isinstance(y,str) and not Decimal(y).is_finite():raise ValueError("nonfinite child bound")
                finite(y)
        if isinstance(x,list):
            for y in x:finite(y)
    finite(v)
    accepted=v["accepted"];unresolved=v["unresolved"];lo,hi=rational(job["left"]),rational(job["right"]);cursor=lo
    for a,b in sorted((rational(t["left"]),rational(t["right"])) for t in accepted+unresolved):
        if a!=cursor or not lo<=a<b<=hi:raise ValueError("child coverage gap/overlap/widening")
        cursor=b
    if cursor!=hi:raise ValueError("child does not cover original endpoints")
    if any(t.get("accepted")is not True or t.get("method")!="SECOND" for t in accepted):raise ValueError("unaccepted/non-SECOND tile")
    if v["certified_negative_stop"] and not unresolved:raise ValueError("negative stop relabelled positive")
    return v

def claim(plan,index,out):
    d=validate(plan)
    if type(index)is not int or not 0<=index<460:raise ValueError("invalid child index")
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    x={"protocol":PROTOCOL_ID,"run_id":d["run_id"],"index":index,"job":d["jobs"][index]["job"],"plan_sha256":digest(plan),"resources":RESOURCE,"budget":"CLAIMED_ONCE_NO_RETRY"}
    exclusive(out/"budget-claim.json",x);write(out/"result.json",pending(x["job"],digest(plan),"CLAIMED_NOT_STARTED"));return x

def upload(name,file):
    helper=HERE/"k3_checkpoint_upload.cjs"
    subprocess.run(["node",str(helper),name,str(file)],check=True,timeout=12)

def run(plan,index,out,with_upload=True):
    d=validate(plan);out=Path(out);x=read(out/"budget-claim.json");job=d["jobs"][index]["job"];ph=digest(plan)
    if x["job"]!=job or x["plan_sha256"]!=ph or x["run_id"]!=d["run_id"]:raise ValueError("wrong durable budget claim")
    if (out/"launch.json").exists():raise ValueError("budget already launched; retry forbidden")
    # Initial checkpoint is recoverable before a single native enclosure is run.
    if with_upload:upload(f"k3-unrun460-cp-{index:03d}-000",out/"result.json")
    exclusive(out/"launch.json",{"plan_sha256":ph,"index":index,"started_utc":time.time(),"max_seconds":1800})
    start=time.monotonic()
    with (out/"worker.log").open("w") as log:
        worker=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),"worker",str(plan),"--index",str(index),"--out",str(out)],stdout=log,stderr=subprocess.STDOUT,start_new_session=os.name!="nt")
    next_cp=start+45;sequence=1;uploader=None;upload_start=None;failure=None
    try:
        while worker.poll()is None:
            now=time.monotonic()
            if now-start>=1800:failure="HARD_WALL_TIMEOUT";break
            if uploader:
                rc=uploader.poll()
                if rc is not None:
                    if rc:failure="NATIVE_NEGATIVE_INVESTIGATION_STOP" if rc==42 else "CHECKPOINT_UPLOAD_FAILED";break
                    uploader=None
                elif now-upload_start>=12:failure="CHECKPOINT_UPLOAD_TIMEOUT";break
            if with_upload and now>=next_cp and uploader is None:
                snapshot=out/f"checkpoint-{sequence:03d}.json"
                # Atomic worker writes ensure each snapshot is one whole receipt.
                write(snapshot,read(out/"result.json"))
                uploader=subprocess.Popen(["node",str(HERE/"k3_checkpoint_upload.cjs"),f"k3-unrun460-cp-{index:03d}-{sequence:03d}",str(snapshot)],stdout=subprocess.DEVNULL,stderr=subprocess.STDOUT)
                upload_start=now;sequence+=1;next_cp=now+45
            time.sleep(.2)
    finally:
        if worker.poll()is None:
            if os.name=="nt":worker.kill()
            else:os.killpg(worker.pid,signal.SIGKILL)
        worker.wait()
        if uploader and uploader.poll()is None:uploader.kill();uploader.wait()
    v=read(out/"result.json")
    if failure or worker.returncode:
        for t in v["unresolved"]:t["reason"]=failure or "WORKER_FAILED"
        v["status"]="UNRESOLVED" if v["unresolved"] else "PASS"
        v["interruption"]=failure or "WORKER_FAILED"
    validate_result(v,job,ph);write(out/"result.json",v)
    write(out/"receipt.json",{"schema":"post290.k3-unrun460-child.v1","index":index,"run_id":d["run_id"],"plan_sha256":ph,"result_sha256":digest(out/"result.json"),"claim_sha256":digest(out/"budget-claim.json"),"launch_sha256":digest(out/"launch.json"),"wall_seconds":time.monotonic()-start,"checkpoint_upload_failure":failure,"terminal_claim":"RH_OPEN"})
    if v["certified_negative_stop"]:
        write(out/"negative-stop.json",{"index":index,"plan_sha256":ph,"result_sha256":digest(out/"result.json"),"disposition":"STOP_FOR_INDEPENDENT_NEGATIVE_INVESTIGATION","terminal_claim":"RH_OPEN"})
        if with_upload:upload("k3-unrun460-negative-stop",out/"negative-stop.json")
    validate(plan)
    return v

def worker(plan,index,out):
    d=validate(plan);out=Path(out)
    import k3_resume_search as S
    S.write=write
    v=S.run_job(d["jobs"][index]["job"],RESOURCE,digest(plan),out/"result.json")
    validate_result(v,d["jobs"][index]["job"],digest(plan));write(out/"result.json",v)

def assemble(plan,results,out):
    d=validate(plan);ph=digest(plan);raw=Path(plan).parent/"producer";jobs,_=archive_review(raw)
    original=read(raw/"candidate/manifest.json");out=Path(out);out.mkdir(parents=True,exist_ok=False)
    found={}
    for f in Path(results).glob("*/receipt.json"):
        receipt=read(f);i=receipt["index"]
        if type(i)is not int or not 0<=i<460 or i in found:raise ValueError("duplicate/out-of-range continuation receipt")
        if receipt["plan_sha256"]!=ph or receipt["run_id"]!=d["run_id"] or receipt["result_sha256"]!=digest(f.parent/"result.json") or receipt["claim_sha256"]!=digest(f.parent/"budget-claim.json") or receipt["launch_sha256"]!=digest(f.parent/"launch.json"):raise ValueError("forged/mismatched continuation receipt")
        expected_claim={"protocol":PROTOCOL_ID,"run_id":d["run_id"],"index":i,"job":jobs[i],"plan_sha256":ph,"resources":RESOURCE,"budget":"CLAIMED_ONCE_NO_RETRY"}
        if read(f.parent/"budget-claim.json")!=expected_claim:raise ValueError("child budget claim differs from frozen plan")
        launch=read(f.parent/"launch.json")
        if launch.get("plan_sha256")!=ph or launch.get("index")!=i or launch.get("max_seconds")!=1800:raise ValueError("child launch differs from its one approved budget")
        found[i]=validate_result(read(f.parent/"result.json"),jobs[i],ph)
    records=[];missing=[];negative=False
    for spec in original["records"]:
        import k3_replay_shards as R
        old=R.target(raw/"candidate",spec);accepted=copy.deepcopy(old["accepted"]);unresolved=[]
        for i,j in enumerate(jobs):
            if (j["Q"],j["parity"])!=(spec["cell"],spec["parity"]):continue
            v=found.get(i)
            if v is None:missing.append(i);v=pending(j,ph,"MISSING_CONTINUATION_RECEIPT")
            accepted.extend({**t,"continuation_ancestry":{"index":i,"job":j["id"],"plan_sha256":ph}} for t in v["accepted"])
            unresolved.extend({**t,"continuation_ancestry":{"index":i,"job":j["id"],"plan_sha256":ph}} for t in v["unresolved"])
            negative|=v["certified_negative_stop"]
        # Replace only the460 original unrun child intervals; all accepted bytes
        # remain unchanged, and coverage equality is checked on every whole layer.
        accepted.sort(key=lambda t:rational(t["left"]));unresolved.sort(key=lambda t:rational(t["left"]))
        v={"Q":old["Q"],"parity":old["parity"],"left":old["left"],"right":old["right"],"accepted":accepted,"unresolved":unresolved,"status":"PASS" if not unresolved else "UNRESOLVED","candidate_only":True}
        s={"cell":v["Q"],"parity":v["parity"],"file":spec["file"],"status":v["status"],"intervals":len(accepted),"unresolved_count":len(unresolved)}
        validate_layer(s,v,"SECOND");write(out/s["file"],v);s["sha256"]=digest(out/s["file"]);records.append(s)
    summary={"plan_sha256":ph,"received_children":len(found),"missing_children":missing,"negative_investigation_stop":negative,"unresolved":sum(s["unresolved_count"] for s in records),"terminal_claim":"RH_OPEN"}
    write(out/"continuation-summary.json",summary)
    complete=not missing and not negative and not summary["unresolved"]
    m={"schema":"post290.k3-candidate.v1","partition_sha256":ph,"current_source":d["current_source"],"historical_source":read(raw/"partition.json")["historical_source"],"original_producer_source":d["original_source"],"original_partition_sha256":PARTITION_SHA,"original_candidate_manifest_sha256":CANDIDATE_SHA,"original_search_campaign_sha256":SEARCH_SHA,"approved_resource_protocol":PROTOCOL_ID,"method":"SECOND","status":"CANDIDATE_COMPLETE" if complete else "UNRESOLVED","records":records,"search_campaign_sha256":digest(out/"continuation-summary.json"),"terminal_claim":"RH_OPEN","all_L_positivity_certified":False,"not_a_lean_proof":True}
    write(out/"manifest.json",m)
    # New genuine producer identity uses its new approved frozen plan. The original
    # producer archive remains separately pinned, never relabelled as this result.
    review=legacy_review.make(plan);write(out/"source-revalidation.json",review)
    import k3_replay_shards as R
    checker=R.freeze(out,plan,out/"source-revalidation.json");write(out/"checker-partition.json",checker)
    batches=list(range((len(checker["chunks"])+255)//256))
    write(out/"checker-batches.json",{"batches":batches,"chunks":len(checker["chunks"]),"size":256})
    return [] if negative else batches

def main():
    p=argparse.ArgumentParser(description=__doc__);s=p.add_subparsers(dest="command",required=True)
    a=s.add_parser("freeze");a.add_argument("archive",type=Path);a.add_argument("--run-id",type=int,required=True);a.add_argument("--attempt",type=int,required=True);a.add_argument("--runs",type=Path,required=True);a.add_argument("--out",type=Path,required=True)
    for name in ["claim","run","worker"]:
        a=s.add_parser(name);a.add_argument("plan",type=Path);a.add_argument("--index",type=int,required=True);a.add_argument("--out",type=Path,required=True)
    a=s.add_parser("assemble");a.add_argument("plan",type=Path);a.add_argument("results",type=Path);a.add_argument("--out",type=Path,required=True)
    a=s.add_parser("check-batch");a.add_argument("plan",type=Path);a.add_argument("--batch",type=int,required=True)
    a=p.parse_args()
    if a.command=="freeze":freeze(a.archive,a.out,a.run_id,a.attempt,a.runs)
    elif a.command=="claim":claim(a.plan,a.index,a.out)
    elif a.command=="run":run(a.plan,a.index,a.out)
    elif a.command=="worker":worker(a.plan,a.index,a.out)
    elif a.command=="assemble":
        batches=assemble(a.plan,a.results,a.out)
        with open(os.environ["GITHUB_OUTPUT"],"a") as f:f.write("batches="+json.dumps(batches,separators=(",",":"))+"\n")
    elif a.command=="check-batch":
        import k3_replay_shards as R
        d=R.validate_plan(a.plan,a.plan.parent,a.plan.parent/"source-revalidation.json")
        if a.batch<0 or a.batch*256>=len(d["chunks"]):raise ValueError("invalid checker batch")
        ids=[x["id"] for x in d["chunks"][a.batch*256:(a.batch+1)*256]]
        with open(os.environ["GITHUB_OUTPUT"],"a") as f:f.write("matrix="+json.dumps({"id":ids},separators=(",",":"))+"\n")
if __name__=="__main__":main()
