"""Authenticate exact integrated producer artifacts, canonical application and original 11-lane aggregate."""
from __future__ import annotations
import argparse, hashlib, io, json, os, re, stat, subprocess, tempfile, zipfile
from pathlib import Path
from .admission import REPO, DIR, MANIFEST, CLAIMS, git, check, source_fingerprint, active_products, BASE, tree
from ..opica_composition.canonical import require
from ..opica_composition.accept import ROUND4_LANES, REPLAY_GROUP_IDS
from ..opica_next_acceptance.targets import _verify_round4_receipt
REPO_NAME="HMarcusWH/zeta-23-lean"
CANDIDATE_WORKFLOW=".github/workflows/opica-integrated-epoch.yml"
ROUND4_WORKFLOW=".github/workflows/rhrc_opica_composition.yml"
CANDIDATE_JOBS=("scope","native-candidate","independent-candidate","dual-review","canonical-candidate")

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def api(path):
    r=subprocess.run(["gh","api","repos/"+REPO_NAME+path],capture_output=True,check=True,timeout=120)
    require(len(r.stdout)<=16<<20,"Actions metadata cap")
    return json.loads(r.stdout)

def authenticate_run(run_id,head,workflow,names):
    require(re.fullmatch(r"[1-9][0-9]{0,20}",run_id) is not None,"Invalid run ID")
    r=api("/actions/runs/"+run_id)
    require(str(r["id"])==run_id and r["head_sha"]==head and r["repository"]["full_name"]==r["head_repository"]["full_name"]==REPO_NAME and r["path"].split("@")[0]==workflow and r["event"] in ("push","workflow_dispatch") and r["status"]=="completed" and r["conclusion"]=="success","Required exact successful run not available")
    attempt=r["run_attempt"];require(type(attempt) is int and attempt>0,"Missing attempt")
    p=api("/actions/runs/"+run_id+"/attempts/"+str(attempt)+"/jobs?per_page=100")
    require(p["total_count"]==len(p["jobs"]),"Incomplete job inventory")
    for n in names:
        j=[x for x in p["jobs"] if x["name"]==n]
        require(len(j)==1 and j[0]["status"]=="completed" and j[0]["conclusion"]=="success" and str(j[0]["run_id"])==run_id and j[0].get("run_attempt",attempt)==attempt,"Required job failed or missing: "+n)
    return attempt

def artifact_member(run_id,name,leaf):
    x=api("/actions/runs/"+run_id+"/artifacts?per_page=100")
    require(x["total_count"]==len(x["artifacts"]),"Incomplete artifact inventory")
    found=[a for a in x["artifacts"] if a["name"]==name and not a["expired"]]
    require(len(found)==1,"Missing or ambiguous artifact: "+name)
    a=found[0];expected=a.get("digest","")
    require(a["workflow_run"]["id"]==int(run_id) and re.fullmatch(r"sha256:[0-9a-f]{64}",expected) and 0<a["size_in_bytes"]<=256<<20,"Unbound or oversized artifact")
    with tempfile.TemporaryDirectory(prefix="opica-integrated-artifact-") as td:
        p=Path(td)/"artifact.zip"
        with p.open("xb") as f:
            subprocess.run(["gh","api","repos/"+REPO_NAME+"/actions/artifacts/"+str(a["id"])+"/zip"],stdout=f,stderr=subprocess.PIPE,timeout=300,check=True)
        require(p.stat().st_size<=256<<20 and "sha256:"+hashlib.file_digest(p.open("rb"),"sha256").hexdigest()==expected,"Artifact digest differs")
        with zipfile.ZipFile(p) as z:
            members=z.infolist()
            require(len(members)<=20000 and sum(m.file_size for m in members)<=768<<20,"Artifact population cap")
            hits=[m for m in members if Path(m.filename).name==leaf]
            require(len(hits)==1 and not stat.S_ISLNK(hits[0].external_attr>>16) and hits[0].file_size<=4<<20,"Missing/linked/oversized receipt")
            raw=z.read(hits[0])
    return json.loads(raw),{"artifact_id":a["id"],"archive_sha256":expected[7:],"member":leaf,"member_sha256":sha(raw)}

def verify_canonical(receipt,source_head,source_tree,before,after,changed):
    require(receipt["status"]=="REVIEW_ONLY_GENERATED_STATE" and receipt["source_head"]==source_head and receipt["source_tree"]==source_tree and all(receipt[k]==v for k,v in CLAIMS.items()),"Wrong canonical receipt identity")
    require((receipt["total_count"],receipt["active_count"],receipt["frozen_count"])==(81,77,4),"Generated census differs")
    require(receipt["before_sha256"]==before and receipt["after_write_sha256"]==receipt["after_check_sha256"]==after,"Canonical application bytes differ")
    require(receipt["changed_paths"]==sorted(changed) and receipt["changed_count"]==len(changed),"Canonical path delta differs")

def verify(repo,candidate_head,candidate_run,current_run,round4_run):
    scope=check(repo,require_clean=True)
    head=scope["checked_commit"];curtree=scope["checked_tree"]
    require(re.fullmatch(r"[0-9a-f]{40}",candidate_head) is not None and git(repo,"merge-base",candidate_head,head)==candidate_head,"Invalid canonical candidate ancestry")
    current=tree(repo,head);previous=tree(repo,candidate_head)
    active=active_products(repo,tree(repo,BASE),current)
    require(set(current)==set(previous) and source_fingerprint(previous,active)==scope["source_fingerprint"],"Source changed between reviewed generation and application")
    items=[x["path"] for x in json.loads((repo/MANIFEST).read_text())["generated"]]
    before={p:sha(subprocess.check_output(["git","-C",str(repo),"show",candidate_head+":"+p])) for p in items}
    after={p:sha((repo/p).read_bytes()) for p in items}
    changed={p for p in items if before[p]!=after[p]}
    require(changed<=active,"Frozen generated products changed")
    oldtree=git(repo,"rev-parse",candidate_head+"^{tree}")
    attempt=authenticate_run(candidate_run,candidate_head,CANDIDATE_WORKFLOW,CANDIDATE_JOBS)
    canonical,ca=artifact_member(candidate_run,f"integrated-canonical-review-{candidate_run}-{attempt}","receipt.json")
    verify_canonical(canonical,candidate_head,oldtree,before,after,changed)
    # Fresh independent qualification on the exact applied head, not a copied
    # predecessor proof or a statement inferred from a matching source hash.
    current_attempt=authenticate_run(current_run,head,CANDIDATE_WORKFLOW,CANDIDATE_JOBS)
    dual,da=artifact_member(current_run,f"integrated-dual-review-{current_run}-{current_attempt}","integrated-dual-review.json")
    roots=json.loads((repo/(DIR+"LOCK.json")).read_text())["roots"]
    require(dual["schema"]=="OPICA_INTEGRATED_DUAL_REVIEW_V1" and dual["status"]=="DUAL_NATIVE_CANDIDATE_PASS_ONLY" and dual["head"]==head and dual["tree"]==curtree and dual["roots"]==roots and all(dual[k]==v for k,v in CLAIMS.items()),"Fresh combined candidate receipt differs")
    names=tuple("Round4 / "+l for l in ROUND4_LANES)+tuple("Round4 / INDEPENDENT_"+g for g in REPLAY_GROUP_IDS)+("Round4 / ACCEPTANCE",)
    ra=authenticate_run(round4_run,head,ROUND4_WORKFLOW,names)
    aggregate,aa=artifact_member(round4_run,f"opica4-release-receipt-{round4_run}-{ra}","acceptance.json")
    profile=sha((repo/"research/RHRC/integration/opica_composition/PROFILE.json").read_bytes())
    _verify_round4_receipt(aggregate,head=head,tree=curtree,run_id=round4_run,attempt=ra,profile=profile)
    require(check(repo,require_clean=True)==scope,"Source changed during release evidence review")
    return {"schema":"OPICA_INTEGRATED_RELEASE_REVIEW_V1","status":"PASS_INTEGRATED_SUPPORT_SCOPE_REVIEW_ONLY","head":head,"tree":curtree,"source_fingerprint":scope["source_fingerprint"],"candidate_head":candidate_head,"canonical":ca,"fresh_combined":da,"round4":aa,"runs":{"canonical":candidate_run,"current":current_run,"round4":round4_run},"canonical_application_count":len(changed),"historical_expected_type_admission":"SEPARATE_REVIEW_REQUIRED","human_review":"PENDING","new_theorem_promotion":False,**CLAIMS}

def main():
    p=argparse.ArgumentParser()
    for k in ("candidate-head","candidate-run","current-run","round4-run","reviewed-head"):p.add_argument("--"+k,required=True)
    p.add_argument("--output",required=True,type=Path)
    a=p.parse_args()
    require(git(REPO,"rev-parse","HEAD")==a.reviewed_head,"Wrong selected head")
    out=a.output.resolve();require(not out.exists() and not out.is_relative_to(REPO),"Fresh external review receipt required")
    out.parent.mkdir(parents=True,exist_ok=True)
    try:
        doc=verify(REPO,a.candidate_head,a.candidate_run,a.current_run,a.round4_run)
    except Exception as exc:
        out.write_text(json.dumps({"status":"INCOMPLETE_OR_REJECTED","reason":str(exc)[:2000],**CLAIMS},indent=2)+"\n")
        raise
    out.write_text(json.dumps(doc,indent=2)+"\n")
    print(doc["status"])

if __name__=="__main__":
    main()
