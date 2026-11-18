"""Externally authorized merge-readiness gate for POST299 support PRs.

This gate NEVER proves Step4/RH. It is only callable on a specified exact
reviewed PR head after an independent GitHub APPROVED review with the reviewed
source-policy blob SHA, complete current-head CI and current-run composite.
No candidate source/policy may authorize its own release review.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
from urllib.request import Request,urlopen

from ..accept import ROUND4_LANES, REPLAY_GROUP_IDS, group_lanes

API="https://api.github.com/repos/HMarcusWH/zeta-23-lean"
SCHEMA="OPICA5_POST299_COMPOSITE_EVIDENCE_CANDIDATE_V1"
POLICY="research/RHRC/integration/opica_composition/post299/descendant.py"
REQUIRED=frozenset((
 "OPICA Round4 governed deduction and independent source gates",
 "OPICA Round3 scoped current-source proof and falsification gates",
 "OPICA Round2 exact-source core and research controls",
 "OPICA follow-up original-contract validation",
 "RHRC research and Lean checks",
 "Post299 parity bridge candidate compiler (not release)",
 # The current workflow is excluded from the external workflow inventory;
 # its complete mandatory internal jobs are checked by needs and composite receipt.
))
HEX40=re.compile(r"[0-9a-f]{40}\Z")
HEX64=re.compile(r"[0-9a-f]{64}\Z")
ROUND4_WORKFLOW=".github/workflows/rhrc_opica_composition.yml"
ROUND4_JOBS=frozenset("Round4 / "+name for name in (*ROUND4_LANES, *("INDEPENDENT_"+g for g in REPLAY_GROUP_IDS), "ACCEPTANCE"))
HISTORY_JOB="Round4 / POST299_HISTORICAL_15_OF_15_REGRESSION_NOT_REPLAY"

def require(ok,message):
    if not ok:raise RuntimeError(message)

def load(path):
    token=os.environ.get("GITHUB_TOKEN")
    require(bool(token),"Missing GitHub review/audit token")
    req=Request(API+path,headers={
       "Accept":"application/vnd.github+json",
       "Authorization":"Bearer "+token,"X-GitHub-Api-Version":"2022-11-28"})
    with urlopen(req,timeout=25) as response:return json.load(response)

def git(root,*args):
    return subprocess.check_output(["git","-C",str(root),*args],text=True).strip()

def head_runs(head):
    runs=[]
    for page in range(1,6):
        v=load("/actions/runs?head_sha="+head+"&per_page=100&page="+str(page))
        batch=v.get("workflow_runs",[])
        runs.extend(batch)
        if len(batch)<100:break
    require(len(runs)<500,"Ambiguous historical workflow inventory exceeds cap")
    return [x for x in runs if x.get("head_sha")==head and x.get("event")=="pull_request"]


def full_workflow_check(number, head, composite_run):
    items=head_runs(head)
    audited=[x for x in items if x.get("id")!=composite_run]
    by_name={}
    for x in audited:
        k=x.get("name")
        stamp=(x.get("run_started_at") or x.get("created_at") or "",x.get("run_attempt") or 0)
        if k not in by_name or stamp > by_name[k][0]:
            by_name[k]=(stamp,x)
    required=REQUIRED
    if number == 301:
        required=required | {"Post300 K5 mixed-source research (candidate only)"}
    require(required<=set(by_name),"Mandatory head-bound workflows missing: "+str(sorted(required-set(by_name))))
    require(len(by_name)>=20,"Insufficient complete exact-head workflow coverage")
    failures={name:{"id":v["id"],"status":v["status"],"result":v["conclusion"]}
              for name,(_,v) in by_name.items()
              if v.get("status")!="completed" or v.get("conclusion")!="success"}
    require(not failures,"Unresolved/failing/queued exact-head workflows: "+str(failures))
    # Ensure the composite is one of the successful identical-head workflow runs.
    require(any(x["id"]==composite_run for x in items),"Composite run not in head-bound PR checks")
    return {"checked_workflow_names":sorted(by_name),"count":len(by_name)}


def current_round4_run(head):
    runs=[r for r in head_runs(head) if r.get("path") == ROUND4_WORKFLOW]
    require(bool(runs), "No current-head Round4 run")
    run=max(runs, key=lambda r: (r.get("created_at") or "", r["id"]))
    require(run.get("status") == "completed" and run.get("conclusion") == "success",
            "Current-head Round4 workflow has not passed")
    run_id, attempt=run["id"], run.get("run_attempt")
    require(type(run_id) is int and run_id > 0 and type(attempt) is int and attempt > 0,
            "Invalid Round4 run/attempt")
    response=load(f"/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100")
    rows=response.get("jobs", [])
    require(len(rows) == response.get("total_count") and len(rows) in (15, 16),
            "Round4 exact attempt job inventory is incomplete")
    names=[job.get("name") for job in rows]
    require(len(names) == len(set(names)) and set(names)-{HISTORY_JOB} == ROUND4_JOBS,
            "Round4 requires eleven producers, three independent groups, and acceptance")
    require(all(job.get("status") == "completed" and job.get("conclusion") == "success"
                and job.get("head_sha") == head and job.get("run_id") == run_id
                and job.get("run_attempt") == attempt
                for job in rows if job["name"] in ROUND4_JOBS),
            "A current-head Round4 producer, independent group, or acceptance job did not pass")
    return {"run_id":run_id, "attempt":attempt,
            "artifact_name":f"opica4-release-receipt-{run_id}-{attempt}"}


def check_round4_receipt(receipt, head, tree, evidence):
    require(receipt.get("schema") == "OPICA4_INTEGRATED_ACCEPTANCE_V1"
            and receipt.get("status") == "PASS_DECLARED_INTEGRATED_SCOPE"
            and receipt.get("RH") == receipt.get("Step4") == "OPEN",
            "Missing current integrated Round4 acceptance")
    experiment=receipt.get("experiment") or {}
    require(experiment.get("requested_commit") == head
            and experiment.get("requested_tree") == tree
            and experiment.get("run_id") == str(evidence["run_id"])
            and experiment.get("attempt") == evidence["attempt"],
            "Round4 receipt differs from successful current head, tree, run, or attempt")
    lanes=receipt.get("independently_reconstructed_lanes") or []
    require([r.get("id") for r in lanes] == list(ROUND4_LANES)
            and all(HEX64.fullmatch(r.get("evidence_digest") or "") for r in lanes),
            "Incomplete current Round4 lane evidence")
    groups=receipt.get("independent_groups") or []
    require([g.get("group_id") for g in groups] == list(REPLAY_GROUP_IDS)
            and all(g.get("conclusion") == "success"
                    and g.get("lanes") == list(group_lanes(g["group_id"]))
                    and HEX64.fullmatch(g.get("evidence_digest") or "") for g in groups),
            "Incomplete current Round4 independent group evidence")
    return evidence

def approval_check(number,head,policy_sha,author):
    reviews=[]
    for page in range(1,5):
        batch=load(f"/pulls/{number}/reviews?per_page=100&page={page}")
        reviews.extend(batch)
        if len(batch)<100:break
    require(len(reviews)<400,"Too many reviews; fail closed")
    latest={}
    for item in reviews:
        u=item.get("user") or {}
        login=u.get("login")
        if login and (login not in latest or item.get("id",0)>latest[login].get("id",0)):
            latest[login]=item
    eligible=[]
    for login,item in latest.items():
        if (login.lower()!=author.lower() and item.get("state")=="APPROVED"
            and item.get("commit_id")==head
            and item.get("author_association") in ("OWNER","MEMBER","COLLABORATOR")
            and "source_policy_git_blob_sha="+policy_sha in (item.get("body") or "")
            and "OPICA5_POST299_COMPOSITE_EVIDENCE_CANDIDATE_V1" in (item.get("body") or "")):
            eligible.append({"reviewer":login,"review_id":item["id"],
                             "review_commit":item["commit_id"],
                             "reviewed_policy_blob":policy_sha})
    require(bool(eligible),"Missing independent current-head APPROVED GitHub review binding exact source-policy blob and composite schema")
    return eligible

def release(root,number,head,tree,policy_sha,composite_run,attempt,candidate,round4_receipt):
    require(number in (300,301),"Only intended post299 source successors are eligible")
    require(type(head) is str and HEX40.fullmatch(head) and type(tree) is str and HEX40.fullmatch(tree),
            "Noncanonical reviewed Git identity")
    require(type(policy_sha) is str and HEX40.fullmatch(policy_sha),"Missing reviewed source-policy Git blob")
    require(git(root,"rev-parse","HEAD")==head and
            git(root,"rev-parse","HEAD^{tree}")==tree and
            git(root,"hash-object","--",POLICY)==policy_sha,
            "Checked source/head/tree does not equal independently reviewed source")
    require(not git(root,"status","--porcelain","--untracked-files=all"),
            "Release checkout not clean")
    pr=load(f"/pulls/{number}")
    require(pr.get("state")=="open" and pr.get("head",{}).get("sha")==head
            and pr.get("base",{}).get("ref")=="main",
            "PR changed, closed, or does not target main")
    author=pr.get("user",{}).get("login","")
    require(bool(author),"No trustworthy PR author")
    run=load("/actions/runs/"+str(composite_run))
    # After independent approval, rerun only the failed final review job:
    # Actions increments its run attempt, but the original already-green
    # mathematical composite retains its exact original attempt and identity.
    require(run.get("head_sha")==head and type(run.get("run_attempt")) is int
            and run["run_attempt"]>=attempt
            and run.get("status") in ("in_progress","completed")
            and run.get("conclusion") in (None,"success")
            and run.get("event")=="pull_request","Incorrect completed candidate workflow identity")
    require(candidate.get("schema")==SCHEMA
            and candidate.get("status")=="PASS_COMPOSITE_EVIDENCE_PENDING_INDEPENDENT_REVIEW"
            and candidate.get("current_head")==head and candidate.get("current_tree")==tree
            and candidate.get("workflow_run_id")==str(composite_run)
            and candidate.get("workflow_attempt")==attempt
            and candidate.get("merge_ready") is False
            and candidate.get("RH")=="OPEN" and candidate.get("Step4")=="OPEN",
            "Unqualified or cross-run composite evidence")
    checks=full_workflow_check(number,head,composite_run)
    checks["current_round4"]=check_round4_receipt(round4_receipt,head,tree,current_round4_run(head))
    reviews=approval_check(number,head,policy_sha,author)
    return {"schema":"OPICA5_REVIEWED_SUPPORT_PR_MERGE_READINESS_V1",
       "status":"PASS_REVIEWED_SUPPORTING_PR_MERGE_GATE",
       "checked_pr":number,"checked_head":head,"checked_tree":tree,
       "reviewed_source_policy_git_blob":policy_sha,
       "composite_run_id":composite_run,"composite_attempt":attempt,
       "independent_approvals":reviews,"workflow_audit":checks,
       "merge_ready_for_supporting_PR":True,
       "RH":"OPEN","Step4":"OPEN",
       "disclaimer":"No theorem, source inequality, or RH is proved by this procedural approval"}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--repo",required=True,type=Path)
    p.add_argument("--pr",required=True,type=int)
    p.add_argument("--head",required=True)
    p.add_argument("--tree",required=True)
    p.add_argument("--policy-git-blob",required=True)
    p.add_argument("--composite-run",required=True,type=int)
    p.add_argument("--composite-attempt",required=True,type=int)
    p.add_argument("--composite",required=True,type=Path)
    p.add_argument("--round4-acceptance",required=True,type=Path)
    p.add_argument("--output",required=True,type=Path)
    a=p.parse_args()
    require(not a.output.exists(),"Release receipt output already exists")
    result=release(a.repo.resolve(strict=True),a.pr,a.head,a.tree,
                   a.policy_git_blob,a.composite_run,a.composite_attempt,
                   json.loads(a.composite.read_bytes()),json.loads(a.round4_acceptance.read_bytes()))
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":result["status"],"head":result["checked_head"],
                      "pr":a.pr,"reviewers":len(result["independent_approvals"]),
                      "RH":"OPEN","Step4":"OPEN"}))

if __name__=="__main__":main()
