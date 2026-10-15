#!/usr/bin/env python3
"""Validate separately reviewed, signed, exact-head prerequisite job results.

This does not turn a green run into a theorem or a failed D2 run into a
certificate. Every output classification requires external human review.
"""
from __future__ import annotations
import argparse
import base64
import gzip
import hashlib
import json
import os
import subprocess
from pathlib import Path
from harvest_workflows import inventory,harvest,APPROVED_D2_RUN_ID
from output_contract_check import checked_checkout,D2_PRODUCER_TREE
from verify_semantic_review_provenance import api,all_pages

REPO=Path(__file__).resolve().parents[5]
ROLES={"FORMAL_VALIDITY_GATE","REGRESSION_GATE","RESEARCH_PRODUCING_CHECK"}
FROZEN_FIELDS=("run_id","workflow","job_id","name","attempt","latest_attempt",
               "status","conclusion","head","head_tree","evidence_scope",
               "required","url","steps")

def canonical(obj):
    return json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()
def digest(review):
    return hashlib.sha256(canonical({k:review.get(k) for k in
        ("head","review_phase","excluded_administrative_runs","jobs")})).hexdigest()
def job_id(row):
    return row.get("run_id"),row.get("job_id"),row.get("attempt")

def validate_jobs(raw,review):
    if (raw.get("head")!=review.get("head") or
        raw.get("claim_cap")!="RH_OPEN" or review.get("claim_cap")!="RH_OPEN" or
        raw.get("review_phase")!="PRE_RELEASE_PREREQUISITES" or
        review.get("review_phase")!="PRE_RELEASE_PREREQUISITES" or
        raw.get("includes_release_run") is not False or
        review.get("includes_release_run") is not False or
        raw.get("excluded_administrative_runs")!=review.get("excluded_administrative_runs")):
        raise ValueError("prerequisite harvest scope/head mismatch")
    actual,submitted=raw.get("jobs"),review.get("jobs")
    if not isinstance(actual,list) or not actual or not isinstance(submitted,list):
        raise ValueError("missing reviewed job inventory")
    original={job_id(x):x for x in actual}
    proposed={job_id(x):x for x in submitted}
    if len(original)!=len(actual) or len(proposed)!=len(submitted) or set(original)!=set(proposed):
        raise ValueError("job inventory omitted, duplicated or inserted")
    for key,row in proposed.items():
        old=original[key]
        if any(row.get(f)!=old.get(f) for f in FROZEN_FIELDS):
            raise ValueError("immutable GitHub job result changed: "+str(key))
        if (row.get("classification") not in ROLES or
            row.get("output_reviewed") is not True or
            type(row.get("scientific_acceptance")) is not bool or
            not isinstance(row.get("review_reason"),str) or not row["review_reason"].strip() or
            row.get("review_source_url")!=row.get("url") or
            row.get("scientific_disposition") in (
                None,"READ_JOB_OUTPUT_REQUIRED","RUNNING_OR_QUEUED")):
            raise ValueError("job scientific output review missing: "+str(key))
        if row["scientific_acceptance"]:
            if row.get("conclusion")!="success" or row.get("status")!="completed":
                raise ValueError("skipped/failed/unrun result promoted: "+str(key))
            if row.get("required"):
                expected=(D2_PRODUCER_TREE if row.get("evidence_scope")=="APPROVED_EXTERNAL_D2"
                          else row.get("head_tree"))
                if checked_checkout(row,expected) is None:
                    raise ValueError("missing required actual checkout identity: "+str(key))
    return True

def reviewer_receipt(review,pr,reviews,commits):
    head=review.get("head")
    user=str(review.get("reviewer_identity") or "").casefold()
    if (pr.get("number")!=292 or pr.get("head",{}).get("sha")!=head or
        not user or user in ("self","automated","none")):
        raise ValueError("stale PR head or unnamed workflow reviewer")
    authors={str(pr.get("user",{}).get("login","")).casefold()}
    for c in commits:
        for field in ("author","committer"):
            login=(c.get(field) or {}).get("login")
            if login:authors.add(str(login).casefold())
    if user in authors:
        raise ValueError("source author self-reviewed workflow results")
    token="PR292-WORKFLOW-HARVEST-SHA256="+digest(review)
    for r in reviews:
        if (str((r.get("user") or {}).get("login","")).casefold()==user
            and r.get("state")=="APPROVED" and r.get("commit_id")==head
            and r.get("html_url")==review.get("external_review_reference")
            and r.get("submitted_at") and isinstance(r.get("body"),str)
            and token in r["body"]):
            return {"schema":"PR292_WORKFLOW_HARVEST_REVIEW_PROVENANCE_V1",
                "head":head,"reviewer":user,"reviewed_jobs_sha256":digest(review),
                "github_review_id":r["id"],"github_review_url":r["html_url"],
                "integrity_status":"PASS","claim_cap":"RH_OPEN",
                "not_mathematical_authority_by_itself":True}
    raise ValueError("independent GitHub APPROVED review did not sign this harvest")

def live_raw(head):
    return harvest(inventory(head,APPROVED_D2_RUN_ID,
                             "PRE_RELEASE_PREREQUISITES"),
                   "PRE_RELEASE_PREREQUISITES")
def verify(raw,review):
    validate_jobs(raw,review)
    return reviewer_receipt(review,api("/pulls/292"),
        all_pages("/pulls/292/reviews"),all_pages("/pulls/292/commits"))
def checkout_head():
    return subprocess.check_output(["git","rev-parse","HEAD"],cwd=REPO,text=True).strip()
def from_event():
    event=json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    encoded=event.get("inputs",{}).get("reviewed_harvest_gzip_b64","")
    if not isinstance(encoded,str) or not 50<len(encoded)<=60000:
        raise ValueError("signed compressed reviewer harvest absent or exceeds intake limit")
    raw=gzip.decompress(base64.b64decode(encoded,validate=True))
    if len(raw)>12000000:
        raise ValueError("review input exceeds decompressed limit")
    return json.loads(raw.decode("utf-8"))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--raw",type=Path)
    p.add_argument("--review",type=Path)
    p.add_argument("--provenance",type=Path)
    p.add_argument("--out-dir",type=Path)
    args=p.parse_args()
    head=checkout_head()
    if args.out_dir:
        if args.raw is None or args.review or args.provenance:p.error("invalid intake inputs")
        raw=json.loads(args.raw.read_text())
        reviewed=from_event()
        if reviewed.get("head")!=head:raise ValueError("stale reviewer source head")
        receipt=verify(raw,reviewed)
        args.out_dir.mkdir(parents=True,exist_ok=True)
        (args.out_dir/"WORKFLOW_HARVEST.json").write_text(
            json.dumps(reviewed,indent=2,sort_keys=True)+"\n")
        (args.out_dir/"WORKFLOW_HARVEST_PROVENANCE.json").write_text(
            json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    else:
        if not args.review or not args.provenance or args.raw:
            p.error("release verification requires reviewed harvest and provenance")
        review=json.loads(args.review.read_text())
        if review.get("head")!=head:raise ValueError("stale release head")
        receipt=verify(live_raw(head),review)
        if json.loads(args.provenance.read_text())!=receipt:
            raise ValueError("reviewed harvest provenance substitution")
    print(json.dumps({"integrity_status":"PASS","claim_cap":"RH_OPEN",
                      "review_not_new_theorem_authority":True}))
if __name__=="__main__":main()
