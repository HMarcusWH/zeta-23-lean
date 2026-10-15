#!/usr/bin/env python3
"""Verify independent PR292 field-review provenance against GitHub approval.

The GitHub approval MUST cover the exact 44-field JSON digest and final head.
This is reviewer/authorship provenance, NOT an automated mathematical proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import subprocess
import urllib.request
from pathlib import Path

REPOSITORY="HMarcusWH/zeta-23-lean"
PR_NUMBER=292
REPO=Path(__file__).resolve().parents[5]
REQUIRED={f"N{i:02d}" for i in range(1,41)} | {f"G{i:02d}" for i in range(1,5)}

def field_digest(rows):
    raw=json.dumps(rows,sort_keys=True,separators=(",",":"),ensure_ascii=False)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()

def api(suffix):
    if not os.environ.get("GH_TOKEN"):
        raise ValueError("missing authenticated GitHub review token")
    req=urllib.request.Request(
        f"https://api.github.com/repos/{REPOSITORY}{suffix}",
        headers={"Accept":"application/vnd.github+json",
                 "Authorization":"Bearer "+os.environ["GH_TOKEN"],
                 "User-Agent":"PR292-independent-field-review"})
    with urllib.request.urlopen(req,timeout=50) as response:
        return json.load(response)

def all_pages(path):
    result=[]
    for page in range(1,100):
        batch=api(f"{path}{'&' if '?' in path else '?'}per_page=100&page={page}")
        if not isinstance(batch,list):
            raise ValueError("unexpected GitHub pagination shape")
        result.extend(batch)
        if len(batch)<100:
            return result
    raise ValueError("reviewer provenance pagination unexpectedly long")

def validate(review,pr,github_reviews,commits,head,tree):
    if (review.get("reviewed_head")!=head or review.get("reviewed_tree")!=tree or
        review.get("schema_version")!="POST290_INDEPENDENT_SEMANTIC_REVIEW_1.0" or
        review.get("claim_cap")!="RH_OPEN" or
        review.get("reviewer_is_source_author") is not False or
        review.get("independent_assumption_review_pass") is not True):
        raise ValueError("independent review not bound to exact proof head/tree")
    fields=review.get("field_reviews")
    if (not isinstance(fields,list) or len(fields)!=44 or
        {f.get("id") for f in fields}!=REQUIRED or
        any(f.get("semantic_proof_review")!="PASS" or
            f.get("evidence_verified") is not True or
            not isinstance(f.get("reason"),str) or not f["reason"] or
            not isinstance(f.get("declaration_ref"),str) or not f["declaration_ref"]
            for f in fields)):
        raise ValueError("incomplete or malformed 44-field independent review")
    user=str(review.get("reviewer_identity","")).casefold()
    if not user or user in ("none","self","automated"):
        raise ValueError("unidentified independent reviewer")
    if pr.get("number")!=PR_NUMBER or pr.get("head",{}).get("sha")!=head:
        raise ValueError("PR head changed before review verification")
    authors={str(pr.get("user",{}).get("login","")).casefold()}
    for commit in commits:
        for field in ("author","committer"):
            login=(commit.get(field) or {}).get("login")
            if login:
                authors.add(str(login).casefold())
    if user in authors:
        raise ValueError("reviewer participated as source author or PR author")
    digest=field_digest(fields)
    signed=f"PR292-44-FIELD-SHA256={digest}"
    for row in github_reviews:
        reviewer=(row.get("user") or {}).get("login")
        review_url=row.get("html_url")
        if (str(reviewer).casefold()!=user or row.get("state")!="APPROVED" or
            row.get("commit_id")!=head or
            not isinstance(row.get("body"),str) or
            signed not in row["body"] or
            review.get("external_review_reference")!=review_url):
            continue
        if not row.get("submitted_at"):
            continue
        return {
            "schema":"PR292_GITHUB_INDEPENDENT_REVIEW_PROVENANCE_V1",
            "integrity_status":"PASS","reviewer":reviewer,
            "github_review_id":row["id"],"github_review_url":review_url,
            "reviewed_head":head,"reviewed_tree":tree,
            "reviewed_field_count":44,"field_reviews_sha256":digest,
            "not_mathematical_authority_by_itself":True,
            "claim_cap":"RH_OPEN",
        }
    raise ValueError("no independent GitHub APPROVED review signs exact 44-field digest")

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--review",required=True,type=Path)
    parser.add_argument("--out",required=True,type=Path)
    args=parser.parse_args()
    head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=REPO,text=True).strip()
    tree=subprocess.check_output(["git","rev-parse","HEAD^{tree}"],cwd=REPO,text=True).strip()
    data=json.loads(args.review.read_text(encoding="utf-8"))
    receipt=validate(data,api(f"/pulls/{PR_NUMBER}"),
                     all_pages(f"/pulls/{PR_NUMBER}/reviews"),
                     all_pages(f"/pulls/{PR_NUMBER}/commits"),head,tree)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"integrity_status":"PASS","reviewed_fields":44,"claim_cap":"RH_OPEN"}))

if __name__=="__main__":
    main()
