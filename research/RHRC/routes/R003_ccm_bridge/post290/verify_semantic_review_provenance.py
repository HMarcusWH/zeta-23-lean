#!/usr/bin/env python3
"""Verify independent PR292 field-review provenance against GitHub approval.

The GitHub approval MUST cover the full review JSON digest and final head.
This is reviewer/authorship provenance, NOT an automated mathematical proof.
"""
from __future__ import annotations
import argparse
import hashlib
from datetime import datetime, timezone
import json
import os
import subprocess
import urllib.request
from pathlib import Path

REPOSITORY="HMarcusWH/zeta-23-lean"
PR_NUMBER=292
REPO=Path(__file__).resolve().parents[5]
REQUIRED={f"N{i:02d}" for i in range(1,41)} | {f"G{i:02d}" for i in range(1,5)}
AUTHORIZED_REVIEW_ASSOCIATIONS=frozenset({"OWNER","MEMBER","COLLABORATOR"})
SEMANTIC_REVIEW_TOKEN_PREFIX="PR292-SEMANTIC-REVIEW-SHA256="

def field_digest(rows):
    raw=json.dumps(rows,sort_keys=True,separators=(",",":"),ensure_ascii=False)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()

def semantic_review_digest(review):
    """Sign all supplied review decisions except the eventual review URL.

    Canonical JSON uses sorted keys, compact separators and literal UTF-8.
    Excluding only external_review_reference avoids a URL/signature cycle;
    that URL is separately checked against the authenticated selected review.
    Unknown future fields remain signed rather than silently becoming inputs.
    The legacy field_digest is a component hash, never sufficient approval.
    """
    if not isinstance(review,dict):
        raise ValueError("semantic review must be a JSON object")
    payload={key:value for key,value in review.items() if key!="external_review_reference"}
    raw=json.dumps(payload,sort_keys=True,separators=(",",":"),ensure_ascii=False)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()

def source_author_logins(pr, commits):
    """Fail closed unless every source author AND committer is attributable.

    A linked Bot may be a source participant; reviewer eligibility is checked
    separately. Null GitHub accounts cannot establish reviewer independence.
    """
    def login(account, role):
        value=account.get("login") if isinstance(account,dict) else None
        if not isinstance(value,str) or not value.strip() or value!=value.strip():
            raise ValueError("unattributed GitHub source identity: "+role)
        return value.casefold()
    authors={login(pr.get("user"),"PR author")}
    if not isinstance(commits,list) or not commits:
        raise ValueError("source commit authorship inventory missing")
    # GitHub caps the pull-request commits endpoint at 250 even with paging.
    # A truncated list cannot establish that every source author is excluded.
    count=pr.get("commits")
    if type(count) is not int or count<=0 or count!=len(commits):
        raise ValueError("source commit authorship inventory incomplete or count mismatched")
    for commit in commits:
        if not isinstance(commit,dict):
            raise ValueError("malformed source commit authorship")
        for role in ("author","committer"):
            authors.add(login(commit.get(role),"commit "+role))
    return authors

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


def latest_submitted_review(github_reviews, reviewer_identity):
    """Current submitted decision for one reviewer, never an earlier signed approval.

    Conservative PR292 policy: even a later COMMENTED submission displaces an
    older APPROVED one. PENDING/unsubmitted drafts do not. A single latest
    approval may carry both the field digest and the workflow-harvest digest.
    """
    if not isinstance(github_reviews, list):
        raise ValueError("GitHub review inventory must be a list")
    user = str(reviewer_identity).casefold()
    eligible = []
    seen_ids = set()
    for row in github_reviews:
        if not isinstance(row, dict):
            raise ValueError("malformed GitHub review row")
        login = str((row.get("user") or {}).get("login") or "").casefold()
        if login != user:
            continue
        submitted = row.get("submitted_at")
        if not submitted:
            if row.get("state") == "PENDING":
                continue
            raise ValueError("submitted reviewer decision has no timestamp")
        if not isinstance(submitted, str):
            raise ValueError("invalid GitHub review timestamp")
        try:
            moment = datetime.fromisoformat(submitted.replace("Z", "+00:00"))
        except ValueError as exc:
            raise ValueError("invalid GitHub review timestamp") from exc
        if moment.tzinfo is None:
            raise ValueError("timezone missing from GitHub review timestamp")
        rid = row.get("id")
        if type(rid) is not int or rid <= 0 or rid in seen_ids:
            raise ValueError("duplicate or invalid GitHub review ID")
        seen_ids.add(rid)
        eligible.append((moment.astimezone(timezone.utc), rid, row))
    if not eligible:
        raise ValueError("no independent GitHub APPROVED review: reviewer has no submitted GitHub decision")
    return max(eligible, key=lambda value: (value[0], value[1]))[2]


def require_repository_authorized_reviewer(row):
    """Require repository authorization on the authenticated selected review.

    This is a repository-association policy, not a mathematical expertise check.
    Apply it AFTER selecting the latest decision; an unauthorized new decision
    must never reveal an older approval as a fallback.
    """
    user = row.get("user")
    if not isinstance(user, dict) or user.get("type") != "User":
        raise ValueError("latest reviewer account is not an authenticated GitHub User")
    association = row.get("author_association")
    if (not isinstance(association, str) or
        association not in AUTHORIZED_REVIEW_ASSOCIATIONS):
        raise ValueError("latest reviewer is not repository-authorized: OWNER/MEMBER/COLLABORATOR required")
    return {"reviewer_author_association": association, "reviewer_account_type": user["type"]}


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
    authors=source_author_logins(pr,commits)
    if user in authors:
        raise ValueError("reviewer participated as source author or PR author")
    digest=field_digest(fields)
    review_digest=semantic_review_digest(review)
    signed=SEMANTIC_REVIEW_TOKEN_PREFIX+review_digest
    row = latest_submitted_review(github_reviews, user)
    authorization = require_repository_authorized_reviewer(row)
    reviewer = (row.get("user") or {}).get("login")
    review_url = row.get("html_url")
    if (row.get("state") != "APPROVED" or row.get("commit_id") != head or
        not isinstance(row.get("body"), str) or signed not in row["body"] or
        review.get("external_review_reference") != review_url):
        raise ValueError("latest independent GitHub review is not a signed current-head APPROVED decision")
    return {
        "schema":"PR292_GITHUB_INDEPENDENT_REVIEW_PROVENANCE_V1",
        "integrity_status":"PASS","reviewer":reviewer,
        **authorization,
        "github_review_id":row["id"],"github_review_url":review_url,
        "reviewed_head":head,"reviewed_tree":tree,
        "reviewed_field_count":44,"field_reviews_sha256":digest,
        "semantic_review_sha256":review_digest,
        "source_commit_authorship_verified":True,"source_commit_count":len(commits),
        "not_mathematical_authority_by_itself":True,
        "claim_cap":"RH_OPEN",
    }

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
