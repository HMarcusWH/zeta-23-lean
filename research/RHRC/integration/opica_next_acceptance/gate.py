#!/usr/bin/env python3
"""Source admission successor for current OPICA 11-lane proof checks.

Do not alter the original documentation_2026_11_21 validator. This
selects an independently reviewed newer exact Git tree only when the
versioned successor policy is part of that tree. It grants NO proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from research.RHRC.integration.documentation_2026_11_21 import source_scope as historical
from research.RHRC.integration.opica_round6 import source_scope as round6
from research.RHRC.integration.opica_composition.descendant import validate_workflow_migration

REPO = Path(__file__).resolve().parents[4]
BASE = "4f81c784d3b330395507f6dcd1c8b0010b3835cc"
TREE = "84b235c455980cfd516a8c0ccaf7749bce3c5339"
PIN = "leanprover/lean4:v4.33.0-rc2"
POLICY = "research/RHRC/integration/opica_next_acceptance/SOURCE_POLICY.json"
VALIDATOR = "research/RHRC/integration/opica_next_acceptance/gate.py"
POLICY_BLOB_OID = "2349873d9f6f65b0512eab8d91ebe3ad853f810d"

ADDED = frozenset({
    ".github/workflows/opica-next-acceptance.yml",
    "research/RHRC/integration/opica_next_acceptance/__init__.py",
    POLICY,
    "research/RHRC/integration/opica_next_acceptance/gate.py",
    "research/RHRC/integration/opica_next_acceptance/test_gate.py",
    "research/RHRC/integration/opica_next_acceptance/README.md",
    "research/RHRC/integration/opica_next_acceptance/NEXT_TARGETS.json",
    "research/RHRC/integration/opica_next_acceptance/targets.py",
})
EDITED = frozenset({
    "research/RHRC/integration/opica_composition/cli.py",
    "research/RHRC/graph/FILE_CLASSES.json",
    "research/RHRC/integration/opica_composition/service.py",
    "research/RHRC/integration/opica_composition/qualification.py",
    ".github/workflows/documentation.yml",
    ".github/workflows/rhrc_opica_composition.yml",
    ".github/workflows/rhrc_opica_round3.yml",
    ".github/workflows/rhrc_opica.yml",
    ".github/workflows/rhrc_opica_followup.yml",
    ".github/workflows/rhrc_opica_round2.yml",
    ".github/workflows/rhrc.yml",
    ".github/workflows/rhrc_opica_round6.yml",
})
FROZEN = frozenset(round6.FROZEN_PRODUCTS)

class ScopeError(ValueError):
    """A closed new-source epoch or claim boundary was rejected."""

def need(ok, message):
    if not ok:
        raise ScopeError(message)

def git(repo, *args):
    return subprocess.run(["git","-C",str(repo),*args], check=True,
                          capture_output=True,text=True,timeout=120).stdout.strip()

def expected_generated(repo):
    # The unchanged, frozen original Round4 registry declares 81 products,
    # four of which are historic/untouchable. The other 77 are derived only.
    data=json.loads((repo/"research/RHRC/integration/opica_round4/BUILD_MANIFEST.json").read_text())
    all_paths=[row["path"] for row in data["generated"]]
    need(len(all_paths)==81 and len(set(all_paths))==81 and FROZEN<=set(all_paths),
         "original 81-product generated inventory differs")
    return sorted(set(all_paths)-FROZEN)

def validate_policy(policy, active):
    fields={"schema","parent_source_head","parent_source_tree",
            "parent_accepted_by","toolchain","allowed_added","allowed_edited",
            "allowed_generated","unchanged_frozen_products",
            "original_round4_acceptance","new_11_lane_acceptance",
            "scientific_claims","proof_acceptance","reviewed_blob_oids",
            "validator_template_blob_oid"}
    need(type(policy) is dict and set(policy)==fields,
         "unreviewed successor source policy fields")
    need(policy["schema"]=="OPICA_NEXT_SOURCE_PROOF_ADMISSION_POLICY_V1",
         "unknown proof admission source epoch")
    need(policy["parent_source_head"]==BASE and policy["parent_source_tree"]==TREE,
         "source epoch parent is not exact PR311 baseline")
    need(policy["toolchain"]==PIN, "native compiler pin differs")
    need(policy["allowed_added"]==sorted(ADDED)
         and policy["allowed_edited"]==sorted(EDITED)
         and policy["allowed_generated"]==active
         and policy["unchanged_frozen_products"]==sorted(FROZEN),
         "unreviewed source or generated path policy")
    need(policy["parent_accepted_by"]=="SEPARATE_EXACT_SOURCE_CI_RECEIPT_REQUIRED"
         and policy["original_round4_acceptance"]=="HISTORICAL_SOURCE_ONLY_NOT_REUSED"
         and policy["new_11_lane_acceptance"]=="NOT_EXECUTED_UNTIL_ALL_LANES_PASS",
         "old or unexecuted source authority was promoted")
    need(policy["scientific_claims"]=={"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
         and policy["proof_acceptance"] is False,
         "unapproved scientific claim or proof acceptance")

def git_blob_oid(raw):
    return hashlib.sha1(b"blob "+str(len(raw)).encode("ascii")+b"\0"+raw).hexdigest()

def normalized_validator_oid(raw):
    line=('POLICY_BLOB_OID = "'+POLICY_BLOB_OID+'"\n').encode("ascii")
    need(raw.count(line)==1,"exactly one validator policy pin required")
    return git_blob_oid(raw.replace(line,b'POLICY_BLOB_OID = "<policy-blob-oid>"\n',1))

def verify_sealed_source(repo,current,policy,raw):
    reviewed=policy["reviewed_blob_oids"]
    need(type(reviewed) is dict and set(reviewed)==(ADDED|EDITED)-{POLICY,VALIDATOR},
         "exact reviewed source content inventory required")
    need(all(type(v) is str and re.fullmatch(r"[0-9a-f]{40}",v)
             for v in reviewed.values()),"invalid reviewed source Git blob OID")
    need(git_blob_oid(raw)==POLICY_BLOB_OID and
         current[POLICY][2]==POLICY_BLOB_OID,"reviewed source policy bytes differ")
    need(normalized_validator_oid((repo/VALIDATOR).read_bytes())==
         policy["validator_template_blob_oid"],"reviewed validator template differs")
    for name,oid in reviewed.items():
        need(current.get(name)==("100644","blob",oid),
             "reviewed source blob differs: "+name)

def check(repo=REPO, *, require_clean=False):
    repo=Path(repo).resolve()
    need(git(repo,"rev-parse",BASE+"^{tree}")==TREE,
         "parent source Git tree differs")
    need(subprocess.run(["git","-C",str(repo),"merge-base","--is-ancestor",BASE,"HEAD"],
                        capture_output=True).returncode==0,
         "not an exact descendant of reviewed PR311 source")
    head=git(repo,"rev-parse","HEAD")
    current=round6.tree(repo,head)
    parent=round6.tree(repo,BASE)
    need(head!=BASE, "successor source must have distinct commit")
    need(POLICY in current,"successor policy missing from Git tree")
    raw=(repo/POLICY).read_bytes()
    need(git(repo,"hash-object",POLICY)==current[POLICY][2],
         "checked policy bytes differ from Git")
    policy=json.loads(raw)
    generated=expected_generated(repo)
    validate_policy(policy,generated)
    verify_sealed_source(repo,current,policy,raw)

    new=set(current)-set(parent)
    need(new==ADDED,"unexpected new-source additions: "+repr(sorted(new^ADDED)))
    need(set(parent)<=set(current),"parent source deleted/renamed")
    changed={p for p in parent if parent[p]!=current[p]}
    actual_generated=changed&set(generated)
    need(changed-actual_generated==EDITED,
         "unreviewed changes beyond sealed source edits/77 derived products: "+
         repr(sorted((changed-actual_generated)^EDITED)))
    for p in FROZEN:
        need(parent[p]==current[p],"frozen historical generated product changed: "+p)
    for p in sorted(new|changed):
        need(current[p][:2]==("100644","blob"),
             "nonregular or executable provider not reviewed: "+p)
        if p in parent:
            need(current[p][:2]==parent[p][:2],"source mode changed: "+p)
    need((repo/"lean-toolchain").read_text().strip()==PIN,
         "native toolchain file differs")

    # The original mathematical source, Lean theorem bodies, constants,
    # claims, imports, old source validators and their manifest bytes are
    # immutable relative to reviewed PR311, not just named in a blacklist.
    for p in sorted(set(parent)-EDITED-set(generated)):
        need(parent[p]==current[p],"inherited reviewed source mutated: "+p)

    if require_clean:
        need(not git(repo,"status","--porcelain","--untracked-files=all"),
             "source checkout dirty")
    historical.check_worktree(repo,current)
    # Retain the unchanged inherited source/workflow migration guard rather
    # than treating the new source epoch as a bypass of earlier preflights.
    validate_workflow_migration(repo)
    ignored=subprocess.check_output(["git","-C",str(repo),"ls-files","-z","--others",
                                     "--ignored","--exclude-standard"]).split(b"\x00")
    for raw_name in ignored:
        name=raw_name.decode()
        need(not (name.startswith(("Zeta23/","research/",".github/","docs/examples/"))
                  and name.endswith((".lean",".lean.in",".py",".yml",".yaml"))),
             "ignored executable/source provider: "+name)
    need(head==git(repo,"rev-parse","HEAD"),
         "source head changed while checking")
    return {
        "schema":"OPICA_NEXT_SOURCE_ACCEPTANCE_ADMISSION_V1",
        "status":"PASS_SOURCE_SCOPE_ONLY",
        "checked_commit":head,
        "checked_tree":git(repo,"rev-parse",head+"^{tree}"),
        "base":BASE,"base_tree":TREE,
        "source_epoch":"OPICA_NEXT_SOURCE_EPOCH_V1",
        "path_policy_sha256":hashlib.sha256(raw).hexdigest(),
        "reviewed_source_blob_count":len(policy["reviewed_blob_oids"]),
        "manifest_sha256":hashlib.sha256((repo/"research/RHRC/integration/opica_round4/BUILD_MANIFEST.json").read_bytes()).hexdigest(),
        "delta":{"added":sorted(new),"edited":sorted(EDITED),
                 "generated":sorted(actual_generated),"deleted":[]},
        "canonical_product_count":len(generated),
        "unchanged_historical_product_count":len(FROZEN),
        "current_compiler_accepted":False,
        "full_round4_accepted":False,
        "new_source_11_lane_status":"PENDING_ACTUAL_PRODUCER_AND_INDEPENDENT_REPLAY",
        "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN",
    }

def validate_descendant(repo=REPO, *, require_clean=False):
    """Current-schema selection does not mutate old validator or proof code."""
    repo=Path(repo).resolve()
    if POLICY not in round6.tree(repo,"HEAD"):
        return historical.validate_descendant(repo,require_clean=require_clean)
    return check(repo,require_clean=require_clean)

def check_classification(repo=REPO):
    report=check(repo,require_clean=True)
    d=json.loads((Path(repo)/"research/RHRC/graph/FILE_CLASSES.json").read_text())
    for p in sorted(ADDED):
        hits=[r for r in d["rules"] if re.fullmatch(r["pattern"],p)]
        need(hits and hits[0]["file_class"] not in (d["unknown_class"],"UNKNOWN_FILE_CLASS")
             and hits[0]["trust_zone"] not in (d["unknown_trust_zone"],"UNKNOWN"),
             "unknown new-source classification: "+p)
    return {"status":"PASS_NEW_SOURCE_CLASSIFICATION_ONLY",
            "source_head":report["checked_commit"],
            "proof_acceptance":False,"RH":"OPEN","Step4":"OPEN"}

def main():
    parser=argparse.ArgumentParser()
    action=parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output",type=Path)
    action.add_argument("--check-classification",action="store_true")
    args=parser.parse_args()
    if args.check_classification:
        print(json.dumps(check_classification()))
        return
    need(not args.output.exists(),"refusing to overwrite earlier evidence")
    try:
        result=validate_descendant(require_clean=True)
    except Exception as e:
        result={"schema":"OPICA_NEXT_SOURCE_ADMISSION_FAILURE_V1",
                "status":"SOURCE_POLICY_REJECTED",
                "error_type":type(e).__name__,
                "message":str(e)[:1024],
                "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+"\n")
        raise
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ("status","checked_commit","proof_acceptance","RH")}))
if __name__=="__main__":
    main()
