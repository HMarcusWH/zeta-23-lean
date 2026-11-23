#!/usr/bin/env python3
"""Fail-closed combined OPICA source epoch; NO proof or old-gate promotion.

This successor is deliberately separate from the frozen Round2/3/4 and
documentation_2026_11_21 policies. An old validator rejecting this source is
correct: only this reviewed new-source transaction can admit the extension.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
POLICY = "research/RHRC/integration/opica_next_epoch/SOURCE_EPOCH.json"
BASE = "bb7c8184a135b2823c6296917c5ac893bebf2a71"
BASE_TREE = "2b19357e1b65cc500f3e3a5b5d4df14601b02062"
LEAN_PIN = "leanprover/lean4:v4.33.0-rc2"

ORIGINAL_PATHS = (
    ".github/workflows/opica-next-arithmetic.yml",
    ".github/workflows/opica-prime-deficit.yml",
    "Zeta23/OPICARound6/NextSearch/SourceEnergies.lean",
    "Zeta23/OPICARound6/NextSearch/Verify.lean",
    "Zeta23/OPICARound6/PrimeDeficit/Source.lean",
    "Zeta23/OPICARound6/PrimeDeficit/Verify.lean",
    "research/RHRC/integration/opica_round6/next_search/FALSIFIERS.json",
    "research/RHRC/integration/opica_round6/next_search/README.md",
    "research/RHRC/integration/opica_round6/next_search/SOURCE_CONTRACTS.json",
    "research/RHRC/integration/opica_round6/next_search/TARGETS.json",
    "research/RHRC/integration/opica_round6/next_search/campaign.py",
    "research/RHRC/integration/opica_round6/next_search/source_scope.py",
    "research/RHRC/integration/opica_round6/next_search/test_source_scope.py",
    "research/RHRC/integration/opica_round6/next_search/typed_export.py",
    "research/RHRC/integration/opica_round6/prime_deficit/README.md",
    "research/RHRC/integration/opica_round6/prime_deficit/SOURCE_CONTRACT.json",
    "research/RHRC/integration/opica_round6/prime_deficit/scope.py",
    "research/RHRC/integration/opica_round6/prime_deficit/test_scope.py",
)
EPOCH_ADDITIONS = (
    ".github/workflows/opica-next-source-epoch.yml",
    POLICY,
    "research/RHRC/integration/opica_next_epoch/scope.py",
    "research/RHRC/integration/opica_next_epoch/test_scope.py",
    "research/RHRC/integration/opica_next_epoch/README.md",
)
REVIEWED_ADDITIONS = frozenset(ORIGINAL_PATHS + EPOCH_ADDITIONS)
REVIEWED_EDITS = frozenset({
    "research/RHRC/graph/FILE_CLASSES.json",
    "research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json",
})
INTEGRATION_OVERRIDES = frozenset({
    "research/RHRC/integration/opica_round6/next_search/campaign.py",
    "research/RHRC/integration/opica_round6/next_search/source_scope.py",
    "research/RHRC/integration/opica_round6/next_search/test_source_scope.py",
    "research/RHRC/integration/opica_round6/prime_deficit/scope.py",
    "research/RHRC/integration/opica_round6/prime_deficit/test_scope.py",
})
ORIGINAL_SOURCE_HEADS = {
    "PR307": "e2f8492e46cf8c3b3a220e2945838ddd20155a9c",
    "PR308": "d78224185055b85effb8b70a11731e23b21b19bb",
}
ORIGINAL_BLOBS = {
    ".github/workflows/opica-next-arithmetic.yml": "b4524f8a69b07315f865ed9302b2f09e62ed6124",
    ".github/workflows/opica-prime-deficit.yml": "c2e1ea2fdbd096062435ec5803079073e2cabb95",
    "research/RHRC/integration/opica_round6/next_search/campaign.py": "64f39c3b5134e1b80d016f87b434fde12d1c7b5c",
    "research/RHRC/integration/opica_round6/next_search/FALSIFIERS.json": "564f0e6eec557fe4de772eb67e18b1158730b894",
    "research/RHRC/integration/opica_round6/next_search/README.md": "fd79e7ff115888a553e596237f317464b2094932",
    "research/RHRC/integration/opica_round6/next_search/SOURCE_CONTRACTS.json": "90459baf84d287cd9933696f9c1153c0aee22f8e",
    "research/RHRC/integration/opica_round6/next_search/source_scope.py": "de1f01761ba0df4b2a0f6f7003bd4f6a60c606ae",
    "research/RHRC/integration/opica_round6/next_search/TARGETS.json": "3db4447712187dd3d7ad28103eecabbf53721c36",
    "research/RHRC/integration/opica_round6/next_search/test_source_scope.py": "c44fcb8e8e042d928bff1d8faba5f616c9d61575",
    "research/RHRC/integration/opica_round6/next_search/typed_export.py": "c6d4eac784ed53a91dfcaa4d239e4fe22935c631",
    "research/RHRC/integration/opica_round6/prime_deficit/README.md": "06d36b100f19c006cddd3baacbcc049e24e8b15c",
    "research/RHRC/integration/opica_round6/prime_deficit/scope.py": "0651e828c1fb029d2f1c34915dab9ed4f8595bf7",
    "research/RHRC/integration/opica_round6/prime_deficit/SOURCE_CONTRACT.json": "0e6aea600c9f4fe49bd67b96f3187392b8697a0c",
    "research/RHRC/integration/opica_round6/prime_deficit/test_scope.py": "dfede1cd1c1238b01ab3a3bed6fb6ca5f2f24b17",
    "Zeta23/OPICARound6/NextSearch/SourceEnergies.lean": "f5024bf53e1472d9229369ad2821993a7ef1ab8a",
    "Zeta23/OPICARound6/NextSearch/Verify.lean": "a185918eba7ef9274013d2f7423f277e0ec2d00f",
    "Zeta23/OPICARound6/PrimeDeficit/Source.lean": "9b231cba5c67ad6b4e1a59e4c39a4ecf6191f5fa",
    "Zeta23/OPICARound6/PrimeDeficit/Verify.lean": "46fe5ccea089883c2ded6c80d24851ffca6f69b9"
}

EXPECTED_ROLES = {
    "Zeta23.OPICARound6.NextSearch.SourceEnergies": "OPICA6_SIGNED_SOURCE_CONDITIONAL",
    "Zeta23.OPICARound6.NextSearch.Verify": "OPICA6_SIGNED_SOURCE_AUDIT",
    "Zeta23.OPICARound6.PrimeDeficit.Source": "OPICA6_PRIME_DEFICIT_SOURCE",
    "Zeta23.OPICARound6.PrimeDeficit.Verify": "OPICA6_PRIME_DEFICIT_AUDIT",
}
FROZEN = (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "research/RHRC/integration/documentation_2026_11_21/SOURCE_SCOPE.json",
    "research/RHRC/integration/documentation_2026_11_21/source_scope.py",
    "research/RHRC/integration/opica_composition/PUBLIC_TARGETS.json",
    "research/RHRC/integration/opica_composition/SEARCH_CONTRACTS.json",
    "research/RHRC/integration/opica_round6/CONSTRAINT_GRAPH.json",
    "Zeta23/OPICARound6/PrimeFactorPaths/NativeCells.lean",
    "Zeta23/OPICARound6/PrimeFactorPaths/NativeFullTransfer.lean",
)

class ScopeError(ValueError):
    pass

def need(ok, message):
    if not ok:
        raise ScopeError(message)

def git(*args):
    return subprocess.run(["git", "-C", str(REPO), *args], check=True,
                          capture_output=True, text=True, timeout=120).stdout.strip()

def contract(policy):
    need(type(policy) is dict, "combined source contract must be an object")
    expected = {
        "schema", "authority", "native_base", "native_base_tree",
        "source_development_heads", "toolchain", "source_pr_original_blob_oids",
        "reviewed_integration_overrides", "allowed_added_paths", "allowed_edited_paths",
        "required_standalone_module_roles", "frozen_historical_source_policies",
        "historical_round4_11_lane_acceptance", "new_source_round4_11_lane_acceptance",
        "original_generated_state", "claims", "proof_acceptance",
    }
    need(set(policy) == expected and policy["schema"] == "OPICA_NEXT_SOURCE_EPOCH_V1",
         "unreviewed epoch contract schema/field set")
    need(policy["native_base"] == BASE and policy["native_base_tree"] == BASE_TREE,
         "unexpected source baseline")
    need(policy["source_development_heads"] == ORIGINAL_SOURCE_HEADS,
         "unreviewed development branch heads")
    need(policy["toolchain"] == LEAN_PIN, "unreviewed Lean version")
    need(policy["authority"] == "REVIEWED_COMBINED_SOURCE_POLICY_NOT_THEOREM_AUTHORITY",
         "epoch authority label changed")
    need(policy["claims"] == {"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
         and policy["proof_acceptance"] is False, "C1/Step4/RH claim promotion")
    need(policy["historical_round4_11_lane_acceptance"] == "NOT_PROMOTED"
         and policy["new_source_round4_11_lane_acceptance"] == "NOT_RUN_UNTIL_NEW_GATE_QUALIFIED",
         "unearned 11-lane acceptance")
    need(policy["frozen_historical_source_policies"] == "UNCHANGED_AND_REPLAYED_ON_ORIGINAL_BASE",
         "historical policy mutation")
    need(policy["original_generated_state"] == "UNCHANGED_ON_MATHEMATICAL_SOURCE_BRANCH",
         "generated source claims unauthorized")
    need(policy["allowed_added_paths"] == sorted(REVIEWED_ADDITIONS)
         and policy["allowed_edited_paths"] == sorted(REVIEWED_EDITS)
         and policy["reviewed_integration_overrides"] == sorted(INTEGRATION_OVERRIDES),
         "path inventory differs")
    need(policy["required_standalone_module_roles"] == EXPECTED_ROLES,
         "source-module dispositions differ")
    original = policy["source_pr_original_blob_oids"]
    need(original == ORIGINAL_BLOBS, "approved original source blobs differ")
    need(type(original) is dict and set(original) == set(ORIGINAL_PATHS),
         "original 18 exact source blobs missing or extra")
    need(all(type(v) is str and re.fullmatch(r"[0-9a-f]{40}",v) for v in original.values()),
         "original Git source blob ID not closed")
    return original

def check():
    need(git("rev-parse", BASE+"^{tree}") == BASE_TREE, "baseline Git tree changed")
    need(subprocess.run(["git","-C",str(REPO),"merge-base","--is-ancestor",BASE,"HEAD"],
                        capture_output=True).returncode == 0, "epoch not a child of native base")
    raw = git("diff","--name-status", BASE, "HEAD").splitlines()
    delta = [r.split("\t",1) for r in raw]
    need(all(len(r)==2 and r[0] in ("A","M") for r in delta),
         "deletion/rename/nonregular source transaction")
    added = {p for action,p in delta if action=="A"}
    edited = {p for action,p in delta if action=="M"}
    need(added == REVIEWED_ADDITIONS,
         "unreviewed added source paths: " + repr(sorted(added ^ REVIEWED_ADDITIONS)))
    need(edited == REVIEWED_EDITS,
         "unreviewed modified source paths: " + repr(sorted(edited ^ REVIEWED_EDITS)))
    need(not git("status","--porcelain","--untracked-files=no"), "tracked worktree drift")
    need((REPO/"lean-toolchain").read_text().strip() == LEAN_PIN, "native compiler pin differs")

    policy = json.loads((REPO/POLICY).read_text())
    original = contract(policy)
    for name in FROZEN:
        need(git("rev-parse","HEAD:"+name)==git("rev-parse",BASE+":"+name),
             "frozen historical object changed: "+name)
    for name in sorted(REVIEWED_ADDITIONS | REVIEWED_EDITS):
        path=REPO/name
        need(path.is_file() and not path.is_symlink(), "missing/link source: "+name)
        head_blob=git("rev-parse","HEAD:"+name)
        need(head_blob == git("hash-object",str(path)), "worktree differs from Git: "+name)
        need(len(head_blob)==40, "malformed reviewed Git blob ID")
    for name, expected in original.items():
        # The five transport/guard scripts have a separately reviewed, narrow
        # combined-epoch override. All mathematical Lean and other original
        # supplied source files MUST be byte-identical to their source PRs.
        if name not in INTEGRATION_OVERRIDES:
            need(git("rev-parse","HEAD:"+name)==expected,
                 "unreviewed source replacement: "+name)

    roles=json.loads((REPO/next(iter([p for p in REVIEWED_EDITS
                                    if p.endswith("SEMANTIC_CLOSURE_CONFIG.json")]))).read_text())
    for module,role in EXPECTED_ROLES.items():
        need(roles.get("standalone_module_roles",{}).get(module)==role,
             "missing RHKG module disposition: "+module)
    classes=json.loads((REPO/"research/RHRC/graph/FILE_CLASSES.json").read_text())
    for name in REVIEWED_ADDITIONS:
        matches=[r for r in classes["rules"] if re.fullmatch(r["pattern"],name)]
        need(matches and matches[0]["file_class"] != classes["unknown_class"]
             and matches[0]["trust_zone"] != classes["unknown_trust_zone"],
             "new source not explicitly classified: "+name)
    # Source validation does not establish any of the OPEN propositions.
    return {
        "schema":"OPICA_NEXT_SOURCE_EPOCH_VERIFICATION_V1",
        "status":"PASS_REVIEWED_COMBINED_EPOCH_V1",
        "head":git("rev-parse","HEAD"),
        "tree":git("rev-parse","HEAD^{tree}"),
        "base_head":BASE, "base_tree":BASE_TREE,
        "source_development_heads":ORIGINAL_SOURCE_HEADS,
        "original_sources":len(original),
        "reviewed_added_paths":len(REVIEWED_ADDITIONS),
        "reviewed_modified_paths":len(REVIEWED_EDITS),
        "source_lean_blobs":{p:git("rev-parse","HEAD:"+p) for p in ORIGINAL_PATHS if p.endswith(".lean")},
        "old_11_lane_acceptance":"NOT_CLAIMED",
        "new_11_lane_acceptance":"NOT_RUN",
        "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN",
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    need(not args.output.exists(),"do not overwrite source receipt")
    try:
        result=check()
    except Exception as exc:
        # Failure evidence is written BEFORE preserving the failing exit.
        # A missing producer receipt must never masquerade as acceptance.
        try:
            checked_head=git("rev-parse","HEAD")
        except Exception:
            checked_head="UNRESOLVED"
        result={
            "schema":"OPICA_NEXT_SOURCE_EPOCH_FAILURE_V1",
            "status":("SOURCE_POLICY_REJECTED" if isinstance(exc,ScopeError)
                      else "SOURCE_INSPECTION_ERROR"),
            "checked_head":checked_head,
            "exception_type":type(exc).__name__,
            "exception_message":str(exc)[:1200],
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN",
        }
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+"\n")
        print(json.dumps(result),flush=True)
        raise
    else:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+"\n")
        print(json.dumps({k:result[k] for k in ("status","head","proof_acceptance","RH")}))
if __name__=="__main__":
    main()
