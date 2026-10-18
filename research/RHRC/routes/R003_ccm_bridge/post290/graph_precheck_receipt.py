#!/usr/bin/env python3
"""Emit a source-tree-bound receipt only after the complete RHKG check passes.

It never generates graph products. This is integrity evidence, not mathematics.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
GENERATED_ROOTS = (
    "research/RHRC/graph/compiler",
    "research/RHRC/graph/generated",
    "research/RHRC/integration/generated",
    "research/RHRC/ffbbp/generated",
    "research/RHRC/ool/generated",
)
CHECK_PROGRAMS = (
    "research/RHRC/tools/materialize_derived_state.py",
    "research/RHRC/routes/R003_ccm_bridge/post290/graph_precheck_receipt.py",
)

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def generated_manifest(repo: Path) -> dict[str, str]:
    """Enumerate and hash every product; no partial output-directory subset."""
    result = {}
    for dirname in GENERATED_ROOTS:
        root = repo / dirname
        if not root.is_dir() or root.is_symlink():
            raise ValueError("RHKG output directory absent or symlinked: " + dirname)
        files = sorted(x for x in root.rglob("*") if x.is_file())
        if not files:
            raise ValueError("RHKG output directory is empty: " + dirname)
        for file in files:
            if file.is_symlink():
                raise ValueError("symlink in RHKG generated products")
            rel = file.relative_to(repo).as_posix()
            if rel in result:
                raise ValueError("duplicate RHKG product path")
            result[rel] = sha256(file)
    return result

def build_receipt(repo: Path, head: str, tree: str, run_id: str) -> dict:
    if not head or len(head)!=40 or not tree or len(tree)!=40 or not run_id:
        raise ValueError("missing exact checkout or CI run identity")
    products = generated_manifest(repo)
    programs = {}
    for file in CHECK_PROGRAMS:
        path=repo / file
        if not path.is_file() or path.is_symlink():
            raise ValueError("RHKG checker implementation not present: "+file)
        programs[file]=sha256(path)
    return {
        "schema":"PR292_RHKG_FULL_PRECHECK_RECEIPT_V1",
        "execution_status":"SUCCESS",
        "integrity_status":"PASS",
        "claim_cap":"RH_OPEN",
        "head":head, "tree":tree, "workflow_run_id":run_id,
        "full_generated_root_count":len(GENERATED_ROOTS),
        "generated_file_count":len(products),
        "generated_files":products,
        "check_program_sha256":programs,
        "checked_command":"python research/RHRC/tools/materialize_derived_state.py --check",
        "read_only":True,
        "no_theorem_authority_from_manifest":True,
    }

def validate_receipt(receipt: dict, repo: Path, head: str,
                     tree: str, run_id: str) -> bool:
    if not isinstance(receipt,dict):
        raise ValueError("RHKG precheck receipt missing")
    if (receipt.get("schema")!="PR292_RHKG_FULL_PRECHECK_RECEIPT_V1" or
        receipt.get("execution_status")!="SUCCESS" or
        receipt.get("integrity_status")!="PASS" or
        receipt.get("claim_cap")!="RH_OPEN" or
        receipt.get("head")!=head or receipt.get("tree")!=tree or
        receipt.get("workflow_run_id")!=run_id or
        receipt.get("read_only") is not True or
        receipt.get("no_theorem_authority_from_manifest") is not True or
        receipt.get("checked_command")!=
            "python research/RHRC/tools/materialize_derived_state.py --check"):
        raise ValueError("RHKG precheck receipt not bound to exact CI context")
    expected=build_receipt(repo,head,tree,run_id)
    for key in ("generated_files","check_program_sha256",
                "generated_file_count","full_generated_root_count"):
        if receipt.get(key)!=expected[key]:
            raise ValueError("RHKG generated state or checker bytes drifted: "+key)
    return True

def git(*args):
    return subprocess.check_output(["git",*args],cwd=REPO,text=True).strip()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",required=True,type=Path)
    args=parser.parse_args()
    run_id=os.environ.get("GITHUB_RUN_ID")
    if not run_id:
        raise SystemExit("RHKG release receipt requires a GitHub Actions run ID")
    head,tree=git("rev-parse","HEAD"),git("rev-parse","HEAD^{tree}")
    # Check first, write a receipt only after the entire deterministic stack
    # is fresh. This is not a generator: --check must never modify products.
    subprocess.run([sys.executable,str(REPO/"research/RHRC/tools/materialize_derived_state.py"),
                    "--check"],cwd=REPO,check=True)
    receipt=build_receipt(REPO,head,tree,run_id)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"integrity_status":"PASS","head":head,"tree":tree,
                      "generated_files":receipt["generated_file_count"]}))
if __name__=="__main__":
    main()
