#!/usr/bin/env python3
"""Additive source epoch: do not rewrite frozen OPICA/graph/axiom history."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
BASE="bb7c8184a135b2823c6296917c5ac893bebf2a71"
BASE_TREE="2b19357e1b65cc500f3e3a5b5d4df14601b02062"
REPO=Path(__file__).resolve().parents[5]
NEW=(
 ".github/workflows/opica-next-arithmetic.yml",
 "Zeta23/OPICARound6/NextSearch/SourceEnergies.lean",
 "Zeta23/OPICARound6/NextSearch/Verify.lean",
 "research/RHRC/integration/opica_round6/next_search/FALSIFIERS.json",
 "research/RHRC/integration/opica_round6/next_search/README.md",
 "research/RHRC/integration/opica_round6/next_search/SOURCE_CONTRACTS.json",
 "research/RHRC/integration/opica_round6/next_search/TARGETS.json",
 "research/RHRC/integration/opica_round6/next_search/source_scope.py",
 "research/RHRC/integration/opica_round6/next_search/test_source_scope.py",
 "research/RHRC/integration/opica_round6/next_search/typed_export.py",
)
FROZEN=(
 "Zeta23/OPICARound6/PrimeFactorPaths/NativeCells.lean",
 "Zeta23/OPICARound6/PrimeFactorPaths/NativeFullTransfer.lean",
 "Zeta23/OPICARound6/PrimeFactorPaths/NativeStoppingCost.lean",
 "Zeta23/OPICARound6/PrimeFactorPaths/StoppingAlgebra.lean",
 "research/RHRC/integration/opica_round6/CONSTRAINTS.json",
 "research/RHRC/integration/opica_round6/CONSTRAINT_GRAPH.json",
 "research/RHRC/integration/opica_composition/PUBLIC_TARGETS.json",
 "research/RHRC/integration/opica_composition/SEARCH_CONTRACTS.json",
 "lean-toolchain","lakefile.toml","lake-manifest.json",
)
class ScopeError(ValueError): pass
def need(ok,msg):
    if not ok:raise ScopeError(msg)
def git(*args):
    return subprocess.run(["git","-C",str(REPO),*args],check=True,
                          capture_output=True,text=True,timeout=120).stdout.strip()
def check(repo=REPO):
    need(repo==REPO,"Unexpected repo")
    need(git("rev-parse",BASE+"^{tree}")==BASE_TREE,"Base original tree changed")
    need(subprocess.run(["git","-C",str(REPO),"merge-base","--is-ancestor",BASE,"HEAD"],
                        capture_output=True).returncode==0,"Not a child of exact native base")
    raw=git("diff","--name-status",BASE,"HEAD").splitlines()
    delta=[line.split("\t",1) for line in raw]
    need(all(len(row)==2 and row[0]=="A" for row in delta),"Non-additive change to original source")
    need(sorted(row[1] for row in delta)==list(NEW),"Added-path scope differs")
    need(not git("status","--porcelain","--untracked-files=no"),
         "Tracked source modified while being checked")
    for path in FROZEN:
        need(git("rev-parse","HEAD:"+path)==git("rev-parse",BASE+":"+path),
             "Historical source changed: "+path)
    inventory=[]
    for path in NEW:
        p=REPO/path
        need(p.is_file() and not p.is_symlink(),"New source missing/linked: "+path)
        need(git("rev-parse","HEAD:"+path)==git("hash-object",str(p)),
             "Checked source content drift: "+path)
        inventory.append({"path":path,"sha256":hashlib.sha256(p.read_bytes()).hexdigest()})
    t=json.loads((REPO/"research/RHRC/integration/opica_round6/next_search/TARGETS.json").read_text())
    need(t["schema"]=="OPICA_NEXT_ARITHMETIC_TARGETS_V1" and t["base_head"]==BASE
         and t["base_tree"]==BASE_TREE,"Wrong mathematical target base")
    need(t["claims"]=={"RH":"OPEN","C1":"OPEN"} and not t["approved_independent_proof_constants"],
         "Target self-authorized a proof constant")
    need([x["id"] for x in t["targets"]]==[
         "DIRECT_SIGNED_SHELL_POSITIVE","DIRECT_SIGNED_SHELL_NEGATIVE",
         "ONE_POLARITY_SHELL_SUBPOWER","P303_OPPOSED_PRODUCT_UPPER",
         "N20_JOINT_ARITHMETIC_UPPER","PAPER_ROUTE_VALIDATION"],"Target registry changed")
    need(all(x["status"]=="OPEN" for x in t["targets"]),"One open target wrongly promoted")
    s=(REPO/"Zeta23/OPICARound6/NextSearch/SourceEnergies.lean").read_text()
    need(not re.search(r"(?m)^\s*(axiom|sorry|unsafe\s+theorem|partial\s+theorem)\b",s),
         "Forbidden placeholder/axiom in source extension")
    need("wholeCoarseKeys X" in s and "removedLabels X j r" in s
         and "OnePolarityRawSubpower" in s,"Missing literal native source interfaces")
    return {
       "schema":"OPICA_NEXT_ARITHMETIC_SOURCE_SCOPE_V1",
       "status":"PASS_ADDITIVE_SOURCE_BYTES_ONLY","head":git("rev-parse","HEAD"),
       "tree":git("rev-parse","HEAD^{tree}"),"base_head":BASE,"base_tree":BASE_TREE,
       "new_files":inventory,"frozen_paths_checked":len(FROZEN),
       "old_11_lane_acceptance":"NOT_RUN","new_lean_compiled":False,
       "proof_acceptance":False,"RH":"OPEN","Step4":"OPEN"
    }
def main():
    a=argparse.ArgumentParser()
    a.add_argument("--output",type=Path,required=True)
    opts=a.parse_args()
    if opts.output.exists():raise ScopeError("Output must be fresh")
    result=check()
    opts.output.parent.mkdir(parents=True,exist_ok=True)
    opts.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":result["status"],"head":result["head"],"proof_acceptance":False}))
if __name__=="__main__":main()
