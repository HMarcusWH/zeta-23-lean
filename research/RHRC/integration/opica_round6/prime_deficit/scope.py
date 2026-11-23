#!/usr/bin/env python3
"""Source-only frozen-base controls for the separate prime-deficit research lane."""
import hashlib, json, re, subprocess
from pathlib import Path
BASE="bb7c8184a135b2823c6296917c5ac893bebf2a71"
TREE="2b19357e1b65cc500f3e3a5b5d4df14601b02062"
REPO=Path(__file__).resolve().parents[5]
ADDITIONS=(
 ".github/workflows/opica-prime-deficit.yml",
 "Zeta23/OPICARound6/PrimeDeficit/Source.lean",
 "Zeta23/OPICARound6/PrimeDeficit/Verify.lean",
 "research/RHRC/integration/opica_round6/prime_deficit/README.md",
 "research/RHRC/integration/opica_round6/prime_deficit/SOURCE_CONTRACT.json",
 "research/RHRC/integration/opica_round6/prime_deficit/scope.py",
 "research/RHRC/integration/opica_round6/prime_deficit/test_scope.py")
FROZEN=("Zeta23/OPICARound6/PrimeFactorPaths/NativeCells.lean",
        "Zeta23/OPICARound6/PrimeFactorPaths/NativeFullTransfer.lean",
        "research/RHRC/integration/opica_composition/PUBLIC_TARGETS.json",
        "research/RHRC/integration/opica_round6/CONSTRAINT_GRAPH.json",
        "lean-toolchain","lake-manifest.json","lakefile.toml")
def git(*args):
    return subprocess.run(["git","-C",str(REPO),*args],check=True,
                          capture_output=True,text=True,timeout=90).stdout.strip()
def assert_source():
    assert git("rev-parse",BASE+"^{tree}")==TREE, "base tree drift"
    assert subprocess.run(["git","-C",str(REPO),"merge-base","--is-ancestor",BASE,"HEAD"],
                          capture_output=True).returncode==0, "not child of base"
    rows=[x.split("\t",1) for x in git("diff","--name-status",BASE,"HEAD").splitlines()]
    assert all(len(x)==2 and x[0]=="A" for x in rows), "original sources modified/deleted"
    assert sorted(x[1] for x in rows)==list(ADDITIONS), "new source scope differs"
    assert git("status","--porcelain","--untracked-files=no")=="", "dirty checked source"
    for path in FROZEN:
        assert git("rev-parse","HEAD:"+path)==git("rev-parse",BASE+":"+path),path
    manifest=json.loads((REPO/"research/RHRC/integration/opica_round6/prime_deficit/SOURCE_CONTRACT.json").read_text())
    assert manifest["schema"]=="OPICA_PRIME_DEFICIT_SOURCE_CONTRACT_V1"
    assert manifest["source_base_head"]==BASE
    assert manifest["RH"]=="OPEN" and manifest["Step4"]=="OPEN"
    for path in ADDITIONS:
        f=REPO/path
        assert f.is_file() and not f.is_symlink(),path
        assert git("hash-object",str(f))==git("rev-parse","HEAD:"+path),path
    lean=(REPO/"Zeta23/OPICARound6/PrimeDeficit/Source.lean").read_text()
    assert not re.search(r"(?m)^\s*(axiom|sorry|unsafe\s+theorem)\b",lean)
    assert "Real.eulerMascheroniConstant" in lean and "Nat.primesLE" in lean
    assert "smallPrimeCenter N" in lean and "positiveDeficitEnergy" in lean
    return {
      "schema":"OPICA_PRIME_DEFICIT_ADDITIVE_SOURCE_V1",
      "status":"SOURCE_SCOPE_PASS_ONLY","head":git("rev-parse","HEAD"),
      "tree":git("rev-parse","HEAD^{tree}"),
      "added":list(ADDITIONS),"preserved":list(FROZEN),
      "compiler_acceptance":False,"analytic_transfer":"OPEN",
      "proof_acceptance":False,"RH":"OPEN","Step4":"OPEN"}
if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,required=True)
    a=p.parse_args()
    if a.output.exists():raise SystemExit("Output exists")
    v=assert_source();a.output.write_text(json.dumps(v,indent=2)+"\n")
    print(json.dumps({"status":v["status"],"head":v["head"],"proof_acceptance":False}))
