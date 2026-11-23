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
class ScopeError(ValueError):
    """Source-epoch rejection, active even with python -O."""
    pass

def need(condition, message):
    if not condition:
        raise ScopeError(message)

def validate_semantics(manifest, lean):
    """Validate immutable source identity and claim boundary in both Python modes.

    This is a lexical/source-policy safeguard, NOT an arithmetic proof or a
    replacement for the exact Lean compiler and axioms gate.
    """
    need(type(manifest) is dict, "source contract object required")
    need(manifest.get("schema")=="OPICA_PRIME_DEFICIT_SOURCE_CONTRACT_V1",
         "source contract schema differs")
    need(manifest.get("source_base_head")==BASE, "source base differs")
    need(manifest.get("source_module")=="Zeta23.OPICARound6.PrimeDeficit.Source",
         "source module differs")
    need(manifest.get("required_lean","leanprover/lean4:v4.33.0-rc2")==
         "leanprover/lean4:v4.33.0-rc2", "native Lean toolchain contract differs")
    need(manifest.get("open_goals")==[
         "LargePrimeDeficitSubpower","MissingPrimeDeficitToLiteralGBridge"],
         "open analytic target inventory differs")
    need(manifest.get("conditional_transfer_status")=="OPEN_NOT_COMPILED_OR_PROVED",
         "unproved conditional transfer promoted")
    need(manifest.get("old_external_Deduction_G_binding")=="NOT_REPLAYED_AT_NATIVE_PIN",
         "unverified external G bridge promoted")
    need(manifest.get("proof_acceptance") is False and
         manifest.get("RH")=="OPEN" and manifest.get("Step4")=="OPEN",
         "forbidden proof or Step4 promotion")
    need(type(lean) is str and bool(lean), "Lean source text required")
    need(not re.search(r"(?m)^\\s*(axiom|sorry|unsafe\\s+theorem|partial\\s+theorem)\\b",lean),
         "source inserted axiom/placeholder")
    need("_root_.riemannHypothesis" not in lean and
         "cofinal_moment_slice_bounds_of_riemannHypothesis" not in lean,
         "RH-dependent source substitution")
    # These textual controls are a fast negative gate; independent Lean
    # verification and exact source equality remain mandatory.
    for name in ("Real.eulerMascheroniConstant","Nat.primesLE",
                 "smallPrimeCenter N","discretePrimeMean p",
                 "smallPrimeCutoff N < (p:ℝ)","primeFractionalPart N p",
                 "Finset.Icc K ⌊(K:ℝ)^((3:ℝ)/2)⌋₊",
                 "ArithmeticFunction.vonMangoldt n"):
        need(name in lean, "canonical prime source/window changed: "+name)

def assert_source():
    need(git("rev-parse",BASE+"^{tree}")==TREE,"base tree drift")
    need(subprocess.run(["git","-C",str(REPO),"merge-base","--is-ancestor",BASE,"HEAD"],
                        capture_output=True).returncode==0,"not child of base")
    rows=[x.split("\\t",1) for x in git("diff","--name-status",BASE,"HEAD").splitlines()]
    need(all(len(x)==2 and x[0]=="A" for x in rows),
         "original sources modified/deleted")
    need(sorted(x[1] for x in rows)==list(ADDITIONS),"new source scope differs")
    need(git("status","--porcelain","--untracked-files=no")=="",
         "dirty checked source")
    for path in FROZEN:
        need(git("rev-parse","HEAD:"+path)==git("rev-parse",BASE+":"+path),
             "frozen path changed: "+path)
    manifest=json.loads((REPO/"research/RHRC/integration/opica_round6/prime_deficit/SOURCE_CONTRACT.json").read_text())
    lean=(REPO/"Zeta23/OPICARound6/PrimeDeficit/Source.lean").read_text()
    validate_semantics(manifest,lean)
    for path in ADDITIONS:
        file=REPO/path
        need(file.is_file() and not file.is_symlink(),
             "source missing/symlink: "+path)
        need(git("hash-object",str(file))==git("rev-parse","HEAD:"+path),
             "checked source bytes differ: "+path)
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
