"""Exact additive candidate scope and named axiom reports."""
from __future__ import annotations
import argparse, hashlib, json, re, subprocess
from pathlib import Path
from research.RHRC.integration.documentation_2026_11_21 import source_scope as historical
from research.RHRC.integration.opica_round6 import source_scope as round6

ROOT=Path(__file__).resolve().parents[5]
BASE="4f81c784d3b330395507f6dcd1c8b0010b3835cc"
TREE="84b235c455980cfd516a8c0ccaf7749bce3c5339"
POLICY="research/RHRC/integration/opica_round6/bipolar_transfer/POLICY.json"
VALIDATOR="research/RHRC/integration/opica_round6/bipolar_transfer/scope.py"
POLICY_BLOB="02b24f149fa44b7a1981cc9728715e0ab5e94963"
ADDED=set([".github/workflows/opica-bipolar-transfer.yml","Zeta23/OPICARound6/NextSearch/BipolarTransfer.lean","Zeta23/OPICARound6/NextSearch/BipolarVerify.lean","research/RHRC/integration/opica_round6/bipolar_transfer/POLICY.json","research/RHRC/integration/opica_round6/bipolar_transfer/README.md","research/RHRC/integration/opica_round6/bipolar_transfer/finite_controls.py","research/RHRC/integration/opica_round6/bipolar_transfer/scope.py"])
ROOTS=tuple(["Zeta23.OPICARound6.NextSearch.raw_survivor_polarity_difference","Zeta23.OPICARound6.NextSearch.reverseOpposedSurvivorEnergy_bracket","Zeta23.OPICARound6.NextSearch.rawNegativeEnergy_bracket","Zeta23.OPICARound6.NextSearch.rawNegativeEnergy_le_full_components","Zeta23.OPICARound6.NextSearch.rawPositiveEnergy_bracket","Zeta23.OPICARound6.NextSearch.rawSquareEnergy_eq_polarities","Zeta23.OPICARound6.NextSearch.rawSquareEnergy_removal_bound","Zeta23.OPICARound6.NextSearch.pairedOpposedSurvivorEnergy_eq","Zeta23.OPICARound6.NextSearch.pairedOpposedSurvivorEnergy_bracket","Zeta23.OPICARound6.NextSearch.rawBipolarEnergy_bracket","Zeta23.OPICARound6.NextSearch.unsignedErrorEnergy_nonnegative","Zeta23.OPICARound6.NextSearch.cofinalSubpower_of_tail_error","Zeta23.OPICARound6.NextSearch.cofinalSubpower_iff_of_tail_error","Zeta23.OPICARound6.NextSearch.positiveRawSubpower_iff_opposed_of_tail_error","Zeta23.OPICARound6.NextSearch.negativeRawSubpower_iff_opposed_of_tail_error","Zeta23.OPICARound6.NextSearch.onePolarityRawSubpower_iff_opposed_of_tail_error"])
ALLOWED={"propext","Classical.choice","Quot.sound"}

def need(ok,msg):
    if not ok: raise ValueError(msg)

def git(*args):
    return subprocess.check_output(["git","-C",str(ROOT),*args],text=True,timeout=180).strip()

def oid(raw):
    return hashlib.sha1(b"blob "+str(len(raw)).encode("ascii")+b"\0"+raw).hexdigest()

def check():
    need(git("rev-parse",BASE+"^{tree}")==TREE and git("merge-base",BASE,"HEAD")==BASE,"wrong parent")
    head=git("rev-parse","HEAD")
    need(not git("status","--porcelain","--untracked-files=all"),"dirty source")
    parent,current=round6.tree(ROOT,BASE),round6.tree(ROOT,head)
    need(set(current)-set(parent)==ADDED and set(parent)<=set(current),"unexpected path delta")
    need(all(parent[p]==current[p] for p in parent),"parent source or historical generated state changed")
    raw=(ROOT/POLICY).read_bytes();policy=json.loads(raw)
    need(oid(raw)==POLICY_BLOB and current[POLICY]==("100644","blob",POLICY_BLOB),"policy seal differs")
    need(policy["base"]==BASE and policy["tree"]==TREE and policy["proof_acceptance"] is False and
         all(policy[k]=="OPEN" for k in ("RH","C1","Step4")) and policy["roots"]==list(ROOTS),"scope authority differs")
    validator=(ROOT/VALIDATOR).read_bytes()
    anchor=('POLICY_BLOB="'+POLICY_BLOB+'"\n').encode("ascii")
    need(validator.count(anchor)==1 and oid(validator.replace(anchor,b'POLICY_BLOB="<policy-blob>"\n'))==policy["validator_template_oid"],"validator seal differs")
    need(set(policy["reviewed"])==ADDED-{POLICY,VALIDATOR},"reviewed inventory differs")
    need(all(current[p]==("100644","blob",v) for p,v in policy["reviewed"].items()),"reviewed source changed")
    historical.check_worktree(ROOT,current)
    ignored=git("ls-files","--others","--ignored","--exclude-standard")
    need(not any(x.startswith(("Zeta23/","research/",".github/")) and x.endswith((".lean",".lean.in",".py",".yml",".yaml")) for x in ignored.splitlines()),"ignored source provider")
    need(head==git("rev-parse","HEAD") and not git("status","--porcelain","--untracked-files=all"),"source changed")
    return {"schema":"OPICA_BIPOLAR_SOURCE_SCOPE_V1","status":"SOURCE_SCOPE_ONLY",
            "head":head,"tree":git("rev-parse","HEAD^{tree}"),"parent":BASE,
            "parent_compiler_run":"45250786114","reviewed_roots":list(ROOTS),
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}

def axioms(text):
    need(not re.search(r"\bsorryAx\b|(?:^|\n).*?\berror:",text),"compiler error or sorryAx")
    rows=re.findall(r"(?m)^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)[ \t]*(?=\n|$)",text)
    out={}
    for name,raw in rows:
        need(name in ROOTS and name not in out,"unexpected or duplicate named axiom report")
        values=[v.strip() for v in raw.split(",") if v.strip()]
        need(len(values)==len(set(values)) and set(values)<=ALLOWED,"nonstandard axiom")
        out[name]=sorted(values)
    need(set(out)==set(ROOTS),"incomplete named axiom inventory")
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument("--output",required=True,type=Path);p.add_argument("--axiom-log",type=Path)
    a=p.parse_args();r=check()
    if a.axiom_log:
        r.update(status="NAMED_TRANSITIVE_AXIOM_REPORTS_PASS",axioms=axioms(a.axiom_log.read_text()))
    need(not a.output.exists() and not a.output.resolve().is_relative_to(ROOT),"fresh external output required")
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(r,indent=2)+"\n")
    print(json.dumps({k:r[k] for k in ("status","head","proof_acceptance","RH")}))

if __name__=="__main__": main()
