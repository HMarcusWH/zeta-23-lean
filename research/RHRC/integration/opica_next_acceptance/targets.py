"""Versioned signed-target extension of the original OPICA proof service.

The independently logged #307 compiler hashes are evaluator inputs.  The two
finite conditional source constants are the entire new research cohort. The
old 462-declaration atlas and PUBLIC_TARGETS/SEARCH_CONTRACTS remain frozen.
A scalar compiler export is a candidate for separate review, not registration.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from ..opica_composition.canonical import require, load_bytes, canonical_bytes, digest
from ..opica_composition.contracts import (
    TargetSpec, StatementInventory, StatementContract, CohortInventory, SearchBudget,
    ExperimentSpec, PER_ATTEMPT_GATES)
from ..opica_composition.inventory import (
    expression_hash, load_statement_inventory, check_membership_coverage)
from ..opica_composition.snapshot import check_snapshot, file_hash, unlinked

REGISTRY="research/RHRC/integration/opica_next_acceptance/NEXT_TARGETS.json"
SELECTION="opica_next_target_registry_sha256"
NAMESPACE="Zeta23.OPICARound6.NextSearch"
MODULE=NAMESPACE+".SourceEnergies"
TARGET_IDS=("NEXT_POSITIVE_RAW_SUBPOWER","NEXT_NEGATIVE_RAW_SUBPOWER",
            "NEXT_ONE_POLARITY_RAW_SUBPOWER")
TARGET_NAMES=tuple(NAMESPACE+"."+x for x in (
    "PositiveRawSubpower","NegativeRawSubpower","OnePolarityRawSubpower"))
THEOREM_NAMES=tuple(NAMESPACE+"."+x for x in (
    "rawPositiveEnergy_le_full_components","rawPositiveEnergy_le_of_component_budgets"))
ALLOWED_AXIOMS={"propext","Classical.choice","Quot.sound"}
FORBIDDEN=sorted({
    "riemannHypothesis","_root_.riemannHypothesis",
    "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_riemannHypothesis",
    "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_cofinal_moment_slice_bounds",
    "Zeta23.OPICAComposition.cofinal_newborn_packet_calibration",
    "Zeta23.OPICAComposition.cofinal_schur_packet_calibration",
})
COHORT="OPICA_NEXT_REVIEWED_FINITE_SIGNED_SOURCE_V1"
TYPE_REVIEW="opica_next_dual_compiler_type_review_v1"
SCALAR_NS="Zeta23.OPICARound6.PrimeDeficit"
SCALAR_MODULE=SCALAR_NS+".Source"
SCALAR_IDS=("NEXT_LARGE_PRIME_DEFICIT_SUBPOWER","NEXT_PRIME_DEFICIT_TO_LITERAL_G_BRIDGE")
SCALAR_NAMES=(SCALAR_NS+".LargePrimeDeficitSubpower",SCALAR_NS+".MissingPrimeDeficitToLiteralGBridge")
ALL_TARGET_IDS=TARGET_IDS+SCALAR_IDS
STOP_MODULE="Zeta23.OPICARound6.PrimeFactorPaths.NativeStoppingCost"
TRANSFER_MODULE="Zeta23.OPICARound6.PrimeFactorPaths.NativeFullTransfer"
EXTRA_SUPPORT=(
    (SCALAR_NS+".positiveDeficitEnergy_nonneg", SCALAR_MODULE),
    (STOP_MODULE+".native_opposed_cost", STOP_MODULE),
    (STOP_MODULE+".native_opposed_cost_reverse", STOP_MODULE),
    (TRANSFER_MODULE+".native_raw_energy_upper", TRANSFER_MODULE),
)
REVIEW_ROLES=("producer","reviewer")
_TYPE_REVIEW_CACHE={}

# These are independently stated propositions and exact typed applications,
# not inferred proposals and not proofs of the two OPEN scalar targets.
EXPECTED_TYPES_LEAN="""
noncomputable section
open scoped Classical
open Zeta23.OPICARound6.PrimeDeficit
open Zeta23.OPICARound6.PrimeFactorPaths
open Zeta23.OPICARound6.PrimeFactorPaths.NativeCells

example : LargePrimeDeficitSubpower =
  (∀ η : ℝ, 0 < η → ∀ K₀ : ℕ,
    ∃ K : ℕ, max K₀ 64 ≤ K ∧ positiveDeficitEnergy K ≤ (K:ℝ)^η) := rfl

example : MissingPrimeDeficitToLiteralGBridge =
  (LargePrimeDeficitSubpower →
    ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ,
      ∃ Y : ℝ, max Y₀ 2 ≤ Y ∧ literalGEnergy Y ≤ Y^η) := rfl

example : ∀ (K : ℕ), 0 ≤ positiveDeficitEnergy K :=
  positiveDeficitEnergy_nonneg

example : ∀ (X : ℕ) (j : Key) (r : Removal),
    4 * max (evenDeviation X j r) 0 * max (-oddDeviation X j r) 0 =
      max ((max (survivorCharge X j r) 0)^2 - (unsignedDiscrepancy X j)^2) 0 :=
  NativeStoppingCost.native_opposed_cost

example : ∀ (X : ℕ) (j : Key) (r : Removal),
    4 * max (oddDeviation X j r) 0 * max (-evenDeviation X j r) 0 =
      max ((max (-survivorCharge X j r) 0)^2 - (unsignedDiscrepancy X j)^2) 0 :=
  NativeStoppingCost.native_opposed_cost_reverse

example : ∀ (X : ℕ) (r : Removal) (nodes : Finset Key),
    (∑ j ∈ nodes, weight j * (max (RoughNodeCharges.charge (roughCutoff X) (rawLabels X j)) 0)^2) ≤
      (∑ j ∈ nodes, weight j * (4 * max (evenDeviation X j r) 0 * max (-oddDeviation X j r) 0)) +
      (∑ j ∈ nodes, weight j * (unsignedDiscrepancy X j)^2) +
      ∑ j ∈ nodes, weight j *
        (2 * (rawLabels X j).card * |RoughNodeCharges.charge (roughCutoff X) (removedLabels X j r)|) :=
  NativeFullTransfer.native_raw_energy_upper
end
"""


def registry(repo):
    repo=Path(repo)
    d=load_bytes((repo/REGISTRY).read_bytes())
    require(set(d)=={"schema","authority","source_head","compiler_run_id",
        "source_path","source_git_blob","toolchain","source_theorems","targets",
        "allowed_axioms","scalar_pending_compiler_type_review",
        "proof_acceptance","RH","C1","Step4"},"closed next-target registry required")
    require(d["schema"]=="OPICA_NEXT_REVIEWED_SIGNED_TARGET_REGISTRY_V1" and
            d["authority"]=="REVIEWED_COMPILER_TYPE_HASHES_ONLY_NOT_PROOF_ACCEPTANCE"
            and d["source_head"]=="e2f8492e46cf8c3b3a220e2945838ddd20155a9c"
            and d["compiler_run_id"]=="45187059999"
            and d["toolchain"]=="leanprover/lean4:v4.33.0-rc2"
            and d["proof_acceptance"] is False
            and all(d[k]=="OPEN" for k in ("RH","C1","Step4")),
            "unreviewed signed target authority")
    require(d["source_path"]=="Zeta23/OPICARound6/NextSearch/SourceEnergies.lean"
            and d["source_git_blob"]=="f5024bf53e1472d9229369ad2821993a7ef1ab8a",
            "signed source binding differs")
    source=(repo/d["source_path"]).read_bytes()
    require(hashlib.sha1(b"blob "+str(len(source)).encode("ascii")+b"\0"+source).hexdigest()
            ==d["source_git_blob"],"reviewed signed mathematical source differs")
    require(set(d["allowed_axioms"])==ALLOWED_AXIOMS and len(d["allowed_axioms"])==3,
            "signed-target axioms differ")
    require([x["declaration"] for x in d["source_theorems"]]==list(THEOREM_NAMES),
            "finite conditional source inventory differs")
    for x in d["source_theorems"]:
        require(set(x)=={"declaration","module","type_sha256"} and x["module"]==MODULE
                and re.fullmatch(r"[0-9a-f]{64}",x["type_sha256"]),
                "invalid reviewed theorem type binding")
    require([x["id"] for x in d["targets"]]==list(TARGET_IDS)
            and [x["declaration"] for x in d["targets"]]==list(TARGET_NAMES),
            "exact three signed targets required")
    menu=[{"declaration":n,"module":MODULE} for n in THEOREM_NAMES]
    for x in d["targets"]:
        require(set(x)=={"id","declaration","module","expected_type_sha256",
                         "target_kind","status","approved_constants"}
                and x["module"]==MODULE and x["target_kind"]=="value"
                and x["status"]=="OPEN" and x["approved_constants"]==menu
                and re.fullmatch(r"[0-9a-f]{64}",x["expected_type_sha256"]),
                "invalid reviewed signed target")
    require(d["scalar_pending_compiler_type_review"]==[
        "Zeta23.OPICARound6.PrimeDeficit.LargePrimeDeficitSubpower",
        "Zeta23.OPICARound6.PrimeDeficit.MissingPrimeDeficitToLiteralGBridge"],
        "unreviewed scalar target promotion")
    return d

def selected(snapshot):
    if SELECTION not in getattr(snapshot,"environment",{}):
        return False
    repo=Path(snapshot.repo)
    require(snapshot.source_policy=="REVIEWED_FROZEN" and
            snapshot.files.get(REGISTRY)==snapshot.environment[SELECTION]==file_hash(repo/REGISTRY),
            "next-target registry not explicitly frozen in experiment")
    registry(repo)
    return True

def _validate_type_receipt(doc, *, head, tree, run_id, attempt, role):
    require(type(doc) is dict and set(doc)=={
        "schema","status","head","tree","run_id","attempt","role","expected_types_checked",
        "target_values","support_types","compiler_log_sha256","proof_acceptance","RH","C1","Step4"},
        "closed dual compiler type receipt required")
    require(doc["schema"]=="OPICA_NEXT_DUAL_COMPILER_TYPES_V1" and
            doc["status"]=="PASS_TYPES_ONLY" and doc["head"]==head and doc["tree"]==tree and
            doc["run_id"]==run_id and doc["attempt"]==attempt and doc["role"]==role and
            doc["expected_types_checked"] is (role=="reviewer") and
            doc["proof_acceptance"] is False and all(doc[k]=="OPEN" for k in ("RH","C1","Step4")),
            "stale or promoted compiler type receipt")
    require(re.fullmatch(r"[0-9a-f]{64}",doc["compiler_log_sha256"]),
            "missing compiler log digest")
    rows=doc["target_values"]
    require(type(rows) is list and len(rows)==2 and
            [x["declaration"] for x in rows]==list(SCALAR_NAMES) and
            all(set(x)=={"declaration","expected_type_sha256"} and
                re.fullmatch(r"[0-9a-f]{64}",x["expected_type_sha256"]) for x in rows),
            "exact scalar target values required")
    supports=doc["support_types"]
    require(type(supports) is list and len(supports)==len(EXTRA_SUPPORT) and
            [(x["declaration"],x["module"]) for x in supports]==list(EXTRA_SUPPORT),
            "exact finite support inventory required")
    for x in supports:
        require(set(x)=={"declaration","module","type_sha256","axioms"} and
                re.fullmatch(r"[0-9a-f]{64}",x["type_sha256"]) and
                type(x["axioms"]) is list and x["axioms"]==sorted(set(x["axioms"])) and
                set(x["axioms"])<=ALLOWED_AXIOMS,"unapproved support type/axiom record")
    return doc

def review_types(repo, output, role, run_id, attempt):
    from .gate import check
    from ..opica_composition.qualification import atlas_driver
    require(role in REVIEW_ROLES,"explicit producer/reviewer role required")
    run_id=_run_id(run_id)
    require(type(attempt) is int and attempt>0,"exact run attempt required")
    repo=Path(repo).resolve(); source=check(repo,require_clean=True)
    output=Path(output).resolve()
    require(not output.exists() and not output.is_relative_to(repo),"fresh external type review directory required")
    output.mkdir(parents=True)
    rows=[{"declaration":n,"module":m} for n,m in EXTRA_SUPPORT]
    driver="import Zeta23.RHRC.OpicaComposition.Export\n"+atlas_driver(rows)
    if role=="reviewer":
        driver+="\n"+EXPECTED_TYPES_LEAN
    for n in SCALAR_NAMES:
        driver+="\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget "+chr(96)+n+' "value"\n'
    path=output/"TypeReview.lean";path.write_text(driver,encoding="utf-8")
    with (output/"compiler.log").open("xb") as log:
        result=subprocess.run(["lake","env","lean","-DwarningAsError=true",str(path)],
                              cwd=repo,stdout=log,stderr=subprocess.STDOUT,timeout=1800)
    require(result.returncode==0,"actual compiler type review failed")
    raw=(output/"compiler.log").read_bytes()
    require(b"sorryAx" not in raw,"sorryAx in compiler review")
    values=[load_bytes(l.split(b"\t",1)[1]) for l in raw.splitlines() if l.startswith(b"OPICA_TARGET\t")]
    exports=[load_bytes(l.split(b"\t",1)[1]) for l in raw.splitlines() if l.startswith(b"OPICA3_ATLAS\t")]
    require(len(values)==2 and len(exports)==len(EXTRA_SUPPORT),"incomplete compiler type review exports")
    by_name={x["declaration"]:x for x in exports}
    require(set(by_name)=={n for n,_ in EXTRA_SUPPORT},"compiler support identities differ")
    support=[]
    for name,module in EXTRA_SUPPORT:
        row=by_name[name]
        require(row["module"]==module and row["kind"]=="THEOREM" and
                not (set(row["value_constants"])&set(FORBIDDEN)),"unapproved source provider")
        support.append({"declaration":name,"module":module,
                        "type_sha256":expression_hash(row["type_expression"]),
                        "axioms":sorted(row["axioms"])})
    doc={"schema":"OPICA_NEXT_DUAL_COMPILER_TYPES_V1","status":"PASS_TYPES_ONLY",
         "head":source["checked_commit"],"tree":source["checked_tree"],"run_id":run_id,"attempt":attempt,
         "role":role,"expected_types_checked":role=="reviewer",
         "target_values":[{"declaration":n,"expected_type_sha256":expression_hash(v)} for n,v in zip(SCALAR_NAMES,values)],
         "support_types":support,"compiler_log_sha256":file_hash(output/"compiler.log"),
         "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    _validate_type_receipt(doc,head=doc["head"],tree=doc["tree"],run_id=run_id,attempt=attempt,role=role)
    require(check(repo,require_clean=True)==source,"source changed during type review")
    (output/"review.json").write_bytes(canonical_bytes(doc))
    return doc

def authenticate_type_review(repo, run_id):
    from .gate import git
    repo=Path(repo).resolve();run_id=_run_id(run_id)
    head,tree=git(repo,"rev-parse","HEAD"),git(repo,"rev-parse","HEAD^{tree}")
    key=(str(repo),head,tree,run_id)
    if key in _TYPE_REVIEW_CACHE:
        return dict(_TYPE_REVIEW_CACHE[key])
    run=_gh_json("/actions/runs/"+run_id)
    attempt=run.get("run_attempt")
    require(type(attempt) is int and attempt>0,"exact type-review attempt required")
    jobs=_gh_json("/actions/runs/"+run_id+"/attempts/"+str(attempt)+"/jobs?per_page=100")
    _verify_run(run,jobs,run_id=run_id,head=head,workflow=".github/workflows/opica-next-acceptance.yml",
                required_jobs=tuple("NextTypes / "+role for role in REVIEW_ROLES))
    docs=[];hashes=[]
    for role in REVIEW_ROLES:
        doc,sha=_receipt(run_id,"opica-next-type-review-"+role+"-"+head+"-"+run_id+"-"+str(attempt),"review.json")
        docs.append(_validate_type_receipt(doc,head=head,tree=tree,run_id=run_id,attempt=attempt,role=role))
        hashes.append(sha)
    for field in ("target_values","support_types"):
        require(docs[0][field]==docs[1][field],"independent compiler type review differs: "+field)
    result={"schema":"OPICA_NEXT_AUTHENTICATED_TYPES_V1","head":head,"tree":tree,
            "run_id":run_id,"attempt":attempt,"producer_receipt_sha256":hashes[0],
            "reviewer_receipt_sha256":hashes[1],"target_values":docs[1]["target_values"],
            "support_types":docs[1]["support_types"],"proof_acceptance":False,
            "RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    _TYPE_REVIEW_CACHE[key]=dict(result)
    return result

def reviewed_registry(snapshot):
    d=registry(snapshot.repo)
    supplied=snapshot.environment.get(TYPE_REVIEW)
    if supplied is None:
        return d
    require(type(supplied) is dict,"authenticated type review required")
    actual=authenticate_type_review(snapshot.repo,supplied.get("run_id"))
    require(supplied==actual and actual["head"]==snapshot.commit and actual["tree"]==snapshot.tree,
            "exact snapshot compiler type review differs")
    support=actual["support_types"]
    d["source_theorems"] += support
    extra_signed=[{"declaration":x["declaration"],"module":x["module"]} for x in support[1:]]
    for row in d["targets"]:
        row["approved_constants"] += extra_signed
    for target_id,row in zip(SCALAR_IDS,actual["target_values"]):
        d["targets"].append({"id":target_id,"declaration":row["declaration"],"module":SCALAR_MODULE,
            "target_kind":"value","status":"OPEN","expected_type_sha256":row["expected_type_sha256"],
            "approved_constants":[{"declaration":support[0]["declaration"],"module":SCALAR_MODULE}]})
    return d

def target(repo,snapshot,target_id):
    require(selected(snapshot),"next-target experiment was not explicitly selected")
    d=reviewed_registry(snapshot)
    matches=[x for x in d["targets"] if x["id"]==target_id]
    require(len(matches)==1,"unregistered next-source target")
    row=matches[0];table=[];constants={}
    for item in row["approved_constants"]:
        name,mod=item["declaration"],item["module"]
        cid=digest({"source_generation":snapshot.generation,"declaration":name,"module":mod},
                   domain="OPICA_APPROVED_CONSTANT_V1")
        constants[cid]=name
        table.append({"id":cid,"declaration":name,"module":mod,"role":"constant"})
    return TargetSpec(target_id,row["declaration"],row["module"],row["expected_type_sha256"],
                      constants,sorted(ALLOWED_AXIOMS),sorted({row["module"]}|{x["module"] for x in row["approved_constants"]}),list(PER_ATTEMPT_GATES),
                      "value",FORBIDDEN),table

def member(name):
    return {"cohort":COHORT,"root_id":name,"declaration":name}

def check_inventory(snapshot,inv):
    require(selected(snapshot) and inv.snapshot_digest==snapshot.generation,
            "signed inventory belongs to a different source generation")
    expected={x["declaration"]:x for x in reviewed_registry(snapshot)["source_theorems"]}
    require(len(inv.statements)==len(expected) and
            {r["declaration"] for r in inv.statements}==set(expected),
            "exact two-source signed cohort required")
    for row in inv.statements:
        rec=StatementContract.from_dict({k:v for k,v in row.items() if k!="memberships"})
        want=expected[rec.declaration]
        require(rec.module==want["module"] and rec.type_sha256==want["type_sha256"]
                and set(rec.axioms)==set(want.get("axioms",ALLOWED_AXIOMS))
                and not (set(rec.value_constants)&set(FORBIDDEN))
                and row.get("memberships")==[member(rec.declaration)],
                "signed theorem type/axiom/membership or premise boundary differs")
    return inv

def validate_retrieval(snapshot,inv,doc):
    check_inventory(snapshot,inv)
    require(set(doc)=={"schema","source_generation","snapshot_digest",
                       "registry_sha256","native_export_sha256","targets","statements",
                       "proof_acceptance"} and
            doc["schema"]=="OPICA_NEXT_NATIVE_RETRIEVAL_CONTRACT_V1"
            and doc["source_generation"]==snapshot.generation
            and doc["snapshot_digest"]==snapshot.digest
            and doc["registry_sha256"]==snapshot.environment[SELECTION]
            and doc["native_export_sha256"]==inv.native_export_sha256
            and doc["proof_acceptance"] is False,"retrieval contract not source-bound")
    d=reviewed_registry(snapshot)
    require(type(doc["targets"]) is list and len(doc["targets"])==len(d["targets"]),
            "exact three compiler target values required")
    for item,want in zip(doc["targets"],d["targets"]):
        require(set(item)=={"target_id","expected_expression","proof_constants"}
                and item["target_id"]==want["id"]
                and expression_hash(item["expected_expression"])==want["expected_type_sha256"],
                "fresh compiler target differs from independently registered type")
        require(type(item["proof_constants"]) is list and
                all(type(v) is str for v in item["proof_constants"]),
                "invalid compiler target proof constants")
    rows={r["declaration"]:r for r in inv.statements}
    require(type(doc["statements"]) is list and len(doc["statements"])==len(rows)
            and {r["declaration"] for r in doc["statements"]}==set(rows),
            "exact signed compiler statement set required")
    for row in doc["statements"]:
        plain={k:v for k,v in row.items() if k!="proof_constants"}
        require(plain==rows[row["declaration"]] and
                type(row.get("proof_constants")) is list and
                all(type(v) is str for v in row["proof_constants"]),
                "retrieval statement differs from native inventory")
    return doc

def search_contract(snapshot,inv,target_spec,path):
    doc=validate_retrieval(snapshot,inv,load_bytes(unlinked(path).read_bytes()))
    row=next(x for x in doc["targets"] if x["target_id"]==target_spec.target_id)
    require(expression_hash(row["expected_expression"])==target_spec.expected_type_hash,
            "retrieval expected type differs from target policy")
    return {"expected_expression":row["expected_expression"],
            "statements":doc["statements"],"proof_constants":row["proof_constants"]}

def inventory(repo,snapshot,output,*,worker):
    """Actual isolated compiler inventory, with the old atlas left separate."""
    from ..opica_composition.qualification import atlas_driver
    from ..opica_composition.executor import run_worker,worker_environment
    require(selected(snapshot) and worker.production,"production signed inventory required")
    check_snapshot(snapshot)
    require(worker_environment(worker)==snapshot.environment["worker_environment"],
            "compiler/import objects differ before signed inventory")
    output=Path(output);native=output/"next-native";native.mkdir()
    d=reviewed_registry(snapshot)
    theorem_names=[x["declaration"] for x in d["source_theorems"]]
    target_names=[x["declaration"] for x in d["targets"]]
    target_ids=[x["id"] for x in d["targets"]]
    driver="import Zeta23.RHRC.OpicaComposition.Export\n"+atlas_driver(d["source_theorems"])
    for name in theorem_names:
        driver+="\nrun_cmd Zeta23.RHRC.OpicaComposition.exportRetrievalProofConstants "+chr(96)+name+' "type"\n'
    for name in target_names:
        driver+="\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget "+chr(96)+name+' "value"\n'
        driver+="run_cmd Zeta23.RHRC.OpicaComposition.exportRetrievalProofConstants "+chr(96)+name+' "value"\n'
    source="NextInventory.lean";(native/source).write_text(driver,encoding="utf-8")
    result=run_worker(worker,native,source,"NextInventory.olean",SearchBudget(**(worker.budget or {})))
    (native/"worker-result.json").write_bytes(canonical_bytes(result))
    require(result["exit_code"]==0 and result["resource_status"] is None,
            "actual native signed inventory compiler failed")
    log=native/(source+".log")
    require(log.is_file() and (native/"NextInventory.olean").is_file(),
            "native inventory proof objects/log absent")
    first=load_statement_inventory(snapshot,log)
    records=[{**r,"memberships":[member(r["declaration"])]} for r in first.statements]
    inv=check_inventory(snapshot,StatementInventory(snapshot.generation,records,
                                                    first.native_export_sha256))
    target_values=[];proofs=[]
    for line in log.read_bytes().splitlines():
        if line.startswith(b"OPICA_TARGET\t"):target_values.append(load_bytes(line.split(b"\t",1)[1]))
        if line.startswith(b"OPICA_RETRIEVAL_PROOFS\t"):proofs.append(load_bytes(line.split(b"\t",1)[1]))
    require(len(target_values)==len(target_names) and len(proofs)==len(theorem_names)+len(target_names),"incomplete signed retrieval exports")
    rows={r["declaration"]:r for r in inv.statements}
    doc={"schema":"OPICA_NEXT_NATIVE_RETRIEVAL_CONTRACT_V1",
         "source_generation":snapshot.generation,"snapshot_digest":snapshot.digest,
         "registry_sha256":snapshot.environment[SELECTION],
         "native_export_sha256":inv.native_export_sha256,
         "targets":[{"target_id":tid,"expected_expression":val,"proof_constants":proofs[i+len(theorem_names)]}
                    for i,(tid,val) in enumerate(zip(target_ids,target_values))],
         "statements":[{**rows[n],"proof_constants":proofs[i]} for i,n in enumerate(theorem_names)],
         "proof_acceptance":False}
    validate_retrieval(snapshot,inv,doc)
    cohort=CohortInventory(theorem_names,[member(n) for n in theorem_names])
    coverage=check_membership_coverage(inv,cohort)
    require(coverage.complete,"signed native membership coverage incomplete")
    check_snapshot(snapshot)
    require(worker_environment(worker)==snapshot.environment["worker_environment"],
            "compiler/import objects changed during signed inventory")
    (output/"inventory.json").write_bytes(inv.to_bytes())
    (output/"coverage.json").write_bytes(coverage.to_bytes())
    (output/"next-contract.json").write_bytes(canonical_bytes(doc))
    return inv

def export_scalar_candidate(repo,output):
    """Source-only fresh compiler types. Never modifies the approved registry."""
    from .gate import check
    repo=Path(repo).resolve();admission=check(repo,require_clean=True)
    output=Path(output).resolve()
    require(not output.exists() and not output.is_relative_to(repo),"fresh external scalar candidate required")
    ns="Zeta23.OPICARound6.PrimeDeficit"
    names=[(ns+".LargePrimeDeficitSubpower","value"),
           (ns+".MissingPrimeDeficitToLiteralGBridge","value"),
           (ns+".positiveDeficitEnergy_nonneg","type")]
    source="import "+ns+".Source\nimport Zeta23.RHRC.OpicaComposition.Export\n"
    for name,kind in names:
        source+="run_cmd Zeta23.RHRC.OpicaComposition.exportTarget "+chr(96)+name+' "'+kind+'"\n'
    with tempfile.TemporaryDirectory(prefix="opica-scalar-candidate-") as tmp:
        driver=Path(tmp)/"ScalarTypes.lean";driver.write_text(source,encoding="utf-8")
        proc=subprocess.run(["lake","env","lean",str(driver)],cwd=repo,capture_output=True,
                            check=True,timeout=1800)
    rows=[load_bytes(line.split(b"\t",1)[1]) for line in proc.stdout.splitlines()
          if line.startswith(b"OPICA_TARGET\t")]
    require(len(rows)==3,"scalar candidate compiler target inventory differs")
    result={"schema":"OPICA_SCALAR_COMPILER_TYPE_CANDIDATE_V1",
            "source_head":admission["checked_commit"],"source_tree":admission["checked_tree"],
            "status":"PENDING_INDEPENDENT_TYPE_REGISTRY_REVIEW",
            "entries":[{"name":n,"kind":k,"expected_expression":v,
                         "type_sha256":expression_hash(v)} for (n,k),v in zip(names,rows)],
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    require(check(repo,require_clean=True)==admission,"scalar source changed during export")
    output.parent.mkdir(parents=True,exist_ok=True)
    log=output.with_suffix(".compiler.log")
    require(not log.exists(),"scalar compiler log already exists")
    log.write_bytes(proc.stdout)
    result["compiler_log_sha256"]=file_hash(log)
    output.write_bytes(canonical_bytes(result))
    return result

# Only authenticated Actions executions supply qualification, not local PASS flags.
QUALIFICATION = "opica_next_qualification_v1"
RUN_REPOSITORY = "HMarcusWH/zeta-23-lean"
_QUALIFICATION_CACHE = {}

def _run_id(value):
    require(type(value) is str and re.fullmatch(r"[1-9][0-9]{0,19}", value),
            "explicit numeric Actions run ID required")
    return value

def _gh_json(endpoint):
    require(bool(os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")),
            "read-only authenticated Actions access required")
    proc = subprocess.run(["gh", "api", "--method", "GET",
                           "repos/" + RUN_REPOSITORY + endpoint],
                          capture_output=True, timeout=90, check=False)
    require(proc.returncode == 0 and len(proc.stdout) <= 16*1024*1024,
            "authenticated Actions metadata unavailable")
    return json.loads(proc.stdout)

def _verify_run(run, jobs, *, run_id, head, workflow, required_jobs):
    require(str(run.get("id")) == run_id and run.get("head_sha") == head
            and run.get("path", "").split("@", 1)[0] == workflow
            and run.get("repository", {}).get("full_name") == RUN_REPOSITORY
            and run.get("head_repository", {}).get("full_name") == RUN_REPOSITORY
            and run.get("event") in {"push", "workflow_dispatch"}
            and run.get("status") == "completed" and run.get("conclusion") == "success"
            and type(run.get("run_attempt")) is int and run["run_attempt"] > 0,
            "Actions run is not the exact successful reviewed source/workflow")
    require(type(jobs) is dict and type(jobs.get("jobs")) is list
            and jobs.get("total_count") == len(jobs["jobs"]),
            "complete Actions attempt job inventory required")
    rows = jobs["jobs"]
    for name in required_jobs:
        matched = [j for j in rows if j.get("name") == name]
        require(len(matched) == 1 and matched[0].get("status") == "completed"
                and matched[0].get("conclusion") == "success"
                and str(matched[0].get("run_id")) == run_id
                and matched[0].get("run_attempt", run["run_attempt"]) == run["run_attempt"],
                "missing or unsuccessful required Actions job: " + name)
    return run["run_attempt"]

def _receipt(run_id, name, filename):
    listing = _gh_json("/actions/runs/" + run_id + "/artifacts?per_page=100")
    require(type(listing.get("artifacts")) is list
            and listing.get("total_count") == len(listing["artifacts"]),
            "complete Actions artifact inventory required")
    rows = [x for x in listing["artifacts"] if x.get("name") == name
            and x.get("expired") is False]
    require(len(rows) == 1 and type(rows[0].get("size_in_bytes")) is int
            and 0 < rows[0]["size_in_bytes"] <= 1024*1024,
            "exact bounded qualification artifact missing or ambiguous")
    with tempfile.TemporaryDirectory(prefix="opica-qualification-") as tmp:
        proc = subprocess.run(["gh", "run", "download", run_id, "--repo",
                               RUN_REPOSITORY, "--name", name, "--dir", tmp],
                              capture_output=True, timeout=120, check=False)
        require(proc.returncode == 0, "authenticated Actions artifact download failed")
        f = unlinked(Path(tmp)/filename)
        require(f.is_file() and f.stat().st_size <= 1024*1024,
                "exact qualification receipt missing")
        raw = f.read_bytes()
        return json.loads(raw), hashlib.sha256(raw).hexdigest()

def _verify_parent_receipt(doc, *, head, tree):
    require(doc.get("schema") == "OPICA_NEXT_SOURCE_EPOCH_VERIFICATION_V1"
            and doc.get("status") == "PASS_REVIEWED_COMBINED_EPOCH_V1"
            and doc.get("head") == head and doc.get("tree") == tree
            and doc.get("proof_acceptance") is False
            and all(doc.get(k) == "OPEN" for k in ("RH", "C1", "Step4")),
            "parent source receipt identity or claim boundary differs")

def _verify_round4_receipt(doc, *, head, tree, run_id, attempt, profile):
    from ..opica_composition.accept import ROUND4_LANES, REPLAY_GROUP_IDS, group_lanes
    expected = {"run_id": run_id, "attempt": attempt, "requested_commit": head,
                "requested_tree": tree, "profile_digest": profile}
    require(doc.get("schema") == "OPICA4_INTEGRATED_ACCEPTANCE_V1"
            and doc.get("status") == "PASS_DECLARED_INTEGRATED_SCOPE"
            and doc.get("experiment") == expected
            and doc.get("RH") == doc.get("Step4") == "OPEN",
            "Round4 aggregate receipt is stale, incomplete, or promoted")
    lanes = doc.get("independently_reconstructed_lanes")
    groups = doc.get("independent_groups")
    require(type(lanes) is list and [x.get("id") for x in lanes] == list(ROUND4_LANES)
            and all(re.fullmatch(r"[0-9a-f]{64}", x.get("evidence_digest", "")) for x in lanes)
            and type(groups) is list and [x.get("group_id") for x in groups] == list(REPLAY_GROUP_IDS),
            "all eleven lanes and three independent groups required")
    require(all(g.get("conclusion") == "success" and g.get("lanes") == list(group_lanes(g["group_id"]))
                and re.fullmatch(r"[0-9a-f]{64}", g.get("evidence_digest", "")) for g in groups),
            "independent acceptance partition differs")

def authenticate_qualification(repo, parent_run, round4_run):
    from .gate import BASE, TREE, git
    from ..opica_composition.accept import ROUND4_LANES, REPLAY_GROUP_IDS
    repo = Path(repo).resolve()
    parent_run, round4_run = _run_id(parent_run), _run_id(round4_run)
    require(parent_run != round4_run, "separate parent and successor runs required")
    head, tree = git(repo, "rev-parse", "HEAD"), git(repo, "rev-parse", "HEAD^{tree}")
    profile = file_hash(repo/"research/RHRC/integration/opica_composition/PROFILE.json")
    key = (str(repo), head, tree, profile, parent_run, round4_run)
    if key in _QUALIFICATION_CACHE:
        return dict(_QUALIFICATION_CACHE[key])
    def checked(run_id, sha, workflow, names):
        run = _gh_json("/actions/runs/" + run_id)
        attempt = run.get("run_attempt")
        require(type(attempt) is int and attempt > 0, "exact Actions attempt required")
        jobs = _gh_json("/actions/runs/" + run_id + "/attempts/" + str(attempt) + "/jobs?per_page=100")
        return _verify_run(run, jobs, run_id=run_id, head=sha,
                           workflow=".github/workflows/" + workflow, required_jobs=names)
    pa = checked(parent_run, BASE, "opica-next-source-epoch.yml",
                 ("source", "native-source-lean", "typed-retrieval"))
    pd, ph = _receipt(parent_run, "opica-next-epoch-source-" + BASE + "-" + parent_run + "-" + str(pa),
                      "OPICA_NEXT_EPOCH_SOURCE.json")
    _verify_parent_receipt(pd, head=BASE, tree=TREE)
    ra = checked(round4_run, head, "rhrc_opica_composition.yml",
                 tuple("Round4 / " + lane for lane in ROUND4_LANES)
                 + tuple("Round4 / INDEPENDENT_" + g for g in REPLAY_GROUP_IDS)
                 + ("Round4 / ACCEPTANCE",))
    rd, rh = _receipt(round4_run, "opica4-release-receipt-" + round4_run + "-" + str(ra),
                      "acceptance.json")
    _verify_round4_receipt(rd, head=head, tree=tree, run_id=round4_run, attempt=ra, profile=profile)
    result = {"schema": "OPICA_NEXT_AUTHENTICATED_PREREQUISITES_V1",
              "parent_run": parent_run, "parent_attempt": pa, "parent_head": BASE, "parent_tree": TREE,
              "parent_receipt_sha256": ph, "round4_run": round4_run, "round4_attempt": ra,
              "successor_head": head, "successor_tree": tree, "round4_receipt_sha256": rh,
              "proof_acceptance": False, "RH": "OPEN", "C1": "OPEN", "Step4": "OPEN"}
    _QUALIFICATION_CACHE[key] = dict(result)
    return result

def enforce_qualification(snapshot):
    if not selected(snapshot):
        return
    supplied = snapshot.environment.get(QUALIFICATION)
    require(type(supplied) is dict, "authenticated parent and full Round4 receipts required")
    actual = authenticate_qualification(snapshot.repo, supplied.get("parent_run"), supplied.get("round4_run"))
    require(supplied == actual and actual["successor_head"] == snapshot.commit
            and actual["successor_tree"] == snapshot.tree,
            "snapshot qualification receipt differs from authenticated source")
    if TYPE_REVIEW in snapshot.environment:
        reviewed_registry(snapshot)


def run_bounded_menu(plan,dispatch,verify):
    """One attempt per reviewed action; distinguish execution from scientific results."""
    ids=set(plan["proposals"])
    batch=plan["candidates"]
    require(type(batch["complete"]) is bool,"closed search completion flag required")
    attempts=[];seen=set();accepted=0;incomplete=None
    for i in range(len(ids)):
        row=dispatch(i,1)
        attempts.append(row)
        if row.get("kind")=="STOP":
            incomplete="EARLY_DISPATCH_STOP"
            break
        action=row["choice"]["action_id"]
        require(action in ids and action not in seen,"repeated or unauthorized action")
        seen.add(action)
        status=row.get("status")
        if status=="PROVED_CONDITIONAL":
            result=verify(i,row)
            if result.status!="PROVED_CONDITIONAL" or result.publication_eligible is not True:
                incomplete="INDEPENDENT_VERIFICATION_NOT_ACCEPTED"
                break
            accepted+=1
        elif status in {"ENVIRONMENT_ERROR","RESOURCE_EXHAUSTED"}:
            incomplete=status
            break
        else:
            require(status in {"TYPE_REJECTED_THIS_APPLICATION","UNRESOLVED","ADAPTER_REQUIRED"},
                    "unexpected native attempt disposition")
    if incomplete is None:
        require(seen==ids,"bounded menu attempt coverage incomplete")
        stop=dispatch(len(ids),0)
        require(stop.get("kind")=="STOP","explicit zero-budget terminal stop required")
        attempts.append(stop)
    if incomplete is not None:
        status="INCOMPLETE_EXECUTION"
    elif not batch["complete"]:
        status="INCOMPLETE_BOUNDED_RETRIEVAL"
    elif accepted:
        status="INDEPENDENT_CONDITIONAL_APPLICATIONS_RECORDED"
    elif ids:
        status="NO_KERNEL_ACCEPTED_APPLICATION_IN_ENUMERATED_MENU"
    else:
        status="NO_MATCH_IN_REVIEWED_GRAMMAR"
    return {"status":status,"incomplete_reason":incomplete,
            "candidate_count":len(ids),"attempted_action_ids":sorted(seen),
            "bounded_menu_complete":batch["complete"],
            "bounded_retrieval_disposition":batch["disposition"],
            "attempts":attempts,"independent_verified_conditional_applications":accepted}

def campaign(repo,output,target_id,reviewed_head,*,worker,parent_run,round4_run,type_run=None):
    """Explicitly selected exact-head governed lifecycle; no automatic theorem promotion."""
    from .gate import check
    from ..opica_composition import service
    from ..opica_composition.executor import worker_environment
    from ..opica_composition.snapshot import discover_source_paths,hash_inventory
    repo=Path(repo).resolve();admission=check(repo,require_clean=True)
    require(admission["checked_commit"]==reviewed_head,"explicitly selected source head differs")
    require(target_id in ALL_TARGET_IDS and worker.production,"reviewed signed target and production worker required")
    output=Path(output).resolve()
    require(not output.exists() and not output.is_relative_to(repo),"fresh external campaign directory required")
    native=Path(os.environ["OPICA_NATIVE_OUTPUT"]).resolve()
    require(output.is_relative_to(native),"campaign must use provisioned bounded native volume")
    output.mkdir(parents=True)
    qualified=authenticate_qualification(repo,parent_run,round4_run)
    require(target_id not in SCALAR_IDS or type_run is not None,"scalar targets require separately authenticated dual compiler review")
    review=authenticate_type_review(repo,type_run) if type_run is not None else None
    require(type_run is None or type_run not in {parent_run,round4_run},"separate compiler review execution required")
    (output/"qualification.json").write_bytes(canonical_bytes(qualified))
    paths=discover_source_paths(repo)|{"lean-toolchain","lake-manifest.json","lakefile.toml"}
    approved=ExperimentSpec("ROUND4_GOVERNED_DEDUCTION_V1",reviewed_head,
                            hash_inventory(repo,paths),
                            {"worker_environment":worker_environment(worker),
                             SELECTION:file_hash(repo/REGISTRY),QUALIFICATION:qualified,
                             **({TYPE_REVIEW:review} if review is not None else {})},"REVIEWED_FROZEN")
    (output/"experiment.json").write_bytes(approved.to_bytes())
    snap=service.freeze(repo,approved,output/"snapshot.json",worker=worker)
    inv=service.inventory(repo,snap,output/"inventory",worker=worker)
    budget=SearchBudget(**(worker.budget or {}))
    plan=service.plan(repo,snap,output/"inventory/inventory.json",target_id,output/"plan",budget=budget)
    journal=output/"journal.sqlite"
    def dispatch(index,credits):
        return service.run_one(repo,snap,output/"plan",journal,
                               output/("iteration-"+str(index)),worker=worker,budget=credits)
    def verify(index,row):
        result=service.verify(repo,snap,Path(row["receipt"]),output/("verified-"+str(index)),worker=worker)
        (output/("independent-verification-"+str(index)+".json")).write_bytes(result.to_bytes())
        return result
    bounded=run_bounded_menu(plan,dispatch,verify)
    replay=service.replay(repo,journal,output/"replay")
    views=service.export(repo,journal,output/"views")
    result={"schema":"OPICA_NEXT_GOVERNED_CAMPAIGN_V1","source_head":reviewed_head,
            "target":target_id,**bounded,"replay":replay["status"],"export":views,
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    (output/"campaign.json").write_bytes(canonical_bytes(result))
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--scalar-candidate",action="store_true")
    p.add_argument("--target",choices=ALL_TARGET_IDS)
    p.add_argument("--type-run")
    p.add_argument("--type-review-role",choices=REVIEW_ROLES)
    p.add_argument("--run-id")
    p.add_argument("--run-attempt",type=int)
    p.add_argument("--reviewed-head")
    p.add_argument("--parent-run")
    p.add_argument("--round4-run")
    a=p.parse_args()
    from .gate import REPO
    if a.type_review_role is not None:
        require(not a.scalar_candidate and a.target is None,"separate type-review execution required")
        r=review_types(REPO,a.output,a.type_review_role,a.run_id,a.run_attempt)
    elif a.scalar_candidate:
        require(a.target is None and a.reviewed_head is None,"scalar candidate is not an approved proof attempt")
        r=export_scalar_candidate(REPO,a.output)
    else:
        from ..opica_composition.cli import worker_from_environment
        require(a.target is not None and a.reviewed_head is not None,"explicit target/head required")
        r=campaign(REPO,a.output,a.target,a.reviewed_head,worker=worker_from_environment(),
                   parent_run=_run_id(a.parent_run),round4_run=_run_id(a.round4_run),
                   type_run=_run_id(a.type_run) if a.type_run else None)
    print(json.dumps({"schema":r["schema"],"status":r["status"],"RH":"OPEN","proof_acceptance":False}))
    if r["status"].startswith("INCOMPLETE_"):
        raise SystemExit(2)

if __name__=="__main__":
    main()
