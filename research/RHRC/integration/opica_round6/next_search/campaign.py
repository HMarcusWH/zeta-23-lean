#!/usr/bin/env python3
"""OPICA native source-qualified compiler-DAG search (NO proof promotion).

Freshly exports the reviewed finite source theorems and three OPEN signed
subpower Prop targets with the SAME compiler as the native source. Calls the
ORIGINAL OPICA inventory, restricted proposer and DAG retrieval. A candidate
is not an accepted theorem without a new source-epoch native kernel+independent
consumer run. No RH or RH-equivalent source constant is admitted.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import source_scope as scope

NAMESPACE = "Zeta23.OPICARound6.NextSearch"
MODULE = NAMESPACE+".SourceEnergies"
THEOREMS = ("rawPositiveEnergy_le_full_components",
            "rawPositiveEnergy_le_of_component_budgets")
TARGETS = ("PositiveRawSubpower","NegativeRawSubpower",
           "OnePolarityRawSubpower")
FORBIDDEN = (
 "_root_.riemannHypothesis",
 "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_riemannHypothesis",
 "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_cofinal_moment_slice_bounds",
 "Zeta23.OPICAComposition.cofinal_newborn_packet_calibration",
 "Zeta23.OPICAComposition.cofinal_schur_packet_calibration",
)
ALLOWED_AXIOMS = {"propext","Classical.choice","Quot.sound"}

def require(ok, why):
    if not ok:raise ValueError(why)
def source_json(name):
    return json.loads((Path(__file__).resolve().parent/name).read_text())
def compiler_run(text):
    with tempfile.TemporaryDirectory(prefix="opica-next-search-",dir=os.environ.get("RUNNER_TEMP")) as d:
        target=Path(d)/"NativeSearchAtlas.lean"
        target.write_text(text,encoding="utf-8")
        env=dict(os.environ)
        env.update({"LEAN_NUM_THREADS":"2","GIT_TERMINAL_PROMPT":"0"})
        run=subprocess.run(["lake","env","lean",str(target)],cwd=scope.REPO,
                           capture_output=True,text=True,env=env,timeout=1800)
        require(run.returncode==0,"Fresh exact Lean atlas export failed: "+
                (run.stdout[-1000:]+run.stderr[-1000:]))
        require(len(run.stdout)<80_000_000,"Native compiler export log too large")
        return run.stdout.encode("utf-8")

def read_exports(data,load):
    proofs=[];statements={};target=[]
    for line in data.splitlines():
        if line.startswith(b"OPICA3_ATLAS\t"):
            row=load(line.split(b"\t",1)[1])
            require(row["declaration"] not in statements,"Repeated compiler theorem export")
            statements[row["declaration"]]=row
        elif line.startswith(b"OPICA_TARGET\t"):
            target.append(load(line.split(b"\t",1)[1]))
        elif line.startswith(b"OPICA_RETRIEVAL_PROOFS\t"):
            proofs.append(load(line.split(b"\t",1)[1]))
    require(len(statements)==len(THEOREMS) and len(target)==len(TARGETS)
            and len(proofs)==len(THEOREMS)+len(TARGETS),
            "Original Lean compiler did not export complete source/target set")
    return statements,target,proofs

def classify_unverified_proposals(candidates):
    """Label seed constants versus nontrivial plans without theorem promotion.

    This function does NOT type-check or kernel-check the retrieved plans.
    The original enumerate_candidates menu, budget and historical receipts
    are intentionally unchanged.
    """
    require(type(candidates) is list, "closed proposal list required")
    bare=structured=rejected=0
    for row in candidates:
        require(type(row) is dict and row.get("kernel_acceptance") is False,
                "retrieval cannot contain a kernel-accepted theorem")
        if row.get("status")=="REJECTED_UNAPPROVED_CONSTANT":
            rejected+=1
            continue
        require(row.get("status")=="PROPOSED_NOT_KERNEL_CHECKED"
                and type(row.get("term_plan")) is dict,
                "unknown proposed candidate disposition")
        if row["term_plan"].get("tag")=="const":
            bare+=1
        else:
            structured+=1
    return {
        "schema":"OPICA_NEXT_SOURCE_CANDIDATE_COUNTS_V2",
        "bare_approved_source_constant_seeds":bare,
        "unverified_nontrivial_composition_plans":structured,
        "rejected_before_kernel":rejected,
        "kernel_accepted_target_proofs":0,
        "research_disposition":("SEED_ONLY_NO_NEW_COMPOSITION" if
                                  structured==0 else
                                  "UNVERIFIED_COMPOSITION_PLANS_PRESENT"),
    }

def campaign(output:Path):
    require(not output.exists(),"Do not overwrite previous research result")
    s=scope.check()
    require(s["status"] in {"PASS_ADDITIVE_SOURCE_BYTES_ONLY",
                            "PASS_REVIEWED_COMBINED_EPOCH_V1"},
            "Native source scope not independently qualified")
    types=source_json("SOURCE_CONTRACTS.json")
    require(types["status"]=="PENDING_FRESH_COMPILER_EXPORT"
            and types["handwritten_expected_type_sha256"] is None,
            "Search type authority changed from compiler to handwritten source")
    target_names=[NAMESPACE+"."+x for x in TARGETS]
    theorem_names=[NAMESPACE+"."+x for x in THEOREMS]
    sys.path.insert(0,str(scope.REPO))
    from research.RHRC.integration.opica_composition.qualification import atlas_driver
    from research.RHRC.integration.opica_composition.executor import lean_name
    from research.RHRC.integration.opica_composition.canonical import load_bytes, digest
    from research.RHRC.integration.opica_composition.inventory import expression_hash
    from research.RHRC.integration.opica_composition.contracts import (
        StatementContract,StatementInventory,TargetSpec,GrammarProfile,
        SearchBudget,PER_ATTEMPT_GATES)
    from research.RHRC.integration.opica_composition.proposals import (
        enumerate_candidates,used_constant_ids)

    rows=[{"declaration":name,"module":MODULE} for name in theorem_names]
    prefix=(f"import {MODULE}\n"
            +"import Zeta23.RHRC.OpicaComposition.Export\n"+atlas_driver(rows))
    for name in theorem_names:
        prefix+="\nrun_cmd Zeta23.RHRC.OpicaComposition.exportRetrievalProofConstants "+chr(96)+lean_name(name)+' "type"\n'
    for name in target_names:
        prefix+="\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget "+chr(96)+lean_name(name)+' "value"\n'
        prefix+="run_cmd Zeta23.RHRC.OpicaComposition.exportRetrievalProofConstants "+chr(96)+lean_name(name)+' "value"\n'
    data=compiler_run(prefix)
    statements,targets,proofs=read_exports(data,load_bytes)
    require(set(statements)==set(theorem_names),"Native approved theorem set changed")
    generation=digest({"current_head":s["head"],"current_tree":s["tree"],
                      "compiler_exports_sha256":hashlib.sha256(data).hexdigest(),
                      "source_sha256":hashlib.sha256(
                         (scope.REPO/"Zeta23/OPICARound6/NextSearch/SourceEnergies.lean").read_bytes()).hexdigest()},
                      domain="OPICA_NEXT_NATIVE_TYPED_RESEARCH_GENERATION_V1")
    typed=[]
    constants={}
    table=[]
    for i,name in enumerate(theorem_names):
        row=statements[name]
        require(row["module"]==MODULE,"Theorem origin does not match original source")
        require(set(row["axioms"])<=ALLOWED_AXIOMS,"Extra unapproved transitive theorem axiom")
        require(not any(bad in row["value_constants"] for bad in FORBIDDEN),
                "A forbidden RH or C1 theorem was imported as a source")
        require(type(proofs[i]) is list,"Native source proof-erasure inventory missing")
        record=StatementContract(
            declaration=row["declaration"],module=row["module"],
            type_expression=row["type_expression"],
            type_sha256=expression_hash(row["type_expression"]),
            universe_parameters=row["universe_parameters"],
            outer_telescope=row["outer_telescope"],
            conclusion_text=row["conclusion_text"],
            type_constants=row["type_constants"],
            value_constants=row["value_constants"],axioms=row["axioms"])
        typed.append(record)
        cid=digest({"source_generation":generation,
                    "declaration":name,"module":MODULE},
                   domain="OPICA_APPROVED_CONSTANT_V1")
        constants[cid]=name
        table.append({"id":cid,"declaration":name,"module":MODULE,"role":"constant"})
    # StatementInventory is a canonical JSON evidence record, not a Python
    # object container. Preserve validated source types in `typed` locally,
    # but seal only their full closed dictionaries in the original codec.
    inv=StatementInventory(generation,[record.to_dict() for record in typed],
                           hashlib.sha256(data).hexdigest())
    budget=SearchBudget(candidates=8,term_nodes=512,term_depth=16,
                        wall_seconds=90,heartbeats=800000)
    results=[]
    for i,name in enumerate(target_names):
        expected=targets[i]
        require(type(proofs[len(THEOREMS)+i]) is list,"Missing target proof constant inventory")
        target=TargetSpec(
            TARGETS[i],name,MODULE,expression_hash(expected),constants,
            sorted(ALLOWED_AXIOMS),[MODULE],list(PER_ATTEMPT_GATES),"value",list(FORBIDDEN))
        contract={"expected_expression":expected,
                  "statements":[{**x.to_dict(),"proof_constants":proofs[j]}
                                for j,x in enumerate(typed)],
                  "proof_constants":proofs[len(THEOREMS)+i]}
        batch=enumerate_candidates(inv,target,GrammarProfile(list(FORBIDDEN),[]),
                                   budget,search_contract=contract)
        candidates=[]
        for item in batch.candidates:
            approved=used_constant_ids(item["term_plan"])
            if not set(approved)<=set(constants):
                candidates.append({"status":"REJECTED_UNAPPROVED_CONSTANT",
                    "action_id":item.get("action_id"),"kernel_acceptance":False})
                continue
            candidates.append({"status":"PROPOSED_NOT_KERNEL_CHECKED",
                "action_id":item["action_id"],"term_plan":item["term_plan"],
                "used_theorems":sorted(constants[c] for c in approved),
                "kernel_acceptance":False})
        # Versioned research-only accounting. enumerate_candidates appends the
        # permitted bare source constants even when no genuine composition is
        # retrieved; never report those seeds as new arithmetic proofs.
        counts=classify_unverified_proposals(candidates)
        results.append({
            "target":name,"exact_type_sha256":target.expected_type_hash,
            "compiler_type_dag":expected,
            "candidate_count":len(candidates),"candidates":candidates,
            "candidate_classification_v2":counts,
            "bounded_disposition":batch.disposition,"bounded_menu_complete":batch.complete,
            "native_kernel_attempt":"NOT_RUN_BY_RETRIEVAL","independent_replay":"NOT_RUN"})
    result={
      "schema":"OPICA_NEXT_SOURCE_NATIVE_COMPILER_DAG_SEARCH_V1",
      "status":"RESEARCH_RETRIEVAL_COMPLETE_NOT_THEOREM",
      "source_head":s["head"],"source_tree":s["tree"],
      "compiler_export_sha256":hashlib.sha256(data).hexdigest(),
      "source_theorem_type_hashes":{x.declaration:x.type_sha256 for x in typed},
      "reviewed_constant_table":table,"targets":results,
      "frozen_prior_target_registry":"UNCHANGED",
      "full_round4_11_lane_gate":"NOT_RUN",
      "formal_kernel_proof":"NOT_ESTABLISHED_BY_THIS_SEARCH",
      "rh_premises_allowed":False,
      "proof_acceptance":False,"RH":"OPEN","Step4":"OPEN"
    }
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open("x",encoding="utf-8") as file:
        json.dump(result,file,indent=2);file.write("\n")
    print(json.dumps({"status":result["status"],
                      "candidate_counts":{x["target"]:x["candidate_count"] for x in results},
                      "proof_acceptance":False,"RH":"OPEN"}),flush=True)
    return result

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path,required=True)
    a=p.parse_args()
    campaign(a.output.resolve())
