#!/usr/bin/env python3
"""Export actual Lean compiler types in original OPICA LEAN_EXPR_DAG_V1 format.

No source text, handwritten type hash or proposal can approve a missing
arithmetic estimate. Output is a compiler-source provenance receipt ONLY.
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

import source_scope as policy
NAMESPACE="Zeta23.OPICARound6.NextSearch"
MODULE=NAMESPACE+".SourceEnergies"
DEFS=("PositiveRawSubpower","NegativeRawSubpower","OnePolarityRawSubpower")
THEOREMS=("rawPositiveEnergy_le_full_components","rawPositiveEnergy_le_of_component_budgets")
NAME=re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")

def export(output:Path):
    if output.exists():raise ValueError("Output must not exist")
    source=policy.check()
    names=[*( (NAMESPACE+"."+x,"value") for x in DEFS),
           *( (NAMESPACE+"."+x,"type") for x in THEOREMS)]
    for name,_ in names:
        if not NAME.fullmatch(name):raise ValueError("Bad registered name")
    text=("import "+MODULE+"\n"
          "import Zeta23.RHRC.OpicaComposition.Export\n"
          "set_option pp.fullNames true\nset_option pp.universes true\n")
    for name,kind in names:
        text+="run_cmd Zeta23.RHRC.OpicaComposition.exportTarget "+chr(96)+name+' "'+kind+'"\n'
    with tempfile.TemporaryDirectory(prefix="opica-typed-",dir=os.environ.get("RUNNER_TEMP")) as d:
        filename=Path(d)/"ExportTargets.lean"
        filename.write_text(text,encoding="utf-8")
        env={**os.environ,"LEAN_NUM_THREADS":"2","GIT_TERMINAL_PROMPT":"0"}
        run=subprocess.run(["lake","env","lean",str(filename)],cwd=policy.REPO,
                           capture_output=True,text=True,env=env,timeout=1800)
        if run.returncode:
            raise RuntimeError("Native Lean type exporter failed exit="+str(run.returncode)+
                               " stderr="+run.stderr[-2500:]+" stdout="+run.stdout[-2500:])
        payloads=[x.split("OPICA_TARGET\t",1)[1] for x in run.stdout.splitlines()
                  if "OPICA_TARGET\t" in x]
        if len(payloads)!=len(names):
            raise RuntimeError("Missing or extra Lean type DAG output")
        from research.RHRC.integration.opica_composition.inventory import expression_hash
        entries=[]
        for (name,kind),body in zip(names,payloads):
            expression=json.loads(body)
            if not isinstance(expression,str):
                raise ValueError("Lean DAG output is not a canonical string")
            h=expression_hash(expression)
            entries.append({"name":name,"kind":kind,"compiler_expression":expression,
                            "type_sha256":h})
        result={
            "schema":"OPICA_NATIVE_NEXT_TARGET_COMPILER_TYPES_V1",
            "status":"COMPILER_TYPE_EXPORT_NOT_THEOREM_PROOF",
            "head":source["head"],"tree":source["tree"],
            "toolchain":(policy.REPO/"lean-toolchain").read_text().strip(),
            "source_file_sha256":hashlib.sha256(
                (policy.REPO/"Zeta23/OPICARound6/NextSearch/SourceEnergies.lean").read_bytes()).hexdigest(),
            "entries":entries,"target_count":3,"conditional_consumer_count":2,
            "allowed_axioms":["propext","Classical.choice","Quot.sound"],
            "independent_checked_proof":"NOT_RUN_BY_THIS_EXPORT",
            "original_11_lane_acceptance":"NOT_RUN_BY_THIS_EXPORT",
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN"
        }
        output.parent.mkdir(parents=True,exist_ok=True)
        with output.open("x",encoding="utf-8") as f:
            json.dump(result,f,indent=2);f.write("\n")
        print(json.dumps({"status":result["status"],"types":len(entries),
                          "type_hashes":[x["type_sha256"] for x in entries],
                          "proof_acceptance":False}))
    return result
if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",required=True,type=Path)
    a=parser.parse_args()
    export(a.output.resolve())
