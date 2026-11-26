#!/usr/bin/env python3
"""Mechanical review packet, NOT canonical admission or RH promotion."""
import json, pathlib, sys
from receipts import verify, read_json, require, digest
from compare import compare
P=pathlib.Path
root,out=map(P,sys.argv[1:3])
modes=("smoke","leaf-pnt","leaf-gamma","leaf-operator","native","arithmetic","terminal","independent","comparator")
rows={mode:verify(root/mode,mode) for mode in modes}
sources=[read_json(root/m/"source.json") for m in modes]
lock=read_json(root/"source"/"source.json")
require(all(s==lock for s in sources),"qualification stages differ from source lock")
compare(root/"terminal",root/"independent")
types=read_json(root/"type-comparison"/"type-comparison.json")
require(types["status"]=="PASS" and types["common_sha256"]==digest(root/"native"/"public-types.json") and
        types["historical_sha256"]==digest(root/"historical"/"public-types.json"),"historical type receipt mismatch")
historical=read_json(root/"historical"/"historical.json")
require(historical["head"]==lock["head"] and historical["tree"]==lock["tree"] and
        historical["status"]=="PASS","historical identity mismatch")
packet={"schema":"OPICA_NATIVE_R2_CANONICAL_REVIEW_PACKET","claim":"RH_OPEN",
 "status":"READY_FOR_MANUAL_CANONICAL_REVIEW","head":lock["head"],"tree":lock["tree"],
 "source_sha256":digest(root/"source"/"source.json"),
 "qualification_sha256":{m:digest(root/m/"qualification.json") for m in modes},
 "type_comparison_sha256":digest(root/"type-comparison"/"type-comparison.json"),
 "historical_public_types_sha256":types["historical_sha256"],
 "open_admission_requirements":["Harvest all PR-attached historical workflows on exact current head/tree",
 "Independent semantic review of proof and mathematical assumptions",
 "Explicit canonical admission decision; do not automatically update claim registry"],
 "attribution":"Alpöge/Claude/Anthropic arithmetic source port; native direct C1 composition",
 "literal_energy_route":"OPEN","independent_arithmetic_invention":False}
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(packet,indent=2)+"\n")
print("NATIVE_R2_REVIEW_PACKET_READY; RH_OPEN")
