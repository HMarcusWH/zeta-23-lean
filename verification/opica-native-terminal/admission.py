#!/usr/bin/env python3
"""Mechanical review packet, NOT canonical admission or RH promotion."""
import json, pathlib, sys
from receipts import verify, read_json, require, digest, expect_text
from compare import compare, equal_checker_environment
from compare_type_surfaces import comparison
P=pathlib.Path
root,out=map(P,sys.argv[1:3])
modes=("smoke","checker-preflight","leaf-pnt","leaf-gamma","leaf-operator","leaf-analytic","native","arithmetic","terminal","independent","comparator")
rows={mode:verify(root/mode,mode) for mode in modes}
sources=[read_json(root/m/"source.json") for m in modes]
lock=read_json(root/"source"/"source.json")
expect_text(root/"source"/"source-lock-pass.txt","NATIVE_R5_SOURCE_LOCK_PASS")
scan=read_json(root/"source"/"compatibility-scan.json")
require(scan["schema"]=="NATIVE_R5_LEXICAL_COMPATIBILITY_SCAN" and
        scan["head"]==lock["head"] and scan["tree"]==lock["tree"] and
        scan["source_sha256"]==digest(root/"source"/"source.json") and
        scan["claim"]=="RH_OPEN" and scan["status"]=="ADVISORY_ONLY",
        "compatibility scan provenance mismatch")
require(all(s==lock for s in sources),"qualification stages differ from source lock")
compare(root/"terminal",root/"independent")
types=read_json(root/"type-comparison"/"type-comparison.json")
require(types==comparison(root/"historical"/"public-types.json",root/"native"/"public-types.json"),
        "recomputed type comparison differs")
equal_checker_environment(read_json(root/"checker-preflight"/"checker-environment.json"),
                          read_json(root/"comparator"/"checker-environment.json"))
require(types["schema"]=="NATIVE_R5_PUBLIC_TYPE_COMPARISON" and types["claim"]=="RH_OPEN" and
        types["status"]=="PASS" and not (types["missing"] or types["extra"] or types["changed"]) and
        types["common_count"]==len(read_json(root/"native"/"public-types.json")) and
        types["historical_count"]==len(read_json(root/"historical"/"public-types.json")) and
        types["common_count"]==types["historical_count"]>0 and
        types["common_sha256"]==digest(root/"native"/"public-types.json") and
        types["historical_sha256"]==digest(root/"historical"/"public-types.json"),"historical type receipt mismatch")
historical=read_json(root/"historical"/"historical.json")
require(historical["head"]==lock["head"] and historical["tree"]==lock["tree"] and
        historical["schema"]=="NATIVE_R5_HISTORICAL_TYPE_SURFACE" and
        historical["claim"]=="RH_OPEN" and historical["status"]=="PASS" and
        historical["toolchain"]=="leanprover/lean4:v4.33.0-rc2" and
        historical["mathlib"]=="51e6992efd06126df61a496bebf8f49482a4e129","historical identity mismatch")
packet={"schema":"OPICA_NATIVE_R5_CANONICAL_REVIEW_PACKET","claim":"RH_OPEN",
 "status":"READY_FOR_MANUAL_CANONICAL_REVIEW","head":lock["head"],"tree":lock["tree"],
 "source_sha256":digest(root/"source"/"source.json"),
 "compatibility_scan_sha256":digest(root/"source"/"compatibility-scan.json"),
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
print("NATIVE_R5_REVIEW_PACKET_READY; RH_OPEN")
