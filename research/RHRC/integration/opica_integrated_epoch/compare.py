"""Compare two fresh integrated candidate receipts; no production admission."""
import json
from pathlib import Path
import sys
from review import need, load, save, sha, HERE, CLAIMS

def compare(stock, independent):
    a,b=load(stock/"receipt.json"),load(independent/"receipt.json")
    need(a["status"]=="INTEGRATED_NATIVE_CANDIDATE_PASS_ONLY","Stock receipt not successful")
    need(b["status"]=="INTEGRATED_INDEPENDENT_CANDIDATE_PASS_ONLY","Independent receipt not successful")
    for k in ("head","tree","parent","overlays","source_sha256","root_count","axioms"):
        need(a[k]==b[k],"Integrated candidate mismatch: "+k)
    need(all(x[k]==v for x in (a,b) for k,v in CLAIMS.items()),"Receipt claim boundary")
    roots=load(HERE/"LOCK.json")["roots"]
    x,y=load(stock/"NATIVE_TYPE_CANDIDATES.json"),load(independent/"NATIVE_TYPE_CANDIDATES.json")
    need(x==y and [r["name"] for r in x]==roots,"Compiler type inventory differs")
    q=b["independent_full_closure"]
    need(q["status"]=="PASS_INDEPENDENT_SELECTED_NATIVE_CLOSURE_ONLY" and q["all_bound_inputs_rehashed"] is True,"Independent replay incomplete")
    need(len(q["selected_roots"])==len(set(q["selected_roots"]))==217 and set(roots)<=set(q["selected_roots"]),"Independent roots differ")
    return {"schema":"OPICA_INTEGRATED_DUAL_REVIEW_V1","status":"DUAL_NATIVE_CANDIDATE_PASS_ONLY","head":a["head"],"tree":a["tree"],"roots":roots,"stock_receipt_sha256":sha(stock/"receipt.json"),"independent_receipt_sha256":sha(independent/"receipt.json"),"types_sha256":sha(stock/"NATIVE_TYPE_CANDIDATES.json"),"historical_expected_type_review":"SEPARATE_ADMISSION_REQUIRED","full_round4_accepted":False,**CLAIMS}

if __name__=="__main__":
    save(Path(sys.argv[3]),compare(Path(sys.argv[1]),Path(sys.argv[2])))
