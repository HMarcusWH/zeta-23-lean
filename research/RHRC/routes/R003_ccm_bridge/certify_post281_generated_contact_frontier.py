#!/usr/bin/env python3
"""Independent Arb replay for the frozen post-#281 selected neighborhoods."""
from __future__ import annotations
import argparse, json
from pathlib import Path
from canonical_contact_frontier_arb import certify_point

SCHEMA="POST281_GENERATED_CONTACT_ARB_v1"

def run(protocol:dict, discovery:dict)->dict:
    selected=discovery.get("selected_neighborhoods",[])
    rows=[]
    for cand in selected:
        L=cand.get("L")
        if L is None:
            L=(float(cand["L_left"])+float(cand["L_right"]))/2.0
        attempts=[]
        final=None
        for prec in protocol["arb"]["precision_bits"]:
            rec=certify_point(L,int(cand["Q"]),int(cand["K"]),int(prec))
            attempts.append(rec)
            final=rec
            if rec["spectral_regime"]!="PARITY_UNRESOLVED":
                sel=rec["even"] if rec["spectral_regime"]=="EVEN_STRICT" else rec["odd"]
                if sel.get("simple_status") in {"SIMPLE_GROUND_RESOLVED","CERTIFIED_ONE_DIMENSIONAL"}:
                    break
        rows.append({"candidate":cand,"attempts":attempts,"final":final,"contact_status":"NEAR_CONTACT_PROXY"})
    return {"schema_version":SCHEMA,"claim_cap":"EXPERIMENTAL_SIGNAL_ONLY","rows":rows,
      "summary":{"row_count":len(rows),"certified_spectral_count":sum(r["final"]["spectral_regime"]!="PARITY_UNRESOLVED" for r in rows),
      "contact_claimed":False,"terminal_claim":"RH_OPEN"}}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--protocol",required=True); ap.add_argument("--discovery",required=True); ap.add_argument("--output",required=True)
    a=ap.parse_args()
    p=json.loads(Path(a.protocol).read_text()); d=json.loads(Path(a.discovery).read_text())
    out=run(p,d); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out["summary"],indent=2,sort_keys=True))
    return 0
if __name__=="__main__": raise SystemExit(main())
