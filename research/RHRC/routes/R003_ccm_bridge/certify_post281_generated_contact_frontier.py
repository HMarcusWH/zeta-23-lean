#!/usr/bin/env python3
"""Independent Arb replay for the frozen post-#281 selected neighborhoods.

Sign-bracket candidates are checked at both endpoints and refined only while
both endpoint signs remain rigorous.  A certified sign bracket is a local-root
existence certificate when combined with the merged continuity theorem; it is
not automatically the first global boundary.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
from flint import arb, ctx
from canonical_contact_frontier_arb import certify_point, global_bottom_bounds, global_bottom_sign

SCHEMA="POST281_GENERATED_CONTACT_ARB_v1"

def exact_cell_point(Q:int, fraction:list[int], prec:int):
    ctx.prec=int(prec)
    j,den=int(fraction[0]),int(fraction[1])
    lo=arb(1)/512 if Q==1 else arb(Q).log()
    hi=arb(Q+1).log()
    return lo+(hi-lo)*arb(j)/den

def ladder_point(L,Q,K,precisions,*,fraction=None):
    attempts=[]
    final=None
    exact_spec=None
    last_L=float(L)
    for prec in precisions:
        if fraction is not None:
            Larg=exact_cell_point(int(Q),fraction,int(prec))
            last_L=float(Larg.mid())
            exact_spec={"Q":int(Q),"fraction":[int(fraction[0]),int(fraction[1])],
                        "left":"1/512" if int(Q)==1 else f"log({int(Q)})",
                        "right":f"log({int(Q)+1})"}
        else:
            Larg=float(L)
        rec=certify_point(Larg,int(Q),int(K),int(prec))
        attempts.append(rec); final=rec
        if global_bottom_sign(rec)!="UNRESOLVED":
            break
    return {"L":last_L,"exact_cell_spec":exact_spec,
            "attempts":attempts,"final":final,
            "global_bounds":global_bottom_bounds(final),
            "global_sign":global_bottom_sign(final)}

def midpoint_fraction(a:list[int],b:list[int])->list[int]:
    from math import gcd
    an,ad=int(a[0]),int(a[1]); bn,bd=int(b[0]),int(b[1])
    num=an*bd+bn*ad
    den=2*ad*bd
    g=gcd(abs(num),den)
    return [num//g,den//g]

def certify_bracket(cand, protocol):
    Q=int(cand["Q"]); K=int(cand["K"])
    precisions=protocol["arb"]["precision_bits"]
    cap=int(protocol["arb"]["root_or_subdivision_cap_per_neighborhood"])
    left=ladder_point(cand["L_left"],Q,K,precisions,
                      fraction=cand.get("fraction_left"))
    right=ladder_point(cand["L_right"],Q,K,precisions,
                       fraction=cand.get("fraction_right"))
    opposite={left["global_sign"],right["global_sign"]}=={"POSITIVE","NEGATIVE"}
    steps=[]
    if opposite:
        for _ in range(cap):
            lf=left.get("exact_cell_spec",{}).get("fraction") if left.get("exact_cell_spec") else None
            rf=right.get("exact_cell_spec",{}).get("fraction") if right.get("exact_cell_spec") else None
            if lf is not None and rf is not None:
                mf=midpoint_fraction(lf,rf)
                midL=(left["L"]+right["L"])/2.0
                mid=ladder_point(midL,Q,K,precisions,fraction=mf)
            else:
                midL=(left["L"]+right["L"])/2.0
                if not (left["L"] < midL < right["L"]):
                    break
                mid=ladder_point(midL,Q,K,precisions)
            steps.append(mid)
            if mid["global_sign"]=="UNRESOLVED":
                break
            if mid["global_sign"]==left["global_sign"]:
                left=mid
            elif mid["global_sign"]==right["global_sign"]:
                right=mid
            else:
                break
    status="CERTIFIED_SIGN_BRACKET" if opposite else "NEAR_CONTACT_PROXY"
    return {"candidate":cand,"left":left,"right":right,"refinement":steps,
            "final_bracket":[left["L"],right["L"]],
            "contact_status":status,
            "continuity_authority":"Zeta23.CCM.continuousOn_globalParitySuccessorBottom_Ioi",
            "first_boundary_claimed":False}

def run(protocol:dict, discovery:dict)->dict:
    selected=discovery.get("selected_neighborhoods",[])
    rows=[]
    for cand in selected:
        if "L_left" in cand and "L_right" in cand:
            rows.append(certify_bracket(cand,protocol))
            continue
        point=ladder_point(cand["L"],int(cand["Q"]),int(cand["K"]),
                           protocol["arb"]["precision_bits"],
                           fraction=cand.get("cell_fraction"))
        rows.append({"candidate":cand,"point":point,
                     "final":point["final"],
                     "contact_status":"NEAR_CONTACT_PROXY",
                     "first_boundary_claimed":False})
    certified=sum(r["contact_status"]=="CERTIFIED_SIGN_BRACKET" for r in rows)
    return {"schema_version":SCHEMA,"claim_cap":"EXPERIMENTAL_SIGNAL_ONLY","rows":rows,
      "summary":{"row_count":len(rows),"certified_sign_bracket_count":certified,
      "first_boundary_certified_count":0,
      "terminal_claim":"RH_OPEN"}}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--protocol",required=True); ap.add_argument("--discovery",required=True); ap.add_argument("--output",required=True)
    a=ap.parse_args()
    p=json.loads(Path(a.protocol).read_text()); d=json.loads(Path(a.discovery).read_text())
    out=run(p,d); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out["summary"],indent=2,sort_keys=True))
    return 0
if __name__=="__main__": raise SystemExit(main())
