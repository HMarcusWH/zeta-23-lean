#!/usr/bin/env python3
"""Independent fail-closed Arb replay for frozen post-#281 neighborhoods."""
from __future__ import annotations
import argparse, json, math
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx
from canonical_contact_frontier_arb import (
    certify_point, global_bottom_bounds, global_bottom_sign,
)

SCHEMA="POST281_GENERATED_CONTACT_ARB_v1"
ALLOWED_K={2,3,4,5,6}


def fail(code:str,msg:str):
    raise ValueError(f"{code}: {msg}")


def require_int(value,name):
    if isinstance(value,bool) or not isinstance(value,int):
        fail("INVALID_INTEGER",f"{name} must be an integer")
    return value


def require_fraction(value,name):
    if not (isinstance(value,list) and len(value)==2):
        fail("INVALID_FRACTION",f"{name} must be [numerator,denominator]")
    n=require_int(value[0],name+" numerator")
    d=require_int(value[1],name+" denominator")
    if d<=0 or n<=0 or n>=d:
        fail("INVALID_FRACTION",f"{name} must satisfy 0<n<d")
    return [n,d]


def validate_candidate(cand, *, bracket:bool):
    if not isinstance(cand,dict):
        fail("INVALID_CANDIDATE","candidate must be an object")
    Q=require_int(cand.get("Q"),"Q")
    K=require_int(cand.get("K"),"K")
    if not 1<=Q<=64: fail("OUT_OF_SCOPE",f"Q={Q}")
    if K not in ALLOWED_K: fail("OUT_OF_SCOPE",f"K={K}")
    if cand.get("model","CANONICAL")!="CANONICAL":
        fail("MODEL_MISMATCH","Arb contact certifier accepts canonical candidates only")
    if bracket:
        lf=require_fraction(cand.get("fraction_left"),"fraction_left")
        rf=require_fraction(cand.get("fraction_right"),"fraction_right")
        if not Fraction(*lf)<Fraction(*rf):
            fail("REVERSED_BRACKET","left exact coordinate must precede right")
    else:
        require_fraction(cand.get("cell_fraction"),"cell_fraction")
    return Q,K


def exact_cell_point(Q:int,fraction:list[int],prec:int):
    fraction=require_fraction(fraction,"cell fraction")
    ctx.prec=int(prec)
    j,den=fraction
    lo=arb(1)/512 if Q==1 else arb(Q).log()
    hi=arb(Q+1).log()
    return lo+(hi-lo)*arb(j)/den


def _j1_resolved(rec:dict)->bool:
    regime=rec.get("spectral_regime")
    sector = rec.get("even") if regime=="EVEN_STRICT" else rec.get("odd") if regime=="ODD_STRICT" else None
    if not isinstance(sector,dict):
        return False
    j1=sector.get("j1")
    return isinstance(j1,dict) and all(k in j1 for k in ("certified_positive","certified_negative"))


def _point_resolution(rec:dict)->dict:
    return {
        "ground_sign":global_bottom_sign(rec),
        "j1_resolved":_j1_resolved(rec),
    }


def ladder_point(Q,K,precisions,*,fraction):
    attempts=[]; final=None; exact_spec=None; last_L=None
    fraction=require_fraction(fraction,"fraction")
    for prec in precisions:
        Larg=exact_cell_point(Q,fraction,int(prec))
        last_L=float(Larg.mid())
        exact_spec={
            "Q":Q,"K":K,"fraction":fraction,
            "left":"1/512" if Q==1 else f"log({Q})",
            "right":f"log({Q+1})",
        }
        rec=certify_point(Larg,Q,K,int(prec))
        attempts.append(rec); final=rec
        resolution=_point_resolution(rec)
        if resolution["ground_sign"]!="UNRESOLVED" and resolution["j1_resolved"]:
            break
    return {
        "L":last_L,
        "exact_cell_spec":exact_spec,
        "attempts":attempts,
        "final":final,
        "global_bounds":global_bottom_bounds(final),
        "global_sign":global_bottom_sign(final),
        "resolution":_point_resolution(final),
    }


def midpoint_fraction(a:list[int],b:list[int])->list[int]:
    m=(Fraction(*a)+Fraction(*b))/2
    return [m.numerator,m.denominator]


def certify_bracket(cand,protocol):
    Q,K=validate_candidate(cand,bracket=True)
    precisions=protocol["arb"]["precision_bits"]
    cap=require_int(protocol["arb"]["root_or_subdivision_cap_per_neighborhood"],"subdivision cap")
    left=ladder_point(Q,K,precisions,fraction=cand["fraction_left"])
    right=ladder_point(Q,K,precisions,fraction=cand["fraction_right"])
    opposite={left["global_sign"],right["global_sign"]}=={"POSITIVE","NEGATIVE"}
    steps=[]
    if opposite:
        for _ in range(cap):
            lf=left["exact_cell_spec"]["fraction"]
            rf=right["exact_cell_spec"]["fraction"]
            mf=midpoint_fraction(lf,rf)
            if not Fraction(*lf)<Fraction(*mf)<Fraction(*rf):
                break
            mid=ladder_point(Q,K,precisions,fraction=mf)
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
    return {
        "candidate":cand,"left":left,"right":right,"refinement":steps,
        "final_bracket_exact":[
            left["exact_cell_spec"]["fraction"],
            right["exact_cell_spec"]["fraction"],
        ],
        "final_bracket":[left["L"],right["L"]],
        "contact_status":status,
        "continuity_authority":"Zeta23.CCM.continuousOn_globalParitySuccessorBottom_Ioi",
        "first_boundary_claimed":False,
    }


def certify_generic_controls(controls:list[dict])->list[dict]:
    """Exact qualification of synthetic polynomial controls.

    They exercise contact-status semantics but never inherit canonical arithmetic.
    """
    out=[]
    for row in controls:
        name=row.get("control_name")
        samples=row.get("samples")
        if not isinstance(samples,list) or len(samples)<3:
            fail("BAD_CONTROL",f"{name}: missing samples")
        left,right=samples[0],samples[-1]
        gl=float(left["global_bottom"]); gr=float(right["global_bottom"])
        opposite=(gl<0<gr) or (gr<0<gl)
        status="CERTIFIED_SIGN_BRACKET" if opposite else "NO_SIGN_CHANGE"
        out.append({
            "control_name":name,
            "model":"GENERIC_SYNTHETIC",
            "contact_status":status,
            "canonical_arithmetic_authority":False,
            "qualification_pass": (
                status=="CERTIFIED_SIGN_BRACKET"
                if name in {"TRANSVERSE_CROSSING","STATIONARY_CUBIC_CROSSING","ODD_SELECTED_REFLECTION","SMALLEST_COMPLEMENT"}
                else status=="NO_SIGN_CHANGE"
            ),
        })
    return out


def run(protocol:dict,discovery:dict)->dict:
    selected=discovery.get("selected_neighborhoods")
    if not isinstance(selected,list) or not selected:
        fail("EMPTY_SELECTION","selected_neighborhoods must be nonempty")
    rows=[]
    for cand in selected:
        if "L_left" in cand or "L_right" in cand:
            rows.append(certify_bracket(cand,protocol))
        else:
            Q,K=validate_candidate(cand,bracket=False)
            point=ladder_point(Q,K,protocol["arb"]["precision_bits"],fraction=cand["cell_fraction"])
            rows.append({
                "candidate":cand,"point":point,"final":point["final"],
                "contact_status":"NEAR_CONTACT_PROXY","first_boundary_claimed":False,
            })
    controls=certify_generic_controls(discovery.get("generic_controls",[]))
    if controls and not all(c["qualification_pass"] for c in controls):
        fail("CONTROL_QUALIFICATION_FAILED","a generic known control was misclassified")
    certified=sum(r["contact_status"]=="CERTIFIED_SIGN_BRACKET" for r in rows)
    return {
        "schema_version":SCHEMA,"claim_cap":"EXPERIMENTAL_SIGNAL_ONLY",
        "rows":rows,"generic_control_certificates":controls,
        "summary":{
            "row_count":len(rows),
            "generic_control_count":len(controls),
            "certified_sign_bracket_count":certified,
            "first_boundary_certified_count":0,
            "terminal_claim":"RH_OPEN",
        },
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--protocol",required=True)
    ap.add_argument("--discovery",required=True)
    ap.add_argument("--output",required=True)
    a=ap.parse_args()
    p=json.loads(Path(a.protocol).read_text())
    d=json.loads(Path(a.discovery).read_text())
    try:
        out=run(p,d)
    except (ValueError,KeyError,TypeError) as exc:
        raise SystemExit(f"post281 generated-contact certifier: {exc}")
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out["summary"],indent=2,sort_keys=True))
    return 0
if __name__=="__main__": raise SystemExit(main())
