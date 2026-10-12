#!/usr/bin/env python3
"""WP4 D2=FULL: all-cell K3 both-parity interval certificate search.

Every accepted tile has a *rigorous lower bound* for the two Sylvester
quantities a and Delta=ad-b^2 on the actual K=3 legal parity carrier.
The old source-normalized 2nd-order enclosure is tried first; on a failed
tile we use ONLY the predeclared order-four Taylor fallback. Failure of
both means UNRESOLVED, not positivity and not an RH counterexample.

The end-cell rational enclosure extends a frozen-Q analytic formula slightly
beyond the exact irrational log seam; only its intersection with the physical
cutoff cell is used in the final mathematical conclusion. This preserves
source normalization and the complete prime-power seam convention.

The generated JSON is bounded research evidence; no Lean theorem consumes
it as an unconditional premise.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent),str(HERE.parent/"post285")]
import canonical_source_arb as C
from post285_m51_k2_even_bottom_certificate import cell_bounds
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as M012)
from post166_fb05_cell_interval import _arb_matrix_from_sympy
from post169_fb05_schur_visibility import one_step_geometry
from wp4_k3_fourth_order_fallback import (
    Q,check_box,coeffs_of_a_and_delta,compressed_jets)


# Freeze the source implementations on which every interval enclosure depends.
SOURCE_INPUTS = [
    "research/RHRC/routes/R003_ccm_bridge/post287/wp4_k3_full_continuum.py",
    "research/RHRC/routes/R003_ccm_bridge/post287/wp4_k3_fourth_order_fallback.py",
    "research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py",
    "research/RHRC/routes/R003_ccm_bridge/post194_fb05_q14_fixed_unit_second_derivative.py",
    "research/RHRC/routes/R003_ccm_bridge/post169_fb05_schur_visibility.py",
]
REPO_ROOT = HERE.parents[4]

def source_input_digests() -> dict:
    return {path: hashlib.sha256((REPO_ROOT / path).read_bytes()).hexdigest()
            for path in SOURCE_INPUTS}

END=Fraction(2772588722239782,10**15)
START=Fraction(1,512)


def interval_bounds(Qcell:int)->tuple[Fraction,Fraction]:
    a,b=cell_bounds(Qcell)
    if Qcell==1:a=START
    if Qcell==15:
        if not bool(Q(END)>arb(16).log()):
            raise AssertionError("endpoint not above exact log 16")
        b=END
    assert a<b
    return a,b


def second_order_lower(c:arb,r:arb,cell:int,parity:str)->tuple[arb,arb]:
    geom=one_step_geometry(2,parity)
    B=_arb_matrix_from_sympy(geom.step_basis_exact)
    def project(M):
        return B.transpose()*M*B
    # Point data suffice for Δ(c) and Δ'(c), but NOT Δ''(x).
    # The latter must use rigorously interval-enclosed a,b,d and their
    # first and second jets at EVERY x in the whole tile.  Reusing the
    # centre a,b,d in the second derivative is a false enclosure and can
    # silently certify a negative determinant; never do that.
    M,Mp,_=M012(c,3,cell)
    Mi,Mpi,Mppi=M012(arb(c,r),3,cell)
    H,Hp=project(M),project(Mp)
    Hi,Hpi,Hppi=project(Mi),project(Mpi),project(Mppi)
    a,b,d=H[0,0],H[0,1],H[1,1]
    da,db,dd=Hp[0,0],Hp[0,1],Hp[1,1]
    ai,bi,di=Hi[0,0],Hi[0,1],Hi[1,1]
    dai,dbi,ddi=Hpi[0,0],Hpi[0,1],Hpi[1,1]
    d2a,d2b,d2d=Hppi[0,0],Hppi[0,1],Hppi[1,1]
    det=a*d-b*b
    dp=da*d+a*dd-2*b*db
    dpp=d2a*di+2*dai*ddi+ai*d2d-2*dbi*dbi-2*bi*d2b
    lower_a=(a-abs(da).upper()*r +
             min(arb(0),d2a.lower())*r*r/2).lower()
    lower_d=(det-abs(dp).upper()*r +
             min(arb(0),dpp.lower())*r*r/2).lower()
    return lower_a,lower_d


def evaluate(tile,parity,cell,method):
    lo,hi=tile
    c,r=(lo+hi)/2,(hi-lo)/2
    if method=="SECOND":
        lower_a,lower_delta=second_order_lower(Q(c),Q(r),cell,parity)
        return {"method":method,"a":C.ball_record(lower_a,36),
                "delta":C.ball_record(lower_delta,36),
                "accepted":bool(lower_a>0 and lower_delta>0)}
    row=check_box(Q(c),Q(r),cell,parity,allow_frozen_extension=True)
    return {"method":"FOURTH","a":row["a_lower"],
            "delta":row["delta_lower"],
            "accepted":row["verdict"]=="PASS"}


def cover(cell:int,parity:str,max_depth:int,max_nodes:int,deadline:float):
    lo,hi=interval_bounds(cell)
    queue=[(lo,hi,0)]
    accepted=[];unresolved=[];processed=0
    while queue:
        l,r,depth=queue.pop()
        if processed>=max_nodes or time.monotonic()>=deadline:
            unresolved += [{"left":[a.numerator,a.denominator],
                            "right":[b.numerator,b.denominator],
                            "depth":d,"reason":"RESOURCE_LIMIT"}
                           for a,b,d in [(l,r,depth),*queue]]
            break
        processed+=1
        try:
            result=evaluate((l,r),parity,cell,"SECOND")
            if not result["accepted"]:
                result=evaluate((l,r),parity,cell,"FOURTH")
        except Exception as exc:
            result={"accepted":False,"method":"FOURTH",
                    "error":repr(exc)}
        if result["accepted"]:
            accepted.append({"left":[l.numerator,l.denominator],
                             "right":[r.numerator,r.denominator],
                             "depth":depth,**result})
        elif depth>=max_depth:
            unresolved.append({"left":[l.numerator,l.denominator],
                               "right":[r.numerator,r.denominator],
                               "depth":depth,"candidate":result,
                               "reason":"UNCERTIFIED_SIGN"})
        else:
            m=(l+r)/2
            queue.extend([(m,r,depth+1),(l,m,depth+1)])
    accepted.sort(key=lambda x:Fraction(*x["left"]))
    return {"Q":cell,"parity":parity,
            "left":[lo.numerator,lo.denominator],
            "right":[hi.numerator,hi.denominator],
            "tested_nodes":processed,"accepted":accepted,
            "unresolved":unresolved,
            "status":"PASS" if not unresolved else "UNRESOLVED"}


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--cells",default="1-15")
    p.add_argument("--parities",default="even,odd")
    p.add_argument("--precision-bits",type=int,default=192)
    p.add_argument("--max-depth",type=int,default=32)
    p.add_argument("--max-nodes",type=int,default=2500)
    p.add_argument("--seconds",type=int,default=20000)
    args=p.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    args.out.mkdir(parents=True,exist_ok=True)
    a,_,b=args.cells.partition("-")
    cells=list(range(int(a),int(b or a)+1))
    parities=args.parities.split(",")
    if any(x not in ("even","odd") for x in parities):raise ValueError("parity")
    deadline=time.monotonic()+args.seconds
    records=[]
    for cell in cells:
        for parity in parities:
            row=cover(cell,parity,args.max_depth,args.max_nodes,deadline)
            file=f"k3_Q{cell:02d}_{parity}.json"
            raw=(json.dumps(row,sort_keys=True,indent=2)+"\n").encode()
            (args.out/file).write_bytes(raw)
            records.append({"cell":cell,"parity":parity,"file":file,
                            "sha256":hashlib.sha256(raw).hexdigest(),
                            "status":row["status"],
                            "intervals":len(row["accepted"]),
                            "unresolved_count":len(row["unresolved"])})
            print(json.dumps(records[-1]),flush=True)
    passed=(cells==list(range(1,16)) and
            set(parities)=={"even","odd"} and
            len(records)==30 and all(x["status"]=="PASS" for x in records))
    manifest={"schema":"post287.wp4.k3-full-continuum.v1",
              "status":"INTERVAL_EVIDENCE" if passed else "UNRESOLVED",
              "terminal_claim":"RH_OPEN",
              "scope":"K3 even+odd across [1/512,log16]" if passed
                       else "only intervals separately listed as accepted",
              "source":"complete fixed-Q Eq4.4, 7x7, two-dimensional legal carriers",
              "method":"validated second order, fixed fourth order fallback",
              "note":"cutoff-Q analytic extensions checked on rational seam covers",
              "precision_bits":args.precision_bits,
              "source_digests":source_input_digests(),
              "source_commit":subprocess.check_output(["git","rev-parse","HEAD"],
                         cwd=REPO_ROOT,text=True).strip(),
              "records":records,
              "all_L_positivity_certified":passed,
              "not_a_lean_proof":True,
              "not_a_proof_of_RH":True}
    (args.out/"manifest.json").write_text(json.dumps(manifest,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":manifest["status"],
                      "layers":len(records),"RH":"OPEN"}))
    return 0 if passed else 2


if __name__=="__main__":
    raise SystemExit(main())
