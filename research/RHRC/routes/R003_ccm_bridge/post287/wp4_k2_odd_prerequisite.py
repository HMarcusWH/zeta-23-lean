#!/usr/bin/env python3
"""WP4 prerequisite: complete K2 ODD scalar-bottom interval certificate.

The one-dimensional legal odd carrier is (1,-2,0,2,-1), norm^2=10.
The source is the exact production fixed-Q canonicalSourceMatrix, and
second-order Taylor bounds use the already-validated #194 analytic jets.

This certifies ONLY its explicit finite interval [1/512,log16] if every
cell covers without unresolved tiles. It is independent of K2 even M51
and cannot be identified with a K3 determinant without the basis theorem.
"""
from __future__ import annotations
import argparse,hashlib,json,sys
from fractions import Fraction
from pathlib import Path

from flint import arb,ctx
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent),str(HERE.parent/"post285")]
import canonical_source_arb as C
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets)
from wp2_k2_even_transcript import verified_cell_bounds

V=(1,-2,0,2,-1)
NORM2=10
START=Fraction(1,512)


def q(x:Fraction)->arb:
    return C.to_arb_rational(x.numerator,x.denominator)


def energy(M):
    return sum(V[i]*M[i,j]*V[j]
               for i in range(5) for j in range(5))/NORM2


def bound(c:Fraction,r:Fraction,Q:int)->dict:
    M,Mp,_=jets(q(c),2,Q)
    _,_,Mpp=jets(arb(q(c),q(r)),2,Q)
    f,g,h=energy(M),energy(Mp),energy(Mpp)
    rr=q(r)
    lower=(f-abs(g).upper()*rr+
           min(arb(0),h.lower())*rr*rr/2).lower()
    return {"centre":[c.numerator,c.denominator],
            "radius":[r.numerator,r.denominator],
            "value":C.ball_record(f,36),
            "first":C.ball_record(g,36),
            "curvature":C.ball_record(h,36),
            "lower":C.ball_record(lower,36),
            "positive":bool(lower>0)}


def cell_interval(Q:int)->tuple[Fraction,Fraction]:
    a,b=verified_cell_bounds(Q)
    if Q==1:a=START
    return a,b


def cover(Q:int,depth_limit:int,max_tiles:int):
    a,b=cell_interval(Q)
    stack=[(a,b,0)];okay=[];failed=[];count=0
    while stack:
        x,y,d=stack.pop();count+=1
        if count>max_tiles:
            failed.extend({"left":[u.numerator,u.denominator],
                           "right":[v.numerator,v.denominator],
                           "depth":k,"reason":"RESOURCE_LIMIT"}
                          for u,v,k in [(x,y,d),*stack])
            break
        c,r=(x+y)/2,(y-x)/2
        try:
            result=bound(c,r,Q)
        except Exception as e:
            result={"positive":False,"error":repr(e)}
        if result["positive"]:
            okay.append({"left":[x.numerator,x.denominator],
                         "right":[y.numerator,y.denominator],
                         **result})
        elif d>=depth_limit:
            failed.append({"left":[x.numerator,x.denominator],
                           "right":[y.numerator,y.denominator],
                           "reason":"UNRESOLVED","probe":result})
        else:
            stack.extend([(c,y,d+1),(x,c,d+1)])
    okay.sort(key=lambda row:Fraction(*row["left"]))
    return {"Q":Q,"parity":"odd",
            "left":[a.numerator,a.denominator],
            "right":[b.numerator,b.denominator],
            "accepted":okay,"unresolved":failed,
            "status":"PASS" if not failed else "UNRESOLVED"}


def verify(directory:Path,precision:int):
    C.set_precision(precision);ctx.prec=precision
    obj=json.loads((directory/"manifest.json").read_text())
    assert obj["terminal_claim"]=="RH_OPEN"
    assert precision>obj["precision_bits"]
    assert obj["status"]=="INTERVAL_EVIDENCE"
    covered=0
    for row in obj["records"]:
        Q=row["Q"];file=directory/row["file"]
        raw=file.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=row["sha256"]:
            raise AssertionError(("sha256",str(file)))
        data=json.loads(raw)
        if data["unresolved"]:raise AssertionError(("unresolved",Q))
        cursor,hi=cell_interval(Q)
        for t in data["accepted"]:
            lo=Fraction(*t["left"]);up=Fraction(*t["right"])
            if lo!=cursor or not lo<up:raise AssertionError(("gap",Q,lo,up))
            c,r=(lo+up)/2,(up-lo)/2
            if not bound(c,r,Q)["positive"]:
                raise AssertionError(("fresh enclosure failed",Q,lo,up))
            covered+=1;cursor=up
        if cursor!=hi:raise AssertionError(("end gap",Q,cursor,hi))
    assert [row["Q"] for row in obj["records"]]==list(range(1,16))
    return {"status":"INTERVAL_CHECK_PASS","intervals":covered,
            "terminal_claim":"RH_OPEN"}


def main()->int:
    p=argparse.ArgumentParser()
    p.add_argument("--out",type=Path)
    p.add_argument("--verify",type=Path)
    p.add_argument("--precision-bits",type=int,default=128)
    p.add_argument("--max-depth",type=int,default=30)
    p.add_argument("--max-tiles",type=int,default=5000)
    args=p.parse_args()
    if args.verify:
        print(json.dumps(verify(args.verify,args.precision_bits)))
        return 0
    if not args.out:raise ValueError("provide --out or --verify")
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    args.out.mkdir(parents=True,exist_ok=True)
    rows=[]
    for Q in range(1,16):
        d=cover(Q,args.max_depth,args.max_tiles)
        file=f"k2_odd_Q{Q:02d}.json"
        raw=(json.dumps(d,sort_keys=True,indent=2)+"\n").encode()
        (args.out/file).write_bytes(raw)
        rows.append({"Q":Q,"file":file,
                     "sha256":hashlib.sha256(raw).hexdigest(),
                     "accepted":len(d["accepted"]),
                     "unresolved":len(d["unresolved"])})
        print(json.dumps(rows[-1]),flush=True)
    passed=all(row["unresolved"]==0 for row in rows)
    out={"schema":"post287.wp4.k2-odd-prerequisite.v1",
         "status":"INTERVAL_EVIDENCE" if passed else "UNRESOLVED",
         "terminal_claim":"RH_OPEN","precision_bits":args.precision_bits,
         "domain":"[1/512,log16]" if passed else "accepted intervals only",
         "source":"complete fixed-Q production Eq4.4",
         "legal_odd_generator":list(V),"norm_square":NORM2,
         "records":rows,"not_a_lean_theorem":True}
    (args.out/"manifest.json").write_text(json.dumps(out,sort_keys=True,indent=2)+"\n")
    return 0 if passed else 2


if __name__=="__main__":
    raise SystemExit(main())
