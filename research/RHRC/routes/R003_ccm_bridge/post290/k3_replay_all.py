#!/usr/bin/env python3
"""Independent 768-bit no-search SECOND checking of all 30 final layer unions.

Curvature/Taylor arithmetic is reconstructed here rather than calling search
acceptance. The canonical analytic Arb backend is shared; this is finite
interval evidence, not a Lean certificate or an independent source derivation.
"""
from __future__ import annotations
import argparse
import concurrent.futures
import json
import sys
import time
from pathlib import Path
from fractions import Fraction
from k3_resume_partition import HERE, OLD, digest, pair, rational, require_current, write, LAYERS, RESOURCES, validate_layer, seam_source_bindings


def exact_ball_record(value):
    if not value.is_finite():
        raise ValueError("nonfinite enclosure")
    def endpoint(bound):
        mantissa, exponent = bound.man_exp()
        q = Fraction(int(mantissa)) * Fraction(2) ** int(exponent)
        return pair(q)
    return {"lower": endpoint(value.lower()), "upper": endpoint(value.upper()), "finite": True}


def independent_second(tile,q,parity):
    from flint import arb
    import canonical_source_arb as C
    from post194_fb05_q14_fixed_unit_second_derivative import fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets
    from post166_fb05_cell_interval import _arb_matrix_from_sympy
    from post169_fb05_schur_visibility import one_step_geometry
    lo,hi=rational(tile["left"]),rational(tile["right"])
    centre,radius=(lo+hi)/2,(hi-lo)/2
    c,r=arb(centre.numerator)/centre.denominator,arb(radius.numerator)/radius.denominator
    basis=_arb_matrix_from_sympy(one_step_geometry(2,parity).step_basis_exact)
    point,first,_=jets(c,3,q)
    whole,whole_first,whole_second=jets(arb(c,r),3,q)
    project=lambda matrix:basis.transpose()*matrix*basis
    H,H1,A,A1,A2=map(project,(point,first,whole,whole_first,whole_second))
    a,b,d=H[0,0],H[0,1],H[1,1]
    ap,bp,dp=H1[0,0],H1[0,1],H1[1,1]
    curvature=A2[0,0]*A[1,1]+2*A1[0,0]*A1[1,1]+A[0,0]*A2[1,1]-2*A1[0,1]**2-2*A[0,1]*A2[0,1]
    # Explicitly reject indeterminate jets BEFORE min/comparison arithmetic.
    quantities=(a,b,d,ap,bp,dp,A2[0,0],curvature,c,r)
    if not all(x.is_finite() for x in quantities):
        return {"accepted":False,"reason":"NONFINITE_ENCLOSURE"}
    det=a*d-b*b
    detp=ap*d+a*dp-2*b*bp
    lower_a=a-abs(ap)*r+min(arb(0),A2[0,0].lower())*r*r/2
    lower_det=det-abs(detp)*r+min(arb(0),curvature.lower())*r*r/2
    if not lower_a.is_finite() or not lower_det.is_finite():
        return {"accepted":False,"reason":"NONFINITE_LOWER_BOUND"}
    return {"accepted":bool(lower_a>0 and lower_det>0),"a":C.ball_record(lower_a,36),"delta":C.ball_record(lower_det,36),"a_interval":exact_ball_record(lower_a),"delta_interval":exact_ball_record(lower_det),"reason":"POSITIVE_WHOLE_INTERVAL" if bool(lower_a>0 and lower_det>0) else "UNCERTIFIED_SIGN"}


def check_layer(directory,spec,seconds):
    sys.path[:0]=[str(OLD),str(HERE.parent)]
    from flint import arb,ctx
    import canonical_source_arb as C
    from wp4_k3_full_continuum import interval_bounds
    C.set_precision(768);ctx.prec=768
    path=Path(directory)/spec["file"]
    if path.name!=spec["file"] or digest(path)!=spec["sha256"]:
        raise ValueError("tampered candidate layer")
    record=json.loads(path.read_text())
    q,parity=spec["cell"],spec["parity"]
    bounds=interval_bounds(q)
    structurally_complete=validate_layer(spec,record,"SECOND",bounds)
    seam_lo=arb(1)/512 if q==1 else arb(q).log()
    seam_hi=arb(q+1).log()
    rational_ball=lambda f:arb(f.numerator)/f.denominator
    if not bool(rational_ball(bounds[0])<=seam_lo and rational_ball(bounds[1])>=seam_hi):
        raise ValueError("physical logarithmic seam not bracketed on required side")
    # At log(q+1), qBasis entering-prime atom vanishes: inspect mathematical source
    # normalization separately. Frozen-Q analytic tails count only in the physical cell.
    verified,failed,unverified=[],[],[]
    start=time.monotonic()
    for i,tile in enumerate(record["accepted"]):
        if time.monotonic()-start>=seconds:
            unverified=[{"index":j,"left":t["left"],"right":t["right"],"reason":"CHECKER_WALL_LIMIT_BETWEEN_EVALUATIONS"} for j,t in enumerate(record["accepted"][i:],start=i)]
            break
        try:
            fresh=independent_second(tile,q,parity)
        except Exception as exc:
            fresh={"accepted":False,"reason":"EVALUATION_ERROR","error":repr(exc)}
        item={"index":i,"left":tile["left"],"right":tile["right"],**fresh}
        (verified if fresh["accepted"] else failed).append(item)
    return {"schema":"post290.k3-layer-replay.v1","Q":q,"parity":parity,"candidate_sha256":spec["sha256"],"precision_bits":768,"verified":verified,"failed":failed,"unverified":unverified,"unresolved":record["unresolved"],"seams_verified":True,"seam_source_bindings":seam_source_bindings(),"physical_scope":{"left":"1/512" if q==1 else f"log({q})","right":f"log({q+1})"},"complete":structurally_complete and not failed and not unverified,"elapsed_seconds":time.monotonic()-start,"terminal_claim":"RH_OPEN"}


def replay(directory,partition,out):
    frozen=json.loads(partition.read_text());require_current(frozen)
    manifest=json.loads((directory/"manifest.json").read_text())
    if manifest["partition_sha256"]!=digest(partition) or manifest["current_source"]!=frozen["current_source"]:
        raise ValueError("wrong candidate source or frozen partition")
    layers=[(r["cell"],r["parity"]) for r in manifest["records"]]
    if len(layers)!=30 or len(set(layers))!=30 or set(layers)!=LAYERS:
        raise ValueError("missing or duplicated D2 layer")
    receipts=[]
    with concurrent.futures.ProcessPoolExecutor(max_workers=RESOURCES["checker_max_concurrency"]) as pool:
        futures={pool.submit(check_layer,str(directory),spec,RESOURCES["checker_seconds_per_layer"]):spec for spec in manifest["records"]}
        for future in concurrent.futures.as_completed(futures):
            spec=futures[future]
            try:
                result=future.result()
            except Exception as exc:
                result={"Q":spec["cell"],"parity":spec["parity"],"candidate_sha256":spec["sha256"],"precision_bits":768,"complete":False,"verified":[],"failed":[],"unverified":[{"reason":"LAYER_CHECK_FAILED","error":repr(exc),"whole_layer":True}],"unresolved":[],"seams_verified":False,"seam_source_bindings":seam_source_bindings(),"terminal_claim":"RH_OPEN"}
            name=f"replay_Q{spec['cell']:02d}_{spec['parity']}.json"
            write(out.parent/"replay-layers"/name,result)
            receipts.append({"file":name,"sha256":digest(out.parent/"replay-layers"/name),**result})
            print(json.dumps({"Q":result["Q"],"parity":result["parity"],"complete":result["complete"],"verified":len(result["verified"]),"failed":len(result["failed"]),"unverified":len(result["unverified"])}),flush=True)
    require_current(frozen)
    complete=all(r["complete"] for r in receipts)
    result={"schema":"post290.k3-independent-full-checker.v1","status":"PASS" if complete else "UNRESOLVED","claimed_scope":"K3_FULL" if complete else "FULL_TARGET_UNVERIFIED_REMAINDER","candidate_manifest_sha256":digest(directory/"manifest.json"),"current_source":frozen["current_source"],"precision_bits":768,"layers":30,"complete_layers":sum(r["complete"] for r in receipts),"verified_tiles":sum(len(r["verified"]) for r in receipts),"failed_tiles":sum(len(r["failed"]) for r in receipts),"unverified_tiles":sum(len(r["unverified"]) for r in receipts),"unresolved_tiles":sum(len(r["unresolved"]) for r in receipts),"seams_verified":all(r["seams_verified"] for r in receipts),"layer_receipts":[{k:r[k] for k in ("file","sha256","Q","parity","complete")} for r in receipts],"terminal_claim":"RH_OPEN","not_a_lean_proof":True}
    write(out,result)
    return 0 if complete else 2


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("candidate",type=Path);p.add_argument("partition",type=Path);p.add_argument("--out",type=Path,required=True)
    a=p.parse_args()
    return replay(a.candidate,a.partition,a.out)


if __name__=="__main__":
    raise SystemExit(main())
