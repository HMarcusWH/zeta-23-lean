#!/usr/bin/env python3
"""Validated contact-balance diagnostics for the post-#282 calculus campaign.

This module is research/certification infrastructure only.  It never upgrades a
finite measurement to theorem authority and never treats a local sign bracket
as a first global boundary.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
from flint import arb, arb_mat, ctx

ROUTE=Path(__file__).resolve().parent
RHRC=ROUTE.parents[1]
sys.path.insert(0,str(RHRC/"closure_batch"))
from interval_codec import DyadicInterval

from canonical_contact_frontier_arb import restricted_jets


def interval_record(x: arb) -> dict:
    d=DyadicInterval.from_arb(x)
    return {
        "dyadic_interval": d.to_json(),
        "sign": d.sign(),
        "display_mid": str(x.mid()),
        "display_rad": str(x.rad()),
        "display_only": True,
    }


def mat_mid(A: arb_mat) -> np.ndarray:
    return np.array([[float(A[i,j].mid()) for j in range(A.ncols())]
                     for i in range(A.nrows())],dtype=float)


def quad(A: arb_mat,v: np.ndarray) -> arb:
    V=arb_mat([[arb(repr(float(x)))] for x in v])
    den=(V.transpose()*V)[0,0]
    if not bool(den>0):
        raise ValueError("nonpositive vector norm")
    return (V.transpose()*A*V)[0,0]/den


def one_dimensional_calibration(L: arb,K:int,Q:int,parity:str,prec:int)->dict:
    ctx.prec=int(prec)
    E,E1,E2=restricted_jets(L,K,Q,parity)
    if E.nrows()!=1:
        return {"status":"NOT_ONE_DIMENSIONAL","dimension":E.nrows()}
    v=np.ones(1,dtype=float)
    energy=quad(E,v)
    j1=quad(E1,v)
    j2=quad(E2,v)
    return {
        "status":"CERTIFIED_ONE_DIMENSIONAL_DIRECTION",
        "dimension":1,
        "energy":interval_record(energy),
        "j1":interval_record(j1),
        "fixed_second":interval_record(j2),
        "response":{
            "status":"EXACT_ZERO_DIMENSIONAL_COMPLEMENT",
            "norm":interval_record(arb(0)),
        },
        "optimized_curvature":interval_record(j2),
    }


def log2_seam_calibration(prec:int)->dict:
    ctx.prec=int(prec)
    L=arb(2).log()
    left=one_dimensional_calibration(L,2,1,"even",prec)
    right=one_dimensional_calibration(L,2,2,"even",prec)
    def same(field:str)->bool:
        if left.get("status")!="CERTIFIED_ONE_DIMENSIONAL_DIRECTION" or right.get("status")!="CERTIFIED_ONE_DIMENSIONAL_DIRECTION":
            return False
        a=DyadicInterval.from_json(left[field]["dyadic_interval"])
        b=DyadicInterval.from_json(right[field]["dyadic_interval"])
        return not (a.hi < b.lo or b.hi < a.lo)
    return {
        "name":"K2_LOG2_COMPRESSED_SEAM",
        "K":2,
        "cutoff_left":1,
        "cutoff_right":2,
        "L_exact":"log(2)",
        "precision_bits":prec,
        "left":left,
        "right":right,
        "value_overlap":same("energy"),
        "first_overlap":same("j1"),
        "second_overlap":same("fixed_second"),
        "qualified": (
            left.get("status")=="CERTIFIED_ONE_DIMENSIONAL_DIRECTION"
            and right.get("status")=="CERTIFIED_ONE_DIMENSIONAL_DIRECTION"
            and same("energy") and same("j1") and same("fixed_second")
        ),
    }


def seam_probe(q:int,K:int,prec:int)->dict:
    ctx.prec=int(prec)
    L=arb(q).log()
    left=one_dimensional_calibration(L,K,max(1,q-1),"even",prec)
    right=one_dimensional_calibration(L,K,q,"even",prec)
    return {
        "q":q,"K":K,"precision_bits":prec,
        "left_status":left.get("status"),
        "right_status":right.get("status"),
        "left":left,"right":right,
    }


def campaign(protocol:dict)->dict:
    ladder=protocol["precision_bits"]
    calibration=None
    for prec in ladder:
        calibration=log2_seam_calibration(int(prec))
        if calibration["qualified"]:
            break
    seams=[]
    for item in protocol["seam_controls"]:
        seams.append(seam_probe(int(item["q"]),int(item["K"]),int(ladder[-1])))
    return {
        "schema_version":"POST282_CONTACT_BALANCE_ARB_v1",
        "claim_cap":"EXPERIMENTAL_SIGNAL_ONLY",
        "calibration":calibration,
        "seam_controls":seams,
        "summary":{
            "calibration_qualified":bool(calibration and calibration["qualified"]),
            "seam_control_count":len(seams),
            "theorem_promotion":False,
            "terminal_claim":"RH_OPEN",
        },
    }


if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument("--protocol",required=True)
    ap.add_argument("--output",required=True)
    a=ap.parse_args()
    protocol=json.loads(Path(a.protocol).read_text())
    out=campaign(protocol)
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out["summary"],indent=2,sort_keys=True))
