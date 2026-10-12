#!/usr/bin/env python3
"""Independent low-order consistency controls for WP4 fourth-order Taylor jets.

Never accept the new high-order enclosure just because it is self-consistent:
its zeroth, first and second coefficients MUST agree entry by entry with the
previously validated source implementation (#175/#177/#194), at genuine
prime-containing cutoff cells.  This is *not* a proof of the global claim.

The stronger fourth-order fallback is rejected if any of these checks fails.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, ctx

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import canonical_source_arb as C
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb,
)
from wp4_k3_fourth_order_fallback import full_matrix_jets, _sinhc, _constant, Q


def compare(Qcell:int,L:arb)->dict:
    jets=full_matrix_jets(L,Qcell)
    known=fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb(
        L,3,Qcell)
    assert len(jets)==5
    for order in range(3):
        f=1 if order<2 else 2
        for i in range(7):
            for j in range(7):
                residual=f*jets[order][i,j]-known[order][i,j]
                if not residual.contains(0):
                    raise AssertionError((Qcell,order,i,j,C.ball_record(residual,28)))
    return {"cell":Qcell,
            "aperture":C.ball_record(L,24),
            "agreement":"ALL_49_ENTRIES_ORDERS_0_1_2",
            "source":"independently existing Eq4.4 fixed-unit analytic first/second jets"}


def main()->int:
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--precision-bits",type=int,default=192)
    args=p.parse_args()
    C.set_precision(args.precision_bits)
    ctx.prec=args.precision_bits
    # Hypergeometric removable regularization at exact origin.
    h=_sinhc(_constant(acb(0)))
    assert list(h.coeffs())[0].contains(1)
    pts=[(13,Q(Fraction(263,100))),
         (14,Q(Fraction(2667,1000)))]
    records=[]
    for q,L in pts:
        assert C.fixed_cell_membership(q,L)["certified"]
        records.append(compare(q,L))
    obj={"schema":"post287.wp4.fourth_order_controls.v1",
         "status":"EXACT_LOWORDER_ARBS_OVERLAP" if len(records)==2 else "UNRESOLVED",
         "terminal_claim":"RH_OPEN","records":records,
         "fourth_order_sign_not_inferred":True}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(obj,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":obj["status"],"count":len(records)}))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
