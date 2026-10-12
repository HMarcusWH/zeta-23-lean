#!/usr/bin/env python3
"""WP2/WP4 formal-object normalization gate (rigorous Arb comparisons).

Cross-check the Eq(4.4) physical matrix in the *original* variable against
the independently changed-variable fixed-unit representation. Both use the
complete pole, regularized arch and exact von Mangoldt prime-power source;
neither uses historical legacy finiteMatrix or an assumed Weil-positivity
theorem. Also check exact legal K3 parity bases and nested K2 matrix.

The two evaluators share source definitions, so this is a source-normalization
audit, NOT a Lean-verified implementation of the Python evaluator.
"""
from __future__ import annotations
import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp
from flint import arb, ctx, fmpq

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import canonical_source_arb as C
from post175_fb05_q13_fixed_unit_enclosure import (
    fixed_unit_fixed_q_canonical_source_matrix_arb)
from post169_fb05_schur_visibility import one_step_geometry


def q(x:Fraction)->arb:
    return arb(fmpq(x.numerator,x.denominator))


def carriers()->dict:
    result={}
    for parity in ("even","odd"):
        geom=one_step_geometry(2,parity)
        B=sp.Matrix(geom.step_basis_exact)
        if B.shape!=(7,2) or B.rank()!=2:
            raise AssertionError(("invalid carrier",parity,B.shape,B.rank()))
        for col in range(2):
            v=[B[i,col] for i in range(7)]
            assert sum(v)==0
            assert sum((i-3)*v[i] for i in range(7))==0
            assert sum((i-3)**2*v[i] for i in range(7))==0
            if parity=="even":
                assert all(v[i]==v[6-i] for i in range(7))
            else:
                assert all(v[i]==-v[6-i] for i in range(7))
        result[parity]={"ambient_dim":7,"carrier_dim":2,
                        "linear_moment_degrees":[0,1,2],
                        "rank":2}
    return result


def compare(Lq:Fraction,Qcell:int,K:int)->dict:
    L=q(Lq)
    if not C.fixed_cell_membership(Qcell,L)["certified"]:
        raise ValueError(("not in requested fixed-Q cell",Qcell,str(Lq)))
    M=C.canonical_source_matrix(L,K,Qcell)
    M2=fixed_unit_fixed_q_canonical_source_matrix_arb(L,K,Qcell)
    for i in range(2*K+1):
        for j in range(2*K+1):
            if not (M[i,j]-M2[i,j]).contains(0):
                raise AssertionError(("Eq4.4 vs fixed-unit source mismatch",
                                      Qcell,K,i,j,C.ball_record(M[i,j]-M2[i,j],30)))
    return {"aperture":[Lq.numerator,Lq.denominator],
            "cell":Qcell,"K":K,"entries_checked":(2*K+1)**2,
            "agreement":"ENCLOSURES_INTERSECT_AT_ALL_MATRIX_ENTRIES"}


def main()->int:
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--precision-bits",type=int,default=256)
    args=p.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    assert (C.von_mangoldt(2)-C.von_mangoldt(4)).contains(0)
    assert (C.von_mangoldt(2)-C.von_mangoldt(8)).contains(0)
    assert C.von_mangoldt(6).is_zero()
    bases=carriers()
    tests=[(Fraction(1,4),1,2),(Fraction(13,10),3,2),
           (Fraction(267,100),14,3),(Fraction(11,4),15,3)]
    rows=[compare(L,Q,K) for L,Q,K in tests]
    # Nested K2 is the central 5x5 block of the SAME actual K3 matrix.
    L=q(Fraction(267,100))
    m2=C.canonical_source_matrix(L,2,14)
    m3=C.canonical_source_matrix(L,3,14)
    for i in range(5):
        for j in range(5):
            if not (m3[i+1,j+1]-m2[i,j]).contains(0):
                raise AssertionError(("K2/K3 nesting mismatch",i,j))
    d={"schema":"post287.wp2.wp4.normalization.v1",
       "terminal_claim":"RH_OPEN",
       "status":"PASS_SOURCE_NORMALIZATION_GATE",
       "source":"canonicalSourceMatrix Eq4.4 vs analytic fixed-unit identity",
       "arch_correction_count":1,
       "prime_weights":"Lambda(p**k)=log(p), exact prime power",
       "carrier_basis":bases,"tested":rows,
       "nested_K2_in_K3":True,
       "does_not_prove":["all-L certificate","Lean-Python equivalence","RH"]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(d,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":d["status"],"tests":len(rows)}))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
