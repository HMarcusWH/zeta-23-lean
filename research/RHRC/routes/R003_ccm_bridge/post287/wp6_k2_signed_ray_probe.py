#!/usr/bin/env python3
"""WP6 bounded native K2 shifted-ray sign test (REPORT ONLY).

On the legal K2 carriers v=(1,-4,6,-4,1), w=(-1,2,0,-2,1)
the actual negative-shift canonical ray at mu=-1 is
x(mu)=3/(5*(b-mu))*v, b=odd canonical bottom. It exists if mu<b.
F04 identifies the complete physical second-source observable via the
Euler-corrected fixed-v0 derivative. An unrestricted positive sign would
need to survive both samples; a false sign does not imply RH failure.
"""
import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from flint import arb,ctx,fmpq

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parent),str(HERE.parent/'post285')]
import canonical_source_arb as C
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets,
)

V=(1,-4,6,-4,1)
W=(-1,2,0,-2,1)
SAMPLES=(Fraction(3,20),Fraction(69,100))

def qarb(x):return arb(fmpq(x.numerator,x.denominator))

def quad(M,v):return sum(v[i]*M[i,j]*v[j] for i in range(5) for j in range(5))

def sample(L):
    Q=1
    z=qarb(L)
    if not C.fixed_cell_membership(Q,z)['certified']:
        raise AssertionError('not inside prime-free cell')
    M,Mp,Mpp=jets(z,2,Q)
    even=quad(M,V)/70
    odd=quad(M,W)/10
    mu=arb(-1)
    if not bool(mu<odd):
        raise AssertionError('negative shifted ray not legitimate')
    scale=arb(3)/(5*(odd-mu))
    euler=quad(Mpp,V)+2*quad(Mp,V)/z
    physicalQ=-(z**4)/((2*arb.pi())**2)*euler
    rayQ=scale*scale*physicalQ
    return {'L':[L.numerator,L.denominator],'Q':Q,
            'odd_bottom':C.ball_record(odd,38),
            'even_bottom':C.ball_record(even,38),
            'negative_shift_mu':-1,
            'shifted_ray_scale':C.ball_record(scale,38),
            'complete_physical_Q_v0':C.ball_record(physicalQ,38),
            'complete_physical_Q_ray':C.ball_record(rayQ,38),
            'ray_Q_positive':bool(rayQ>0),'ray_Q_negative':bool(rayQ<0)}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path)
    ap.add_argument('--precision-bits',type=int,default=256)
    a=ap.parse_args()
    ctx.prec=a.precision_bits
    C.set_precision(a.precision_bits)
    rows=[sample(L) for L in SAMPLES]
    checked=rows[0]['ray_Q_positive'] and rows[1]['ray_Q_negative']
    obj={'package':'WP6_BOUNDED_SIGNED_RAY_PROBE','terminal_claim':'RH_OPEN',
         'status':'EXPERIMENTAL_SIGNAL' if checked else 'UNRESOLVED',
         'tested_statement':'unrestricted Qcomplete(L,Dx(mu))>=0 on all odd-positive K2 shifted rays',
         'disposition':'FALSIFIED_BY_BOUNDED_ACTUAL_SOURCE_ARBS' if checked else 'UNRESOLVED',
         'nonclaims':['not a first contact','not a selected negative eigenmode',
                      'not a universal zeta exclusion'],
         'observations':rows}
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps({'package':obj['package'],'status':obj['status'],
                      'positive_at_first':rows[0]['ray_Q_positive'],
                      'negative_at_second':rows[1]['ray_Q_negative']}))
    return 0 if checked else 1

if __name__=='__main__':raise SystemExit(main())
