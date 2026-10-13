#!/usr/bin/env python3
"""WP6: one bounded K2 native signed-source shifted-ray probe (report only).

For legal vectors v=(1,-4,6,-4,1), w=(-1,2,0,-2,1), the exact
K2 canonical index map obeys D(v)=2w and the projected odd cubic normal
is (6/5)w. For the actual odd Rayleigh bottom b and negative shift mu=-1,
the exact #287 ray is x(mu)=(3/(5*(b-mu)))*v.

The Euler-corrected second complete-source test is obtained from the
real canonical fixed-cell M,M',M'' at exactly that ray.  This tests and can
falsify an *unrestricted* sign assumption on all odd-positive shifted
rays; it is not a test on the negative #247 ground or an RH proof.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx, fmpq

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parent),str(HERE.parent/'post285')]
import canonical_source_arb as C
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets,
)

V=(1,-4,6,-4,1)
W=(-1,2,0,-2,1)
SAMPLES=(Fraction(3,20),Fraction(69,100))


def qarb(x):
    return arb(fmpq(x.numerator,x.denominator))


def quad(M,v):
    return sum(v[i]*M[i,j]*v[j] for i in range(5) for j in range(5))


def test_aperture(L:Fraction):
    a=qarb(L)
    if not C.fixed_cell_membership(1,a)['certified']:
        raise ValueError('source must be prime-free and seam-free')
    M,Mp,Mpp=jets(a,2,1)
    even=quad(M,V)/70
    odd=quad(M,W)/10
    mu=arb(-1)
    if not bool(mu<odd):
        raise AssertionError('shift does not lie below odd ground')
    scale=arb(3)/(5*(odd-mu))
    euler=quad(Mpp,V)+2*quad(Mp,V)/a
    # F04: E''+2E'/L=-(2π)^2 Q(L,Dv)/L^4.
    Q=-(a**4)/((2*arb.pi())**2)*euler
    Qray=scale*scale*Q
    return {'aperture':[L.numerator,L.denominator],
            'physical_source':'exact pole/arch, no primes in cutoff Q1',
            'odd_bottom':C.ball_record(odd,38),
            'even_bottom':C.ball_record(even,38),
            'negative_shift':-1,
            'selected_ray_scale':C.ball_record(scale,38),
            'physical_Q_v':C.ball_record(Q,38),
            'physical_Q_shifted_ray':C.ball_record(Qray,38),
            'positive':bool(Qray>0),'negative':bool(Qray<0)}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--precision-bits',type=int,default=256)
    args=p.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    rows=[test_aperture(x) for x in SAMPLES]
    witness=rows[0]['positive'] and rows[1]['negative']
    rec={'schema':'post287.wp6.k2-sign-v1',
         'terminal_claim':'RH_OPEN',
         'status':'EXPERIMENTAL_SIGNAL' if witness else 'UNRESOLVED',
         'tested_target':'unrestricted complete physical Q>=0 on all B>0 shifted K2 rays',
         'disposition':'FALSIFIED_AT_BOUNDED_TRUE_SOURCE_APERTURES' if witness else 'UNRESOLVED',
         'observations':rows,
         'not_claimed':['any first contact','the #247 negative selected ground',
                        'universal signed cancellation','RH']}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':rec['status'],'signs':[(x['positive'],x['negative']) for x in rows]}))
    return 0 if witness else 1


if __name__=='__main__':
    raise SystemExit(main())
