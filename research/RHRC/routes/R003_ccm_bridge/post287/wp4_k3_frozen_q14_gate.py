#!/usr/bin/env python3
"""WP4 D2=Full feasibility gate on frozen K3 Q14 2x2 certificate boxes.

Tests exact #176 Q14 centres/radii at 384 bits using the production
canonical 7x7 fixed-Q source and the 2-dimensional legal even/odd
predecessor+shell basis. Outputs UNRESOLVED when channel-dependency
enclosures cannot prove a>0 and Delta>0. It is NOT an all-interval certificate.

The one allowed order-four Taylor alternative is a separate proof obligation,
not smuggled into a second-order gate. RH remains OPEN.
"""
import argparse
import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx, fmpq

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(ROOT))
import canonical_source_arb as C
from post166_fb05_cell_interval import _arb_matrix_from_sympy,cell_coordinate_L_arb
from post169_fb05_schur_visibility import one_step_geometry
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets,
)

FIXTURE=ROOT/'fixtures'/'post175_fb05_q13_fixed_unit_enclosure_v1.json'


def qarb(x):
    return arb(fmpq(x.numerator,x.denominator))


def midpoint_radius(t,r,Q):
    lo=cell_coordinate_L_arb(Q,qarb(t-r))
    hi=cell_coordinate_L_arb(Q,qarb(t+r))
    mid=cell_coordinate_L_arb(Q,qarb(t))
    return mid,lo.union(hi),(hi-lo).upper()/2


def restrict(M,geom):
    b=_arb_matrix_from_sympy(geom.step_basis_exact)
    return b.transpose()*M*b


def scalars(M,Mp,Mpp,geom):
    m,p,q=restrict(M,geom),restrict(Mp,geom),restrict(Mpp,geom)
    a,b,d=m[0,0],m[0,1],m[1,1]
    da,db,dd=p[0,0],p[0,1],p[1,1]
    dda,ddb,ddd=q[0,0],q[0,1],q[1,1]
    determinant=a*d-b*b
    first=da*d+a*dd-2*b*db
    second=dda*d+2*da*dd+a*ddd-2*(db*db+b*ddb)
    return ((a,da,dda),(determinant,first,second))


def lower_bound(curve,rad):
    val,deriv,second=curve
    mu=min(arb(0),second.lower())
    return (val-abs(deriv).upper()*rad+mu*rad*rad/2).lower()


def check(Q,t,r,parity,geom):
    t0=time.monotonic()
    centre,box,rad=midpoint_radius(t,r,Q)
    M,Mp,_=jets(centre,3,Q)
    _,_,Mpp=jets(box,3,Q)
    a,delta=scalars(M,Mp,Mpp,geom)
    a_low=lower_bound(a,rad)
    delta_low=lower_bound(delta,rad)
    return {'Q':Q,'t':[t.numerator,t.denominator],
            'halfwidth':[r.numerator,r.denominator],
            'parity':parity,'a_lower':C.ball_record(a_low,32),
            'delta_lower':C.ball_record(delta_low,32),
            'a_positive':bool(a_low>0),'delta_positive':bool(delta_low>0),
            'elapsed_seconds':round(time.monotonic()-t0,2)}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--precision-bits',type=int,default=384)
    ap.add_argument('--max-boxes',type=int,default=1)
    args=ap.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    fixture=json.loads(FIXTURE.read_text())
    geoms={p:one_step_geometry(2,p) for p in ('even','odd')}
    boxes=[]
    for centre in fixture['primary_Q14_centers']:
        t=Fraction(str(centre['t']))
        for k in fixture['primary_radius_bits']:
            boxes.extend([(14,t,Fraction(1,2**k),p) for p in ('even','odd')])
    output={'package':'WP4_FROZEN_Q14_FEASIBILITY_GATE',
            'terminal_claim':'RH_OPEN','precision_bits':args.precision_bits,
            'full_D2_claim':False,'gate':'UNRESOLVED','boxes':[],
            'scope':'K3 two parities on predeclared frozen Q14 boxes; NOT an interval cover',
            'predeclared_alternative':'fourth-order Taylor model: separate unproved implementation'}
    for Q,t,r,parity in boxes[:args.max_boxes]:
        record=check(Q,t,r,parity,geoms[parity])
        output['boxes'].append(record)
        print(json.dumps({'t':str(t),'radius':str(r),'parity':parity,
                          'a_positive':record['a_positive'],
                          'delta_positive':record['delta_positive']}),flush=True)
    output['box_count_tested']=len(output['boxes'])
    output['complete_frozen_box_gate']=(len(output['boxes'])==len(boxes) and
            all(x['a_positive'] and x['delta_positive'] for x in output['boxes']))
    output['gate']='PASS' if output['complete_frozen_box_gate'] else 'UNRESOLVED'
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
    return 0  # Unresolved research gate is a recorded outcome, not a theorem.

if __name__=='__main__':
    raise SystemExit(main())
