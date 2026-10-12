#!/usr/bin/env python3
"""WP4 D2=Full: mandatory *feasibility gate*, not the full K3 certificate.

Checks the #176 frozen Q14 boxes for both K=3 parity carriers in the exact
2x2 predecessor+shell basis, using the fixed-Q 7x7 production source and
128/384-bit Arb Taylor bounds.  Each box is bisected up to the *frozen*
max-depth 40.  UNRESOLVED means neither sign.  No amount of grid sampling
is promoted to an all-L statement.

A failed method gate routes to the *single predeclared fourth-order Taylor
alternative*. This module does not implement that alternative or claim its
success. Stop conditions and hard resource ceilings are explicit.
"""
from __future__ import annotations

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


def exact_ball(f:Fraction)->arb:
    return arb(fmpq(f.numerator,f.denominator))


def t_to_aperture(Q:int,t:Fraction,r:Fraction)->tuple[arb,arb,arb]:
    lo=cell_coordinate_L_arb(Q,exact_ball(t-r))
    hi=cell_coordinate_L_arb(Q,exact_ball(t+r))
    centre=cell_coordinate_L_arb(Q,exact_ball(t))
    return centre,lo.union(hi),(hi-lo).upper()/2


def restricted(M,geom):
    basis=_arb_matrix_from_sympy(geom.step_basis_exact)
    return basis.transpose()*M*basis


def two_scalar_jets(M,Mp,Mpp,geom):
    m,p,q=(restricted(x,geom) for x in (M,Mp,Mpp))
    a,b,d=m[0,0],m[0,1],m[1,1]
    da,db,dd=p[0,0],p[0,1],p[1,1]
    dda,ddb,ddd=q[0,0],q[0,1],q[1,1]
    # Sylvester: a>0 and Delta=ad-b²>0; NEVER divide by a.
    return ((a,da,dda),
            (a*d-b*b,da*d+a*dd-2*b*db,
             dda*d+2*da*dd+a*ddd-2*(db*db+b*ddb)))


def taylor_lower(jets3:tuple,rad:arb)->arb:
    value,d1,d2=jets3
    d2_floor=min(arb(0),d2.lower())
    return (value-abs(d1).upper()*rad+d2_floor*rad*rad/2).lower()


def evaluate(Q:int,t:Fraction,r:Fraction,geom)->dict:
    centre,box,rad=t_to_aperture(Q,t,r)
    M,Mp,_=jets(centre,3,Q)
    _,_,Mpp=jets(box,3,Q)
    a,delta=two_scalar_jets(M,Mp,Mpp,geom)
    a_low=taylor_lower(a,rad)
    delta_low=taylor_lower(delta,rad)
    return {'t':[t.numerator,t.denominator],'radius':[r.numerator,r.denominator],
            'a_lower':C.ball_record(a_low,32),
            'det_lower':C.ball_record(delta_low,32),
            'a_positive':bool(a_low>0),'det_positive':bool(delta_low>0),
            'accepted':bool(a_low>0 and delta_low>0)}


def bounded_cover(Q:int,t:Fraction,r:Fraction,geom,depth:int,
                  max_nodes:int,deadline:float)->dict:
    stack=[(t,r,0)];node_count=0;accepted=0;unresolved=[]
    while stack:
        if node_count>=max_nodes or time.monotonic()>=deadline:
            unresolved += [{'t':str(a),'radius':str(b),'depth':d,
                            'reason':'RESOURCE_LIMIT'} for a,b,d in stack]
            break
        tc,rc,d=stack.pop();node_count+=1
        row=evaluate(Q,tc,rc,geom)
        if row['accepted']:
            accepted+=1;continue
        if d>=depth:
            unresolved.append({'t':str(tc),'radius':str(rc),
                               'depth':d,'reason':'UNRESOLVED_INTERVAL',
                               'enclosures':row})
            continue
        half=rc/2
        stack.extend(((tc-half,half,d+1),(tc+half,half,d+1)))
    return {'nodes':node_count,'accepted':accepted,'unresolved':unresolved,
            'verdict':'PASS' if not unresolved else 'UNRESOLVED'}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--precision-bits',type=int,default=384)
    p.add_argument('--max-depth',type=int,default=40)
    p.add_argument('--max-nodes',type=int,default=1000)
    p.add_argument('--time-seconds',type=int,default=1200)
    p.add_argument('--max-boxes',type=int,default=0,
                   help='0 means all frozen primary and control boxes')
    args=p.parse_args()
    if args.max_depth>40:raise ValueError('rev4 frozen depth cap 40')
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    fixture=json.loads(FIXTURE.read_text())
    geoms={par:one_step_geometry(2,par) for par in ('even','odd')}
    boxes=[]
    for case in fixture['primary_Q14_centers']:
        t=Fraction(str(case['t']))
        for k in fixture['primary_radius_bits']:
            for parity in ('even','odd'):
                boxes.append((14,t,Fraction(1,2**k),parity,'primary'))
    for ctrl in fixture['control_boxes']:
        for parity in ('even','odd'):
            boxes.append((ctrl['Q'],Fraction(str(ctrl['t'])),
                          Fraction(1,2**ctrl['radius_bit']),parity,'control'))
    chosen=boxes[:args.max_boxes] if args.max_boxes else boxes
    start=time.monotonic();deadline=start+args.time_seconds
    records=[]
    for Q,t,r,parity,kind in chosen:
        result=bounded_cover(Q,t,r,geoms[parity],args.max_depth,
                             args.max_nodes,deadline)
        rec={'Q':Q,'t':str(t),'radius':str(r),'parity':parity,
             'kind':kind,**result}
        records.append(rec)
        print(json.dumps({k:rec[k] for k in
              ('Q','t','radius','parity','verdict','nodes')}),
              flush=True)
        if time.monotonic()>=deadline:break
    complete=(len(records)==len(boxes) and
              all(x['verdict']=='PASS' for x in records))
    obj={'schema':'post287.wp4.k3-frozen-gate.v1',
         'terminal_claim':'RH_OPEN',
         'scope':'D2=Full target K3 both parities over [1/512,log16]',
         'evaluated_scope':'frozen #176 boxes only',
         'all_aperture_positivity_certified':False,
         'precision_bits':args.precision_bits,
         'max_depth':args.max_depth,
         'gate':'PASS' if complete else 'UNRESOLVED',
         'predeclared_next_if_failed':'fourth-order Taylor model on a,b,d; no unbounded repr retry',
         'elapsed_seconds':round(time.monotonic()-start,2),
         'frozen_boxes':len(boxes),'tested_boxes':len(records),
         'boxes':records,'not_claimed':['continuous full K3 positivity',
                                       'false negative zeta ground','RH']}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'gate':obj['gate'],'tested':len(records),
                      'required':len(boxes)}))
    return 0  # an honest UNRESOLVED gate is a legitimate research disposition


if __name__=='__main__':
    raise SystemExit(main())
