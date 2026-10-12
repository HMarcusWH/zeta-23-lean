#!/usr/bin/env python3
"""WP2: M51 Arb per-interval evidence producer, not a Lean theorem.

The original M51 certifies K2 even positivity at [1/400,log16] by Taylor
enclosures. This reproducible replay records every accepted rational
interval. Results stay INTERVAL_EVIDENCE unless checked by a trusted proof
checker. No finite cover implies RH or positivity for K>=3.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parent),str(HERE.parent/'post285')]
from post285.post285_m51_k2_even_bottom_certificate import (
    MAX_DEPTH, ball, cell_bounds, quad,
)
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets,
)
import canonical_source_arb as C


def qpair(x:Fraction) -> list[int]:
    return [x.numerator,x.denominator]


def accepted_bound(c:Fraction,r:Fraction,Q:int) -> dict:
    M,Mprime,_=jets(ball(c),2,Q)
    _,_,Msecond=jets(ball(c,r),2,Q)
    f,fp,fpp=quad(M),quad(Mprime),quad(Msecond)
    curvature_floor=min(arb(0),fpp.lower())
    rr=ball(r)
    lb=(f-abs(fp).upper()*rr+curvature_floor*rr*rr/2).lower()
    return {
        'centre':qpair(c),'radius':qpair(r),
        'lambda_c':C.ball_record(f,35),
        'lambda_prime_c':C.ball_record(fp,35),
        'curvature_interval':C.ball_record(fpp,35),
        'lower':C.ball_record(lb,35),
        'strictly_positive':bool(lb>0),
    }


def cover_cell(Q:int,max_depth:int) -> dict:
    a,b=cell_bounds(Q)
    stack=[(a,b,0)]
    yes,no=[],[]
    while stack:
        lo,hi,depth=stack.pop()
        c,r=(lo+hi)/2,(hi-lo)/2
        row=accepted_bound(c,r,Q)
        row['left']=qpair(lo);row['right']=qpair(hi)
        if row['strictly_positive']:
            yes.append(row)
        elif depth>=max_depth:
            no.append({'left':qpair(lo),'right':qpair(hi),
                       'depth':depth,'candidate':row})
        else:
            stack.extend(((c,hi,depth+1),(lo,c,depth+1)))
    yes.sort(key=lambda r:Fraction(*r['left']))
    return {'cell_Q':Q,'left':qpair(a),'right':qpair(b),
            'intervals':yes,'accepted_count':len(yes),
            'unresolved':no}


def main() -> int:
    p=argparse.ArgumentParser()
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--cells',default='1-15')
    p.add_argument('--max-depth',type=int,default=MAX_DEPTH)
    p.add_argument('--precision-bits',type=int,default=128)
    args=p.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    lo,sep,hi=args.cells.partition('-')
    cells=list(range(int(lo),int(hi or lo)+1))
    args.output_dir.mkdir(parents=True,exist_ok=True)
    rows=[]
    for Q in cells:
        data=cover_cell(Q,args.max_depth)
        name=f'cell_{Q:02}.json'
        raw=(json.dumps(data,indent=2,sort_keys=True)+'\n').encode()
        (args.output_dir/name).write_bytes(raw)
        row={'Q':Q,'file':name,'sha256':hashlib.sha256(raw).hexdigest(),
             'accepted_count':data['accepted_count'],
             'unresolved_count':len(data['unresolved'])}
        rows.append(row)
        print(json.dumps(row),flush=True)
    complete=(cells==list(range(1,16)) and
              all(q['unresolved_count']==0 for q in rows))
    manifest={'schema':'post287.wp2.k2-m51.arb.v1',
              'terminal_claim':'RH_OPEN',
              'status':'INTERVAL_EVIDENCE' if complete else 'UNRESOLVED',
              'prec_bits':args.precision_bits,
              'domain':'[1/400, log16]' if complete else 'named cells only',
              'backend':'full production fixed-Q matrix and 2nd derivative',
              'arch_correction':'once',
              'prime_weights':'Lambda(p**j)=log(p)',
              'interval_records':sum(q['accepted_count'] for q in rows),
              'cells':rows,'not_claimed':['Lean proof','all-K positivity','RH']}
    (args.output_dir/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    return 0 if complete else 2


if __name__=='__main__':
    raise SystemExit(main())
