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
import time
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
from certificate_integrity import source_input_digests, source_commit, assert_source_unchanged


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


# M51's historical LOG16_UP=2772588722239781/10^15 is actually
# *below* exact log(16).  Do not inherit its comment as a rigorous upper
# bound. This enhanced WP2 cover goes slightly beyond the true endpoint.
LOG16_CERTIFIED_UPPER=Fraction(2772588722239782,10**15)


def verified_cell_bounds(Q:int)->tuple[Fraction,Fraction]:
    a,b=cell_bounds(Q)
    if Q==15:
        endpoint=arb(16).log()
        target=ball(LOG16_CERTIFIED_UPPER)
        if not bool(target>endpoint):
            raise ArithmeticError("rational upper must rigorously exceed log16")
        b=max(b,LOG16_CERTIFIED_UPPER)
    return a,b


def cover_cell(Q:int,max_depth:int,max_nodes:int=50000,deadline:float=float('inf')) -> dict:
    a,b=verified_cell_bounds(Q)
    stack=[(a,b,0)]
    yes,no=[],[]
    nodes=0
    while stack:
        lo,hi,depth=stack.pop()
        if nodes>=max_nodes or time.monotonic()>=deadline:
            no.extend({'left':qpair(a),'right':qpair(b),'depth':d,
                       'reason':'RESOURCE_LIMIT'}
                      for a,b,d in [(lo,hi,depth),*stack])
            break
        nodes+=1
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
    p.add_argument('--max-nodes',type=int,default=50000)
    p.add_argument('--seconds',type=int,default=18000)
    args=p.parse_args()
    initial_source=source_input_digests()
    if not 0 <= args.max_depth <= 40 or args.max_nodes <= 0 or args.seconds <= 0:
        raise ValueError('positive finite resources and depth cap 40 required')
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    lo,sep,hi=args.cells.partition('-')
    cells=list(range(int(lo),int(hi or lo)+1))
    if not cells or any(not 1 <= Q <= 15 for Q in cells):
        raise ValueError('select cells Q1..Q15')
    args.output_dir.mkdir(parents=True,exist_ok=True)
    rows=[]
    deadline=time.monotonic()+args.seconds
    for Q in cells:
        data=cover_cell(Q,args.max_depth,args.max_nodes,deadline)
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
              'source_digests':assert_source_unchanged(initial_source),'source_commit':source_commit(),
              'domain':'[1/400, log16] rigorously (final rational above log16)' if complete else 'named cells only',
              'backend':'full production fixed-Q matrix and 2nd derivative',
              'arch_correction':'once',
              'prime_weights':'Lambda(p**j)=log(p)',
              'interval_records':sum(q['accepted_count'] for q in rows),
              'cells':rows,'not_claimed':['Lean proof','all-K positivity','RH']}
    (args.output_dir/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    return 0 if complete else 2


if __name__=='__main__':
    raise SystemExit(main())
