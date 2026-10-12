#!/usr/bin/env python3
"""WP2: reproducible per-interval M51 Arb certificate transcript.

The original M51 report records aggregate intervals. This script records every
accepted rational interval, its complete Taylor lower bound and an exact
cell-coverage ledger. Positivity remains INTERVAL_EVIDENCE, not a Lean theorem.
"""
import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parent),str(HERE.parent/'post285')]
from post285.post285_m51_k2_even_bottom_certificate import (  # noqa
    LOG16_UP, ball, cell_bounds, quad, MAX_DEPTH,
)
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets,
)
import canonical_source_arb as C


def frac(f:Fraction)->list[int]:
    return [f.numerator,f.denominator]


def bound(c:Fraction,r:Fraction,Q:int)->dict:
    M,Mp,_=jets(ball(c),2,Q)
    _,_,Mpp=jets(ball(c,r),2,Q)
    z,d,curv=quad(M),quad(Mp),quad(Mpp)
    curv_lo=min(arb(0),curv.lower())
    rr=ball(r)
    low=(z-abs(d).upper()*rr+curv_lo*rr*rr/2).lower()
    return {'centre':frac(c),'radius':frac(r),
            'lambda_c':C.ball_record(z,35),
            'lambda_prime_c':C.ball_record(d,35),
            'curvature_interval':C.ball_record(curv,35),
            'lower':C.ball_record(low,35),
            'strictly_positive':bool(low>0)}


def write_cover(Q:int,max_depth:int)->dict:
    a,b=cell_bounds(Q)
    stack=[(a,b,0)]
    accepted=[];unresolved=[]
    while stack:
        lo,hi,depth=stack.pop()
        c,r=(lo+hi)/2,(hi-lo)/2
        rec=bound(c,r,Q)
        if rec['strictly_positive']:
            rec['left']=frac(lo);rec['right']=frac(hi)
            accepted.append(rec)
        elif depth>=max_depth:
            unresolved.append({'left':frac(lo),'right':frac(hi),
                               'depth':depth,'record':rec})
        else:
            stack.extend(((c,hi,depth+1),(lo,c,depth+1)))
    accepted.sort(key=lambda x:Fraction(*x['left']))
    return {'cell_Q':Q,'left':frac(a),'right':frac(b),
            'accepted_count':len(accepted),'unresolved':unresolved,
            'intervals':accepted}


def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument('--output-dir',required=True)
    ap.add_argument('--cells',default='1-15')
    ap.add_argument('--max-depth',type=int,default=MAX_DEPTH)
    ap.add_argument('--precision-bits',type=int,default=128)
    args=ap.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    p=Path(args.output_dir);p.mkdir(parents=True,exist_ok=True)
    ai,_,bi=args.cells.partition('-')
    cells=list(range(int(ai),int(bi or ai)+1))
    reports=[]
    for Q in cells:
        obj=write_cover(Q,args.max_depth)
        fp=p/f'cell_{Q:02}.json'
        bb=(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()
        fp.write_bytes(bb)
        reports.append({'Q':Q,'file':fp.name,'sha256':hashlib.sha256(bb).hexdigest(),
                        'accepted_count':obj['accepted_count'],
                        'unresolved_count':len(obj['unresolved'])})
        print(json.dumps(reports[-1]),flush=True)
    complete=all(x['unresolved_count']==0 for x in reports) and cells==list(range(1,16))
    manifest={'package':'WP2_K2_M51_FULL_INTERVAL_TRANSCRIPT',
              'claim_status':'INTERVAL_EVIDENCE' if complete else 'PARTIAL_UNRESOLVED',
              'terminal_claim':'RH_OPEN','precision_bits':args.precision_bits,
              'full_domain':'[1/400, log(16)]' if complete else 'named cells only',
              'interval_records':sum(x['accepted_count'] for x in reports),
              'cells':reports,
              'backend':'post194 fixed-Q jets + M51 Taylor lower-bound formula',
              'nonclaims':['not Lean checked','not all K positivity','not RH']}
    (p/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    return 0 if complete else 2

if __name__=='__main__':
    raise SystemExit(main())
