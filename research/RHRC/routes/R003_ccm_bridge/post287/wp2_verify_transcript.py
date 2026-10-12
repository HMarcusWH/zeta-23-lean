#!/usr/bin/env python3
"""WP2 no-search checker: full rational cover and recomputed Arb lower bounds.

Higher precision verification and an independent code path for coverage;
both generator and verifier share the already audited fixed-Q evaluator.
"""
import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from flint import ctx

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent),str(HERE.parent/'post285')]
import canonical_source_arb as C
from wp2_k2_even_transcript import bound,cell_bounds


def f(x):return Fraction(int(x[0]),int(x[1]))


def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument('directory',type=Path)
    ap.add_argument('--precision-bits',type=int,default=192)
    args=ap.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    m=json.loads((args.directory/'manifest.json').read_text())
    if m['terminal_claim']!='RH_OPEN':raise AssertionError('claim firewall')
    qs=[];checked=0
    for cell in m['cells']:
        Q=cell['Q'];qs.append(Q)
        path=args.directory/cell['file'];raw=path.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=cell['sha256']:raise AssertionError('digest')
        d=json.loads(raw)
        if d['unresolved']:raise AssertionError(f'unresolved cell {Q}')
        if len(d['intervals'])!=cell['accepted_count']:raise AssertionError('count')
        lo,hi=cell_bounds(Q);cursor=lo
        for row in d['intervals']:
            left,right=f(row['left']),f(row['right'])
            if left!=cursor or not left<right:
                raise AssertionError((Q,'gap/overlap',cursor,left,right))
            c,r=(left+right)/2,(right-left)/2
            if f(row['centre'])!=c or f(row['radius'])!=r:
                raise AssertionError('centre/radius')
            if not bound(c,r,Q)['strictly_positive']:
                raise AssertionError((Q,'recomputed lower not positive',left,right))
            cursor=right;checked+=1
        if cursor!=hi:raise AssertionError((Q,'right mismatch',cursor,hi))
    if qs!=list(range(1,16)):raise AssertionError('not entire cutoff-cell range')
    print(json.dumps({'verdict':'PASS','package':'WP2_INDEPENDENT_NO_SEARCH_ARITH_CHECK',
                      'intervals':checked,'precision_bits':args.precision_bits,
                      'claim_status':'INTERVAL_EVIDENCE','terminal_claim':'RH_OPEN'}))
    return 0

if __name__=='__main__':
    raise SystemExit(main())
