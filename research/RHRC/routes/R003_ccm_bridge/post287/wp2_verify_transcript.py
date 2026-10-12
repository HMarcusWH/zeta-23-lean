#!/usr/bin/env python3
"""WP2 no-search checker for M51 Arb coverage.

Checks manifest SHA256, exact rational partition of each prime-cutoff cell,
recomputes every strict lower enclosure at fresh higher precision, and
rejects omissions/overlaps/unresolved intervals. Uses the same source matrix
backend; it is not an independent Lean↔Python compilation proof.
"""
from __future__ import annotations

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
from wp2_k2_even_transcript import accepted_bound,verified_cell_bounds


def rational(t:list[int])->Fraction:
    assert len(t)==2
    return Fraction(int(t[0]),int(t[1]))


def main():
    p=argparse.ArgumentParser()
    p.add_argument('directory',type=Path)
    p.add_argument('--precision-bits',type=int,default=192)
    args=p.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    m=json.loads((args.directory/'manifest.json').read_text())
    assert m['terminal_claim']=='RH_OPEN'
    assert m['status']=='INTERVAL_EVIDENCE'
    assert args.precision_bits>m['prec_bits']
    qs=[];count=0
    for info in m['cells']:
        Q=info['Q'];qs.append(Q)
        path=args.directory/info['file']
        raw=path.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=info['sha256']:
            raise AssertionError(('digest mismatch',Q))
        cell=json.loads(raw)
        if cell['unresolved']:
            raise AssertionError(('unresolved',Q,len(cell['unresolved'])))
        if len(cell['intervals'])!=info['accepted_count']:
            raise AssertionError(('count mismatch',Q))
        a,b=verified_cell_bounds(Q)
        current=a
        for row in cell['intervals']:
            left,right=rational(row['left']),rational(row['right'])
            if left!=current or not left<right:
                raise AssertionError(('gap or overlap',Q,current,left,right))
            centre,radius=(left+right)/2,(right-left)/2
            if rational(row['centre'])!=centre or rational(row['radius'])!=radius:
                raise AssertionError(('centre mismatch',Q,left,right))
            if not accepted_bound(centre,radius,Q)['strictly_positive']:
                raise AssertionError(('invalid Arb lower bound',Q,left,right))
            current=right;count+=1
        if current!=b:
            raise AssertionError(('right endpoint',Q,current,b))
    if qs!=list(range(1,16)):
        raise AssertionError(('not all Q1..15 covered',qs))
    print(json.dumps({'verdict':'PASS','package':'WP2_CHECK_M51_COVER_NO_SEARCH',
                      'intervals':count,'precision_bits':args.precision_bits,
                      'status':'INTERVAL_EVIDENCE','terminal_claim':'RH_OPEN'}))
    return 0


if __name__=='__main__':
    raise SystemExit(main())
