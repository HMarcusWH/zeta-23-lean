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
from flint import arb, ctx, fmpq

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent),str(HERE.parent/'post285')]
import canonical_source_arb as C
from wp2_k2_even_transcript import verified_cell_bounds
from post285.post285_m51_k2_even_bottom_certificate import quad
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as matrix_jets)
from certificate_integrity import rational, record_path, source_input_digests



def exact_arb(value: Fraction) -> arb:
    """The checker never converts a transcript rational via binary float."""
    return arb(fmpq(value.numerator, value.denominator))


def verify_fresh_lower(centre: Fraction, radius: Fraction, cell: int) -> bool:
    """Fresh higher-precision formula, not the transcript writer's accepted_bound."""
    C, R = exact_arb(centre), exact_arb(radius)
    M0, M1, _ = matrix_jets(C, 2, cell)
    _, _, M2box = matrix_jets(arb(C, R), 2, cell)
    value, slope, curvature = quad(M0), quad(M1), quad(M2box)
    bound = (value - abs(slope).upper() * R +
             min(arb(0), curvature.lower()) * R * R / 2).lower()
    return bool(bound > 0)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('directory',type=Path)
    p.add_argument('--precision-bits',type=int,default=192)
    args=p.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    m=json.loads((args.directory/'manifest.json').read_text())
    if (m.get('schema')!='post287.wp2.k2-m51.arb.v1' or
            m.get('terminal_claim')!='RH_OPEN' or
            m.get('status')!='INTERVAL_EVIDENCE' or
            m.get('source_digests')!=source_input_digests() or
            args.precision_bits<=m['prec_bits']):
        raise AssertionError('manifest schema/claim/source/precision mismatch')
    qs=[];count=0
    for info in m['cells']:
        Q=info['Q'];qs.append(Q)
        path=record_path(args.directory,info['file'])
        raw=path.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=info['sha256']:
            raise AssertionError(('digest mismatch',Q))
        cell=json.loads(raw)
        if cell['cell_Q'] != Q or info['file'] != f'cell_{Q:02}.json':
            raise AssertionError(('manifest/payload cell mismatch',Q))
        if cell['unresolved']:
            raise AssertionError(('unresolved',Q,len(cell['unresolved'])))
        if (len(cell['intervals'])!=info['accepted_count'] or
                cell['accepted_count']!=info['accepted_count'] or
                info['unresolved_count']!=0):
            raise AssertionError(('count mismatch',Q))
        a,b=verified_cell_bounds(Q)
        if rational(cell['left'])!=a or rational(cell['right'])!=b:
            raise AssertionError(('incorrect target bounds',Q))
        current=a
        for row in cell['intervals']:
            left,right=rational(row['left']),rational(row['right'])
            if left!=current or not left<right:
                raise AssertionError(('gap or overlap',Q,current,left,right))
            centre,radius=(left+right)/2,(right-left)/2
            if rational(row['centre'])!=centre or rational(row['radius'])!=radius:
                raise AssertionError(('centre mismatch',Q,left,right))
            if row.get('strictly_positive') is not True or not verify_fresh_lower(centre,radius,Q):
                raise AssertionError(('invalid Arb lower bound',Q,left,right))
            current=right;count+=1
        if current!=b:
            raise AssertionError(('right endpoint',Q,current,b))
    if qs!=list(range(1,16)):
        raise AssertionError(('not all Q1..15 covered',qs))
    if count != m['interval_records']:
        raise AssertionError('incorrect manifest total interval count')
    print(json.dumps({'verdict':'PASS','package':'WP2_CHECK_M51_COVER_NO_SEARCH',
                      'intervals':count,'precision_bits':args.precision_bits,
                      'status':'INTERVAL_EVIDENCE','terminal_claim':'RH_OPEN'}))
    return 0


if __name__=='__main__':
    raise SystemExit(main())
