#!/usr/bin/env python3
"""Reject unknown Taylor remainders, including the historical nan -> zero bug.

The analytic negative control f(x)=1-4*x^2 has positive centre value and zero
slope, but is negative at x=1. An unavailable curvature bound cannot justify
dropping that remainder. Backend stubs inject exactly that missing information
into every production/checker entry point; no synthetic matrix is evidence.
"""
from __future__ import annotations

import sys
import time
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from flint import arb,arb_mat,ctx

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent),str(HERE.parent/'post285')]
import canonical_source_arb as C
import wp2_k2_even_transcript as even
import wp2_verify_transcript as checker
import wp4_k2_odd_prerequisite as odd
import wp4_k3_frozen_q14_gate as frozen
import wp4_k3_full_continuum as full
import wp4_k3_fourth_order_fallback as fourth
import wp2_wp4_normalization_gate as normalization
import post285_m51_k2_even_bottom_certificate as legacy


def fake_jets(size:int):
    identity=arb_mat([[arb(int(i==j)) for j in range(size)] for i in range(size)])
    zero=arb_mat([[arb(0) for _ in range(size)] for _ in range(size)])
    unknown=arb_mat([[arb('nan') for _ in range(size)] for _ in range(size)])
    return identity,zero,unknown


def check()->None:
    ctx.prec=192
    nan=arb('nan')
    # Demonstrate the old failure; this must never be used for acceptance.
    assert min(arb(0),nan.lower()).is_zero()
    assert bool(arb(1)-4*arb(1)**2<0)
    assert not C.definitely_positive(C.finite_second_order_lower(arb(1),arb(0),nan,arb(1)))
    assert not C.definitely_positive(C.finite_second_order_lower(arb(1),arb(0),arb(-8),arb(1)))
    assert C.definitely_positive(C.finite_second_order_lower(arb(1),arb(0),arb(8),arb(1)))
    for missing in (nan,arb('+inf'),arb('-inf')):
        for index in range(4):
            jets=[arb(1),arb(0),arb(0),arb(1)]
            jets[index]=missing
            assert not C.definitely_positive(C.finite_second_order_lower(*jets))
    assert not C.definitely_positive(arb('+inf'))
    assert not C.definitely_negative(arb('-inf'))

    small=fake_jets(5)
    with patch.object(even,'jets',return_value=small):
        assert even.accepted_bound(Fraction(3,2),Fraction(1,100),4)['strictly_positive'] is False
    with patch.object(checker,'matrix_jets',return_value=small):
        assert checker.verify_fresh_lower(Fraction(3,2),Fraction(1,100),4) is False
    with patch.object(odd,'jets',return_value=small):
        assert odd.bound(Fraction(3,2),Fraction(1,100),4)['positive'] is False
    with patch.object(legacy,'jets',return_value=small):
        assert not C.definitely_positive(legacy.lower_bound(Fraction(3,2),Fraction(1,100),4))
    assert not C.definitely_positive(frozen.taylor_lower((arb(1),arb(0),nan),arb(1)))

    with patch.object(full,'M012',return_value=fake_jets(7)):
        tile=(Fraction(149,100),Fraction(151,100))
        assert full.evaluate(tile,'even',4,'SECOND')['accepted'] is False
        result=full.cover(4,'even','SECOND',0,10,time.monotonic()+60)
        assert result['status']=='UNRESOLVED' and result['accepted']==[] and result['unresolved']
    for index in range(5):
        centre=[arb(1),arb(0),arb(0),arb(0)]
        remainder=arb(0)
        if index<4:centre[index]=nan
        else:remainder=nan
        assert not C.definitely_positive(fourth.taylor_lower(centre,remainder,arb(1)))

    # Unknown overlap is not source-normalization agreement either.
    identity,_,unknown=fake_jets(7)
    with patch.object(C,'canonical_source_matrix',return_value=unknown),\
         patch.object(normalization,'fixed_unit_fixed_q_canonical_source_matrix_arb',return_value=identity):
        try:
            normalization.compare(Fraction(267,100),14,3)
        except ArithmeticError:
            pass
        else:
            raise AssertionError('indeterminate source comparison accepted')
    print('WP2/WP4 FINITE-BOUND REGRESSION: PASS (unknown remainder rejects; finite positive and negative controls; producer/checker/gate/fallback/normalization coverage)')


if __name__=='__main__':
    check()
