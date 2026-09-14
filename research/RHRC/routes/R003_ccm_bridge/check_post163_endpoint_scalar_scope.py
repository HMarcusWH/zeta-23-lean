#!/usr/bin/env python3
"""Deterministic plumbing audit for the post-#163 FB-05 endpoint scalar.

This script checks implementation/normalization consistency only.  It does not
require a positive sign and does not promote any theorem or RH claim.
"""
from __future__ import annotations

import json

import mpmath as mp
import sympy as sp
from flint import arb

from canonical_riesz_endpoint_scalar import (
    canonical_riesz_endpoint_scalar_arb,
    canonical_riesz_endpoint_scalar_mp,
    dyadic_inside_cell,
    endpoint_record_arb,
    pole_endpoint_primitive_mp,
    pole_endpoint_primitive_nine_expanded_mp,
    pole_prime_endpoint_primitive_mp,
)
from canonical_source_arb import set_precision, to_arb_rational


def von_mangoldt_mp(q: int) -> mp.mpf:
    fac = sp.factorint(int(q))
    if len(fac) != 1:
        return mp.mpf("0")
    p = next(iter(fac))
    return mp.log(int(p))


def independent_convolution_mp(primitive_order: int, Q: int, L: mp.mpf) -> mp.mpf:
    """Independent piecewise convolution of the exact Lean discrepancy."""
    n = int(primitive_order)
    if n < 1:
        raise ValueError("primitive_order must be >=1")
    L = mp.mpf(L)
    events = []
    for q in range(2, Q + 1):
        vm = von_mangoldt_mp(q)
        if vm == 0:
            continue
        events.append((mp.log(q), vm / mp.sqrt(q)))
    events.sort(key=lambda row: row[0])

    fact = mp.factorial(n - 1)
    total = mp.mpf("0")
    cumulative = mp.mpf("0")
    left = mp.mpf("0")

    def integrate_piece(a: mp.mpf, b: mp.mpf, stair: mp.mpf) -> mp.mpf:
        if not b > a:
            return mp.mpf("0")
        return mp.quad(
            lambda t: ((L - t) ** (n - 1) / fact)
            * (4 * mp.sinh(t / 2) - stair),
            [a, b],
        )

    for threshold, weight in events:
        if threshold > L:
            break
        total += integrate_piece(left, threshold, cumulative)
        cumulative += weight
        left = threshold
    total += integrate_piece(left, L, cumulative)
    return total


def close_enough(a: mp.mpf, b: mp.mpf, digits: int = 55) -> bool:
    scale = max(mp.mpf("1"), abs(a), abs(b))
    return abs(a - b) <= mp.power(10, -digits) * scale


def main() -> int:
    mp.mp.dps = 100
    failures: list[dict] = []
    checks: list[dict] = []

    # 1. Exact convention lock: Riesz order 8 means primitive order 9 and L^-9.
    Q = 4
    num, den = dyadic_inside_cell(Q, mp.mpf("0.5"), bits=48)
    L = mp.mpf(num) / den
    p9 = pole_prime_endpoint_primitive_mp(9, Q, L)
    s8 = canonical_riesz_endpoint_scalar_mp(8, Q, L)
    convention_ok = close_enough(s8, p9 / L**9, digits=70)
    checks.append({"name": "r8_uses_p9_and_L_minus_9", "pass": convention_ok})
    if not convention_ok:
        failures.append({"check": "r8_uses_p9_and_L_minus_9"})

    # 2. Stable Taylor-tail pole formula agrees with the expanded order-nine form.
    pole_rows = []
    for Q in (1, 2, 4, 8):
        num, den = dyadic_inside_cell(Q, mp.mpf("0.5"), bits=48)
        L = mp.mpf(num) / den
        stable = pole_endpoint_primitive_mp(9, L)
        expanded = pole_endpoint_primitive_nine_expanded_mp(L)
        ok = close_enough(stable, expanded, digits=65)
        pole_rows.append({"Q": Q, "pass": ok, "difference": mp.nstr(stable - expanded, 20)})
        if not ok:
            failures.append({"check": "order_nine_pole_expansion", "Q": Q})
    checks.append({"name": "order_nine_pole_expansion", "rows": pole_rows})

    # 3. Closed finite form agrees with an independent piecewise convolution.
    conv_rows = []
    for Q in (1, 2, 3, 4, 5):
        num, den = dyadic_inside_cell(Q, mp.mpf("0.5"), bits=44)
        L = mp.mpf(num) / den
        for n in (1, 2, 3, 9):
            closed = pole_prime_endpoint_primitive_mp(n, Q, L)
            direct = independent_convolution_mp(n, Q, L)
            ok = close_enough(closed, direct, digits=45)
            conv_rows.append(
                {
                    "Q": Q,
                    "primitive_order": n,
                    "pass": ok,
                    "difference": mp.nstr(closed - direct, 20),
                }
            )
            if not ok:
                failures.append(
                    {"check": "closed_form_vs_piecewise_convolution", "Q": Q, "n": n}
                )
    checks.append({"name": "closed_form_vs_piecewise_convolution", "rows": conv_rows})

    # 4. Adjacent cell formulas agree at every tested threshold.  A newly entering
    # prime-power term vanishes there because (L-log q)^n = 0.
    threshold_rows = []
    for Q in range(1, 13):
        L0 = mp.log(Q + 1)
        left = pole_prime_endpoint_primitive_mp(9, Q, L0)
        right = pole_prime_endpoint_primitive_mp(9, Q + 1, L0)
        ok = close_enough(left, right, digits=65)
        threshold_rows.append(
            {"Q_left": Q, "Q_right": Q + 1, "pass": ok, "difference": mp.nstr(left - right, 20)}
        )
        if not ok:
            failures.append({"check": "cutoff_threshold_continuity", "Q": Q})
    checks.append({"name": "cutoff_threshold_continuity", "rows": threshold_rows})

    # 5. High-precision mpmath values overlap the raw rigorous Arb balls.  Do not
    # compare against ball_record display strings: those are intentionally rounded.
    arb_rows = []
    set_precision(320)
    for Q in (1, 2, 4, 8):
        num, den = dyadic_inside_cell(Q, mp.mpf("0.5"), bits=48)
        L = mp.mpf(num) / den
        value = canonical_riesz_endpoint_scalar_mp(8, Q, L)
        rec = endpoint_record_arb(8, Q, num, den, precision_bits=320)
        L_arb = to_arb_rational(num, den)
        raw_ball = canonical_riesz_endpoint_scalar_arb(8, Q, L_arb)
        mp_ball = arb(mp.nstr(value, 90))
        delta = raw_ball - mp_ball
        ok = bool(rec["cell"]["certified"] and delta.contains(0))
        arb_rows.append(
            {
                "Q": Q,
                "L_num": num,
                "L_den": den,
                "pass": ok,
                "mp_value": mp.nstr(value, 30),
                "arb": rec["endpoint_scalar"],
                "raw_overlap_difference": delta.str(30, more=True),
            }
        )
        if not ok:
            failures.append({"check": "mp_value_overlaps_raw_arb_ball", "Q": Q})
    checks.append({"name": "mp_value_overlaps_raw_arb_ball", "rows": arb_rows})

    payload = {
        "schema_version": "POST163_ENDPOINT_SCALAR_CHECK_v1",
        "status": "PASS" if not failures else "FAIL",
        "claim_cap": "NORMALIZATION_AND_IMPLEMENTATION_AUDIT_ONLY",
        "checks": checks,
        "failures": failures,
        "nonclaims": [
            "No sign of canonicalPolePrimeRieszEndpointScalar L 8 is asserted globally.",
            "No finite numerical audit is Lean theorem authority.",
            "No FB-05 closure follows from this plumbing check.",
            "RH remains OPEN.",
        ],
    }
    print(json.dumps(payload, indent=2))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
