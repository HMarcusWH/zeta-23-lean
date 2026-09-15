#!/usr/bin/env python3
"""Correlation-preserving determinant-derivative utilities after PR #179.

This module reuses the complete fixed-Q canonical derivative implementation
validated by PR #178 and compares two exact enclosure graphs for the same
q13/N2/K3/even determinant derivative:

    raw:   Delta_2' = a'd + ad' - 2bb'

and, only inside certified H1 scope a>0,

    x  = b/a
    P  = d - b*x
    P' = d' - 2b'*x + a'*x^2
    Delta_2' = a'P + aP'.

The Schur form is the one-dimensional specialization of the theorem-aligned
[W|c] directional Schur derivative already used elsewhere in the R003 route.
It is an alternative interval dependency graph, not a new mathematical object.

Research/audit tooling only. No output here is Lean theorem authority.
RH remains OPEN.
"""
from __future__ import annotations

from flint import arb

from canonical_source_arb import definitely_negative, definitely_positive
from post166_fb05_cell_interval import arb_unit_interval, cell_coordinate_L_arb
from post177_fb05_q13_fixed_unit_derivative import (
    fixed_unit_derivative_scalar_interval_record_arb,
    fixed_unit_derivative_scalar_record_arb_at_L,
)


def overlap(x: arb, y: arb) -> bool:
    return bool((x - y).contains(0))


def arb_width(x: arb) -> arb:
    return arb(x.upper()) - arb(x.lower())


def sign_class(x: arb) -> str:
    if definitely_positive(x):
        return "POSITIVE_CERTIFIED"
    if definitely_negative(x):
        return "NEGATIVE_CERTIFIED"
    return "UNRESOLVED"


def schur_factorized_even_record(even: dict) -> dict:
    """Return the H1-guarded Schur graph for one even scalar record."""
    a = even["a"]
    b = even["b"]
    d = even["d"]
    ap = even["a_prime"]
    bp = even["b_prime"]
    dp = even["d_prime"]
    delta = even["delta2"]
    delta_prime_raw = even["delta2_prime"]

    if not definitely_positive(a):
        return {
            "h1_certified": False,
            "scope": "OUT_OF_CERTIFIED_H1_SCOPE",
        }

    x = b / a
    pivot = d - b * x
    pivot_prime_directional = dp - 2 * bp * x + ap * x * x
    delta_factorized = a * pivot
    delta_prime_factorized = ap * pivot + a * pivot_prime_directional
    pivot_prime_quotient = (delta_prime_raw * a - delta * ap) / (a * a)

    return {
        "h1_certified": True,
        "scope": "CERTIFIED_H1_SCOPE",
        "x": x,
        "pivot": pivot,
        "pivot_prime_directional": pivot_prime_directional,
        "pivot_prime_quotient": pivot_prime_quotient,
        "delta2_factorized": delta_factorized,
        "delta2_prime_factorized": delta_prime_factorized,
        "delta2_overlap": overlap(delta, delta_factorized),
        "delta2_prime_overlap": overlap(delta_prime_raw, delta_prime_factorized),
        "pivot_prime_overlap": overlap(pivot_prime_directional, pivot_prime_quotient),
    }


def augment_derivative_record(rec: dict) -> dict:
    even = rec["even"]
    return {
        "record": rec,
        "raw_delta2": even["delta2"],
        "raw_delta2_prime": even["delta2_prime"],
        "raw_delta2_prime_sign": sign_class(even["delta2_prime"]),
        "schur": schur_factorized_even_record(even),
    }


def point_record_from_box(box: dict) -> dict:
    """Evaluate the exact dyadic center of one inherited #178 schedule box."""
    den = int(box["den"])
    center_num = int(box["center_num"])
    if den <= 0 or not 0 <= center_num <= den:
        raise ValueError("invalid exact dyadic center")
    t = arb(center_num) / den
    Q = int(box["Q"])
    L = cell_coordinate_L_arb(Q, t)
    rec = fixed_unit_derivative_scalar_record_arb_at_L(Q, L)
    return {
        "label": box["label"],
        "Q": Q,
        "t": t,
        "L": L,
        "center_num": center_num,
        "den": den,
        **augment_derivative_record(rec),
    }


def interval_record_from_box(box: dict) -> dict:
    """Evaluate one inherited finite-width #178 schedule box."""
    Q = int(box["Q"])
    rec = fixed_unit_derivative_scalar_interval_record_arb(
        Q,
        int(box["lo_num"]),
        int(box["hi_num"]),
        int(box["den"]),
    )
    return {
        "label": box["label"],
        "Q": Q,
        "t": rec["t"],
        "L": rec["L"],
        **augment_derivative_record(rec),
    }


def inherited_box_ball(box: dict) -> arb:
    return arb_unit_interval(int(box["lo_num"]), int(box["hi_num"]), int(box["den"]))
