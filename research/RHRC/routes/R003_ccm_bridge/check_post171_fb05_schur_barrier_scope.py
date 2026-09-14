#!/usr/bin/env python3
"""Deterministic acceptance checks for post-#171 Schur-barrier tooling."""
from __future__ import annotations

import json

import numpy as np
from numpy.polynomial.legendre import leggauss

from post169_fb05_schur_visibility import directional_schur_derivative_float, schur_pivot_float
from post171_fb05_schur_barrier import arithmetic_cell, barrier_point, direct_cell_budget


def _synthetic_envelope_check() -> dict:
    H0 = np.array([[4.0, 0.5, 0.3], [0.5, 3.0, -0.2], [0.3, -0.2, 2.5]])
    D1 = np.array([[0.2, -0.1, 0.05], [-0.1, 0.3, 0.04], [0.05, 0.04, -0.15]])
    D2 = np.array([[0.03, 0.02, -0.01], [0.02, -0.04, 0.03], [-0.01, 0.03, 0.02]])

    def H(t: float) -> np.ndarray:
        return H0 + t * D1 + (t * t) * D2

    p0 = schur_pivot_float(H(0.0))["pivot"]
    p1 = schur_pivot_float(H(1.0))["pivot"]

    xs, ws = leggauss(32)
    ts = 0.5 * (xs + 1.0)
    weights = 0.5 * ws
    total = 0.0
    channel1 = 0.0
    channel2 = 0.0
    for t, w in zip(ts, weights):
        Ht = H(float(t))
        d1 = directional_schur_derivative_float(Ht, D1)
        d2 = directional_schur_derivative_float(Ht, 2.0 * float(t) * D2)
        channel1 += float(w) * d1
        channel2 += float(w) * d2
        total += float(w) * (d1 + d2)

    direct = float(p1 - p0)
    err = abs(total - direct)
    channel_err = abs((channel1 + channel2) - total)
    if err > 2e-12:
        raise AssertionError(f"synthetic envelope integration mismatch: {err}")
    if channel_err > 2e-14:
        raise AssertionError(f"synthetic channel additivity mismatch: {channel_err}")
    return {
        "direct_pivot_change": direct,
        "integrated_directional_change": total,
        "channel1_integral": channel1,
        "channel2_integral": channel2,
        "integration_error": err,
        "channel_additivity_error": channel_err,
    }


def _arithmetic_cell_checks() -> list[dict]:
    expected = {9: 11, 11: 13, 13: 16, 16: 17, 17: 19}
    rows = []
    for q, qnext in expected.items():
        cell = arithmetic_cell(q)
        if cell.q_next != qnext:
            raise AssertionError(f"wrong next von-Mangoldt threshold after {q}: {cell.q_next}")
        rows.append({"q": q, "q_next": cell.q_next, "omega_end": cell.omega_end})
    return rows


def _production_budget_check() -> dict:
    budget = direct_cell_budget(17, 3, "odd")
    err = abs(float(budget["unit_cell_budget_reconstruction_error"]))
    if err > 5e-15:
        raise AssertionError(f"direct q17 cell-budget reconstruction failed: {err}")
    start = barrier_point(17, 3, "odd", 0.0)
    if abs(float(start["unit_exact_entry_lift"])) > 5e-15:
        raise AssertionError("entering q atom does not vanish at its threshold")
    return {
        "q": 17,
        "N": 3,
        "parity": "odd",
        "budget_reconstruction_error": err,
        "threshold_entry_lift": start["unit_exact_entry_lift"],
        "H1_start": start["H1_full"],
    }


def main() -> int:
    synthetic = _synthetic_envelope_check()
    cells = _arithmetic_cell_checks()
    production = _production_budget_check()
    payload = {
        "schema_version": "POST171_FB05_SCHUR_BARRIER_CHECK_v1",
        "status": "PASS",
        "claim_cap": "EXACT_EXECUTABLE_ACCOUNTING_AND_NUMERICAL_METHOD_CHECK_ONLY",
        "checks": {
            "synthetic_envelope_integral_matches_direct_pivot_change": True,
            "synthetic_channel_integrals_add": True,
            "genuine_von_mangoldt_seams_identified": True,
            "q17_direct_cell_budget_reconstructs": True,
            "entering_atom_lift_vanishes_at_threshold": True,
        },
        "synthetic": synthetic,
        "arithmetic_cells": cells,
        "production_smoke": production,
        "nonclaims": [
            "The production derivative quadrature is a diagnostic, not a theorem or hard sign gate.",
            "No sampled barrier survival is promoted by this acceptance checker.",
            "No whole-cell Arb positivity is claimed.",
            "RH remains OPEN."
        ],
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
