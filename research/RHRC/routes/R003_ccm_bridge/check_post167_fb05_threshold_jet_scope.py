#!/usr/bin/env python3
"""Deterministic acceptance test for the post-#167 prime-threshold jet."""
from __future__ import annotations

import json
import math

import numpy as np
import sympy as sp

from post150_selected_residual import exact_parity_basis
from post167_fb05_threshold_jet import (
    centered_moment_row,
    predicted_even_order9_normalized,
    predicted_odd_order7_normalized,
    restricted_normalized_series_coefficient_sympy,
    source_entry_float,
    source_matrix_float,
)


def _physical_qbasis_from_omega(omega: float, n: int, m: int) -> float:
    ratio = 1.0 - omega
    if n == m:
        return 2.0 * omega * math.cos(2.0 * math.pi * n * ratio)
    return (
        math.sin(2.0 * math.pi * n * ratio)
        - math.sin(2.0 * math.pi * m * ratio)
    ) / (math.pi * (m - n))


def _assert_zero_matrix(A: sp.Matrix, label: str) -> None:
    if A != sp.zeros(A.rows, A.cols):
        raise AssertionError(f"{label} is not exactly zero: {A}")


def main() -> int:
    checks: list[dict] = []

    # Exact geometry and exact rational Taylor-coefficient identities.
    for K in range(2, 9):
        for parity in ("even", "odd"):
            B = exact_parity_basis(K, parity)
            for order in range(3):
                row = centered_moment_row(K, B, order)
                _assert_zero_matrix(row, f"K={K} parity={parity} M{order}")

        # Odd boundary-flat: orders 1,3,5 vanish; order 7 is the M3 square.
        for k in range(3):
            A = restricted_normalized_series_coefficient_sympy(K, "odd", k)
            _assert_zero_matrix(A, f"K={K} odd source order {2*k+1}")
        odd7 = restricted_normalized_series_coefficient_sympy(K, "odd", 3)
        odd7_expected = predicted_odd_order7_normalized(K)
        _assert_zero_matrix(sp.simplify(odd7 - odd7_expected), f"K={K} odd order-7 M3 law")

        # Even boundary-flat: parity additionally kills M3, so orders 1..7
        # vanish and order 9 is the M4 square.
        for k in range(4):
            A = restricted_normalized_series_coefficient_sympy(K, "even", k)
            _assert_zero_matrix(A, f"K={K} even source order {2*k+1}")
        even9 = restricted_normalized_series_coefficient_sympy(K, "even", 4)
        even9_expected = predicted_even_order9_normalized(K)
        _assert_zero_matrix(sp.simplify(even9 - even9_expected), f"K={K} even order-9 M4 law")

        checks.append(
            {
                "K": K,
                "odd_dimension": exact_parity_basis(K, "odd").cols,
                "even_dimension": exact_parity_basis(K, "even").cols,
                "odd_first_surviving_order": 7,
                "even_first_surviving_order": 9,
            }
        )

    # Independent convention acceptance: direct source-coordinate formula must
    # agree with qBasis after y/L = 1-omega.
    max_convention_error = 0.0
    for omega in (-0.125, -0.03125, 0.03125, 0.125):
        for n in range(-4, 5):
            for m in range(-4, 5):
                a = source_entry_float(omega, n, m)
                b = _physical_qbasis_from_omega(omega, n, m)
                max_convention_error = max(max_convention_error, abs(a - b))
    if max_convention_error > 2e-13:
        raise AssertionError(f"source/qBasis convention drift: {max_convention_error}")

    if not np.array_equal(source_matrix_float(0.0, 4), np.zeros((9, 9))):
        raise AssertionError("sourceMatrix(omega=0) is not exactly zero in executable layer")

    payload = {
        "schema_version": "POST167_FB05_THRESHOLD_JET_CHECK_v1",
        "status": "PASS",
        "claim_cap": "EXACT_EXECUTABLE_ALGEBRA_ONLY",
        "checked_K": list(range(2, 9)),
        "exact_identities": {
            "boundary_flat_M0_M1_M2": True,
            "odd_orders_1_3_5_zero": True,
            "odd_order_7_eq_minus_2_over_7fact_M3sq_after_common_pi_factor": True,
            "even_orders_1_3_5_7_zero": True,
            "even_order_9_eq_plus_2_over_9fact_M4sq_after_common_pi_factor": True,
        },
        "source_qbasis_max_abs_error": max_convention_error,
        "source_matrix_zero_at_threshold": True,
        "records": checks,
        "interpretation": (
            "These are exact SymPy identities for the executable source-atom Taylor coefficients "
            "on the exact boundary-flat parity bases. They are not Lean theorem authority."
        ),
        "nonclaims": [
            "No aperture-cell positivity theorem is claimed.",
            "No finite bad successor is claimed.",
            "No RH-equivalent conclusion is claimed.",
            "RH remains OPEN.",
        ],
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
