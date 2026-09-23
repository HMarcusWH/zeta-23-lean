#!/usr/bin/env python3
"""Assert PR #247 scout semantics and positive controls.

This is implementation QA only. Synthetic matrices/values exercise classifier
behavior; real canonical float64 rows are checked only for internal
consistency and reconstruction, never for near-zero sign certification.
"""
from __future__ import annotations

import math

import numpy as np

from post247_global_bottom_scout import classify_bottoms, run as run_ground
from post247_global_bottom_arithmetic_scout import run as run_arithmetic


def _synthetic_bottom(A: np.ndarray) -> float:
    A = np.asarray(A, dtype=float)
    assert np.allclose(A, A.T)
    return float(np.linalg.eigvalsh(A)[0])


def _assert_synthetic_controls() -> None:
    controls = [
        (
            (np.diag([-2.0, 3.0]), np.diag([1.0, 4.0])),
            ("EVEN_BELOW_ODD", True, "EVEN_STRICT"),
        ),
        (
            (np.diag([1.0, 3.0]), np.diag([-2.0, 4.0])),
            ("ODD_BELOW_EVEN", True, "ODD_STRICT"),
        ),
        (
            (np.diag([-2.0, 4.0]), np.diag([-2.0, 7.0])),
            ("TIE", True, "TIE"),
        ),
        (
            (np.diag([1.0, 3.0]), np.diag([2.0, 4.0])),
            ("EVEN_BELOW_ODD", False, "NONE"),
        ),
        (
            (np.diag([2.0, 4.0]), np.diag([1.0, 3.0])),
            ("ODD_BELOW_EVEN", False, "NONE"),
        ),
        (
            (np.diag([1.0, 4.0]), np.diag([1.0, 7.0])),
            ("TIE", False, "NONE"),
        ),
    ]
    for (even_matrix, odd_matrix), expected in controls:
        le = _synthetic_bottom(even_matrix)
        lo = _synthetic_bottom(odd_matrix)
        got = classify_bottoms(le, lo)
        assert (
            got["ordering"],
            got["bad_regime"],
            got["applicable_branch"],
        ) == expected


def _assert_classifier_row(row: dict) -> None:
    le = float(row["lambda_even"])
    lo = float(row["lambda_odd"])
    expected = classify_bottoms(le, lo)
    for key in (
        "ordering",
        "bad_regime",
        "applicable_branch",
        "lambda_global",
        "absolute_gap",
    ):
        assert row[key] == expected[key]
    assert row["any_parity_bad_numeric"] == row["bad_regime"]


def main() -> int:
    _assert_synthetic_controls()

    ground = run_ground()
    assert ground["schema_version"] == "POST247_GLOBAL_BOTTOM_SCOUT_v2"
    assert len(ground["rows"]) == 3
    for row in ground["rows"]:
        _assert_classifier_row(row)
        for parity in ("even", "odd"):
            assert math.isclose(
                float(row[parity]["norm"]), 1.0, rel_tol=0.0, abs_tol=1e-10
            )

    arithmetic = run_arithmetic()
    assert arithmetic["schema_version"] == "POST247_GLOBAL_BOTTOM_ARITHMETIC_SCOUT_v2"
    assert len(arithmetic["rows"]) == 3
    for row in arithmetic["rows"]:
        expected = classify_bottoms(
            float(row["parities"]["even"]["lambda"]),
            float(row["parities"]["odd"]["lambda"]),
        )
        for key in (
            "ordering",
            "bad_regime",
            "applicable_branch",
            "lambda_global",
            "absolute_gap",
        ):
            assert row[key] == expected[key]
        for parity in ("even", "odd"):
            err = float(row["parities"][parity]["rayleigh_reconstruction_error"])
            assert math.isfinite(err)
            assert err < 1e-7

    print("POST247 GLOBAL BOTTOM SCOUT RESULTS: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
