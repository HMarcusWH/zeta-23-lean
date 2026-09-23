#!/usr/bin/env python3
"""PR #247 global-parity-bottom canonical scout.

Research/falsification tooling only. The scout separates parity ordering from
entry into the theorem-relevant bad regime. A strict ordering with
lambda_global >= 0 is *not* called an EVEN_STRICT/ODD_STRICT bad branch.
"""
from __future__ import annotations

import json

import numpy as np

from canonical_source_numeric import canonical_source_matrix_L
from post150_selected_residual import exact_parity_basis, sympy_to_numpy
from post166_fb05_cell_interval import cell_coordinate_L
from post214_fb05_kernel_dual_geometry import quadratic_normal_exact

TARGET_K = 3
FROZEN_POINTS = (
    ("Q13_midpoint", 13, 0.5),
    ("Q14_midpoint", 14, 0.5),
    ("Q15_midpoint", 15, 0.5),
)


def classify_bottoms(le: float, lo: float) -> dict:
    if le < lo:
        ordering = "EVEN_BELOW_ODD"
    elif lo < le:
        ordering = "ODD_BELOW_EVEN"
    else:
        ordering = "TIE"

    lam = min(le, lo)
    bad = lam < 0.0
    if not bad:
        applicable = "NONE"
    elif le < lo:
        applicable = "EVEN_STRICT"
    elif lo < le:
        applicable = "ODD_STRICT"
    else:
        applicable = "TIE"

    return {
        "ordering": ordering,
        "bad_regime": bad,
        "applicable_branch": applicable,
        "lambda_global": lam,
        "absolute_gap": abs(le - lo),
    }


def _orthonormal_parity_basis(parity: str, K: int = TARGET_K) -> np.ndarray:
    B = sympy_to_numpy(exact_parity_basis(K, parity)).astype(float)
    Q, _ = np.linalg.qr(B)
    return Q


def _ground_record(M: np.ndarray, parity: str, K: int = TARGET_K) -> dict:
    Q = _orthonormal_parity_basis(parity, K)
    A = 0.5 * (Q.T @ M @ Q + (Q.T @ M @ Q).T)
    vals, vecs = np.linalg.eigh(A)
    j = int(np.argmin(vals))
    lam = float(vals[j])
    x = Q @ vecs[:, j]
    x = x / np.linalg.norm(x)

    n2 = np.array([float(v) for v in quadratic_normal_exact(K)], dtype=float)
    den = float(n2 @ n2)
    source = float((n2 @ M @ x) / den)
    idx = np.arange(-K, K + 1, dtype=float)
    moment4 = float((idx ** 4) @ x)

    return {
        "lambda": lam,
        "norm": float(np.linalg.norm(x)),
        "source_kernel_coordinate": source,
        "moment_four": moment4,
        "source_times_moment_four": source * moment4,
        "ground_vector": [float(v) for v in x],
    }


def evaluate_point(label: str, Qcell: int, t: float) -> dict:
    L = float(cell_coordinate_L(Qcell, t))
    M = np.asarray(canonical_source_matrix_L(L, TARGET_K), dtype=float)
    M = 0.5 * (M + M.T)

    even = _ground_record(M, "even")
    odd = _ground_record(M, "odd")
    cls = classify_bottoms(even["lambda"], odd["lambda"])

    return {
        "label": label,
        "Q": Qcell,
        "t": t,
        "L": L,
        "K": TARGET_K,
        "N": TARGET_K - 1,
        "lambda_even": even["lambda"],
        "lambda_odd": odd["lambda"],
        **cls,
        "any_parity_bad_numeric": cls["bad_regime"],
        "even": even,
        "odd": odd,
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
    }


def run() -> dict:
    rows = [evaluate_point(*p) for p in FROZEN_POINTS]
    return {
        "schema_version": "POST247_GLOBAL_BOTTOM_SCOUT_v2",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "scope": {
            "K": TARGET_K,
            "points": [
                {"label": label, "Q": q, "t": t}
                for label, q, t in FROZEN_POINTS
            ],
            "adaptive_search": False,
        },
        "rows": rows,
        "nonclaims": [
            "Numerical eigenvalues are not Lean theorem authority.",
            "Parity ordering outside lambda_global<0 is not a theorem branch.",
            "A sign at a frozen point is not a retained-state sign theorem.",
            "This scout does not evaluate an off-line-zero-generated state.",
            "No branch exclusion or RH claim is established.",
        ],
    }


def main() -> int:
    print(json.dumps(run(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
