#!/usr/bin/env python3
"""PR #247 frozen arithmetic/channel scout.

Research-only companion to post247_global_bottom_scout.py.  It evaluates the
canonical channel decomposition on the normalized parity ground vectors at the
same preregistered Q13/Q14/Q15 midpoint points.

This is deliberately not the generated retained zero-shift witness and is not
used as theorem authority.  Its purpose is adversarial: candidate sign or
magnitude laws proposed for the formal global-bottom route should survive this
cheap canonical check before being promoted to a Lean theorem target.
"""
from __future__ import annotations

import json

import numpy as np

from canonical_source_numeric import (
    canonical_channel_energies_L,
    canonical_source_matrix_L,
)
from post247_global_bottom_scout import (
    FROZEN_POINTS,
    TARGET_K,
    _orthonormal_parity_basis,
)
from post166_fb05_cell_interval import cell_coordinate_L


def ground_vector(M: np.ndarray, parity: str) -> tuple[float, np.ndarray]:
    Q = _orthonormal_parity_basis(parity, TARGET_K)
    A = 0.5 * (Q.T @ M @ Q + (Q.T @ M @ Q).T)
    vals, vecs = np.linalg.eigh(A)
    j = int(np.argmin(vals))
    x = Q @ vecs[:, j]
    x = x / np.linalg.norm(x)
    return float(vals[j]), x


def evaluate(label: str, q: int, t: float) -> dict:
    L = float(cell_coordinate_L(q, t))
    M = np.asarray(canonical_source_matrix_L(L, TARGET_K), dtype=float)
    M = 0.5 * (M + M.T)
    out = {"label": label, "Q": q, "t": t, "L": L, "parities": {}}
    for parity in ("even", "odd"):
        lam, x = ground_vector(M, parity)
        channels = canonical_channel_energies_L(L, TARGET_K, x)
        out["parities"][parity] = {
            "lambda": lam,
            "channel_energies": channels,
            "rayleigh_reconstruction_error": abs(
                channels["total_direct"] - lam
            ),
        }
    out["claim_cap"] = "EXPERIMENTAL_SIGNAL_ONLY"
    return out


def main() -> int:
    payload = {
        "schema_version": "POST247_GLOBAL_BOTTOM_ARITHMETIC_SCOUT_v1",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "scope": {
            "K": TARGET_K,
            "points": [
                {"label": label, "Q": q, "t": t}
                for label, q, t in FROZEN_POINTS
            ],
            "adaptive_search": False,
        },
        "rows": [evaluate(*p) for p in FROZEN_POINTS],
        "nonclaims": [
            "Ground-vector channel data are numerical research signals only.",
            "These vectors are not off-line-zero-generated retained witnesses.",
            "No channel sign is promoted to a theorem.",
            "No branch exclusion or RH claim is established.",
        ],
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
