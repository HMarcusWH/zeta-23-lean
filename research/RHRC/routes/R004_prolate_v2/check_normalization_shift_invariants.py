"""R004 scalar-shift invariance audit after the PR #71 normalization repair.

REFERENCE/REGRESSION CHECK ONLY.  Lean is theorem authority for the exact
commutator transfer.  This script checks that the historical printed matrix M
and canonical direct-source matrix Q = M + 2*cCorrection(L) I behave exactly as
the scalar-shift analysis predicts.

Invariant lanes checked:
- centered-index commutator,
- eigenvalue gaps,
- eigenvector projectors,
- displacement singular values.

Shift-sensitive lanes checked:
- absolute eigenvalues,
- trace,
- Frobenius/operator norms.

No RH evidence or theorem promotion follows from this script.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np

from run_commutator_gauntlet_v2 import build_ccm_matrix, c_correction


DEFAULT_CASES = [(2.0, 2), (2.0, 4), (3.0, 2), (3.0, 4), (5.0, 2), (5.0, 4)]


def run_case(lam: float, N: int) -> dict:
    legacy = build_ccm_matrix(lam, N)
    L = 2.0 * math.log(lam)
    shift = 2.0 * c_correction(L)
    canonical = legacy + shift * np.eye(legacy.shape[0])

    dim = legacy.shape[0]
    D = np.diag(np.arange(dim) - (dim - 1) / 2)
    comm_legacy = D @ legacy - legacy @ D
    comm_canonical = D @ canonical - canonical @ D

    eval_legacy, evec_legacy = np.linalg.eigh(legacy)
    eval_canonical = np.linalg.eigvalsh(canonical)

    # Do not compare independently returned LAPACK eigenvector bases here:
    # repeated or numerically clustered eigenvalues permit arbitrary rotations
    # inside an eigenspace.  Scalar-shift invariance is tested directly by
    # applying the canonical matrix to the legacy eigenbasis.
    canonical_on_legacy_basis = canonical @ evec_legacy
    shifted_legacy_action = evec_legacy * (eval_legacy + shift)[None, :]
    eigenvector_equation_residual = np.linalg.norm(
        canonical_on_legacy_basis - shifted_legacy_action, ord="fro"
    )

    gap_legacy = np.diff(eval_legacy)
    gap_canonical = np.diff(eval_canonical)

    trace_expected = dim * shift
    return {
        "lambda": lam,
        "N": N,
        "dimension": dim,
        "L": L,
        "scalar_shift": shift,
        "max_matrix_shift_residual": float(
            np.max(np.abs(canonical - legacy - shift * np.eye(dim)))
        ),
        "max_commutator_delta": float(np.max(np.abs(comm_canonical - comm_legacy))),
        "max_eigenvalue_shift_residual": float(
            np.max(np.abs((eval_canonical - eval_legacy) - shift))
        ),
        "max_gap_delta": float(np.max(np.abs(gap_canonical - gap_legacy)))
        if gap_legacy.size
        else 0.0,
        "legacy_eigenbasis_canonical_equation_residual": float(
            eigenvector_equation_residual
        ),
        "trace_shift_residual": float(
            abs((np.trace(canonical) - np.trace(legacy)) - trace_expected)
        ),
        "legacy_min_eigenvalue": float(eval_legacy[0]),
        "canonical_min_eigenvalue": float(eval_canonical[0]),
        "min_eigenvalue_shift": float(eval_canonical[0] - eval_legacy[0]),
        "legacy_fro_norm": float(np.linalg.norm(legacy, ord="fro")),
        "canonical_fro_norm": float(np.linalg.norm(canonical, ord="fro")),
        "legacy_op_norm": float(np.linalg.norm(legacy, ord=2)),
        "canonical_op_norm": float(np.linalg.norm(canonical, ord=2)),
    }


def main() -> int:
    cases = [run_case(lam, N) for lam, N in DEFAULT_CASES]
    invariant_metrics = {
        "max_matrix_shift_residual": max(c["max_matrix_shift_residual"] for c in cases),
        "max_commutator_delta": max(c["max_commutator_delta"] for c in cases),
        "max_eigenvalue_shift_residual": max(
            c["max_eigenvalue_shift_residual"] for c in cases
        ),
        "max_gap_delta": max(c["max_gap_delta"] for c in cases),
        "max_legacy_eigenbasis_canonical_equation_residual": max(
            c["legacy_eigenbasis_canonical_equation_residual"] for c in cases
        ),
        "max_trace_shift_residual": max(c["trace_shift_residual"] for c in cases),
    }
    tolerance = 5e-9
    status = "PASS" if all(v <= tolerance for v in invariant_metrics.values()) else "FAIL"

    payload = {
        "schema_version": "R004_SOURCE_NORMALIZATION_SHIFT_AUDIT_v1",
        "status": status,
        "phase": "DISCOVERY_AUDIT",
        "claim_cap": "FINITE_NUMERICAL_REGRESSION_ONLY",
        "tested_relation": "canonical = legacy + 2*cCorrection(L)*I",
        "tolerance": tolerance,
        "invariant_metrics": invariant_metrics,
        "cases": cases,
        "interpretation": {
            "invariant": [
                "index commutator",
                "eigenvectors/eigenspaces",
                "eigenvalue gaps",
                "displacement rank structure",
            ],
            "shift_sensitive": [
                "absolute eigenvalues",
                "trace",
                "matrix norms",
                "positive semidefiniteness/inertia in general",
                "absolute spectral lower bound",
            ],
        },
        "nonclaims": [
            "Lean, not this numerical audit, is theorem authority.",
            "No positivity theorem.",
            "No QW_lambda finite-restriction theorem.",
            "No finite-to-infinite theorem.",
            "No RH evidence or proof.",
        ],
    }

    out = Path("/tmp/R004_SOURCE_NORMALIZATION_SHIFT_AUDIT.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": status, **invariant_metrics}, indent=2))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
