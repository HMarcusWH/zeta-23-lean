"""Exact complex Schur completion retaining a multidimensional complement.

Synthetic matrices are falsification controls, never generated zeta output.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as s

from pole_neutral_exact import require_checks


def run() -> dict:
    eta = s.Rational(1)
    P = s.diag(4, 5)
    B = s.Matrix([[1 + s.I, 2], [0, 1 - s.I]])
    C = s.diag(-8, -10)
    T = P.row_join(B).col_join(B.H.row_join(C))
    p = s.Matrix([s.Rational(3, 5), 0, 0, s.Rational(4, 5)])
    x, y = p[:2, 0], p[2:, 0]
    shifted = P + eta * s.eye(2)
    Schur = C + eta * s.eye(2) - B.H * shifted.inv() * B
    completed = x + shifted.inv() * B * y
    energy = s.simplify((p.H * T * p)[0])
    norm_sq = (p.H * p)[0]
    square = s.simplify((completed.H * shifted * completed)[0])
    schur_loss = s.simplify((y.H * Schur * y)[0])
    depth = s.Rational(3)
    lam = energy / norm_sq
    residual = (T - lam * s.eye(4)) * p
    channels = [(s.diag(4, 5, 0, 0) - lam * s.eye(4)) * p,
                s.zeros(2).row_join(B).col_join(B.H.row_join(s.zeros(2))) * p,
                s.diag(0, 0, -8, -10) * p]
    gram = s.Matrix(3, 3, lambda i, j: (channels[i].H * channels[j])[0])
    checks = {
        "hermitian": T.H == T,
        "same_trial_unit": norm_sq == 1,
        "same_trial_deep": bool(energy <= -depth),
        "predecessor_positive": bool(shifted[0, 0] > 0 and shifted[1, 1] > 0),
        "completion_of_squares": s.simplify(energy + eta * norm_sq - square - schur_loss) == 0,
        "complement_nonzero": y != s.zeros(2, 1),
        "detector_loss_lower": bool(schur_loss <= -(depth - eta)),
        "threshold_less_than_half_depth": bool(eta < depth / 2),
        "complement_dimension_two": y.rows == 2,
        "channels_sum_same_residual": sum(channels, s.zeros(4, 1)) == residual,
        "variance_identity": s.simplify((residual.H * residual)[0] - ((p.H * T * T * p)[0] - lam**2 * norm_sq)) == 0,
        "complex_gram_sum": s.simplify(sum(gram) - (residual.H * residual)[0]) == 0,
        "diagonal_only_gram_fails": s.simplify(sum(gram[i, i] for i in range(3)) - (residual.H * residual)[0]) != 0,
    }
    require_checks(checks)
    return {"status": "PASS", "authority": "EXACT_FINITE_CONTROL", "RH_status": "OPEN",
            "scope": "one complex Hermitian split with two-dimensional detector complement",
            "is_actual_zeta": False, "Lean_authority": False, "checks": checks,
            "trial_energy": str(energy), "trial_depth": str(depth), "threshold": str(eta),
            "detector_schur_loss": str(schur_loss), "assertion_count": len(checks)}


if __name__ == "__main__":
    report = run()
    out = Path(__file__).parent / "evidence" / "detector_schur_provenance.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
