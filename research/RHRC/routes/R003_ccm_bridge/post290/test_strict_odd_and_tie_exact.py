"""Independent complex-adjoint sign and singular-tie finite controls."""
from __future__ import annotations

import json
from pathlib import Path

import sympy as s

from pole_neutral_exact import geometry, is_zero, require_checks


def run() -> dict:
    # A nonunitary intertwiner and genuinely complex Riesz/channel vectors.
    A, B, D = s.diag(1, 3), s.diag(-2, 3), s.diag(2, 3)
    g, S = s.Matrix([s.I, 0]), s.Matrix([[6 * s.I, 0]])
    checks = {"rank_one_identity": B * D - D * A == g * S,
              "adjoint_identity": D.H * B - A * D.H == S.H * g.H}
    w = s.Matrix([1, 0])
    lam = -2
    y = -D.H.inv() * (A - lam * s.eye(2)).inv() * S.H
    overlap = (g.H * w)[0]
    checks.update({"strict_odd_ground": B * w == lam * w and lam < 1,
                   "odd_reconstruction": w == overlap * y,
                   "odd_overlap_nonzero": overlap != 0,
                   "odd_ray_normalization": (g.H * y)[0] == 1,
                   "missing_minus_fails": w != overlap * (-y),
                   "unitary_inverse_substitution_fails": w != overlap * (-D.H * (A-lam*s.eye(2)).inv() * S.H),
                   "unconjugated_riesz_fails": w != overlap * (-D.H.inv() * (A - lam * s.eye(2)).inv() * S.T)})
    for lam in (-5, -3, -2, 0):
        y = -D.H.inv() * (A - lam * s.eye(2)).inv() * S.H
        checks[f"odd_determinant_at_{lam}"] = s.simplify(
            (B - lam * s.eye(2)).det() - (A - lam * s.eye(2)).det() * (1 - (g.H * y)[0])) == 0
    require_checks(checks)

    ties = []
    for K in (3, 4, 5, 6):
        d = geometry(K, s.Rational(1))
        Qe, Qo, D, n = (d[k] for k in ("Qe", "Qo", "D", "n"))
        basis = s.Matrix.hstack(*Qe.columnspace())
        M4 = n.applyfunc(lambda t: t**4).T
        A0, B0 = -Qe, -Qo
        if K == 3:
            u = basis[:, 0]
            tests = {"simple_even": basis.cols == 1,
                     "moment_nonzero": (M4 * u)[0] != 0,
                     "source_can_vanish": is_zero(B0 * D * Qe - D * A0),
                     "odd_shift_singular": (B0 + Qo) == s.zeros(len(n))}
            conclusion = "A simple tie permits nonzero M4 with S0=0; strict resolvent is unavailable."
        else:
            coeff = (M4 * basis).nullspace()[0]
            u = basis * coeff
            tests = {"vector_nonzero": not is_zero(u), "moment_zero": (M4 * u)[0] == 0,
                     "even_eigenvector": A0 * u == -u,
                     "odd_eigenvector": B0 * D * u == -D * u,
                     "rank_one_zero_defect": is_zero(B0 * D * Qe - D * A0),
                     "simplicity_fails": basis.cols > 1,
                     "index_squared_not_scalar": s.Matrix.hstack(u, D * D * u).rank() == 2}
            conclusion = "Removing the simple-even hypothesis makes M4 nonvanishing false."
        require_checks(tests)
        ties.append({"K": K, "checks": tests, "conclusion": conclusion})
    return {"status": "PASS", "authority": "EXACT_FINITE_CONTROL", "RH_status": "OPEN",
            "scope": "complex 2D adjoint sign control and four pole-neutral scalar tie controls",
            "is_actual_zeta": False, "Lean_authority": False, "strict_odd_checks": checks,
            "tie_rows": ties, "assertion_count": len(checks) + sum(len(x["checks"]) for x in ties)}


if __name__ == "__main__":
    report = run()
    out = Path(__file__).parent / "evidence" / "strict_odd_and_tie_exact.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "tie_rows"}))
