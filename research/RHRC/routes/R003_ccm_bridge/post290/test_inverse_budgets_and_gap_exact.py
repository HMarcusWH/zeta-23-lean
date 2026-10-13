"""Exact amendment controls: two shifts, tiny parity gap, scalar blindness.

These are finite algebra controls, not actual zeta or generated detector states.
"""
from __future__ import annotations

from fractions import Fraction as F
import json
from pathlib import Path

import sympy as s

from pole_neutral_exact import geometry, is_zero, require_checks


def run():
    depth, Kd, eta = F(12), 5, F(5)
    gap = depth/(12*(Kd-1))
    lam = -eta-gap
    predecessors = [F(-19, 4), F(-9, 2)]
    ground_inverse = max(1/(v-lam) for v in predecessors)
    detector_inverse = max(1/(v+eta) for v in predecessors)
    budgets = {
        "threshold_window": depth/3 < eta < depth/2,
        "lambda_separate_from_threshold": lam == -eta-gap and lam != -eta,
        "both_predecessors_threshold_gap": all(v >= -eta+gap for v in predecessors),
        "ground_shift_gap_2g": all(v-lam >= 2*gap for v in predecessors),
        "detector_shift_gap_g": all(v+eta >= gap for v in predecessors),
        "ground_budget_exact": ground_inverse == 6*(Kd-1)/depth,
        "detector_budget_exact": detector_inverse == 12*(Kd-1)/depth,
        "wrong_ground_budget_for_detector_fails": detector_inverse > 6*(Kd-1)/depth,
    }
    require_checks(budgets)

    d = geometry(3, s.Rational(1))
    Qe, Qo, D, g0, n = (d[k] for k in ("Qe", "Qo", "D", "g0", "n"))
    seed1, seed2 = s.Matrix([0, 1, -4, 6, -4, 1, 0]), s.Matrix([1, 0, -9, 16, -9, 0, 1])
    u = 30*seed1-10*seed2
    M4 = n.applyfunc(lambda t: t**4).T
    small_gaps = []
    for exponent in range(1, 9):
        delta = s.Rational(1, 10**exponent)
        even_bottom, odd_bottom = -s.Rational(depth.numerator, depth.denominator), -s.Rational(depth.numerator, depth.denominator)+delta
        A, B = even_bottom*Qe, odd_bottom*Qo
        defect = B*D*Qe-D*A
        source = g0.T*defect/(g0.T*g0)[0]
        product = (source*u)[0]*(M4*u)[0]
        shifted_A, shifted_B = A+13*Qe, B+13*Qo
        shifted_defect = shifted_B*D*Qe-D*shifted_A
        checks = {
            "simple_even_dimension": s.trace(Qe) == 1,
            "actual_strict_even_gap": bool(odd_bottom-even_bottom == delta and delta > 0),
            "gap_much_less_than_depth_third": bool(delta < depth/3),
            "both_bottoms_negative": bool(even_bottom < odd_bottom < 0),
            "same_nonzero_pole_neutral_vector": not is_zero(u) and Qe*u == u,
            "even_eigenvector": A*u == even_bottom*u,
            "rank_one_identity": is_zero(defect-g0*source),
            "source_product_exact_gap": product == delta*(D*u).dot(D*u),
            "fourth_moment_nonzero": (M4*u)[0] == -720,
            "common_scalar_shift_preserves_defect": shifted_defect == defect,
            "common_scalar_shift_preserves_gap": (odd_bottom+13)-(even_bottom+13) == delta,
            "common_scalar_shift_changes_negative_to_positive": bool(even_bottom < 0 < even_bottom+13),
            "common_scalar_shift_preserves_source_and_M4": is_zero(g0.T*shifted_defect/(g0.T*g0)[0]-source),
        }
        require_checks(checks)
        small_gaps.append({"depth": str(depth), "delta": str(delta), "source_moment_product": str(product),
                           "checks": checks})
    return {"status": "PASS", "authority": "EXACT_FINITE_CONTROL", "is_actual_zeta": False,
            "is_generated_detector": False, "Lean_authority": False, "RH_status": "OPEN",
            "inverse_budget_checks": budgets, "ground_inverse_budget": str(ground_inverse),
            "detector_inverse_budget": str(detector_inverse), "eta": str(eta), "lambda": str(lam),
            "gap": str(gap), "small_gap_rows": small_gaps,
            "conclusion": "Cutoff predecessor separation does not bound the parity gap. Common-shift-invariant source data do not determine the absolute energy.",
            "assertion_count": len(budgets)+sum(len(r["checks"]) for r in small_gaps)}


if __name__ == "__main__":
    report = run()
    path = Path(__file__).parent/"evidence"/"inverse_budgets_and_gap_exact.json"
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k: v for k, v in report.items() if k != "small_gap_rows"}))
