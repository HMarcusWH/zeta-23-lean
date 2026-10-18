"""Independently authored finite continuum and rational-root controls.

No external archive is needed. These exact identities supply no selected
native ground, native discrepancy upper bound, or new Lean/RH authority.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as s

from pole_neutral_exact import geometry, is_zero, require_checks

PROVENANCE_DIGEST = "affc1f6d92336a34190e154078dd73def4ed0cb2cfb054e3fc35e82d39e7821f"


def continuum_blocks(K, a):
    G = geometry(K, a)
    h, ve, Qe, Qo, D, g0, b = (G[k] for k in ("h", "ve", "Qe", "Qo", "D", "g0", "b"))
    v = 1/(4*a)
    diagonal = s.diag(*[value/v for value in h])
    A0, B0 = Qe*diagonal*Qe, Qo*diagonal*Qo
    alpha = ve.T*diagonal*Qe/(ve.T*ve)[0]
    source = -b*alpha
    return G | {"v": v, "continuum_diagonal": diagonal, "A0": A0, "B0": B0,
                "alpha_P": alpha, "source_P0": source}


def rational_root_probe(K, a, roots):
    z = s.symbols("z")
    denominator = s.prod(z+j*j for j in range(K+1))
    numerator = (z-a)*s.prod(z+t for t in roots)
    coefficients = []
    for j in range(K+1):
        residual_denominator = s.prod(m*m-j*j for m in range(K+1) if m != j)
        residue = s.cancel(numerator.subs(z, -j*j)/residual_denominator)
        coefficients.append(residue if j == 0 else residue/2)
    u = s.Matrix([coefficients[abs(n)] for n in range(-K, K+1)])
    return z, denominator, numerator, u


def run():
    rows = []
    for K in range(3, 8):
        for a in (s.Rational(1, 16), s.Rational(1, 4), s.Rational(1), s.Rational(4)):
            G = continuum_blocks(K, a)
            D, Qe, Qo, A0, B0, g0, source = (G[k] for k in ("D", "Qe", "Qo", "A0", "B0", "g0", "source_P0"))
            defect = B0*D*Qe-D*A0
            checks = {"corrected_continuum_rank_one": is_zero(defect-g0*source),
                      "zero_continuum_defect_is_false": not is_zero(defect),
                      "pole_covariance_negative": bool(G["b"] < 0),
                      "legal_input_neutral_output_inference_fails": not is_zero(G["h"].T*G["continuum_diagonal"]*Qe),
                      "common_scalar_shift_invisible": is_zero((B0-7*Qo)*D*Qe-D*(A0-7*Qe)-defect)}
            require_checks(checks)
            rows.append({"K": K, "a": str(a), "checks": checks,
                         "native_ground_eligible": False, "ground_only_native_budget_observable": "NOT_APPLICABLE"})
    G = continuum_blocks(3, s.Rational(1))
    u = s.Matrix([-10, 30, -30, 20, -30, 30, -10])
    du = G["D"]*u
    example = {
        "input_pole_neutral": G["Qe"]*u == u,
        "output_pole_moment_144_over_5": (G["h"].T*G["continuum_diagonal"]*u)[0] == s.Rational(144, 5),
        "alpha_P_140": (G["alpha_P"]*u)[0] == 140,
        "source_P0_10": (G["source_P0"]*u)[0] == 10,
        "even_rayleigh_8_over_5": (u.T*G["A0"]*u)[0]/u.dot(u) == s.Rational(8, 5),
        "odd_rayleigh_14_over_15": (du.T*G["B0"]*du)[0]/du.dot(du) == s.Rational(14, 15),
        "defect_pairing_minus_7200": (du.T*(G["B0"]*du-s.Rational(8, 5)*du))[0] == -7200,
    }
    require_checks(example)

    root_rows = []
    for K in range(3, 8):
        roots = [s.Rational((2*j+1)**2, 4) for j in range(1, K-2)]
        for a in (s.Rational(1, 16), s.Rational(1), s.Rational(4)):
            G = continuum_blocks(K, a)
            z, denominator, numerator, u = rational_root_probe(K, a, roots)
            H = sum(u[i]/(z+n*n) for i, n in enumerate(G["n"]))
            M4 = sum(n**4*u[i] for i, n in enumerate(G["n"]))
            omega = s.prod(a+t for t in roots)/denominator.subs(z, a)
            budget = -G["b"]*omega/(G["v"]*G["ve"].dot(G["ve"]))
            checks = {
                "rational_source": s.cancel(H-numerator/denominator) == 0,
                "M0": sum(u) == 0,
                "M2": sum(n*n*u[i] for i, n in enumerate(G["n"])) == 0,
                "pole_neutral": (G["h"].T*u)[0] == 0,
                "M4_leading_coefficient": M4 == 1,
                "simple_root_derivative": s.simplify(s.diff(H, z).subs(z, a)-omega) == 0,
                "opposing_source_budget": s.simplify((G["source_P0"]*u)[0]+budget) == 0,
                "budget_positive": bool(budget > 0),
            }
            for label, phase in (("i", s.I), ("one_plus_i", 1+s.I)):
                phased_product = s.conjugate((G["source_P0"]*(phase*u))[0])*(phase*M4)
                checks["phase_covariance_"+label] = s.simplify(phased_product+s.conjugate(phase)*phase*budget) == 0
            require_checks(checks)
            root_rows.append({"K": K, "a": str(a), "budget": str(budget), "checks": checks,
                              "root_pattern_constructed": True, "has_native_ground_proof": False,
                              "native_ground_eligible": False, "ground_only_native_budget_observable": "NOT_APPLICABLE"})

    a, z = s.symbols("a z", positive=True)
    n = list(range(-3, 4))
    modified_u = [-(a+9), 6*a+24, -15*a-15, 20*a, -15*a-15, 6*a+24, -(a+9)]
    H = sum(value/(z+t*t) for value, t in zip(modified_u, n))
    target = -720*(z-a)/(z*(z+1)*(z+4)*(z+9))
    modified_checks = {
        "rational_source_exact": s.cancel(H-target) == 0,
        "M4_minus_720": s.expand(sum(t**4*value for value, t in zip(modified_u, n))) == -720,
        "root_pattern_not_excluded": s.Poly(-720*(z-a), z).degree() == 1,
        "simple_elementary_root": bool((-720/(a*(a+1)*(a+4)*(a+9))).is_negative),
    }
    require_checks(modified_checks)
    return {"status": "PASS", "authority": "EXACT_FINITE_CONTROL", "Lean_authority": False,
            "provenance_digest": PROVENANCE_DIGEST, "external_archive_required": False,
            "continuum_cases": rows, "explicit_K3_L_4pi": {"checks": example,
                "is_actual_continuum_formula": True, "is_actual_zeta_negative_ground": False,
                "native_ground_eligible": False},
            "root_cases": root_rows, "modified_prime_root_pattern": {"checks": modified_checks,
                "is_actual_zeta": False, "prime_coefficient_mutated": True,
                "native_divisor_compatibility": "FAILS_AT_CHANGED_COEFFICIENT_2",
                "native_ground_eligible": False},
            "assertion_count": sum(len(r["checks"]) for r in rows)+len(example)+sum(len(r["checks"]) for r in root_rows)+len(modified_checks),
            "actual_selected_ground_root_classification": "INHERITED_PAPER_NOT_NEW_LEAN_PROOF",
            "native_signed_budget_upper_bound": "OPEN", "terminal_claim": "RH_OPEN"}


if __name__ == "__main__":
    report = run()
    out = Path(__file__).parent/"evidence/argon_continuum_and_roots_exact.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(json.dumps({"status": report["status"], "assertion_count": report["assertion_count"], "terminal_claim": "RH_OPEN"}))
