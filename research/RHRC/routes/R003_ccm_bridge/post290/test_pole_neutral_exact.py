"""Exact controls for R1 geometry and the actual first-prime atom formula."""
from __future__ import annotations

import json
from pathlib import Path

import sympy as s

from pole_neutral_exact import geometry, is_zero, require_checks


def run() -> dict:
    rows = []
    for K in range(3, 10):
        for a in (s.Rational(1, 16), s.Rational(1, 3), s.Rational(1), s.Rational(7)):
            d = geometry(K, a)
            E, O, D, ve, vo, Qe, Qo, g, g0, b, n = (
                d[x] for x in ("E", "O", "D", "ve", "vo", "Qe", "Qo", "g", "g0", "b", "n")
            )
            M4 = n.applyfunc(lambda t: t**4).T
            checks = {
                "legal_index_map": O * D * E == D * E,
                "pole_moment_map": vo.T * D * E == -a * ve.T,
                "restricted_index_map": Qo * D * Qe == D * Qe,
                "cubic_pairing": g0.T * D * Qe == M4 * Qe,
                "corrected_pole_channel": Qo * D * ve == -b * g0,
                "projector_idempotence": Qe * Qe == Qe and Qo * Qo == Qo,
                "projector_selfadjointness": Qe.T == Qe and Qo.T == Qo,
                "dimensions": s.trace(Qe) == K - 2 and s.trace(Qo) == K - 2,
                "normal_nonzero": not is_zero(ve) and not is_zero(vo),
                "cubic_nonzero": not is_zero(g0),
                "coefficient_sign": bool(b < 0),
            }
            require_checks(checks)
            rows.append({"K": K, "a": str(a), "b": str(b), "checks": checks})

    # Actual native source-atom pattern at omega=1/4, but modified coefficient.
    # pi is left symbolic: this is an exact algebra control, not a zeta sample.
    d = geometry(3, s.Rational(1))
    p = s.symbols("pi", nonzero=True, real=True)
    n = list(range(-3, 4))
    atom = s.Matrix(7, 7, lambda i, j: s.cos(s.pi * n[i] / 2) / 2 if i == j else
                    (s.sin(s.pi * n[j] / 2) - s.sin(s.pi * n[i] / 2)) / (p * (n[j] - n[i])))
    M = s.eye(7) - atom
    E, O, D, Qe, Qo, g, g0, ve, b = (d[k] for k in ("E", "O", "D", "Qe", "Qo", "g", "g0", "ve", "b"))
    A, B = E * M * E, O * M * O
    defect = B * D * E - D * A
    S = g.T * defect / g.dot(g)
    alpha = ve.T * A / ve.dot(ve)
    corrected = (S - b * alpha) * Qe
    restricted = Qo * M * Qo * D * Qe - D * Qe * M * Qe
    atom_checks = {
        "original_rank_one": is_zero(defect - g * S),
        "corrected_rank_one": is_zero(restricted - g0 * corrected),
        "uncorrected_source_is_false": not is_zero(restricted - g0 * S * Qe),
    }
    require_checks(atom_checks)
    return {"status": "PASS", "authority": "EXACT_FINITE_CONTROL", "RH_status": "OPEN",
            "scope": "28 rational geometries, K=3..9; one symbolic modified-prime source-atom control",
            "is_actual_zeta": False, "Lean_authority": False,
            "assertion_count": sum(len(r["checks"]) for r in rows) + len(atom_checks),
            "rows": rows, "modified_atom_checks": atom_checks}


if __name__ == "__main__":
    report = run()
    out = Path(__file__).parent / "evidence" / "pole_neutral_exact.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}))
