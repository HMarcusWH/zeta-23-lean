"""POST285 M27 regression: alternating root slopes of the canonical secular function.

Lean (Zeta23/CCM/CanonicalAlternatingRootSlopes.lean) proves, for the actual
canonical parity compressions A_L (even carrier) and B_L (odd carrier) and the
secular function T_L(lambda) = H_L(D^-1 (B_L - lambda)^-1 g):

    1 - T_L(lambda) = prod_i (a_i - lambda) / prod_k (b_k - lambda)   (lambda < odd floor),
    T_L'(a_j) = prod_{i != j} (a_i - a_j) / prod_k (b_k - a_j),
    sign T_L'(a_j) = (-1)^{#{i : a_i < a_j}}  (nonzero),

at every even eigenvalue a_j below the odd Rayleigh bottom.

This script regresses those identities on the production float canonical source
matrices (canonical_source_numeric.py, the same matrices as the M76 probe):

  * the resolvent derivative T'(a) = H(D^-1 (B - a)^-2 g) against the product
    formula (relative residual), and against a central finite difference of T;
  * the sign rule, with roots ordered increasingly;
  * the determinant-ratio form of 1 - T at a sample point between roots.

Negative controls (must break the identities):
  C1  replace B by B + eps*P (P a fixed symmetric perturbation) while keeping
      H read off from the unperturbed rank-one relation: the product formula
      and the resolvent derivative then disagree;
  C2  the decreasing-order sign rule (-1)^{#{i : a_i > a_j}} (Mathlib's
      eigenvalue order) is wrong at some root whenever dim A_L is even.

REGRESSION ONLY: float matrices, no certified enclosure.  The Lean theorem is
the proof; this checks the statement against the numerical operator and shows
the checks have discriminating power.  Nothing here is about contacts, M76 or RH.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

from canonical_source_numeric import canonical_source_matrix_L  # noqa: E402
from post285_m76_secular_margin import carriers  # noqa: E402

RESOLVE = 1e-8


def secular_data(S, n, E, O):
    A = E.T @ S @ E
    B = O.T @ S @ O
    D = O.T @ np.diag(n) @ E
    g = O.T @ (n ** 3)
    R = B @ D - D @ A
    h = R.T @ g / (g @ g)
    return A, B, D, g, h


def T_of(lam, B, D, g, h):
    return float(h @ np.linalg.solve(D, np.linalg.solve(B - lam * np.eye(B.shape[0]), g)))


def dT_of(lam, B, D, g, h):
    Bs = B - lam * np.eye(B.shape[0])
    return float(h @ np.linalg.solve(D, np.linalg.solve(Bs, np.linalg.solve(Bs, g))))


def product_slope(ev_a, ev_b, j):
    a = ev_a[j]
    num = np.prod([ev_a[i] - a for i in range(len(ev_a)) if i != j])
    den = np.prod(ev_b - a)
    return float(num / den)


def check(K, L, S, n, E, O, perturb=None):
    A, B, D, g, h = secular_data(S, n, E, O)
    if perturb is not None:
        B = B + perturb
    ev_a = np.linalg.eigvalsh(A)
    ev_b = np.linalg.eigvalsh(B)
    scale = float(np.abs(S).max())
    floor = RESOLVE * scale
    rows = []
    for j, a in enumerate(ev_a):
        if a >= ev_b.min() - floor:
            break
        gaps = [abs(a - x) for i, x in enumerate(ev_a) if i != j]
        if gaps and min(gaps) <= floor:
            continue
        formula = product_slope(ev_a, ev_b, j)
        resolvent = dT_of(a, B, D, g, h)
        # the step must be small against the nearest root and the odd pole
        step = 1e-4 * min(gaps + [ev_b.min() - a])
        fd = (T_of(a + step, B, D, g, h) - T_of(a - step, B, D, g, h)) / (2 * step)
        below = int(sum(1 for x in ev_a if x < a))
        above = int(sum(1 for x in ev_a if x > a))
        rows.append({
            "j_increasing": below + 1, "a": float(a),
            "b_min_minus_a": float(ev_b.min() - a), "slope_formula": formula, "slope_resolvent": resolvent, "slope_fd": float(fd),
            "rel_residual": abs(formula - resolvent) / max(abs(formula), 1e-300),
            "fd_rel_residual": abs(fd - resolvent) / max(abs(resolvent), 1e-300),
            "sign_ok": bool(np.sign(formula) == (-1) ** below and formula != 0),
            "decreasing_sign_ok": bool(np.sign(formula) == (-1) ** above),
        })
    # determinant-ratio form at a point strictly below the odd floor
    lam = float(ev_a.min() - 0.5 * max(1.0, abs(ev_a.min())))
    if lam < ev_b.min():
        ratio = float(np.prod(ev_a - lam) / np.prod(ev_b - lam))
        det_res = abs((1 - T_of(lam, B, D, g, h)) - ratio) / max(1.0, abs(ratio))
    else:
        det_res = None
    return {"K": K, "L": L, "dim_A": len(ev_a), "roots": rows, "det_ratio_residual": det_res}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=5)
    ap.add_argument("--lmax", type=float, default=6.0)
    ap.add_argument("--dl", type=float, default=0.5)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rows, c1_rows = [], []
    for K in range(2, args.kmax + 1):
        n, E, O = carriers(K)
        L = args.dl
        while L <= args.lmax + 1e-12:
            Lr = round(L, 10)
            S = canonical_source_matrix_L(Lr, K)
            rows.append(check(K, Lr, S, n, E, O))
            dimB = O.shape[1]
            P = np.diag(np.linspace(1.0, 2.0, dimB))
            eps = 1e-3 * float(np.abs(S).max())
            c1_rows.append(check(K, Lr, S, n, E, O, perturb=eps * P))
            L += args.dl
    roots = [x for r in rows for x in r["roots"]]
    c1_roots = [x for r in c1_rows for x in r["roots"]]
    dets = [r["det_ratio_residual"] for r in rows if r["det_ratio_residual"] is not None]
    summary = {
        "roots_checked": len(roots),
        "rows": len(rows),
        "max_rel_residual": max((x["rel_residual"] for x in roots), default=None),
        "max_fd_rel_residual": max((x["fd_rel_residual"] for x in roots), default=None),
        "sign_failures": sum(1 for x in roots if not x["sign_ok"]),
        "max_det_ratio_residual": max(dets) if dets else None,
        "C1_roots": len(c1_roots),
        "C1_max_rel_residual": max((x["rel_residual"] for x in c1_roots), default=None),
        "C2_decreasing_sign_failures": sum(1 for x in roots if not x["decreasing_sign_ok"]),
        "multi_root_rows": sum(1 for r in rows if len(r["roots"]) >= 2),
        "max_roots_below_odd_floor": max((len(r["roots"]) for r in rows), default=0),
    }
    ok = (summary["roots_checked"] > 0 and summary["max_rel_residual"] < 1e-6
          and summary["max_fd_rel_residual"] < 1e-4 and summary["sign_failures"] == 0
          and (summary["max_det_ratio_residual"] or 0) < 1e-6)
    controls = (summary["C1_max_rel_residual"] is not None and summary["C1_max_rel_residual"] > 1e-3
                and summary["C2_decreasing_sign_failures"] > 0)
    disposition = "PASS_REGRESSION" if ok and controls else (
        "FAIL_IDENTITY" if not ok else "FAIL_CONTROLS_NOT_DISCRIMINATING")
    report = {"terminal_claim": "RH_OPEN", "authority": "REGRESSION_ONLY",
              "package": "M27_ALTERNATING_ROOT_SLOPES", "disposition": disposition,
              "summary": summary, "rows": rows, "control_C1_rows": c1_rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k not in ("rows", "control_C1_rows")}, indent=2))
    return 0 if disposition == "PASS_REGRESSION" else 1


if __name__ == "__main__":
    raise SystemExit(main())
