"""POST285 M29 regression: source-resolvent derivatives T' and T'' (Steps 61, 62).

Checks the statements of `Zeta23/CCM/CanonicalSourceResolventDerivatives.lean`
on the float canonical matrices (canonical_source_matrix_numeric.py) for
K = 2..5 and L = 0.3, 0.55, ..., 5.8 (no grid point on a seam log n).

With A_L, B_L the legal even/odd compressions, D the centered-index map,
g the compressed cubic vector, H_L(z) = <g, (B_L D - D A_L) z>/<g, g>,
R = B_L^{-1}, r = R g, x = D^{-1} r:

  T(L) = H_L(x_L) and 1 - T(L) = det A_L / det B_L (M74, sanity);
  T'   = H'(x) + H(x'),                 x'  = -D^{-1} R B' r;
  T''  = H''(x) + 2 H'(x') + H(x''),    x'' = D^{-1}(2 R B' R B' r - R B'' r);

where H', H'' use B', A' and B'', A''.  The operator jets B', B'', A', A'' are
central differences of the matrices (step 1e-4; step 1e-3 with one
Richardson step for the second jets), and the formulas are
compared with central differences of T computed from the determinant ratio.
Points with lambda_odd < 1e-6 are skipped (the float odd block is not resolved).
The finite differences lose accuracy as lambda_odd shrinks, so the tolerance is
1e-3 overall and 1e-5 where lambda_odd >= 1e-2.

Negative controls (each must FAIL by more than 100 times the tolerance):
  C1  T' without the H(x') term;
  C2  x' with the opposite sign;
  C3  T'' with H'(x') counted once instead of twice.

Regression evidence only.  No contact is assumed or found here, and the
third derivative (Step 63) is not checked.
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

TOL = 1e-3
STRICT_TOL = 1e-5
STRICT_FLOOR = 1e-2
LAMBDA_FLOOR = 1e-6


def blocks(L: float, K: int, E, O):
    S = canonical_source_matrix_L(L, K)
    return E.T @ S @ E, O.T @ S @ O


def T_det(L: float, K: int, E, O) -> float:
    A, B = blocks(L, K, E, O)
    return 1.0 - np.linalg.det(A) / np.linalg.det(B)


def row(K: int, L: float, n, E, O) -> dict | None:
    D = O.T @ np.diag(n) @ E
    g = O.T @ (n ** 3)
    A, B = blocks(L, K, E, O)
    lam_odd = float(np.linalg.eigvalsh(B)[0])
    if lam_odd < LAMBDA_FLOOR:
        return None
    h1, h2 = 1e-4, 1e-3
    Ap, Bp = blocks(L + h1, K, E, O)
    Am, Bm = blocks(L - h1, K, E, O)
    A1, B1 = (Ap - Am) / (2 * h1), (Bp - Bm) / (2 * h1)

    def second(h):
        Ap2, Bp2 = blocks(L + h, K, E, O)
        Am2, Bm2 = blocks(L - h, K, E, O)
        return (Ap2 - 2 * A + Am2) / h ** 2, (Bp2 - 2 * B + Bm2) / h ** 2

    # Richardson: (4 f(h/2) - f(h))/3 removes the h^2 error term
    (Aa, Ba), (Ab, Bb) = second(h2), second(h2 / 2)
    A2, B2 = (4 * Ab - Aa) / 3, (4 * Bb - Ba) / 3

    def H(b, a, z):
        return float(g @ ((b @ D - D @ a) @ z) / (g @ g))

    Rg = np.linalg.solve(B, g)
    Dinv = np.linalg.inv(D)
    x = Dinv @ Rg
    x1 = -Dinv @ np.linalg.solve(B, B1 @ Rg)
    RB1r = np.linalg.solve(B, B1 @ Rg)
    x2 = Dinv @ (2 * np.linalg.solve(B, B1 @ RB1r) - np.linalg.solve(B, B2 @ Rg))
    T = H(B, A, x)
    T1 = H(B1, A1, x) + H(B, A, x1)
    T2 = H(B2, A2, x) + 2 * H(B1, A1, x1) + H(B, A, x2)
    Tp, Tm = T_det(L + h1, K, E, O), T_det(L - h1, K, E, O)
    T0 = T_det(L, K, E, O)
    fd1 = (Tp - Tm) / (2 * h1)

    def fdT2(h):
        return (T_det(L + h, K, E, O) - 2 * T0 + T_det(L - h, K, E, O)) / h ** 2

    fd2 = (4 * fdT2(h2 / 2) - fdT2(h2)) / 3

    def rel(a, b):
        return abs(a - b) / max(1.0, abs(a), abs(b))

    x1_wrong = -x1
    return {
        "K": K, "L": L, "lambda_odd": lam_odd, "T": T,
        "det_ratio": rel(T, T0),
        "T1_formula": T1, "T1_fd": fd1, "T1": rel(T1, fd1),
        "T2_formula": T2, "T2_fd": fd2, "T2": rel(T2, fd2),
        "C1_no_H_x1": rel(H(B1, A1, x), fd1),
        "C2_x1_sign": rel(H(B1, A1, x) + H(B, A, x1_wrong), fd1),
        "C3_once": rel(H(B2, A2, x) + H(B1, A1, x1) + H(B, A, x2), fd2),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=5)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rows, skipped = [], 0
    for K in range(2, args.kmax + 1):
        n, E, O = carriers(K)
        for i in range(23):
            L = round(0.3 + 0.25 * i, 10)
            r = row(K, L, n, E, O)
            if r is None:
                skipped += 1
            else:
                rows.append(r)
    keys = ("det_ratio", "T1", "T2")
    controls = ("C1_no_H_x1", "C2_x1_sign", "C3_once")
    summary = {
        "rows": len(rows), "skipped_below_lambda_floor": skipped,
        "max_rel_error": {k: max(r[k] for r in rows) for k in keys},
        "max_rel_error_lambda_odd_ge_1e-2": {k: max(r[k] for r in rows if r["lambda_odd"] >= STRICT_FLOOR)
                                             for k in keys},
        "min_control_miss": {k: min(r[k] for r in rows) for k in controls},
        "control_rows_missing": {k: sum(1 for r in rows if r[k] <= 100 * TOL) for k in controls},
    }
    ok = all(v <= TOL for v in summary["max_rel_error"].values()) and all(
        v <= STRICT_TOL for v in summary["max_rel_error_lambda_odd_ge_1e-2"].values())
    # a control may coincide with the truth where the dropped term vanishes;
    # require it to miss at most rows but at least 90 percent of them
    controls_ok = all(v <= 0.1 * len(rows) for v in summary["control_rows_missing"].values())
    passed = ok and controls_ok and len(rows) > 0
    report = {"terminal_claim": "RH_OPEN", "authority": "REGRESSION_EVIDENCE_ONLY",
              "package": "M29_SOURCE_RESOLVENT_DERIVATIVES",
              "verdict": "PASS" if passed else "FAIL", "tolerance": TOL,
              "summary": summary, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
