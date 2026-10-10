"""POST285 M76 research probe: actual-canonical secular margin 1 - T(L).

Uses the production canonical source matrix (canonical_source_numeric.py, float
discovery data) to build the actual parity compressions A_L (even legal carrier)
and B_L (odd legal carrier), the centered-index map D : E -> O, the odd cubic
vector g = P_O(n^3), and the actual source functional H_L read off from the
rank-one relation  B_L D - D A_L = g H_L  (M74).  Then, where B_L > 0,

    r = B^-1 g,  x = D^-1 r,  gamma = <g, r>,  T(L) = H_L(x),
    det A_L / det B_L = 1 - T(L)       (contact  <=>  T = 1).

Reports per (K, L): the rank-one residual (numerical check of the Lean rank-one
theorem on the float matrices), lambda_min(A), lambda_min(B), T and the margin,
the determinant-ratio residual, and the channel split of T (pole, signed arch,
signed prime, scalar shift) to show the pole/prime cancellation.

EXPERIMENTAL SIGNAL ONLY: float matrices, no certified enclosure.  A margin
1 - T > 0 on the sampled grid is consistent with positivity there; it proves
nothing about other L, other K, contacts, or RH.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from canonical_source_numeric import (  # noqa: E402
    canonical_source_matrix_L,
    signed_channel_matrices_L,
)


RESOLVE = 1e-10


def null_basis(C: np.ndarray, dim: int) -> np.ndarray:
    if C.size == 0:
        return np.eye(dim)
    _, s, vt = np.linalg.svd(C)
    rank = int((s > 1e-10 * max(1.0, s.max())).sum())
    return vt[rank:].T


def carriers(K: int):
    n = np.arange(-K, K + 1, dtype=float)
    dim = 2 * K + 1
    rows_e, rows_o = [], []
    for k in range(1, K + 1):
        r = np.zeros(dim); r[K + k] = 1; r[K - k] = -1
        rows_e.append(r)
    for k in range(0, K + 1):
        r = np.zeros(dim); r[K + k] += 1; r[K - k] += 1
        rows_o.append(r)
    E = null_basis(np.array(rows_e + [n ** 0, n ** 2]), dim)
    O = null_basis(np.array(rows_o + [n ** 1]), dim)
    return n, E, O


def secular(K: int, L: float, S: np.ndarray, n, E, O, channels=None):
    A = E.T @ S @ E
    B = O.T @ S @ O
    Dfull = np.diag(n)
    leak = float(np.abs((np.eye(len(n)) - O @ O.T) @ Dfull @ E).max())
    D = O.T @ Dfull @ E
    g = O.T @ (n ** 3)
    R = B @ D - D @ A
    h = R.T @ g / (g @ g)
    rank_one = float(np.abs(R - np.outer(g, h)).max())
    scale = float(np.abs(S).max())
    out = {"K": K, "L": L, "D_leak": leak, "rank_one_residual": rank_one,
           "lambda_min_A": float(np.linalg.eigvalsh(A).min()),
           "lambda_min_B": float(np.linalg.eigvalsh(B).min()),
           "matrix_scale": scale}
    # float64 cannot resolve eigenvalues below ~1e-10 of the matrix scale
    floor = RESOLVE * scale
    out["float_resolved"] = bool(abs(out["lambda_min_A"]) > floor and abs(out["lambda_min_B"]) > floor)
    if out["lambda_min_B"] <= 0:
        out["T"] = None
        return out
    r = np.linalg.solve(B, g)
    x = np.linalg.solve(D, r)
    T = float(h @ x)
    out["gamma"] = float(g @ r)
    out["T"] = T
    out["margin"] = 1 - T
    out["det_ratio_residual"] = float(abs(np.linalg.det(A) / np.linalg.det(B) - (1 - T)))
    if channels is not None:
        split = {}
        for name, C in channels.items():
            Ac, Bc = E.T @ C @ E, O.T @ C @ O
            hc = (Bc @ D - D @ Ac).T @ g / (g @ g)
            split[name] = float(hc @ x)
        split["sum_residual"] = abs(sum(split.values()) - T)
        out["T_channels"] = split
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=4)
    ap.add_argument("--lmax", type=float, default=5.0)
    ap.add_argument("--dl", type=float, default=0.25)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rows = []
    for K in range(2, args.kmax + 1):
        n, E, O = carriers(K)
        L = args.dl
        while L <= args.lmax + 1e-12:
            S = canonical_source_matrix_L(round(L, 10), K)
            ch = signed_channel_matrices_L(round(L, 10), K)
            rows.append(secular(K, round(L, 10), S, n, E, O, ch))
            L += args.dl
    with_T = [r for r in rows if r.get("T") is not None and r["float_resolved"]]
    summary = {
        "max_rank_one_residual": max(r["rank_one_residual"] for r in rows),
        "max_D_leak": max(r["D_leak"] for r in rows),
        "max_det_ratio_residual": max(r["det_ratio_residual"] for r in with_T) if with_T else None,
        "min_margin": min(r["margin"] for r in with_T) if with_T else None,
        "resolved_rows": len(with_T),
        "unresolved_float_rows": [(r["K"], r["L"]) for r in rows if not r["float_resolved"]],
        "resolved_A_not_positive": [(r["K"], r["L"]) for r in rows
                                    if r["float_resolved"] and r["lambda_min_A"] <= 0],
        "pole_prime_cancellation_ratio_max": max(
            (abs(r["T_channels"]["pole"]) / max(abs(r["T"]), 1e-300)
             for r in with_T if "T_channels" in r), default=None),
    }
    worst = min(with_T, key=lambda r: r["margin"]) if with_T else None
    if worst:
        summary["argmin_margin"] = {"K": worst["K"], "L": worst["L"]}
    disposition = "EXPERIMENTAL_SIGNAL"
    if summary["max_rank_one_residual"] > 1e-6 or summary["max_D_leak"] > 1e-9:
        disposition = "FAIL_RANK_ONE_CONSISTENCY"
    report = {"terminal_claim": "RH_OPEN", "authority": "EXPERIMENTAL_SIGNAL_ONLY",
              "package": "M76_SECULAR_MARGIN", "disposition": disposition,
              "summary": summary, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
    return 0 if disposition == "EXPERIMENTAL_SIGNAL" else 1


if __name__ == "__main__":
    raise SystemExit(main())
