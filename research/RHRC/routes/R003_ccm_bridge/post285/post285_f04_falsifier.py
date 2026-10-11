"""POST285 F04 (M65) and M66 regression and falsifier.

Floating-point checks of statements proved in
`Zeta23/CCM/CanonicalPrimeFreeF04.lean`, `Zeta23/CCM/CanonicalGlobalF04.lean`
and `Zeta23/CCM/CanonicalLocalBirdfishie.lean`, on the executable canonical
matrices (`canonical_source_matrix_L`, which already carries the single
`2 cCorrection(L)` diagonal repair).

On the even boundary-flat carrier `P` (orthonormal columns), with `M(L)` the
canonical matrix and `S(w)`, `S'(w)`, `S''(w)` the source matrix and its
derivatives:

* F04 first:  P^T M'(L) P = P^T (Q1(L) - P1(L)) P,
    Q1(L) = int_0^L (t/L^2) S'(1 - t/L) (W - rho)(t) dt,
    P1(L) = sum_{q <= e^L} Lambda(q)/sqrt(q) (log q/L^2) S'(1 - log q/L);
* F04 Euler:  P^T (M''(L) + (2/L) M'(L)) P = P^T (Q2(L) - P2(L)) P,
    Q2(L) = int_0^L (t^2/L^4) S''(1 - t/L) (W - rho)(t) dt,
    P2(L) = sum_{q <= e^L} Lambda(q)/sqrt(q) ((log q)^2/L^4) S''(1 - log q/L).
  Checked on the prime-free window, inside prime cells, and exactly at the
  seams L = log 3, log 4, log 5 (where the Lean proof glues by e(0) = e'(0) =
  e''(0) = 0);
* M66: lambda_max(P^T Q2 P) <= -(1/L^2)(1 - 2 pi^2 L (2K+1) K^2) on
  0 < L < eps_K = 1/(2 pi^2 (2K+1) K^2).

M'(L) and M''(L) come from 5-point finite differences of the canonical matrix,
so agreement is to roughly 1e-6 relative.

Negative controls (must FAIL):
* the Euler identity on a vector with nonzero coefficient sum misses by the
  predicted boundary term e'_z(0) (W(L) - rho(L)) / L, where
  e'_z(0) = 2 (sum z)^2 (S'(0) is twice the all-ones matrix, so zero sum is
  what kills the boundary term);
* the first identity with the scalar correction added twice
  (M + 2 cCorrection(L) I) misses by 2 cCorrectionIntegrand(L) |z|^2.

Research signals (not proved):
* the first L in (0, log 2) where lambda_max(P^T Q2 P) >= 0, against eps_K;
* lambda_min of the even compressed canonical matrix on (0, log 2), which says
  whether any even contact lies in the prime-free window at all.

Regression evidence only; says nothing about the prime staircase, global F04,
other branches, or RH.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from canonical_source_numeric import canonical_source_matrix_L  # noqa: E402
from run_commutator_gauntlet_v2 import c_correction, von_mangoldt  # noqa: E402

LOG2 = math.log(2.0)


def source_mats(omega: float, K: int):
    n = np.arange(-K, K + 1, dtype=float)
    N, Mm = np.meshgrid(n, n, indexing="ij")
    a = 2 * math.pi
    with np.errstate(divide="ignore", invalid="ignore"):
        d = N - Mm
        s0 = (np.sin(a * N * omega) - np.sin(a * Mm * omega)) / (math.pi * d)
        s1 = (2 * N * np.cos(a * N * omega) - 2 * Mm * np.cos(a * Mm * omega)) / d
        s2 = (-2 * a * N ** 2 * np.sin(a * N * omega) + 2 * a * Mm ** 2 * np.sin(a * Mm * omega)) / d
    eye = N == Mm
    s0 = np.where(eye, 0.0, s0)
    s1 = np.where(eye, 0.0, s1)
    s2 = np.where(eye, 0.0, s2)
    idx = np.diag_indices(2 * K + 1)
    s0[idx] = 2 * omega * np.cos(a * n * omega)
    s1[idx] = 2 * np.cos(a * n * omega) - 2 * a * n * omega * np.sin(a * n * omega)
    s2[idx] = -4 * a * n * np.sin(a * n * omega) - 2 * a * a * n ** 2 * omega * np.cos(a * n * omega)
    return s0, s1, s2


def kernel(t: np.ndarray) -> np.ndarray:
    W = np.exp(-t / 2) + np.exp(t / 2)
    rho = np.exp(t / 2) / (np.exp(t) - np.exp(-t))
    return W - rho


def physical_mats(L: float, K: int, nodes: int = 160):
    x, w = np.polynomial.legendre.leggauss(nodes)
    t = 0.5 * L * (x + 1)
    wt = 0.5 * L * w
    k = kernel(t)
    dim = 2 * K + 1
    Q1 = np.zeros((dim, dim))
    Q2 = np.zeros((dim, dim))
    for ti, wi, ki in zip(t, wt, k):
        _, s1, s2 = source_mats(1 - ti / L, K)
        Q1 += wi * ki * (ti / L ** 2) * s1
        Q2 += wi * ki * (ti ** 2 / L ** 4) * s2
    return Q1, Q2


def prime_mats(L: float, K: int):
    dim = 2 * K + 1
    P1 = np.zeros((dim, dim))
    P2 = np.zeros((dim, dim))
    for q in range(2, int(math.floor(math.exp(L) + 1e-12)) + 1):
        lam = von_mangoldt(q)
        if not lam:
            continue
        lq = math.log(q)
        _, s1, s2 = source_mats(1 - lq / L, K)
        P1 += lam / math.sqrt(q) * (lq / L ** 2) * s1
        P2 += lam / math.sqrt(q) * (lq ** 2 / L ** 4) * s2
    return P1, P2


def fd_derivs(L: float, K: int, h: float):
    Ms = [canonical_source_matrix_L(L + j * h, K) for j in (-2, -1, 0, 1, 2)]
    d1 = (Ms[0] - 8 * Ms[1] + 8 * Ms[3] - Ms[4]) / (12 * h)
    d2 = (-Ms[0] + 16 * Ms[1] - 30 * Ms[2] + 16 * Ms[3] - Ms[4]) / (12 * h * h)
    return Ms[2], d1, d2


def null_basis(C: np.ndarray, dim: int) -> np.ndarray:
    _, s, vt = np.linalg.svd(C)
    rank = int((s > 1e-10 * max(1.0, s.max())).sum())
    return vt[rank:].T


def even_flat(K: int) -> np.ndarray:
    n = np.arange(-K, K + 1, dtype=float)
    dim = 2 * K + 1
    rows = []
    for k in range(1, K + 1):
        r = np.zeros(dim); r[K + k] = 1; r[K - k] = -1
        rows.append(r)
    return null_basis(np.array(rows + [n ** 0, n ** 2]), dim)


def rel(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.abs(a - b).max() / max(1e-300, np.abs(b).max()))


def eps_K(K: int) -> float:
    return 1.0 / (2 * math.pi ** 2 * (2 * K + 1) * K ** 2)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=5)
    ap.add_argument("--tol", type=float, default=1e-5)
    ap.add_argument("--output", type=Path, default=None)
    args = ap.parse_args()

    out = {"identity": [], "negative_controls": [], "euler_bound": [], "signals": []}
    worst_first = worst_euler = 0.0
    ok = True
    for K in range(2, args.kmax + 1):
        P = even_flat(K)
        if P.shape[1] == 0:
            continue
        windows = [(L, "prime-free") for L in (0.08, 0.2, 0.35, 0.5, 0.62)]
        windows += [(L, "prime cell") for L in (0.9, 1.3, 1.5)]
        windows += [(math.log(q), f"seam log {q}") for q in (3, 4, 5)]
        for L, where in windows:
            h = 1e-3 * L
            M, d1, d2 = fd_derivs(L, K, h)
            Q1, Q2 = physical_mats(L, K, nodes=200)
            P1, P2 = prime_mats(L, K)
            r1 = rel(P.T @ d1 @ P, P.T @ (Q1 - P1) @ P)
            r2 = rel(P.T @ (d2 + 2 * d1 / L) @ P, P.T @ (Q2 - P2) @ P)
            worst_first = max(worst_first, r1)
            worst_euler = max(worst_euler, r2)
            out["identity"].append({"K": K, "L": L, "where": where,
                                    "first_rel": r1, "euler_rel": r2})

        # Negative control 1: coefficient sum nonzero, so e'_z(0) = 2 (sum z)^2 != 0.
        L = 0.35
        h = 1e-3 * L
        z = np.zeros(2 * K + 1); z[K] = 1.0
        _, d1, d2 = fd_derivs(L, K, h)
        _, Q2 = physical_mats(L, K)
        lhs = z @ (d2 + 2 * d1 / L) @ z
        rhs = z @ Q2 @ z
        _, s1, _ = source_mats(0.0, K)
        pred = (z @ s1 @ z) * float(kernel(np.array([L]))[0]) / L
        nc1 = {
            "control": "nonzero coefficient sum (e'_z(0) = 2)",
            "mismatch": float(lhs - rhs), "predicted_boundary_term": float(pred),
            "fails": bool(abs(lhs - rhs) > 1e-3 * max(1.0, abs(rhs))),
            "matches_prediction": bool(abs((lhs - rhs) - pred) <= 1e-4 * max(1.0, abs(pred))),
        }
        # Negative control 2: scalar correction added twice.
        zf = P[:, 0]
        Ms = [canonical_source_matrix_L(L + j * h, K) + 2 * c_correction(L + j * h) * np.eye(2 * K + 1)
              for j in (-2, -1, 1, 2)]
        d1x = (Ms[0] - 8 * Ms[1] + 8 * Ms[2] - Ms[3]) / (12 * h)
        Q1, _ = physical_mats(L, K)
        miss = zf @ d1x @ zf - zf @ Q1 @ zf
        integrand = (1 - math.exp(-L / 2)) / (math.exp(L) - math.exp(-L))
        nc2 = {
            "control": "cCorrection double-added",
            "mismatch": float(miss), "predicted": float(2 * integrand),
            "fails": bool(abs(miss) > 1e-3),
        }
        out["negative_controls"].append({"K": K, "non_flat": nc1, "double_correction": nc2})
        ok &= nc1["fails"] and nc1["matches_prediction"] and nc2["fails"]

        # M66 bound on (0, eps_K).
        e = eps_K(K)
        for frac in (0.25, 0.5, 0.9):
            L = frac * e
            _, Q2 = physical_mats(L, K)
            lam = float(np.linalg.eigvalsh(P.T @ Q2 @ P).max())
            bound = -(1 / L ** 2) * (1 - 2 * math.pi ** 2 * L * (2 * K + 1) * K ** 2)
            good = lam <= bound * (1 - 1e-9)
            ok &= good
            out["euler_bound"].append({"K": K, "L": L, "lambda_max": lam, "bound": bound, "holds": bool(good)})

        # Signals: Euler sign radius and even ground on (0, log 2).
        grid = np.linspace(1e-3, LOG2 - 1e-3, 120)
        lam_euler = []
        lam_ground = []
        for L in grid:
            _, Q2 = physical_mats(L, K, nodes=96)
            lam_euler.append(float(np.linalg.eigvalsh(P.T @ Q2 @ P).max()))
            lam_ground.append(float(np.linalg.eigvalsh(P.T @ canonical_source_matrix_L(float(L), K) @ P).min()))
        nonneg = [float(L) for L, v in zip(grid, lam_euler) if v >= 0]
        out["signals"].append({
            "K": K,
            "eps_K": e,
            "first_L_euler_max_nonneg": nonneg[0] if nonneg else None,
            "euler_max_negative_on_grid": not nonneg,
            "even_ground_min_on_grid": min(lam_ground),
            "even_ground_argmin_L": float(grid[int(np.argmin(lam_ground))]),
        })

    ok &= worst_first <= args.tol and worst_euler <= args.tol
    out["summary"] = {
        "max_first_identity_rel": worst_first,
        "max_euler_identity_rel": worst_euler,
        "disposition": "PASS_REGRESSION" if ok else "FAIL",
    }
    text = json.dumps(out, indent=2)
    if args.output:
        args.output.write_text(text + "\n")
    print(json.dumps(out["summary"]))
    for s in out["signals"]:
        print(json.dumps(s))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
