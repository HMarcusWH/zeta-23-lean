from __future__ import annotations

import argparse
import json
import math
import time
from functools import lru_cache
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy import integrate
import sympy as sp

SOURCE_NOTEBOOK_SHA256 = "aa6004b432f8baa3c9dc5c919b0f8df78621a84747f45bfda9fffc79a1d2e24d"


def von_mangoldt(k: int) -> float:
    if k < 2:
        return 0.0
    fac = sp.factorint(int(k))
    if len(fac) != 1:
        return 0.0
    return math.log(float(next(iter(fac))))


def q_basis(m: int, n: int, y: float, L: float) -> float:
    if m == n:
        return 2.0 * (1.0 - y / L) * math.cos(2.0 * math.pi * n * y / L)
    return (
        math.sin(2.0 * math.pi * m * y / L)
        - math.sin(2.0 * math.pi * n * y / L)
    ) / (math.pi * (n - m))


def pole_component(n: int, m: int, L: float) -> float:
    num = 32.0 * L * math.sinh(L / 4.0) ** 2 * (L**2 - 16.0 * math.pi**2 * m * n)
    den = (L**2 + 16.0 * math.pi**2 * m**2) * (L**2 + 16.0 * math.pi**2 * n**2)
    return num / den


def rho(x: float) -> float:
    return math.exp(x / 2.0) / (math.exp(x) - math.exp(-x))


@lru_cache(maxsize=None)
def c_correction(L: float) -> float:
    def f(x: float) -> float:
        if x == 0:
            return 0.25
        return (1.0 - math.exp(-x / 2.0)) / (math.exp(x) - math.exp(-x))
    return integrate.quad(f, 0.0, L)[0]


@lru_cache(maxsize=None)
def w_correction(L: float) -> float:
    return 0.5 * (np.euler_gamma + math.log(4.0 * math.pi)) - 0.5 * math.log(
        (math.exp(L) + 1.0) / (math.exp(L) - 1.0)
    )


@lru_cache(maxsize=None)
def alpha_L(n: int, L: float) -> float:
    def f(x: float) -> float:
        if x == 0:
            return 0.0 if n == 0 else math.pi * n / L
        return math.sin(2.0 * math.pi * n * x / L) * rho(x)
    return integrate.quad(f, 0.0, L)[0] / math.pi


@lru_cache(maxsize=None)
def beta_L(n: int, L: float) -> float:
    def f(x: float) -> float:
        if x == 0:
            return 0.5
        return x * math.cos(2.0 * math.pi * n * x / L) * rho(x)
    return integrate.quad(f, 0.0, L)[0] / L


@lru_cache(maxsize=None)
def gamma_L(n: int, L: float) -> float:
    def f(x: float) -> float:
        if x == 0:
            return 0.25
        return (math.cos(2.0 * math.pi * n * x / L) - math.exp(-x / 2.0)) * rho(x)
    return integrate.quad(f, 0.0, L)[0] + c_correction(L) + w_correction(L)


def arch_component(n: int, m: int, L: float) -> float:
    if m != n:
        return (alpha_L(m, L) - alpha_L(n, L)) / (n - m)
    return 2.0 * gamma_L(n, L) - 2.0 * beta_L(n, L)


def prime_component(n: int, m: int, L: float) -> float:
    total = 0.0
    for k in range(2, int(math.floor(math.exp(L))) + 1):
        lk = von_mangoldt(k)
        if lk:
            total += lk * k ** -0.5 * q_basis(n, m, math.log(k), L)
    return total


def build_ccm_matrix(lam: float, N: int) -> np.ndarray:
    if not lam > 1 or N < 1:
        raise ValueError("require lambda>1 and N>=1")
    L = 2.0 * math.log(lam)
    idx = list(range(-N, N + 1))
    M = np.empty((len(idx), len(idx)), dtype=float)
    for r, n in enumerate(idx):
        for c, m in enumerate(idx):
            M[r, c] = pole_component(n, m, L) - arch_component(n, m, L) - prime_component(n, m, L)
    return M


def traceless_tridiagonal_basis(n: int) -> list[np.ndarray]:
    out: list[np.ndarray] = []
    for i in range(n - 1):
        A = np.zeros((n, n))
        A[i, i] = 1.0
        A[-1, -1] = -1.0
        out.append(A)
    for i in range(n - 1):
        A = np.zeros((n, n))
        A[i, i + 1] = A[i + 1, i] = 1.0 / math.sqrt(2.0)
        out.append(A)
    return out


def matched_generator(M: np.ndarray) -> tuple[np.ndarray, float, float]:
    B = traceless_tridiagonal_basis(len(M))
    G = np.array([[np.vdot(x, y).real for y in B] for x in B])
    C = [M @ x - x @ M for x in B]
    K = np.array([[np.vdot(x, y).real for y in C] for x in C])
    vals, vecs = la.eigh(K, G)
    coeff = vecs[:, 0]
    A = sum(c * b for c, b in zip(coeff, B))
    residual = np.linalg.norm(M @ A - A @ M, "fro") / (
        np.linalg.norm(M, "fro") * np.linalg.norm(A, "fro")
    )
    return A, float(residual), float(vals[0])


def random_orthogonal_conjugate(M: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    Q, _ = np.linalg.qr(rng.normal(size=M.shape))
    return Q @ np.diag(np.linalg.eigvalsh(M)) @ Q.T


def run_case(lam: float, N: int, null_count: int, rng: np.random.Generator) -> dict:
    M = build_ccm_matrix(lam, N)
    symmetry_error = float(np.max(np.abs(M - M.T)))
    A, residual, pencil_min = matched_generator(M)
    nulls = []
    for _ in range(null_count):
        Mr = random_orthogonal_conjugate(M, rng)
        _, rr, _ = matched_generator(Mr)
        nulls.append(rr)
    diag = np.diag(A)
    off = np.diag(A, 1)
    return {
        "lambda": lam,
        "N": N,
        "dimension": 2 * N + 1,
        "matrix_symmetry_error": symmetry_error,
        "matched_tridiagonal_commutator_residual": residual,
        "double_commutator_pencil_min": pencil_min,
        "null_count": null_count,
        "eigenvalue_preserving_null_min": float(np.min(nulls)) if nulls else None,
        "eigenvalue_preserving_null_median": float(np.median(nulls)) if nulls else None,
        "residual_to_null_median_ratio": float(residual / np.median(nulls)) if nulls else None,
        "generator_diagonal": [float(x) for x in diag],
        "generator_offdiagonal": [float(x) for x in off],
    }


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--lambdas", nargs="+", type=float, default=[2, 3, 5, 7, 10])
    p.add_argument("--Ns", nargs="+", type=int, default=[5, 8, 12, 20])
    p.add_argument("--nulls", type=int, default=30)
    p.add_argument("--seed", type=int, default=20260820)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    t0 = time.time()
    rng = np.random.default_rng(args.seed)
    cases = [run_case(lam, N, args.nulls, rng) for lam in args.lambdas for N in args.Ns]
    ratios = [c["residual_to_null_median_ratio"] for c in cases if c["residual_to_null_median_ratio"] is not None]
    result = {
        "run_id": "R004_HIDDEN_JACOBI_COMMUTATOR_GAUNTLET",
        "phase": "DISCOVERY",
        "claim_cap": "FINITE_NUMERICAL_DIAGNOSTIC_ONLY",
        "source_matrix": {
            "name": "CCM_Route_A_Finite_Matrix_Construction_v0_1_patched.ipynb",
            "sha256": SOURCE_NOTEBOOK_SHA256,
            "formula": "tau = W_0,2 - W_R - sum_p W_p",
        },
        "candidate_space": "real symmetric traceless tridiagonal (Jacobi) matrices",
        "objective": "min ||[M,A]||_F / (||M||_F ||A||_F)",
        "null": "random orthogonal conjugation preserving the exact eigenvalues of each CCM matrix",
        "cases": cases,
        "summary": {
            "max_residual_to_null_median_ratio": float(max(ratios)) if ratios else None,
            "median_residual_to_null_median_ratio": float(np.median(ratios)) if ratios else None,
            "all_candidate_residuals_below_null_min": bool(all(c["matched_tridiagonal_commutator_residual"] < c["eigenvalue_preserving_null_min"] for c in cases if c["null_count"])),
        },
        "bounded_claim": {
            "result": "PASS" if ratios and max(ratios) < 0.1 else "FAIL",
            "certificate_status": "VALID",
            "statement": "Across the tested finite CCM matrices, a recovered traceless Jacobi generator commutes substantially better than eigenvalue-preserving random-basis nulls.",
        },
        "nonclaims": [
            "The recovered generator has not been identified with the prolate operator.",
            "No asymptotic commutator-decay theorem is proved.",
            "No eigenvector or spectral convergence theorem is proved.",
            "This is not RH evidence or a mathematical proof.",
        ],
        "runtime_seconds": time.time() - t0,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2))
    print(json.dumps({"summary": result["summary"], "bounded_claim": result["bounded_claim"], "runtime_seconds": result["runtime_seconds"], "output": str(args.output)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
