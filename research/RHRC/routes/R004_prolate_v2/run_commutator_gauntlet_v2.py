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


@lru_cache(maxsize=None)
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
            total += lk * k**-0.5 * q_basis(n, m, math.log(k), L)
    return total


def build_ccm_matrix(lam: float, N: int) -> np.ndarray:
    if not lam > 1 or N < 1:
        raise ValueError("require lambda>1 and N>=1")
    L = 2.0 * math.log(lam)
    idx = list(range(-N, N + 1))
    M = np.empty((len(idx), len(idx)), dtype=float)
    for r, n in enumerate(idx):
        for c, m in enumerate(idx):
            M[r, c] = (
                pole_component(n, m, L)
                - arch_component(n, m, L)
                - prime_component(n, m, L)
            )
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


def matched_generator(M: np.ndarray) -> tuple[np.ndarray, float]:
    basis = traceless_tridiagonal_basis(len(M))
    gram = np.array([[np.vdot(x, y).real for y in basis] for x in basis])
    commutators = [M @ x - x @ M for x in basis]
    comm_gram = np.array(
        [[np.vdot(x, y).real for y in commutators] for x in commutators]
    )
    vals, vecs = la.eigh(comm_gram, gram)
    coeff = vecs[:, 0]
    A = sum(c * b for c, b in zip(coeff, basis))
    return A, float(vals[0])


def comm_metrics(M: np.ndarray, A: np.ndarray) -> dict:
    comm = M @ A - A @ M
    mf = np.linalg.norm(M, "fro")
    af = np.linalg.norm(A, "fro")
    cf = np.linalg.norm(comm, "fro")
    mo = np.linalg.norm(M, 2)
    ao = np.linalg.norm(A, 2)
    co = np.linalg.norm(comm, 2)
    eigenvalues = np.linalg.eigvalsh(A)
    gaps = np.diff(eigenvalues)
    min_gap = float(np.min(gaps)) if len(gaps) else float("nan")
    return {
        "commutator_fro": float(cf),
        "M_fro": float(mf),
        "J_fro": float(af),
        "fro_normalized": float(cf / (mf * af)) if mf * af else None,
        "commutator_op": float(co),
        "M_op": float(mo),
        "J_op": float(ao),
        "op_normalized": float(co / (mo * ao)) if mo * ao else None,
        "J_min_adjacent_gap": min_gap,
        "commutator_over_J_gap": float(cf / min_gap) if min_gap > 0 else None,
        "commutator_over_Mfro_Jgap": float(cf / (mf * min_gap))
        if mf > 0 and min_gap > 0
        else None,
    }


def random_orthogonal_conjugate(
    M: np.ndarray, rng: np.random.Generator
) -> np.ndarray:
    Q, _ = np.linalg.qr(rng.normal(size=M.shape))
    return Q @ np.diag(np.linalg.eigvalsh(M)) @ Q.T


def band_profile_shuffle(M: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    """Preserve each diagonal band's value multiset while destroying coherent index alignment."""
    n = len(M)
    out = np.zeros_like(M)
    for d in range(n):
        vals = np.array([M[i, i + d] for i in range(n - d)], dtype=float)
        vals = rng.permutation(vals)
        for i, value in enumerate(vals):
            out[i, i + d] = out[i + d, i] = value
    return out


def displacement_metrics(M: np.ndarray) -> dict:
    """Audit low displacement rank against the centered Fourier-index operator D."""
    n = len(M)
    D = np.diag(np.arange(n) - (n - 1) / 2)
    comm = D @ M - M @ D
    singular = la.svdvals(comm)
    total = np.linalg.norm(comm, "fro")
    tail = math.sqrt(float(np.sum(singular[2:] ** 2))) if len(singular) > 2 else 0.0
    return {
        "displacement_commutator_fro": float(total),
        "rank2_tail_fro": tail,
        "rank2_relative_residual": float(tail / total) if total else 0.0,
        "leading_singular_values": [float(x) for x in singular[:6]],
    }


def run_case(
    lam: float, N: int, null_count: int, rng: np.random.Generator
) -> dict:
    M = build_ccm_matrix(lam, N)
    A, pencil_min = matched_generator(M)
    metrics = comm_metrics(M, A)

    eigenvalue_nulls: list[float] = []
    band_nulls: list[float] = []
    for _ in range(null_count):
        M_eig = random_orthogonal_conjugate(M, rng)
        A_eig, _ = matched_generator(M_eig)
        eigenvalue_nulls.append(comm_metrics(M_eig, A_eig)["fro_normalized"])

        M_band = band_profile_shuffle(M, rng)
        A_band, _ = matched_generator(M_band)
        band_nulls.append(comm_metrics(M_band, A_band)["fro_normalized"])

    return {
        "lambda": lam,
        "N": N,
        "dimension": 2 * N + 1,
        "matrix_symmetry_error": float(np.max(np.abs(M - M.T))),
        "matched_generator": metrics,
        "double_commutator_pencil_min": pencil_min,
        "eigenvalue_null": {
            "count": null_count,
            "min": float(np.min(eigenvalue_nulls)),
            "median": float(np.median(eigenvalue_nulls)),
            "ratio_to_median": float(
                metrics["fro_normalized"] / np.median(eigenvalue_nulls)
            ),
        },
        "band_profile_null": {
            "count": null_count,
            "min": float(np.min(band_nulls)),
            "median": float(np.median(band_nulls)),
            "ratio_to_median": float(metrics["fro_normalized"] / np.median(band_nulls)),
        },
        "displacement": displacement_metrics(M),
        "generator_diagonal": [float(x) for x in np.diag(A)],
        "generator_offdiagonal": [float(x) for x in np.diag(A, 1)],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lambdas", nargs="+", type=float, default=[2, 3, 5, 7, 10])
    parser.add_argument("--Ns", nargs="+", type=int, default=[5, 8, 12, 20])
    parser.add_argument("--nulls", type=int, default=20)
    parser.add_argument("--seed", type=int, default=20260820)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    t0 = time.time()
    rng = np.random.default_rng(args.seed)
    cases = [
        run_case(lam, N, args.nulls, rng)
        for lam in args.lambdas
        for N in args.Ns
    ]

    result = {
        "run_id": "R004_HIDDEN_JACOBI_COMMUTATOR_GAUNTLET_V2",
        "phase": "DISCOVERY",
        "claim_cap": "FINITE_NUMERICAL_DIAGNOSTIC_ONLY",
        "source_notebook_sha256": SOURCE_NOTEBOOK_SHA256,
        "configuration": {
            "lambdas": args.lambdas,
            "Ns": args.Ns,
            "nulls_per_case": args.nulls,
            "seed": args.seed,
        },
        "cases": cases,
        "summary": {
            "max_eigenvalue_null_ratio": max(
                c["eigenvalue_null"]["ratio_to_median"] for c in cases
            ),
            "max_band_profile_null_ratio": max(
                c["band_profile_null"]["ratio_to_median"] for c in cases
            ),
            "max_rank2_displacement_residual": max(
                c["displacement"]["rank2_relative_residual"] for c in cases
            ),
        },
        "nonclaims": [
            "No asymptotic commutator theorem.",
            "No prolate identification.",
            "No eigenvector convergence theorem.",
            "No RH evidence or proof.",
        ],
        "runtime_seconds": time.time() - t0,
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2))
    print(json.dumps(result["summary"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
