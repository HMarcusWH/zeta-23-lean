#!/usr/bin/env python3
"""Post-#280 production saturation-frontier measurements.

Claim cap: EXPERIMENTAL_SIGNAL_ONLY.

This executable measures the exact source/arithmetic quantity isolated by the
handoff and PR #280 on frozen canonical near-seam states. It does not assert
that any sampled point is an actual first contact.

For a simple even ground eigenvector z it records:
  * the production source moment S = A_L[H_z],
  * M4(z),
  * Q_arith = S*M4,
  * the independent spectral identity
        Q_spectral = <Dz,M Dz> - lambda_even ||Dz||^2,
  * the response vector w from ordinary simple-eigenvalue perturbation,
  * the exact handoff remainder source R(t),
  * A_L[R],
  * Delta_sat = A_L[R] - (2*pi)^2 Q/L^2,
  * finite-difference optimized curvature and stationarity diagnostics.

Only a state with a strict/simple even branch is source-eligible. Even then the
reported Delta is a NEAR_CONTACT_PROXY unless zero energy and stationarity are
separately established. No finite measurement is theorem authority.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad
import sympy as sp

from canonical_source_numeric import canonical_source_matrix_L

SCHEMA = "POST280_PRODUCTION_SATURATION_FRONTIER_v1"
CLAIM_CAP = "EXPERIMENTAL_SIGNAL_ONLY"


def centered(K: int) -> np.ndarray:
    return np.arange(-K, K + 1, dtype=float)


def boundary_flat_parity_basis(K: int, parity: str) -> np.ndarray:
    if K < 2:
        raise ValueError("require K>=2")
    idx = list(range(-K, K + 1))
    pos = {n: n + K for n in idx}

    def v(j: int) -> np.ndarray:
        col = np.zeros(2 * K + 1, dtype=float)
        col[pos[j]] += 1.0
        col[pos[-1]] -= j * (j - 1) / 2.0
        col[pos[0]] -= 1.0 - j * j
        col[pos[1]] -= j * (j + 1) / 2.0
        return col

    cols = []
    for j in range(2, K + 1):
        vp, vm = v(j), v(-j)
        cols.append(vp + vm if parity == "even" else vp - vm)
    B = np.column_stack(cols)
    for p in range(3):
        err = np.max(np.abs((centered(K) ** p) @ B))
        if err > 1e-10:
            raise AssertionError("boundary-flat basis construction drift")
    Q, _ = np.linalg.qr(B)
    return Q


def source_matrix(omega: float, K: int) -> np.ndarray:
    ns = centered(K)
    out = np.zeros((len(ns), len(ns)), dtype=float)
    two_pi = 2.0 * math.pi
    for i, n in enumerate(ns):
        for j, m in enumerate(ns):
            if i == j:
                out[i, j] = 2.0 * omega * math.cos(two_pi * n * omega)
            else:
                out[i, j] = (
                    math.sin(two_pi * n * omega)
                    - math.sin(two_pi * m * omega)
                ) / (math.pi * (n - m))
    return out


def source_matrix_prime(omega: float, K: int) -> np.ndarray:
    ns = centered(K)
    out = np.zeros((len(ns), len(ns)), dtype=float)
    two_pi = 2.0 * math.pi
    for i, n in enumerate(ns):
        for j, m in enumerate(ns):
            if i == j:
                a = two_pi * n
                out[i, j] = (
                    2.0 * math.cos(a * omega)
                    - 2.0 * omega * a * math.sin(a * omega)
                )
            else:
                out[i, j] = 2.0 * (
                    n * math.cos(two_pi * n * omega)
                    - m * math.cos(two_pi * m * omega)
                ) / (n - m)
    return out


def von_mangoldt_float(q: int) -> float:
    if q < 2:
        return 0.0
    fac = sp.factorint(int(q))
    if len(fac) != 1:
        return 0.0
    p = next(iter(fac))
    return math.log(float(p))


def production_kernel(t: float) -> float:
    if t == 0.0:
        return float("-inf")
    arch = math.exp(1.5 * t) / math.expm1(2.0 * t)
    return 2.0 * math.cosh(t / 2.0) - arch


def production_value(L: float, f) -> tuple[float, float]:
    if not L > 0:
        raise ValueError("require L>0")

    def integrand(t: float) -> float:
        if abs(t) < 1e-13:
            return 0.0
        return production_kernel(t) * float(f(t))

    continuous, err = quad(
        integrand,
        0.0,
        L,
        epsabs=2e-10,
        epsrel=2e-10,
        limit=400,
        points=[0.0, L],
    )
    Q = int(math.floor(math.exp(L) + 1e-12))
    discrete = 0.0
    for q in range(2, Q + 1):
        vm = von_mangoldt_float(q)
        if vm == 0.0:
            continue
        discrete += vm / math.sqrt(q) * float(f(math.log(q)))
    return float(continuous - discrete), float(err)


def derivative_step(L: float) -> float:
    Q = max(1, int(math.floor(math.exp(L))))
    lo = math.log(Q)
    hi = math.log(Q + 1)
    room = min(L - lo, hi - L)
    if room <= 0:
        raise ValueError("derivative point is not strictly inside one cutoff cell")
    return min(2.0 ** -15, room / 8.0)


def eigen_data(L: float, K: int, parity: str):
    U = boundary_flat_parity_basis(K, parity)
    M = canonical_source_matrix_L(float(L), K)
    H = U.T @ M @ U
    H = (H + H.T) / 2.0
    vals, vecs = np.linalg.eigh(H)
    return M, U, H, vals, vecs


def evaluate(L: float, K: int) -> dict:
    M, Ue, He, evals, evecs = eigen_data(L, K, "even")
    _, Uo, Ho, ovals, _ = eigen_data(L, K, "odd")
    lam = float(evals[0])
    odd_bottom = float(ovals[0])
    even_gap = float(evals[1] - evals[0]) if len(evals) > 1 else float("inf")
    zc = evecs[:, 0]
    z = Ue @ zc
    z = z / np.linalg.norm(z)

    hfd = derivative_step(L)
    Mp = canonical_source_matrix_L(float(L + hfd), K)
    Mm = canonical_source_matrix_L(float(L - hfd), K)
    dM = (Mp - Mm) / (2.0 * hfd)
    d2M = (Mp - 2.0 * M + Mm) / (hfd * hfd)
    dH = Ue.T @ dM @ Ue
    d2H = Ue.T @ d2M @ Ue

    lam_prime = float(zc @ dH @ zc)
    fixed_second = float(zc @ d2H @ zc)
    mixing = 0.0
    wc = np.zeros_like(zc)
    for j in range(1, len(evals)):
        coupling = float(evecs[:, j] @ dH @ zc)
        gap = float(evals[j] - evals[0])
        mixing += 2.0 * coupling * coupling / gap
        wc += -(coupling / gap) * evecs[:, j]
    kappa_fd = fixed_second - mixing
    w = Ue @ wc

    ns = centered(K)
    m4 = float(np.dot(ns ** 4, z))
    Nvec = ns ** 2 - float(np.mean(ns ** 2))
    nu = float(np.dot(Nvec, Nvec))
    hvec = ns ** 2 * z - (m4 / nu) * Nvec

    def H_source(omega: float) -> float:
        return float(Nvec @ source_matrix(omega, K) @ z / nu)

    S, S_err = production_value(L, lambda t: H_source(1.0 - t / L))
    q_arith = float(m4 * S)

    Dz = ns * z
    odd_energy = float(Dz @ M @ Dz)
    q_spectral = float(odd_energy - lam * float(Dz @ Dz))

    a2 = (2.0 * math.pi) ** 2

    def remainder_source(t: float) -> float:
        omega = 1.0 - t / L
        A = source_matrix(omega, K)
        Ap = source_matrix_prime(omega, K)
        mH = m4 * H_source(omega)
        ehz = float(hvec @ A @ z)
        ezw_prime = float(z @ Ap @ w)
        return (
            a2 * (L * L - t * t) / (L ** 4) * mH
            - a2 * t * t / (L ** 4) * ehz
            + 2.0 * t / (L * L) * ezw_prime
        )

    arithmetic_remainder, remainder_err = production_value(L, remainder_source)
    delta_sat = float(arithmetic_remainder - a2 / (L * L) * q_arith)

    strict_even = bool(lam < odd_bottom)
    simple_even = bool(even_gap > 1e-9)
    source_identity_error = abs(q_arith - q_spectral)

    return {
        "L": L,
        "K": K,
        "cutoff_Q": int(math.floor(math.exp(L))),
        "classification": (
            "STRICT_EVEN_SIMPLE_NEAR_CONTACT_PROXY"
            if strict_even and simple_even
            else "NOT_STRICT_EVEN_FRONTIER_ELIGIBLE"
        ),
        "contact_claimed": False,
        "lambda_even": lam,
        "lambda_odd": odd_bottom,
        "even_ground_gap": even_gap,
        "lambda_prime_fd": lam_prime,
        "finite_difference_step": hfd,
        "fixed_vector_second_fd": fixed_second,
        "mixing_subtraction": mixing,
        "kappa_fd": kappa_fd,
        "M4": m4,
        "source_moment_S": S,
        "source_moment_integral_error_estimate": S_err,
        "Q_arithmetic": q_arith,
        "Q_spectral_reduced": q_spectral,
        "Q_representation_abs_error": source_identity_error,
        "production_arithmetic_remainder": arithmetic_remainder,
        "production_remainder_integral_error_estimate": remainder_err,
        "delta_sat_proxy": delta_sat,
        "delta_minus_kappa_fd": delta_sat - kappa_fd,
        "strict_even_numeric": strict_even,
        "simple_even_numeric": simple_even,
        "nonclaims": [
            "This is floating discovery output, not interval certification.",
            "No sampled point is asserted to be an actual first contact.",
            "Delta_sat is a near-contact proxy unless zero energy and stationarity are independently established.",
            "No finite observation is theorem authority or an RH claim."
        ]
    }


def validate_fixture(fixture: dict) -> None:
    if fixture.get("schema_version") != "POST280_PRODUCTION_SATURATION_FRONTIER_PROTOCOL_v1":
        raise ValueError("fixture schema drift")
    if fixture.get("claim_cap") != CLAIM_CAP:
        raise ValueError("claim cap drift")
    if fixture.get("adaptive_search") is not False:
        raise ValueError("adaptive search is forbidden in this frozen campaign")
    if fixture.get("offset_powers") != [10, 12]:
        raise ValueError("offset schedule drift")


def run(fixture: dict) -> dict:
    validate_fixture(fixture)
    rows = []
    for case in fixture["cases"]:
        q = int(case["q"])
        K = int(case["K"])
        L0 = math.log(float(q))
        for p in fixture["offset_powers"]:
            L = L0 + 2.0 ** (-p)
            row = evaluate(L, K)
            row.update({"q": q, "kind": case["kind"], "offset_power": p})
            rows.append(row)
    eligible = [r for r in rows if r["strict_even_numeric"] and r["simple_even_numeric"]]
    return {
        "schema_version": SCHEMA,
        "claim_cap": CLAIM_CAP,
        "adaptive_search": False,
        "fixture": fixture,
        "measurements": rows,
        "summary": {
            "measurement_count": len(rows),
            "strict_even_simple_count": len(eligible),
            "max_Q_representation_abs_error": max(
                (r["Q_representation_abs_error"] for r in rows), default=None
            ),
            "delta_sat_signs_on_eligible": [
                1 if r["delta_sat_proxy"] > 0 else -1 if r["delta_sat_proxy"] < 0 else 0
                for r in eligible
            ],
            "theorem_promotion": False,
            "terminal_claim": "RH_OPEN"
        }
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    fixture = json.loads(Path(args.input).read_text(encoding="utf-8"))
    out = run(fixture)
    Path(args.output).write_text(
        json.dumps(out, indent=2, sort_keys=True) + "\n",
        encoding="utf-8"
    )
    print(json.dumps(out["summary"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
