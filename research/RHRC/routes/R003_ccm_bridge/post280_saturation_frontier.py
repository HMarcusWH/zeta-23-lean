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
import cmath
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad
import sympy as sp

from canonical_source_numeric import canonical_source_matrix_L

SCHEMA = "POST280_PRODUCTION_SATURATION_FRONTIER_v1_1"
CLAIM_CAP = "EXPERIMENTAL_SIGNAL_ONLY"

# Floating Q-representation integrity policy.
#
# The previous implementation divided |Q_arith-Q_spectral| by
# 1+|Q_arith|+|Q_spectral| and called the result a relative error.  Near the
# frontier Q can be tiny, so that quantity is effectively an absolute residual
# and can hide large fractional disagreement.  Use an explicit mixed tolerance
# instead and fail closed by classifying under-resolved rows separately.
Q_REPRESENTATION_ATOL = 5e-15
Q_REPRESENTATION_RTOL = 5e-7
Q_ARITHMETIC_ERROR_MULTIPLIER = 5.0
Q_NUMERICAL_RESOLUTION_FACTOR = 20.0

Q_STATUS_PASS = "Q_REPRESENTATION_PASS"
Q_STATUS_UNRESOLVED = "Q_NUMERICALLY_UNRESOLVED"
Q_STATUS_MISMATCH = "Q_REPRESENTATION_MISMATCH"
Q_STATUS_NOT_APPLICABLE = "Q_REPRESENTATION_NOT_APPLICABLE"


def q_representation_diagnostic(
    q_arith: float,
    q_spectral: float,
    q_arith_error_estimate: float,
    *,
    theorem_expected: bool,
) -> dict:
    """Classify the floating arithmetic/spectral Q comparison.

    This is an execution-integrity diagnostic only; the exact equality is Lean
    theorem authority on the canonical zero-mode branch.  The quadrature error
    is not a rigorous interval bound, so rows too small relative to that error
    budget are marked numerically unresolved rather than passed.
    """
    abs_error = abs(q_arith - q_spectral)
    scale = max(abs(q_arith), abs(q_spectral))
    fractional_discrepancy = abs_error / scale if scale > 0.0 else None
    arith_error = max(0.0, float(q_arith_error_estimate))
    error_budget = max(
        Q_REPRESENTATION_ATOL,
        Q_ARITHMETIC_ERROR_MULTIPLIER * arith_error,
    )
    resolution_threshold = Q_NUMERICAL_RESOLUTION_FACTOR * error_budget
    mixed_tolerance = (
        Q_REPRESENTATION_ATOL
        + Q_REPRESENTATION_RTOL * scale
        + Q_ARITHMETIC_ERROR_MULTIPLIER * arith_error
    )

    if not theorem_expected:
        status = Q_STATUS_NOT_APPLICABLE
        consistent = None
        resolved = None
    elif scale <= resolution_threshold:
        status = Q_STATUS_UNRESOLVED
        consistent = None
        resolved = False
    elif abs_error <= mixed_tolerance:
        status = Q_STATUS_PASS
        consistent = True
        resolved = True
    else:
        status = Q_STATUS_MISMATCH
        consistent = False
        resolved = True

    return {
        "status": status,
        "consistent": consistent,
        "resolved": resolved,
        "abs_error": abs_error,
        "fractional_discrepancy": fractional_discrepancy,
        "mixed_tolerance": mixed_tolerance,
        "resolution_threshold": resolution_threshold,
        "arithmetic_error_estimate": arith_error,
    }


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



def exp_weight_sprime_float(c: complex, weight: complex, K: int) -> np.ndarray:
    """Floating twin of the frozen post-#247 zero-side exp-weight matrix."""
    ec = cmath.exp(c)
    a: dict[int, float] = {}
    b: dict[int, float] = {}

    def j0(k: float) -> complex:
        s = 1j * k - c
        return (1.0 - ec) / s

    def j1(k: float) -> complex:
        s = 1j * k - c
        return ((s - 1.0) + ec) / (s * s)

    for n in range(0, K + 1):
        k = 2.0 * math.pi * n
        an = (weight * (j0(k) + j0(-k)) / 2.0).real
        bn = (weight * (j1(k) - j1(-k)) / (2.0j)).real
        a[n] = a[-n] = float(an)
        b[n], b[-n] = float(bn), float(-bn)

    idx = list(range(-K, K + 1))
    out = np.zeros((len(idx), len(idx)), dtype=float)
    for r, n in enumerate(idx):
        for col, m in enumerate(idx):
            if n == m:
                out[r, col] = 2.0 * a[n] - 4.0 * math.pi * n * b[n]
            else:
                out[r, col] = 2.0 * (n * a[n] - m * a[m]) / (n - m)
    return (out + out.T) / 2.0


def planted_increment_float(
    L: float, K: int, gamma: float, delta: float
) -> np.ndarray:
    """Historical scoped zero-side quartet control.

    This is a local falsifier only. It is not a globally self-consistent
    alternate Euler product, prime system, or zeta function.
    """
    out = np.zeros((2 * K + 1, 2 * K + 1), dtype=float)
    for sign in (1.0, -1.0):
        s = complex(sign * delta, gamma)
        out += exp_weight_sprime_float(s * L, -2.0 / s, K)
    return (out + out.T) / 2.0


def matrix_builder_for_provenance(
    provenance: str, gamma: float, delta: float | None
):
    if provenance == "UNCONDITIONAL_CANONICAL":
        return lambda L, K: canonical_source_matrix_L(float(L), K)
    if provenance != "PLANTED_CONTROL_ONLY" or delta is None:
        raise ValueError("invalid saturation-frontier provenance")

    def build(L: float, K: int) -> np.ndarray:
        return canonical_source_matrix_L(float(L), K) - planted_increment_float(
            float(L), K, gamma, delta
        )

    return build

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


def eigen_data(L: float, K: int, parity: str, matrix_builder):
    U = boundary_flat_parity_basis(K, parity)
    M = matrix_builder(float(L), K)
    H = U.T @ M @ U
    H = (H + H.T) / 2.0
    vals, vecs = np.linalg.eigh(H)
    return M, U, H, vals, vecs


def evaluate(
    L: float,
    K: int,
    *,
    provenance: str = "UNCONDITIONAL_CANONICAL",
    control_name: str | None = None,
    gamma: float = 10.0,
    delta: float | None = None,
) -> dict:
    matrix_builder = matrix_builder_for_provenance(provenance, gamma, delta)
    M, Ue, He, evals, evecs = eigen_data(L, K, "even", matrix_builder)
    _, Uo, Ho, ovals, _ = eigen_data(L, K, "odd", matrix_builder)
    lam = float(evals[0])
    odd_bottom = float(ovals[0])
    even_gap = float(evals[1] - evals[0]) if len(evals) > 1 else float("inf")
    zc = evecs[:, 0]
    z = Ue @ zc
    z = z / np.linalg.norm(z)

    hfd = derivative_step(L)
    Mp = matrix_builder(float(L + hfd), K)
    Mm = matrix_builder(float(L - hfd), K)
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
    theorem_q_identity_expected = provenance == "UNCONDITIONAL_CANONICAL"
    q_arith_error_estimate = abs(m4) * abs(S_err)
    q_diag = q_representation_diagnostic(
        q_arith,
        q_spectral,
        q_arith_error_estimate,
        theorem_expected=theorem_q_identity_expected,
    )

    if strict_even and simple_even:
        if q_diag["status"] == Q_STATUS_PASS:
            row_classification = "STRICT_EVEN_SIMPLE_NEAR_CONTACT_PROXY"
        elif q_diag["status"] == Q_STATUS_UNRESOLVED:
            row_classification = "STRICT_EVEN_SIMPLE_Q_NUMERICALLY_UNRESOLVED"
        elif q_diag["status"] == Q_STATUS_MISMATCH:
            row_classification = "STRICT_EVEN_SIMPLE_Q_REPRESENTATION_MISMATCH"
        else:
            row_classification = "STRICT_EVEN_SIMPLE_CONTROL_PROXY"
    else:
        row_classification = "NOT_STRICT_EVEN_FRONTIER_ELIGIBLE"

    return {
        "provenance": provenance,
        "control_name": control_name,
        "L": L,
        "K": K,
        "cutoff_Q": int(math.floor(math.exp(L))),
        "classification": row_classification,
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
        "Q_representation_abs_error": q_diag["abs_error"],
        "Q_representation_fractional_discrepancy": q_diag["fractional_discrepancy"],
        "Q_representation_mixed_tolerance": q_diag["mixed_tolerance"],
        "Q_representation_resolution_threshold": q_diag["resolution_threshold"],
        "Q_arithmetic_error_estimate": q_diag["arithmetic_error_estimate"],
        "Q_representation_status": q_diag["status"],
        "Q_representation_consistent": q_diag["consistent"],
        "Q_numerically_resolved": q_diag["resolved"],
        "Q_representation_theorem_expected": theorem_q_identity_expected,
        "production_arithmetic_remainder": arithmetic_remainder,
        "production_remainder_integral_error_estimate": remainder_err,
        "delta_sat_proxy": delta_sat,
        "delta_minus_kappa_fd": delta_sat - kappa_fd,
        "strict_even_numeric": strict_even,
        "simple_even_numeric": simple_even,
        "nonclaims": [
            "This is floating discovery output, not interval certification.",
            "PLANTED_CONTROL_ONLY rows are local zero-side falsifiers, not alternate zeta/Euler products.",
            "No sampled point is asserted to be an actual first contact.",
            "Canonical Q rows below the floating resolution threshold are Q_NUMERICALLY_UNRESOLVED, not passed.",
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
    if fixture.get("offset_powers") != [8, 10, 12]:
        raise ValueError("offset schedule drift")
    if fixture.get("planted_gamma") != [10, 1]:
        raise ValueError("planted gamma drift")
    if fixture.get("planted_on_line_delta") != [0, 1]:
        raise ValueError("planted on-line delta drift")
    if fixture.get("planted_off_line_delta") != [1, 20]:
        raise ValueError("planted off-line delta drift")
    expected_cases = [
        (13, 3, "VON_MANGOLDT_SEAM"),
        (16, 3, "VON_MANGOLDT_SEAM"),
        (17, 3, "VON_MANGOLDT_SEAM"),
        (19, 3, "VON_MANGOLDT_SEAM"),
        (14, 3, "ZERO_VON_MANGOLDT_CONTROL"),
        (15, 3, "ZERO_VON_MANGOLDT_CONTROL"),
        (18, 3, "ZERO_VON_MANGOLDT_CONTROL"),
        (16, 4, "VON_MANGOLDT_REPLICATION"),
        (17, 4, "VON_MANGOLDT_REPLICATION"),
        (16, 6, "VON_MANGOLDT_REPLICATION"),
        (17, 6, "VON_MANGOLDT_REPLICATION"),
    ]
    actual_cases = [
        (int(row["q"]), int(row["K"]), row["kind"])
        for row in fixture.get("cases", [])
    ]
    if actual_cases != expected_cases:
        raise ValueError("frozen case schedule drift")


def run(fixture: dict) -> dict:
    validate_fixture(fixture)
    rows = []
    gamma = fixture["planted_gamma"][0] / fixture["planted_gamma"][1]
    on_delta = (
        fixture["planted_on_line_delta"][0] /
        fixture["planted_on_line_delta"][1]
    )
    off_delta = (
        fixture["planted_off_line_delta"][0] /
        fixture["planted_off_line_delta"][1]
    )
    for case in fixture["cases"]:
        q = int(case["q"])
        K = int(case["K"])
        L0 = math.log(float(q))
        for p in fixture["offset_powers"]:
            L = L0 + 2.0 ** (-p)
            canonical = evaluate(L, K)
            canonical.update({"q": q, "kind": case["kind"], "offset_power": p})
            rows.append(canonical)
            planted_on = evaluate(
                L, K,
                provenance="PLANTED_CONTROL_ONLY",
                control_name="PLANTED_ON_LINE",
                gamma=gamma,
                delta=on_delta,
            )
            planted_on.update({"q": q, "kind": case["kind"], "offset_power": p})
            rows.append(planted_on)
            planted_off = evaluate(
                L, K,
                provenance="PLANTED_CONTROL_ONLY",
                control_name="PLANTED_OFF_LINE",
                gamma=gamma,
                delta=off_delta,
            )
            planted_off.update({"q": q, "kind": case["kind"], "offset_power": p})
            rows.append(planted_off)
    canonical_rows = [
        r for r in rows if r["provenance"] == "UNCONDITIONAL_CANONICAL"
    ]
    mismatches = [
        r for r in canonical_rows
        if r["Q_representation_status"] == Q_STATUS_MISMATCH
    ]
    if mismatches:
        bad = [
            {
                "q": r["q"],
                "K": r["K"],
                "offset_power": r["offset_power"],
                "abs_error": r["Q_representation_abs_error"],
                "fractional_discrepancy": r["Q_representation_fractional_discrepancy"],
                "mixed_tolerance": r["Q_representation_mixed_tolerance"],
            }
            for r in mismatches
        ]
        raise AssertionError(f"Q representation disagreement: {bad}")

    q_resolved = [
        r for r in canonical_rows
        if r["Q_representation_status"] == Q_STATUS_PASS
    ]
    q_unresolved = [
        r for r in canonical_rows
        if r["Q_representation_status"] == Q_STATUS_UNRESOLVED
    ]
    eligible = [
        r for r in q_resolved
        if r["strict_even_numeric"] and r["simple_even_numeric"]
    ]
    planted_rows = [r for r in rows if r["provenance"] == "PLANTED_CONTROL_ONLY"]
    signs_by_kind = {}
    for kind in sorted({r["kind"] for r in eligible}):
        signs_by_kind[kind] = [
            1 if r["delta_sat_proxy"] > 0 else -1 if r["delta_sat_proxy"] < 0 else 0
            for r in eligible if r["kind"] == kind
        ]
    return {
        "schema_version": SCHEMA,
        "claim_cap": CLAIM_CAP,
        "adaptive_search": False,
        "fixture": fixture,
        "measurements": rows,
        "summary": {
            "measurement_count": len(rows),
            "canonical_measurement_count": len(canonical_rows),
            "planted_control_measurement_count": len(planted_rows),
            "strict_even_simple_count": len(eligible),
            "max_Q_representation_abs_error": max(
                (r["Q_representation_abs_error"] for r in canonical_rows), default=None
            ),
            "max_Q_representation_fractional_discrepancy_resolved": max(
                (
                    r["Q_representation_fractional_discrepancy"]
                    for r in q_resolved
                    if r["Q_representation_fractional_discrepancy"] is not None
                ),
                default=None,
            ),
            "Q_representation_resolved_count": len(q_resolved),
            "Q_representation_unresolved_count": len(q_unresolved),
            "Q_representation_mismatch_count": 0,
            "Q_representation_integrity_pass": True,
            "Q_representation_consistency_pass": True,
            "delta_sat_signs_on_eligible": [
                1 if r["delta_sat_proxy"] > 0 else -1 if r["delta_sat_proxy"] < 0 else 0
                for r in eligible
            ],
            "delta_sat_signs_by_kind": signs_by_kind,
            "planted_control_delta_signs": {
                name: [
                    1 if r["delta_sat_proxy"] > 0 else -1 if r["delta_sat_proxy"] < 0 else 0
                    for r in planted_rows if r["control_name"] == name
                ]
                for name in ("PLANTED_ON_LINE", "PLANTED_OFF_LINE")
            },
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
