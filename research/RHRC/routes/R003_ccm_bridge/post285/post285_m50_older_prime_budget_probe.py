"""POST285 M50 research probe: the older-prime budget on the canonical grid (Step 91).

`Zeta23/CCM/CanonicalContactOlderPrimeBudget.lean` proves, at every stationary
generated strict-even contact (aperture L, cutoff K, normalized even z),

    P - sum_q beta_q e(omega_q) = -kappa C,        kappa = 2 L^4/(2 pi)^2, C >= 0,
    (91.1)  sum_O beta_q e(omega_q) >= P + kappa C + b sum_N beta_q omega_q^7,
    (91.2)  P + kappa C + b sum_N beta_q omega_q^7 <= 2(2K+1)K^2 sum_O beta_q omega_q,

with e = e_{Dz}, P = int_0^L t^2 e(1 - t/L) (e^{-t/2} + e^{t/2} - rho(t)) dt,
beta_q = Lambda(q)(log q)^2/sqrt(q), omega_q = 1 - log q/L, near N = {omega_q <= theta},
older O = {omega_q > theta} and b = (pi^6/90)(delta/(4|H(z)|))^2.

No contact is known, so this probe evaluates the same quantities at the even
ground state z of the float canonical matrices (K = 2..6, L = 0.25..6), with
delta = lambda_odd - lambda_even and theta = theta_*(c = 4) from the M49 probe.
It checks the two proved ingredients at every sample:

    |e(omega_q)| <= 2 omega_q (2K+1) K^2                 (size bound, |z| = 1),
    beta_q e(omega_q) <= -b beta_q omega_q^7 on N        (M49 near-edge bound),

and reports, per row, the complete value V = P - sum_q beta_q e(omega_q) (a
contact needs V = -kappa C <= 0; its sign is read only when |V| exceeds
1e-9 max(1, |P|), since V cancels P against the prime sum) and the finite-form slack
2(2K+1)K^2 sum_O beta_q omega_q - P - b sum_N beta_q omega_q^7 (a contact needs
slack >= kappa C >= 0).

EXPERIMENTAL SIGNAL ONLY: float matrices, ground states rather than contacts,
this grid only.  A row with V > 0 or negative slack says only that its ground
state is not a stationary contact; it excludes nothing.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

from canonical_source_numeric import canonical_source_matrix_L  # noqa: E402
from post285_m49_near_edge_probe import elementary_energy, prime_powers  # noqa: E402
from post285_m76_secular_margin import carriers  # noqa: E402


def von_mangoldt(q: int) -> float:
    for p in range(2, int(math.isqrt(q)) + 1):
        if q % p == 0:
            return math.log(p)
    return math.log(q)


def energy_float(n: np.ndarray, u: np.ndarray, w: np.ndarray) -> np.ndarray:
    """Elementary source energy e_u(w) for an array of w (float64)."""
    a = 2 * math.pi * w[:, None] * n[None, :]
    sv = np.sin(a)
    out = np.zeros_like(w)
    for i in range(len(n)):
        for j in range(len(n)):
            if i == j:
                s = 2 * w * np.cos(a[:, i])
            else:
                s = (sv[:, i] - sv[:, j]) / ((n[i] - n[j]) * math.pi)
            out += u[i] * s * u[j]
    return out


@lru_cache(maxsize=None)
def gauss_legendre(nodes: int = 400):
    return np.polynomial.legendre.leggauss(nodes)


def pole_arch_value(n: np.ndarray, u: np.ndarray, L: float, nodes: int = 400) -> float:
    """P = int_0^L t^2 e(1 - t/L) (e^{-t/2} + e^{t/2} - rho(t)) dt by Gauss-Legendre."""
    x, wts = gauss_legendre(nodes)
    t = 0.5 * L * (x + 1)
    rho = np.exp(t / 2) / (np.exp(t) - np.exp(-t))
    kern = np.exp(-t / 2) + np.exp(t / 2) - rho
    f = t ** 2 * energy_float(n, u, 1 - t / L) * kern
    return float(0.5 * L * np.dot(wts, f))


def row(K: int, L: float, n, E, O) -> dict:
    S = canonical_source_matrix_L(L, K)
    A = E.T @ S @ E
    B = O.T @ S @ O
    D = O.T @ np.diag(n) @ E
    g = O.T @ (n ** 3)
    h = (B @ D - D @ A).T @ g / (g @ g)
    ea, va = np.linalg.eigh(A)
    lam_a, lam_b = float(ea[0]), float(np.linalg.eigvalsh(B)[0])
    delta = lam_b - lam_a
    v = va[:, 0]
    z = E @ v
    Dz = n * z
    H = float(h @ v)
    out = {"K": K, "L": L, "lambda_even": lam_a, "lambda_odd": lam_b, "delta": delta, "H_v": H}
    AK = math.sqrt(2 * sum(k ** 10 for k in range(1, K + 1)))
    size_const = 2 * (2 * K + 1) * K ** 2
    qs = prime_powers(math.exp(L))
    samples = []
    for q in qs:
        w = 1 - math.log(q) / L
        beta = von_mangoldt(q) * math.log(q) ** 2 / math.sqrt(q)
        e = elementary_energy(K, Dz, w)
        samples.append((q, w, beta, e))
    P = pole_arch_value(n, Dz, L)
    total = sum(beta * e for _, _, beta, e in samples)
    out["P"] = P
    out["prime_sum"] = total
    out["V"] = P - total
    # V cancels P against the prime sum; its sign is read only above float resolution
    out["V_resolved"] = abs(P - total) > 1e-9 * max(1.0, abs(P))
    size_ok = all(abs(e) <= size_const * max(w, 0.0) * (1 + 1e-9) + 1e-14 for _, w, _, e in samples)
    out["size_bound_ok"] = size_ok
    if delta <= 0 or H == 0:
        out["skipped"] = "nonpositive parity gap"
        return out
    theta = math.sqrt(5 * delta / (AK * abs(H) * 2)) / (2 * math.pi)
    b = math.pi ** 6 / 90 * (delta / (4 * abs(H))) ** 2
    near = [s for s in samples if s[1] <= theta]
    older = [s for s in samples if s[1] > theta]
    near_ok = all(beta * e <= -b * beta * w ** 7 * (1 - 1e-9) + 1e-30 for _, w, beta, e in near)
    S_N = sum(beta * e for _, _, beta, e in near)
    S_O = sum(beta * e for _, _, beta, e in older)
    bonus = b * sum(beta * w ** 7 for _, w, beta, _ in near)
    finite_rhs = size_const * sum(beta * w for _, w, beta, _ in older)
    out.update({"theta": theta, "b": b, "near_samples": len(near), "older_samples": len(older),
                "near_bound_ok": near_ok, "S_near": S_N, "S_older": S_O, "near_bonus": bonus,
                "budget_gap_91_1": S_O - P - bonus, "finite_slack_91_2": finite_rhs - P - bonus,
                "finite_rhs": finite_rhs})
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=6)
    ap.add_argument("--lmax", type=float, default=6.0)
    ap.add_argument("--dl", type=float, default=0.25)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rows = []
    for K in range(2, args.kmax + 1):
        n, E, O = carriers(K)
        L = args.dl
        while L <= args.lmax + 1e-12:
            rows.append(row(K, round(L, 10), n, E, O))
            L += args.dl
    live = [r for r in rows if "skipped" not in r]
    summary = {
        "rows": len(rows),
        "rows_with_positive_gap": len(live),
        "size_bound_failures": sum(1 for r in rows if not r["size_bound_ok"]),
        "near_bound_failures": sum(1 for r in live if not r["near_bound_ok"]),
        "rows_V_negative_resolved": sum(1 for r in rows if r["V_resolved"] and r["V"] < 0),
        "rows_V_positive_resolved": sum(1 for r in rows if r["V_resolved"] and r["V"] > 0),
        "rows_V_unresolved": sum(1 for r in rows if not r["V_resolved"]),
        "max_abs_V_over_abs_P_L_ge_2": max(
            (abs(r["V"]) / abs(r["P"]) for r in rows if r["L"] >= 2 and r["P"] != 0), default=None),
        "min_finite_rhs_over_abs_P_with_older": min(
            (r["finite_rhs"] / abs(r["P"]) for r in live if r["older_samples"] > 0 and r["P"] != 0),
            default=None),
        "rows_P_negative": sum(1 for r in rows if r["P"] < 0),
        "rows_finite_slack_negative": sum(1 for r in live if r["finite_slack_91_2"] < 0),
        "rows_with_near_samples": sum(1 for r in live if r["near_samples"] > 0),
        "rows_V_positive_resolved_list": [(r["K"], r["L"]) for r in rows
                                          if r["V_resolved"] and r["V"] > 0],
        "rows_finite_slack_negative_list": [(r["K"], r["L"]) for r in live
                                            if r["finite_slack_91_2"] < 0],
        "skipped": [(r["K"], r["L"]) for r in rows if "skipped" in r],
    }
    disposition = "EXPERIMENTAL_SIGNAL"
    if summary["size_bound_failures"] or summary["near_bound_failures"]:
        disposition = "FAIL_PROVED_INGREDIENT"
    report = {"terminal_claim": "RH_OPEN", "authority": "EXPERIMENTAL_SIGNAL_ONLY",
              "package": "M50_OLDER_PRIME_BUDGET", "disposition": disposition,
              "summary": summary, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
    return 0 if disposition == "EXPERIMENTAL_SIGNAL" else 1


if __name__ == "__main__":
    raise SystemExit(main())
