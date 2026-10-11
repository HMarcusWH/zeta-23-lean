"""POST285 M33/M34 probe: contact source sign reversal and remainder oscillation.

Checks, on the float canonical matrices (K = 2..5, L = 1, 1.25, ..., 6) at the
even ground state z (not a contact), the statements of
`Zeta23/CCM/CanonicalContactRemainderOscillation.lean`:

  Step 68  e_{Dz}(omega) < 0 at omega = theta/100, theta/10, theta/2, theta (50 digits,
           Dz projected onto the legal odd carrier) with
           theta = min(1/2, 5 delta/(4 pi^2 (X + 1))), X = 2 A_K |H(z)|, and
           e_{Dz}(1) = 2 |Dz|^2 > 0, so e_{Dz} has a zero in (theta, 1); rows with
           theta < 1e-6 are below the 50-digit floor and reported as unresolved;
  Step 70  the M09 identity on the actual source energy:
           P - sum_q beta_q e(omega_q) = int R(e^t) h' + int (e^{-t/2} - rho) h,
           h(t) = t^2 e_{Dz}(1 - t/L), beta_q = Lambda(q)(log q)^2/sqrt q;
  Step 71  |int R(e^t) h'| <= (Omega/2) int |h'|, Omega = sup R - inf R on [1, e^L]
           (sup over integers, inf over left limits, as in M38).

Research signal: at a stationary contact the proved budget reads
|int (e^{-t/2} - rho) h + kappa C| <= (Omega/2) int |h'|.  The probe reports
how much of that room the ground states use, through
r_R = |int R h'| / ((Omega/2) int |h'|) and r_0 = |int (e^{-t/2} - rho) h| / ((Omega/2) int |h'|).

EXPERIMENTAL SIGNAL for the ratios; the three checks are regressions of proved
statements.  Ground states are not contacts, and nothing is excluded.
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
from post285_m49_near_edge_probe import prime_powers  # noqa: E402
from post285_m50_older_prime_budget_probe import energy_float  # noqa: E402
from post285_m76_secular_margin import carriers  # noqa: E402

TOL = 1e-7


@lru_cache(maxsize=None)
def gauss_legendre(nodes: int):
    return np.polynomial.legendre.leggauss(nodes)


def quad(f, a: float, b: float, nodes: int = 40) -> float:
    x, w = gauss_legendre(nodes)
    t = 0.5 * (b - a) * (x + 1) + a
    return float(0.5 * (b - a) * np.dot(w, f(t)))


def energy_mp_legal(K: int, u: np.ndarray, w: float):
    """e_u(w) at 50 digits after projecting the float u onto the legal odd
    carrier (odd part, M_1 = 0) in 50-digit arithmetic: near omega = 0 the true
    value is O(omega^7), and float residuals in M_1 would swamp it."""
    with mp.workdps(50):
        n = list(range(-K, K + 1))
        uu = [mp.mpf(float(x)) for x in u]
        uo = [(uu[i] - uu[2 * K - i]) / 2 for i in range(2 * K + 1)]
        m1 = sum(n[i] * uo[i] for i in range(2 * K + 1))
        s2 = sum(k * k for k in n)
        uo = [uo[i] - m1 / s2 * n[i] for i in range(2 * K + 1)]
        W = mp.mpf(w)
        a = 2 * mp.pi * W
        sins = [mp.sin(k * a) for k in n]
        total = mp.mpf(0)
        for i, ni in enumerate(n):
            for j, nj in enumerate(n):
                if i == j:
                    sv = 2 * W * mp.cos(2 * mp.pi * ni * W)
                else:
                    sv = (sins[i] - sins[j]) / ((ni - nj) * mp.pi)
                total += uo[i] * sv * uo[j]
        return total


def energy_deriv_float(n: np.ndarray, u: np.ndarray, w: np.ndarray) -> np.ndarray:
    """d/d omega of the elementary source energy."""
    a = 2 * math.pi * w[:, None] * n[None, :]
    cv = np.cos(a)
    out = np.zeros_like(w)
    for i in range(len(n)):
        for j in range(len(n)):
            if i == j:
                s = 2 * np.cos(a[:, i]) - 4 * math.pi * n[i] * w * np.sin(a[:, i])
            else:
                s = 2 * (n[i] * cv[:, i] - n[j] * cv[:, j]) / (n[i] - n[j])
            out += u[i] * s * u[j]
    return out


def mangoldt(k: int) -> float:
    """Lambda(k): log p if k = p^a (a >= 1), else 0."""
    for p in range(2, math.isqrt(k) + 1):
        if k % p == 0:
            while k % p == 0:
                k //= p
            return math.log(p) if k == 1 else 0.0
    return math.log(k) if k >= 2 else 0.0


@lru_cache(maxsize=None)
def S_sum(N: int) -> float:
    """S(N) = sum_{n <= N} Lambda(n)/sqrt(n) for an integer N >= 0."""
    return S_sum(N - 1) + mangoldt(N) / math.sqrt(N) if N >= 2 else 0.0


def row(K: int, L: float, n, E, O) -> dict:
    S = canonical_source_matrix_L(L, K)
    A = E.T @ S @ E
    B = O.T @ S @ O
    D = O.T @ np.diag(n) @ E
    g = O.T @ (n ** 3)
    hfun = (B @ D - D @ A).T @ g / (g @ g)
    ea, va = np.linalg.eigh(A)
    delta = float(np.linalg.eigvalsh(B)[0] - ea[0])
    v = va[:, 0]
    z = E @ v
    u = n * z
    Hv = float(hfun @ v)
    out = {"K": K, "L": L, "delta": delta, "H_v": Hv}

    def e(w):
        return energy_float(n, u, np.asarray(w, dtype=float))

    def h(t):
        return t ** 2 * e(1 - t / L)

    def hp(t):
        return 2 * t * e(1 - t / L) - t ** 2 / L * energy_deriv_float(n, u, 1 - t / L)

    def rho(t):
        return np.exp(t / 2) / (np.exp(t) - np.exp(-t))

    # Step 68
    AK = math.sqrt(2 * sum(k ** 10 for k in range(1, K + 1)))
    X = 2 * AK * abs(Hv)
    if delta > 0:
        theta = min(0.5, 5 * delta / (4 * math.pi ** 2 * (X + 1)))
        out["theta"] = theta
        # below theta ~ 1e-6 the O(omega^7) energy is under the 50-digit floor
        out["theta_resolved"] = theta >= 1e-6
        out["neg_on_angle"] = all(energy_mp_legal(K, u, theta * f) < 0 for f in (0.01, 0.1, 0.5, 1.0)) \
            if out["theta_resolved"] else None
        out["e_one_ok"] = bool(abs(e([1.0])[0] - 2 * float(u @ u)) <= 1e-9 * max(1.0, float(u @ u)))
        # e(theta) < 0 (above, at 50 digits) and e(1) > 0 force a zero in (theta, 1)
        out["zero_in_theta_one"] = bool(out["neg_on_angle"] and e([1.0])[0] > 0) \
            if out["theta_resolved"] else None
    # Steps 70-71: break [0, L] at log n
    qs = list(range(2, int(math.floor(math.exp(L))) + 1))
    cuts = [0.0] + [math.log(q) for q in qs] + [L]
    IR = 0.0
    for a, b in zip(cuts[:-1], cuts[1:]):
        if b - a <= 0:
            continue
        Sval = S_sum(int(math.floor(math.exp(0.5 * (a + b)))))
        IR += quad(lambda t: (Sval - 2 * np.exp(t / 2)) * hp(t), a, b)
    x2, w2 = gauss_legendre(400)
    t2 = 0.5 * L * (x2 + 1)
    Ikappa = float(0.5 * L * np.dot(w2, (np.exp(-t2 / 2) - rho(t2)) * h(t2)))
    W = np.exp(-t2 / 2) + np.exp(t2 / 2)
    P = float(0.5 * L * np.dot(w2, (W - rho(t2)) * h(t2)))
    prime = sum(mangoldt(q) * math.log(q) ** 2 / math.sqrt(q) * e([1 - math.log(q) / L])[0]
                for q in prime_powers(math.exp(L)))
    Vh = sum(quad(lambda t: np.abs(hp(t)), a, b, 200)
             for a, b in zip(np.linspace(0, L, 41)[:-1], np.linspace(0, L, 41)[1:]))
    N = int(math.floor(math.exp(L)))
    sups = [S_sum(k) - 2 * math.sqrt(k) for k in range(1, N + 1)]
    infs = [S_sum(k - 1) - 2 * math.sqrt(k) for k in range(2, N + 1)] + [S_sum(N) - 2 * math.exp(L / 2)]
    Omega = max(sups) - min(infs)
    bound = Omega / 2 * Vh
    lhs = P - prime
    rhs = IR + Ikappa
    out.update({"A_L": lhs, "int_R_hprime": IR, "int_kappa_h": Ikappa, "Omega": Omega,
                "V_h": Vh, "osc_bound": bound,
                "m09_rel": abs(lhs - rhs) / max(1.0, abs(P), abs(IR)),
                "osc_ok": bool(abs(IR) <= bound * (1 + 1e-9)),
                "r_R": abs(IR) / bound if bound > 0 else None,
                "r_0": abs(Ikappa) / bound if bound > 0 else None})
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=5)
    ap.add_argument("--lmin", type=float, default=1.0)
    ap.add_argument("--lmax", type=float, default=6.0)
    ap.add_argument("--dl", type=float, default=0.25)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rows = []
    for K in range(2, args.kmax + 1):
        n, E, O = carriers(K)
        L = args.lmin
        while L <= args.lmax + 1e-12:
            rows.append(row(K, round(L, 10), n, E, O))
            L += args.dl
    gap = [r for r in rows if r["delta"] > 0]
    summary = {
        "rows": len(rows),
        "rows_with_positive_gap": len(gap),
        "step68_rows_resolved": sum(1 for r in gap if r["theta_resolved"]),
        "step68_failures": sum(1 for r in gap if r["theta_resolved"] and not (
            r["neg_on_angle"] and r["e_one_ok"] and r["zero_in_theta_one"])),
        "e_one_failures": sum(1 for r in gap if not r["e_one_ok"]),
        "max_m09_rel": max(r["m09_rel"] for r in rows),
        "osc_failures": sum(1 for r in rows if not r["osc_ok"]),
        "max_r_R": max(r["r_R"] for r in rows if r["r_R"] is not None),
        "max_r_0": max(r["r_0"] for r in rows if r["r_0"] is not None),
        "theta_by_K": {K: [min(r["theta"] for r in gap if r["K"] == K),
                           max(r["theta"] for r in gap if r["K"] == K)]
                       for K in sorted({r["K"] for r in gap})},
    }
    passed = (summary["step68_failures"] == 0 and summary["e_one_failures"] == 0
              and summary["osc_failures"] == 0
              and summary["max_m09_rel"] <= TOL)
    report = {"terminal_claim": "RH_OPEN", "authority": "REGRESSION_AND_EXPERIMENTAL_SIGNAL",
              "package": "M33_M34_REMAINDER_OSCILLATION",
              "verdict": "PASS" if passed else "FAIL", "summary": summary, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
