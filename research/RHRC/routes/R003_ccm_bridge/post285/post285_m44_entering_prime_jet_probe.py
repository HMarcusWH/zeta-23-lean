"""POST285 M44 probe: the entering-prime physical jet at a seam (Step 81).

Checks the statements of `Zeta23/CCM/CanonicalEnteringPrimePhysicalJet.lean` at
50 digits, for K = 2..5 and legal even vectors z (the even ground states of the
float canonical matrices at L = 1, 2, 3, 4, and two random legal even vectors per K),
at the seams q in {2, 3, 4, 5, 7, 8, 9, 11, 13}:

  jump     Delta Q_z(log q + h) = -beta_q e_{Dz}(h/(log q + h)),
           beta_q = Lambda(q)(log q)^2/sqrt(q), Dz projected onto the legal odd carrier;
  (81.1)   with a = 2 Lambda(q)(2 pi)^6 |M_4(z)|^2/(7! sqrt(q) (log q)^5),
           r(h) = Delta Q/(a h^7) -> 1 as h -> 0+ (|r - 1| <= 20 h/log q at h = 1e-4);
  h^8      d(h) = |Delta Q - a h^7|/h^8 is stable between h = 1e-3 and 1e-4 (bounded, as in
           the Lean statement); since e_u
           is odd in omega the h^8 term comes only from omega^7 = (h/L0)^7 (1 - 7h/L0 + ...),
           so d(h) L0/(7a) -> 1 (reported as EXPERIMENTAL SIGNAL);
  angle    where (2 pi omega_h)^2 B(Dz) <= 5 |M_4|, Delta Q >= (pi^6/90) beta_q |M_4|^2 omega_h^7,
           and Delta Q > 0 at every grid h inside the angle.

Negative controls (each must FAIL):
  C1  the even energy e_z in place of e_{Dz} (the Step 56 ninth-order seam term):
      -beta_q e_z(omega_h) < 0 at h = 1e-2, the opposite sign;
  C2  (log q)^7 in place of (log q)^5 in a (the (log q)^2 weight dropped):
      r(1e-4) misses 1 by at least 0.1.

Fixed-vector regression only: nothing here is a contact, and no total Q sign follows.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

from canonical_source_numeric import canonical_source_matrix_L  # noqa: E402
from post285_m76_secular_margin import carriers  # noqa: E402

SEAMS = (2, 3, 4, 5, 7, 8, 9, 11, 13)
HS = (1e-2, 1e-3, 1e-4)
DPS = 60


def mangoldt(k: int) -> float:
    """Lambda(k): log p if k = p^a (a >= 1), else 0."""
    for p in range(2, math.isqrt(k) + 1):
        if k % p == 0:
            while k % p == 0:
                k //= p
            return math.log(p) if k == 1 else 0.0
    return math.log(k) if k >= 2 else 0.0


def project(K: int, x, parity: str):
    """Project a real vector (mp) onto the legal carrier: odd with M_1 = 0, or
    even with M_0 = M_2 = 0, in DPS-digit arithmetic."""
    n = [mp.mpf(k) for k in range(-K, K + 1)]
    s = -1 if parity == "odd" else 1
    y = [(x[i] + s * x[2 * K - i]) / 2 for i in range(2 * K + 1)]
    if parity == "odd":
        m1 = sum(n[i] * y[i] for i in range(2 * K + 1))
        s2 = sum(k * k for k in n)
        return [y[i] - m1 / s2 * n[i] for i in range(2 * K + 1)]
    basis = [[mp.mpf(1)] * (2 * K + 1), [k * k for k in n]]
    G = mp.matrix(2, 2)
    rhs = mp.matrix(2, 1)
    for a in range(2):
        rhs[a] = sum(basis[a][i] * y[i] for i in range(2 * K + 1))
        for b in range(2):
            G[a, b] = sum(basis[a][i] * basis[b][i] for i in range(2 * K + 1))
    c = mp.lu_solve(G, rhs)
    return [y[i] - c[0] * basis[0][i] - c[1] * basis[1][i] for i in range(2 * K + 1)]


def energy(K: int, u, w) -> mp.mpf:
    """Elementary source energy e_u(w) = u^T S(w) u for a real vector u."""
    n = list(range(-K, K + 1))
    W = mp.mpf(w)
    a = 2 * mp.pi * W
    sins = [mp.sin(k * a) for k in n]
    total = mp.mpf(0)
    for i, ni in enumerate(n):
        for j, nj in enumerate(n):
            sv = 2 * W * mp.cos(ni * a) if i == j else (sins[i] - sins[j]) / ((ni - nj) * mp.pi)
            total += u[i] * sv * u[j]
    return total


def vectors(K: int, n, E, O, rng):
    out = []
    for L in (1.0, 2.0, 3.0, 4.0):
        S = canonical_source_matrix_L(L, K)
        _, va = np.linalg.eigh(E.T @ S @ E)
        out.append((f"ground_L{L:g}", E @ va[:, 0]))
    for k in range(2):
        v = rng.standard_normal(E.shape[1])
        out.append((f"random{k}", E @ (v / np.linalg.norm(v))))
    return out


def check(K: int, tag: str, zf: np.ndarray) -> list[dict]:
    rows = []
    with mp.workdps(DPS):
        nn = [mp.mpf(k) for k in range(-K, K + 1)]
        z = project(K, [mp.mpf(float(t)) for t in zf], "even")
        u = project(K, [nn[i] * z[i] for i in range(2 * K + 1)], "odd")
        M4 = sum(nn[i] ** 4 * z[i] for i in range(2 * K + 1))
        M3u = sum(nn[i] ** 3 * u[i] for i in range(2 * K + 1))
        B = sum(abs(nn[i]) ** 5 * abs(u[i]) for i in range(2 * K + 1))
        for q in SEAMS:
            lam = mp.mpf(mangoldt(q))
            L0 = mp.log(q)
            beta = lam * L0 ** 2 / mp.sqrt(q)
            a = 2 * lam * (2 * mp.pi) ** 6 * M4 ** 2 / (mp.factorial(7) * mp.sqrt(q) * L0 ** 5)
            rec = {"K": K, "vector": tag, "q": q, "M4": float(M4),
                   "M3_Dz_minus_M4": float(abs(M3u - M4) / max(1, abs(M4))), "a": float(a)}
            r, d = {}, {}
            for h in HS:
                H = mp.mpf(h)
                w = H / (L0 + H)
                dQ = -beta * energy(K, u, w)
                r[h] = dQ / (a * H ** 7)
                d[h] = abs(dQ - a * H ** 7) / H ** 8
            rec["ratio"] = {str(h): float(r[h]) for h in HS}
            rec["ratio_ok"] = bool(abs(r[1e-4] - 1) <= 20 * 1e-4 / L0)
            # asymptotic regime: d(1e-3) and d(1e-4) agree within a factor 2 (at h = 1e-2 the
            # omega^9 term can still be comparable when |M_4| is small)
            rec["h8_bounded"] = bool(max(d[1e-3], d[1e-4]) <= 2 * min(d[1e-3], d[1e-4]))
            rec["h8_by_h"] = {str(h): float(d[h]) for h in HS}
            rec["h8_signal"] = float(d[1e-4] * L0 / (7 * a))
            # angle bound and positivity on a grid up to the angle edge
            angle_hits, angle_fail, pos_fail = 0, 0, 0
            for k in range(1, 41):
                H = mp.mpf(k) / 40
                w = H / (L0 + H)
                if (2 * mp.pi * w) ** 2 * B > 5 * abs(M4):
                    break
                angle_hits += 1
                dQ = -beta * energy(K, u, w)
                if dQ < mp.pi ** 6 / 90 * beta * M4 ** 2 * w ** 7 * (1 - mp.mpf(10) ** -20):
                    angle_fail += 1
                if not dQ > 0:
                    pos_fail += 1
            rec.update({"angle_grid_points": angle_hits, "angle_failures": angle_fail,
                        "positivity_failures": pos_fail})
            # controls
            H = mp.mpf("1e-2")
            w = H / (L0 + H)
            rec["C1_even_energy_jump"] = float(-beta * energy(K, z, w))
            rec["C2_ratio_miss"] = float(abs(r[1e-4] * L0 ** 2 - 1))
            rows.append(rec)
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=5)
    ap.add_argument("--seed", type=int, default=20261011)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    rows = []
    for K in range(2, args.kmax + 1):
        n, E, O = carriers(K)
        for tag, zf in vectors(K, n, E, O, rng):
            rows.extend(check(K, tag, zf))
    summary = {
        "rows": len(rows),
        "max_M3_Dz_minus_M4": max(r["M3_Dz_minus_M4"] for r in rows),
        "ratio_failures": sum(1 for r in rows if not r["ratio_ok"]),
        "max_ratio_error_1e-4": max(abs(r["ratio"]["0.0001"] - 1) for r in rows),
        "h8_unbounded": sum(1 for r in rows if not r["h8_bounded"]),
        "h8_signal_range": [min(r["h8_signal"] for r in rows), max(r["h8_signal"] for r in rows)],
        "angle_grid_points": sum(r["angle_grid_points"] for r in rows),
        "angle_failures": sum(r["angle_failures"] for r in rows),
        "positivity_failures": sum(r["positivity_failures"] for r in rows),
        "C1_rows_with_negative_even_jump": sum(1 for r in rows if r["C1_even_energy_jump"] < 0),
        "C2_min_ratio_miss": min(r["C2_ratio_miss"] for r in rows),
    }
    controls_ok = (summary["C1_rows_with_negative_even_jump"] == len(rows)
                   and summary["C2_min_ratio_miss"] >= 0.1)
    passed = (summary["ratio_failures"] == 0 and summary["h8_unbounded"] == 0
              and summary["angle_failures"] == 0 and summary["positivity_failures"] == 0
              and summary["max_M3_Dz_minus_M4"] <= 1e-40 and controls_ok)
    report = {"terminal_claim": "RH_OPEN", "authority": "REGRESSION_AND_EXPERIMENTAL_SIGNAL",
              "package": "M44_ENTERING_PRIME_PHYSICAL_JET",
              "verdict": "PASS" if passed else "FAIL", "summary": summary, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
