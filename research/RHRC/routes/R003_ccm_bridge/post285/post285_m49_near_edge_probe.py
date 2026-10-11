"""POST285 M49 research probe: is the near-edge contact angle theta_* populated?

On the production canonical source matrix (canonical_source_numeric.py, float
discovery data) this probe takes, for each (K, L), the actual even ground
eigenvector v of A_L on the legal even carrier (normalized), the parity gap
delta = lambda_min(B_L) - lambda_min(A_L), and the source functional H_L read off
from the rank-one relation B_L D - D A_L = g H_L (as in the M76 probe).  It then
evaluates the quantities of `CanonicalRecentPrimeSecondVariation.lean`:

    theta_*(c) = (1/2pi) sqrt(5 delta / (A_K |H(v)| sqrt c)),  c = 4 (M73) or C_K (M46),
    A_K = (2 sum_{n<=K} n^10)^{1/2},

and every prime-power sample q <= e^L with omega_q = 1 - log q / L in (0, theta_*].
At each such sample it checks the proved chain

    -e_{Dz}(omega_q) >= (pi^6/90) |M_4|^2 omega_q^7 >= (pi^6/90) (delta/(c|H(v)|))^2 omega_q^7

on the elementary source matrix, and the parity-gap inequality
delta |Dz|^2 <= H(v) M_4(z) that feeds it.

The research question (plan, M51 experiment 3) is whether the growing Taylor
constant A_K makes theta_* too small to contain any prime sample; an empty
near-edge set gives no arithmetic information.

EXPERIMENTAL SIGNAL ONLY: float matrices, not contacts (v is the even ground
state at every sampled L, not a zero eigenvector).  Counts describe this grid
only.
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


def prime_powers(limit: float) -> list[int]:
    out = []
    for q in range(2, int(math.floor(limit)) + 1):
        p = q
        for d in range(2, int(math.isqrt(q)) + 1):
            if q % d == 0:
                p = d
                break
        r = q
        while r % p == 0:
            r //= p
        if r == 1:
            out.append(q)
    return out


def elementary_energy(K: int, u: np.ndarray, w: float) -> float:
    """Elementary source energy of the (float) vector u at 50 digits: near-edge
    energies are O(w^7) and cancel below float64 resolution."""
    with mp.workdps(50):
        n = list(range(-K, K + 1))
        W = mp.mpf(w)
        a = 2 * mp.pi * W
        uu = [mp.mpf(float(x)) for x in u]
        sins = [mp.sin(k * a) for k in n]
        total = mp.mpf(0)
        for i, ni in enumerate(n):
            for j, nj in enumerate(n):
                if i == j:
                    s = 2 * W * mp.cos(2 * mp.pi * ni * W)
                else:
                    s = (sins[i] - sins[j]) / ((ni - nj) * mp.pi)
                total += uu[i] * s * uu[j]
        return float(total)


def coercivity_C(K: int) -> float:
    return 1 + 2 * sum(1 / k ** 2 for k in range(1, K + 1))


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
    M4 = float(n ** 4 @ z)
    H = float(h @ v)
    out = {"K": K, "L": L, "lambda_even": lam_a, "lambda_odd": lam_b, "delta": delta,
           "H_v": H, "M4": M4}
    if delta <= 0:
        out["skipped"] = "nonpositive parity gap"
        return out
    out["parity_gap_slack"] = H * M4 - delta * float(Dz @ Dz)
    AK = math.sqrt(2 * sum(k ** 10 for k in range(1, K + 1)))
    q_all = prime_powers(math.exp(L))
    omegas = sorted(1 - math.log(q) / L for q in q_all if 1 - math.log(q) / L > 0)
    for tag, c in (("four", 4.0), ("C_K", coercivity_C(K))):
        theta = math.sqrt(5 * delta / (AK * abs(H) * math.sqrt(c))) / (2 * math.pi)
        near = [w for w in omegas if w <= theta]
        checks = []
        for w in near:
            e = elementary_energy(K, Dz, w)
            b1 = math.pi ** 6 / 90 * M4 ** 2 * w ** 7
            b2 = math.pi ** 6 / 90 * (delta / (c * abs(H))) ** 2 * w ** 7
            checks.append({"omega": w, "minus_e": -e, "bound_M4": b1, "bound_delta": b2,
                           "ok": bool(-e >= b1 * (1 - 1e-9) and b1 >= b2 * (1 - 1e-9))})
        out[f"theta_{tag}"] = theta
        out[f"near_samples_{tag}"] = len(near)
        out[f"near_checks_{tag}"] = checks
    out["smallest_positive_omega"] = omegas[0] if omegas else None
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
    checks = [c for r in live for t in ("four", "C_K") for c in r[f"near_checks_{t}"]]
    summary = {
        "rows": len(rows),
        "rows_with_positive_gap": len(live),
        "min_parity_gap_slack": min(r["parity_gap_slack"] for r in live) if live else None,
        "rows_with_near_sample_four": sum(1 for r in live if r["near_samples_four"] > 0),
        "rows_with_near_sample_C_K": sum(1 for r in live if r["near_samples_C_K"] > 0),
        "near_sample_checks": len(checks),
        "near_sample_checks_failed": sum(1 for c in checks if not c["ok"]),
        "max_theta_four": max((r["theta_four"] for r in live), default=None),
        "max_theta_C_K": max((r["theta_C_K"] for r in live), default=None),
        "theta_four_by_K": {K: [min(r["theta_four"] for r in live if r["K"] == K),
                                max(r["theta_four"] for r in live if r["K"] == K)]
                            for K in sorted({r["K"] for r in live})},
        "skipped": [(r["K"], r["L"]) for r in rows if "skipped" in r],
    }
    disposition = "EXPERIMENTAL_SIGNAL"
    if summary["near_sample_checks_failed"] or (summary["min_parity_gap_slack"] is not None
                                                and summary["min_parity_gap_slack"] < -1e-8):
        disposition = "FAIL_PROVED_CHAIN"
    report = {"terminal_claim": "RH_OPEN", "authority": "EXPERIMENTAL_SIGNAL_ONLY",
              "package": "M49_NEAR_EDGE_PRIME_BENEFIT", "disposition": disposition,
              "summary": summary, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
    return 0 if disposition == "EXPERIMENTAL_SIGNAL" else 1


if __name__ == "__main__":
    raise SystemExit(main())
