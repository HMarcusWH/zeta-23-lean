"""POST285 M63 probe: the two contact identities at the K = 2 near-contacts (Step 100).

M63 compares the F04 curvature route with the F04-free source-moment route on the
same state and normalization.  For K = 2 the legal even carrier is spanned by
z = (1, -4, 6, -4, 1), the even compressed operator is the scalar
lambda(L) = <z, S_L z>/<z, z>, and lambda has four near-contacts on [1/400, log 16]
(post285_m51_k2_even_bottom_certificate.py: certified positive, local minima about
1.4e-6, 4.5e-9, 8.8e-9 and 3.2e-10).  At each near-contact, with v = z/|z|:

  Route A (F04 curvature, M65/M66/M50).  At a stationary generated contact the
  physical second test V = P - sum_q Lambda(q)(log q)^2/sqrt(q) e_{Dz}(omega_q)
  equals -kappa C, and C = 0 for K = 2 (the stationary response is zero).  By the
  F04 identity V = -(L^4/(4 pi^2))(lambda'' + 2 lambda'/L), checked here with
  Arb jets of lambda.  Reported: V, and V relative to the pole/archimedean part P
  (the size of the terms that cancel).

  Route B (source moment, M74/M59/M61).  At any even contact (no stationarity)
  I - sum_q (Lambda(q)/sqrt(q)) p_v(omega_q) = |M|^2/gamma with M = M_4(v),
  gamma = <g, B^{-1} g>.  Away from a contact the left side equals
  |M|^2/gamma - Re(conj(M) <B^{-1} g, D A v>)/gamma (the Ward form checked by the
  M61 probe).  Reported: the left side from the kernel quadrature, |M|^2/gamma,
  their relative difference, and lambda/lambda_odd.

What the comparison shows (EXPERIMENTAL SIGNAL): both contact identities are
nearly satisfied at the near-contacts, and more nearly as they deepen.  Route B's
relative defect equals lambda/lambda_odd to three or more digits (0.027 down to
0.0054); route A's V/|P| is the curvature term and falls from 1.7e-2 to 1.4e-5.
An opposite-side inequality for either route ((98C)/(99C) for B, V > 0 at a
stationary contact for A) must therefore separate an exact contact from these
near-contacts, at which its own identity already holds to those margins.

Negative control (must FAIL): C1 route B with the M50 weights
Lambda(q)(log q)^2/sqrt(q) in place of Lambda(q)/sqrt(q) misses |M|^2/gamma by
more than 10 percent at every near-contact.

Float canonical matrices, K = 2 only, these four points only.  Nothing here is a
contact, and nothing is excluded.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import numpy as np
from flint import arb, ctx, fmpq

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

from canonical_source_numeric import canonical_source_matrix_L  # noqa: E402
from post285_m50_older_prime_budget_probe import pole_arch_value, von_mangoldt  # noqa: E402
from post285_m49_near_edge_probe import elementary_energy  # noqa: E402
from post285_m61_source_balance_falsifier import kernel_parts  # noqa: E402
from post285_m76_secular_margin import carriers  # noqa: E402
from post194_fb05_q14_fixed_unit_second_derivative import (  # noqa: E402
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets,
)

# refined minimizers of lambda from the M51 certificate (Arb, 128 bits)
NEAR_CONTACTS = (1.333902999431, 1.778426590794, 2.222959772751, 2.668246053124)


def lam_jets(L: float, z: np.ndarray) -> tuple[float, float, float]:
    """lambda, lambda', lambda'' from the Arb fixed-Q jets (128 bits)."""
    ctx.prec = 128
    La = arb(fmpq(round(L * 10 ** 12), 10 ** 12))
    M, Mp, Mpp = jets(La, 2, int(math.floor(math.exp(L))))
    q = lambda A: float(sum(z[i] * A[i, j] * z[j] for i in range(5) for j in range(5)).mid())
    return q(M), q(Mp), q(Mpp)


def row(L: float, n, E, O) -> dict:
    zr = np.array([1.0, -4.0, 6.0, -4.0, 1.0])
    z = zr / np.linalg.norm(zr)
    lam, lam1, lam2 = lam_jets(L, z)
    # route A
    Dz = n * z
    P = pole_arch_value(n, Dz, L, 1200)
    qs = [q for q in range(2, int(math.floor(math.exp(L))) + 1) if _is_prime_power(q)]
    F = -sum(von_mangoldt(q) * math.log(q) ** 2 / math.sqrt(q)
             * elementary_energy(2, Dz, 1 - math.log(q) / L) for q in qs)
    V = P + F
    V_f04 = -(L ** 4 / (4 * math.pi ** 2)) * (lam2 + 2 * lam1 / L)
    # route B
    S = canonical_source_matrix_L(L, 2)
    B = O.T @ S @ O
    g = O.T @ (n ** 3)
    r = np.linalg.solve(B, g)
    gamma = float(g @ r)
    lam_odd = float(np.linalg.eigvalsh(B)[0])
    N = n ** 2 - np.mean(n ** 2)
    M = float((n ** 4) @ z)
    pole, arch, samples = kernel_parts(n, z.astype(complex), N, L, 1200)
    I = (np.conj(M) * (pole - arch)).real
    lhs = I - sum(b * (np.conj(M) * hq).real for _, _, b, hq in samples)
    rhs = M * M / gamma
    lhs_m50 = I - sum(von_mangoldt(q) * math.log(q) ** 2 / math.sqrt(q) * (np.conj(M) * hq).real
                      for q, _, _, hq in samples)
    return {"L": L, "lambda": lam, "lambda1": lam1, "lambda2": lam2, "lambda_odd": lam_odd,
            "A_P": P, "A_V": V, "A_V_f04": V_f04, "A_V_over_P": V / abs(P),
            "B_lhs": lhs, "B_contact_rhs": rhs, "B_rel_defect": abs(lhs - rhs) / abs(rhs),
            "lambda_over_lambda_odd": lam / lam_odd,
            "C1_m50_weights_rel_miss": abs(lhs_m50 - rhs) / abs(rhs)}


def _is_prime_power(q: int) -> bool:
    p = next(d for d in range(2, q + 1) if q % d == 0)
    while q % p == 0:
        q //= p
    return q == 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    n, E, O = carriers(2)
    rows = [row(L, n, E, O) for L in NEAR_CONTACTS]
    summary = {
        "near_contacts": len(rows),
        "A_V_over_P": [r["A_V_over_P"] for r in rows],
        "A_f04_max_rel": max(abs(r["A_V"] - r["A_V_f04"]) / abs(r["A_V"]) for r in rows),
        "B_rel_defect": [r["B_rel_defect"] for r in rows],
        "lambda_over_lambda_odd": [r["lambda_over_lambda_odd"] for r in rows],
        "C1_min_rel_miss": min(r["C1_m50_weights_rel_miss"] for r in rows),
    }
    passed = (summary["A_f04_max_rel"] <= 1e-6 and summary["C1_min_rel_miss"] > 0.1
              and all(r["A_V"] < 0 and r["lambda2"] > 0 for r in rows))
    report = {"terminal_claim": "RH_OPEN", "authority": "EXPERIMENTAL_SIGNAL_ONLY",
              "package": "M63_ROUTE_COMPARISON", "verdict": "PASS" if passed else "FAIL",
              "summary": summary, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k not in ("rows", "cells")}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
