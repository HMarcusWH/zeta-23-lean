"""POST285 M59/M61 regression: source-moment kernel and the exact older-prime balance.

Checks the statements of `Zeta23/CCM/CanonicalContactSourceOlderPrimeBalance.lean`
and the merged kernel representation they rest on, on the float canonical
matrices (canonical_source_numeric.py) for K = 2..5 and L = 0.25, 0.5, ..., 6.

For each (K, L) and three legal even vectors v (the even ground state and two
complex random vectors), with z the raw coefficients, N the centered quadratic
normal, h_v(omega) = (S(omega) z . N)/(N . N) the mixed atom on the elementary
source matrix S(omega), beta_q = Lambda(q)/sqrt(q) and omega_q = 1 - log q/L:

  (98A)  H(v) = int_0^L h_v(1 - t/L)(e^{-t/2} + e^{t/2} - rho(t)) dt
                - sum_q beta_q h_v(omega_q),
         with H(v) read off the rank-one relation B D - D A = g H;
  Ward   gamma H(v) = M_4(v) - <B^{-1} g, D A v>,  gamma = <g, B^{-1} g>
         (checked where lambda_odd >= 1e-6; below that the float odd block is
         the small net of large pole/prime channels and B^{-1} g is not resolved);
  (98B)  I - sum_q beta_q p_v(omega_q) = Re(conj(M) H(v))
                                       = |M|^2/gamma - Re(conj(M) <B^{-1} g, D A v>)/gamma,
         p_v = Re(conj(M) h_v), M = M_4(v): at a contact (A v = 0) the right
         side is the proved |M|^2/gamma;
  (99B)  I - O + N = Re(conj(M) H(v)) for theta in {0.05, 0.2, 0.5};
  gap    gamma <= |g|^2 / lambda_odd.

Negative controls (each must FAIL (98A) by more than the tolerance):
  C1  the M50 weights Lambda(q)(log q)^2/sqrt(q) in place of beta_q (rows with
      L >= 1, where a prime is sampled away from the seam);
  C2  the archimedean integral dropped;
  C3  the energy e_{Dz} in place of the mixed atom h_z (on the ground state).

Regression evidence only.  No vector here is a contact, and nothing is excluded.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from functools import lru_cache
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

from canonical_source_numeric import canonical_source_matrix_L  # noqa: E402
from post285_m49_near_edge_probe import prime_powers  # noqa: E402
from post285_m50_older_prime_budget_probe import energy_float, von_mangoldt  # noqa: E402
from post285_m76_secular_margin import carriers  # noqa: E402

THETAS = (0.05, 0.2, 0.5)
TOL = 1e-8
WARD_FLOOR = 1e-6


def atoms(n: np.ndarray, z: np.ndarray, N: np.ndarray, w: np.ndarray) -> np.ndarray:
    """Mixed atom h(w) = (S(w) z . N)/(N . N) on the elementary source matrix,
    vectorized over w: S_ij = (sin 2 pi n_i w - sin 2 pi n_j w)/(pi (n_i - n_j)),
    S_ii = 2 w cos(2 pi n_i w)."""
    d = n[:, None] - n[None, :]
    C = np.zeros_like(d)
    off = d != 0
    C[off] = 1 / (math.pi * d[off])
    a = 2 * math.pi * w[:, None] * n[None, :]
    sv = np.sin(a)
    Sz = sv * (C @ z)[None, :] - (sv * z[None, :]) @ C.T + 2 * w[:, None] * np.cos(a) * z[None, :]
    return Sz @ N / (N @ N)


@lru_cache(maxsize=None)
def gauss_legendre(nodes: int = 400):
    return np.polynomial.legendre.leggauss(nodes)


def kernel_parts(n, z, N, L: float, nodes: int = 400):
    x, wts = gauss_legendre(nodes)
    t = 0.5 * L * (x + 1)
    rho = np.exp(t / 2) / (np.exp(t) - np.exp(-t))
    W = np.exp(-t / 2) + np.exp(t / 2)
    h = atoms(n, z, N, 1 - t / L)
    pole = complex(0.5 * L * np.dot(wts, h * W))
    arch = complex(0.5 * L * np.dot(wts, h * rho))
    qs = prime_powers(math.exp(L))
    ws = np.array([1 - math.log(q) / L for q in qs])
    hs = atoms(n, z, N, ws) if qs else np.zeros(0, dtype=complex)
    samples = [(q, float(w), von_mangoldt(q) / math.sqrt(q), complex(h))
               for q, w, h in zip(qs, ws, hs)]
    return pole, arch, samples


def rel(a: complex, b: complex) -> float:
    return abs(a - b) / max(1.0, abs(a), abs(b))


def row(K: int, L: float, n, E, O, rng) -> dict:
    S = canonical_source_matrix_L(L, K)
    A = E.T @ S @ E
    B = O.T @ S @ O
    D = O.T @ np.diag(n) @ E
    g = O.T @ (n ** 3)
    R = B @ D - D @ A
    lam_odd = float(np.linalg.eigvalsh(B)[0])
    ea, va = np.linalg.eigh(A)
    r = np.linalg.solve(B, g)
    gamma = float(g @ r)
    N = n ** 2 - np.mean(n ** 2)
    vecs = [("ground", va[:, 0].astype(complex))]
    for k in range(2):
        u = rng.standard_normal(E.shape[1]) + 1j * rng.standard_normal(E.shape[1])
        vecs.append((f"random{k}", u / np.linalg.norm(u)))
    out = {"K": K, "L": L, "lambda_odd": lam_odd, "gamma": gamma,
           "gap_ok": bool(lam_odd <= 0 or gamma <= float(g @ g) / lam_odd * (1 + 1e-12)),
           "vectors": []}
    for tag, v in vecs:
        z = E @ v
        H = complex(g @ (R @ v) / (g @ g))
        M = complex((n ** 4) @ z)
        pole, arch, samples = kernel_parts(n, z, N, L)
        prime = sum(b * h for _, _, b, h in samples)
        H_ker = pole - arch - prime
        ward = rel(gamma * H, M - complex(r @ (D @ (A @ v))))
        I = (np.conj(M) * (pole - arch)).real
        p = [(w, b, (np.conj(M) * h).real) for _, w, b, h in samples]
        lhs98 = I - sum(b * pv for _, b, pv in p)
        rhs98 = (np.conj(M) * H).real
        rhs98b = abs(M) ** 2 / gamma - (np.conj(M) * complex(r @ (D @ (A @ v)))).real / gamma
        part = []
        for th in THETAS:
            Osum = sum(b * pv for w, b, pv in p if w > th)
            Nsum = sum(b * (-pv) for w, b, pv in p if w <= th)
            part.append(rel(I - Osum + Nsum, rhs98))
        # The float odd block is the small net of large pole/prime channels;
        # below lambda_odd = WARD_FLOOR it is not resolved and B^{-1} g is noise
        ward_resolved = lam_odd >= WARD_FLOOR
        rec = {"vector": tag, "kernel_98A": rel(H_ker, H), "ward": ward,
               "ward_resolved": ward_resolved, "ward_ok": bool(not ward_resolved or ward <= TOL),
               "pairing_98B": rel(lhs98, rhs98), "pairing_98B_ward_form": rel(rhs98, rhs98b),
               "partition_99B": max(part), "seam_terms_zero": all(
                   abs(h) < 1e-14 for _, w, _, h in samples if abs(w) < 1e-15)}
        if tag == "ground":
            m50 = sum(von_mangoldt(q) * math.log(q) ** 2 / math.sqrt(q) * h for q, _, _, h in samples)
            rec["C1_m50_weights"] = rel(pole - arch - m50, H)
            rec["C2_no_arch"] = rel(pole - prime, H)
            x, wts = gauss_legendre(400)
            t = 0.5 * L * (x + 1)
            rho = np.exp(t / 2) / (np.exp(t) - np.exp(-t))
            Wt = np.exp(-t / 2) + np.exp(t / 2)
            Dz = n * z.real
            e = energy_float(n, Dz, 1 - t / L)
            e_ker = 0.5 * L * np.dot(wts, e * (Wt - rho)) - sum(
                b * energy_float(n, Dz, np.array([w]))[0] for _, w, b, _ in samples)
            rec["C3_energy_for_atom"] = rel(complex(e_ker), H)
        out["vectors"].append(rec)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=5)
    ap.add_argument("--lmax", type=float, default=6.0)
    ap.add_argument("--dl", type=float, default=0.25)
    ap.add_argument("--seed", type=int, default=20261011)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    rows = []
    for K in range(2, args.kmax + 1):
        n, E, O = carriers(K)
        L = args.dl
        while L <= args.lmax + 1e-12:
            rows.append(row(K, round(L, 10), n, E, O, rng))
            L += args.dl
    recs = [rec for r in rows for rec in r["vectors"]]
    ground = [rec for rec in recs if rec["vector"] == "ground"]
    keys = ("kernel_98A", "pairing_98B", "pairing_98B_ward_form", "partition_99B")
    summary = {
        "rows": len(rows),
        "vectors_checked": len(recs),
        "max_rel_error": {k: max(rec[k] for rec in recs) for k in keys},
        "ward_failures": sum(1 for rec in recs if not rec["ward_ok"]),
        "ward_vectors_resolved": sum(1 for rec in recs if rec["ward_resolved"]),
        "max_ward_resolved": max((rec["ward"] for rec in recs if rec["ward_resolved"]), default=None),
        "gap_failures": sum(1 for r in rows if not r["gap_ok"]),
        "seam_term_failures": sum(1 for rec in recs if not rec["seam_terms_zero"]),
        # C1 only differs where primes are sampled away from the seam (L >= 1)
        "min_control_miss": {
            "C1_m50_weights": min(rec["C1_m50_weights"] for r in rows if r["L"] >= 1
                                  for rec in r["vectors"] if rec["vector"] == "ground"),
            "C2_no_arch": min(rec["C2_no_arch"] for rec in ground),
            "C3_energy_for_atom": min(rec["C3_energy_for_atom"] for rec in ground)},
    }
    identities_ok = all(v <= TOL for v in summary["max_rel_error"].values())
    controls_ok = all(v > 1e3 * TOL for v in summary["min_control_miss"].values())
    passed = identities_ok and controls_ok and not summary["gap_failures"] \
        and not summary["ward_failures"] \
        and not summary["seam_term_failures"]
    report = {"terminal_claim": "RH_OPEN", "authority": "REGRESSION_EVIDENCE_ONLY",
              "package": "M61_SOURCE_OLDER_PRIME_BALANCE",
              "verdict": "PASS" if passed else "FAIL",
              "tolerance": TOL, "summary": summary, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
