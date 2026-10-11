"""POST285 M74 regression and falsifier for the canonical secular resolvent ray.

Checks, in floating point, the linear-algebra identities that
`Zeta23/CCM/CanonicalSecularResolvent.lean` proves exactly:

  B D - D A = g H,   r = B^-1 g,   x = D^-1 r,   gamma = <g, r>,   T = H(x)

* A x = (1 - T) D^-1 g;  det A = det B (1 - T);
* gamma real and > 0 when B > 0;
* Ward identity  gamma H(v) = <g, D v> - <r, D A v>  for arbitrary complex v
  (inner product conjugate-linear in the first slot, as in Mathlib);
* at contact (T = 1): ker A = span{x} and Re(conj(H z) <g, D z>) = gamma |H z|^2;
* approximate bound |gamma H(v) - <g, D v>| <= |r| |D A v|.

Negative controls (must FAIL, otherwise the test is vacuous):
* a bilinear (unconjugated) pairing breaks the Ward identity on non-real v;
* replacing D^-1 by D^* (assuming D unitary) breaks the ray identity;
* the PR #285 2x2 cubic crossing: every identity holds, yet A(s) has a negative
  eigenvalue for s > 0 -- the secular algebra alone cannot exclude a crossing.

This is regression evidence for the algebra only. It says nothing about the sign
of the physical arithmetic functional, contact existence, or RH.
"""
from __future__ import annotations

import argparse
import json

import numpy as np

TOL = 1e-8


def inner(a: np.ndarray, b: np.ndarray) -> complex:
    """Mathlib convention: conjugate-linear in the first argument."""
    return complex(np.vdot(a, b))


def random_instance(rng: np.random.Generator, n: int):
    M = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    B = M.conj().T @ M + 0.5 * np.eye(n)  # Hermitian positive definite
    D = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))  # not unitary
    D += 3 * np.eye(n)
    g = rng.normal(size=n) + 1j * rng.normal(size=n)
    h = rng.normal(size=n) + 1j * rng.normal(size=n)  # H(v) = h . v (linear)
    A = np.linalg.solve(D, B @ D - np.outer(g, h))
    return A, B, D, g, h


def check_instance(A, B, D, g, h, rng):
    n = len(g)
    r = np.linalg.solve(B, g)
    x = np.linalg.solve(D, r)
    gamma = inner(g, r)
    T = complex(h @ x)
    out = {}
    out["rank_one"] = float(np.abs(B @ D - D @ A - np.outer(g, h)).max())
    out["ray"] = float(np.abs(A @ x - (1 - T) * np.linalg.solve(D, g)).max())
    out["det"] = abs(np.linalg.det(A) - np.linalg.det(B) * (1 - T)) / max(1.0, abs(np.linalg.det(B)))
    out["gamma_imag"] = abs(gamma.imag)
    out["gamma_pos"] = gamma.real > 0
    out["gauge"] = abs(inner(g, D @ x) - gamma)
    ward = 0.0
    approx_ok = True
    for _ in range(20):
        v = rng.normal(size=n) + 1j * rng.normal(size=n)
        lhs = gamma * (h @ v)
        rhs = inner(g, D @ v) - inner(r, D @ (A @ v))
        ward = max(ward, abs(lhs - rhs))
        err = abs(gamma * (h @ v) - inner(g, D @ v))
        approx_ok &= err <= np.linalg.norm(r) * np.linalg.norm(D @ (A @ v)) + TOL
    out["ward"] = ward
    out["approx_ok"] = bool(approx_ok)
    return out, r, x, gamma, T


def run_random(rng, trials, nmax):
    worst = {}
    for _ in range(trials):
        n = int(rng.integers(2, nmax + 1))
        A, B, D, g, h = random_instance(rng, n)
        out, *_ = check_instance(A, B, D, g, h, rng)
        for k, val in out.items():
            if isinstance(val, bool):
                worst[k] = worst.get(k, True) and val
            else:
                worst[k] = max(worst.get(k, 0.0), val)
    ok = all(
        (v if isinstance(v, bool) else v < 1e-6) for v in worst.values()
    )
    return {"package": "M74_RANDOM_OFF_CONTACT", "worst": worst,
            "disposition": "EXACT_IDENTITY_REGRESSION_PASS" if ok else "FAIL"}


def run_contact(rng, trials, nmax):
    worst_phase = 0.0
    kernel_dims = set()
    for _ in range(trials):
        n = int(rng.integers(2, nmax + 1))
        _, B, D, g, h = random_instance(rng, n)
        r = np.linalg.solve(B, g)
        x = np.linalg.solve(D, r)
        h = h / complex(h @ x)  # force T = H(x) = 1 (contact)
        A = np.linalg.solve(D, B @ D - np.outer(g, h))
        sv = np.linalg.svd(A, compute_uv=False)
        kernel_dims.add(int((sv < 1e-9 * sv.max()).sum()))
        gamma = inner(g, r).real
        c = rng.normal() + 1j * rng.normal()
        z = c * x  # complex phase on the kernel line
        Hz = complex(h @ z)
        lhs = (np.conj(Hz) * inner(g, D @ z)).real
        worst_phase = max(worst_phase, abs(lhs - gamma * abs(Hz) ** 2))
        assert lhs > 0
    ok = worst_phase < 1e-8 and kernel_dims == {1}
    return {"package": "M74_CONTACT_PHASE", "worst_phase": worst_phase,
            "kernel_dims": sorted(kernel_dims),
            "disposition": "EXACT_IDENTITY_REGRESSION_PASS" if ok else "FAIL"}


def run_negative_controls(rng):
    A, B, D, g, h = random_instance(rng, 4)
    r = np.linalg.solve(B, g)
    x = np.linalg.solve(D, r)
    gamma = inner(g, r)
    v = rng.normal(size=4) + 1j * rng.normal(size=4)
    bilinear = gamma * (h @ v) - (g @ (D @ v) - r @ (D @ (A @ v)))
    T = complex(h @ x)
    x_unitary = D.conj().T @ r
    unitary_err = np.abs(A @ x_unitary - (1 - complex(h @ x_unitary)) * D.conj().T @ g).max()
    bilinear_fails = abs(bilinear) > 1e-3
    unitary_fails = unitary_err > 1e-3
    return {"package": "M74_CONVENTION_CONTROLS",
            "bilinear_ward_residual": abs(bilinear),
            "unitary_D_ray_residual": float(unitary_err),
            "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED"
            if bilinear_fails and unitary_fails else "FAIL"}


def run_crossing():
    D = np.array([[4.0, 3.0], [3.0, 2.0]])
    g = np.array([1.0, 1.0])
    rows = []
    for s in [0.0, 0.05, 0.1, 0.2]:
        A = np.diag([-s ** 3, 1.0])
        B = np.array([[3.0, -2 * s ** 3], [-2 * s ** 3, 4 + s ** 3]])
        h = np.array([12 - 2 * s ** 3, 6 - 4 * s ** 3])
        rng = np.random.default_rng(7)
        out, r, x, gamma, T = check_instance(A, B, D, g, h, rng)
        rows.append({"s": s, "T": T.real, "gamma": gamma.real,
                     "min_even_eig": float(np.linalg.eigvalsh(A).min()),
                     "B_pos": bool(np.linalg.eigvalsh(B).min() > 0),
                     "ward": out["ward"], "ray": out["ray"], "det": out["det"]})
    ok = all(r_["ward"] < 1e-9 and r_["ray"] < 1e-9 and r_["det"] < 1e-9 for r_ in rows)
    crossing = rows[0]["min_even_eig"] >= 0 and all(r_["min_even_eig"] < 0 for r_ in rows[1:])
    return {"package": "M30_CROSSING_UNDER_M74", "rows": rows,
            "disposition": "COUNTERMODEL_SURVIVES_M74_IDENTITIES" if ok and crossing else "FAIL"}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=200)
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--seed", type=int, default=20261010)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    results = [run_random(rng, args.trials, args.nmax),
               run_contact(rng, args.trials, args.nmax),
               run_negative_controls(rng),
               run_crossing()]
    report = {"terminal_claim": "RH_OPEN", "authority": "REGRESSION_EVIDENCE_ONLY",
              "results": results}
    text = json.dumps(report, indent=2, default=float)
    if args.output:
        with open(args.output, "w") as f:
            f.write(text)
    print(text)
    bad = [r["package"] for r in results if r["disposition"] == "FAIL"]
    if bad:
        raise SystemExit(f"M74 falsifier failures: {bad}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
