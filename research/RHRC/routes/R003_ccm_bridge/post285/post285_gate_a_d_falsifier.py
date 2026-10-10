"""POST285 Gate A/D regression and falsifier: M70 (Step 108), M73 (Step 115),
M75 (Steps 119-120).

Floating-point checks of statements proved in
`Zeta23/CCM/CanonicalSourceExcursion.lean`,
`Zeta23/CCM/CanonicalCenteredIndexPoincare.lean` and
`Zeta23/CCM/CanonicalSourcePrimeSampling.lean`, plus numerical signals for what
those files do NOT prove.

* M70: for nonzero zero-sum z, max e_{Dz} > |z|^2/pi^2 and min e_{Dz} < -|z|^2/pi^2.
* M73: sum n^2|z_n|^2 >= (1/4) sum |z_n|^2 on the zero-sum carrier; the telescoped
  mass sum_{0<|n|<=K} 1/(n^2-1/4) = 4 - 4/(2K+1).  SIGNAL (not proved): the
  optimal constant tends to 1/4 from above as K grows.
* M75: |dS_nm/domega| <= 2 + 4 pi K on [0,1]; the Step 119 window
  [w- - eta_K, w- + eta_K] has e <= -|z|^2/(2 pi^2) and sits inside (0,1).
  SIGNAL: how crude eta_K is (ratio of true negative-run width to 2 eta_K).

Negative controls (must FAIL):
* M70 without the zero-sum condition: e can stay nonnegative (z = e_0 basis
  vector, Dz = 0 gives e = 0, so no strict excursion).
* M73 with constant 1/4 + 0.01 fails for large K (the 1/4 is asymptotically sharp
  on the whole zero-sum carrier).

Regression evidence only; says nothing about the prime sum, contact, or RH.
"""
from __future__ import annotations

import argparse
import json
import math

import numpy as np


def source_matrix(omega: float, K: int) -> np.ndarray:
    n = np.arange(-K, K + 1, dtype=float)
    N, M = np.meshgrid(n, n, indexing="ij")
    with np.errstate(divide="ignore", invalid="ignore"):
        off = (np.sin(2 * np.pi * N * omega) - np.sin(2 * np.pi * M * omega)) / (np.pi * (N - M))
    diag = 2 * omega * np.cos(2 * np.pi * n * omega)
    S = np.where(N == M, 0.0, off)
    S[np.diag_indices_from(S)] = diag
    return S


def energy(z: np.ndarray, omega: float) -> float:
    K = (len(z) - 1) // 2
    u = np.arange(-K, K + 1) * z
    return float(np.real(np.vdot(u, source_matrix(omega, K) @ u)))


def random_zero_sum(rng, K):
    z = rng.normal(size=2 * K + 1) + 1j * rng.normal(size=2 * K + 1)
    return z - z.mean()


def m70(rng, trials, kmax, grid):
    ws = np.linspace(0, 1, grid)
    worst_lo, worst_hi = -np.inf, np.inf
    for _ in range(trials):
        K = int(rng.integers(1, kmax + 1))
        z = random_zero_sum(rng, K)
        c = float(np.sum(np.abs(z) ** 2))
        es = np.array([energy(z, w) for w in ws]) / c
        worst_lo = max(worst_lo, es.min() * np.pi ** 2)   # must be < -1
        worst_hi = min(worst_hi, es.max() * np.pi ** 2)   # must be > 1
    ok = worst_lo < -1 and worst_hi > 1
    # negative control: drop the zero-sum hypothesis
    K = 3
    z = np.zeros(2 * K + 1, complex)
    z[K] = 1.0
    ctrl = max(abs(energy(z, w)) for w in ws)
    return {"package": "M70_SOURCE_EXCURSION",
            "worst_min_times_pi2": worst_lo, "worst_max_times_pi2": worst_hi,
            "control_no_zero_sum_max_abs_e": ctrl,
            "disposition": "EXACT_THEOREM_REGRESSION_PASS" if ok and ctrl < 1e-12 else "FAIL"}


def poincare_constant(K: int) -> float:
    n = np.arange(-K, K + 1, dtype=float)
    D2 = np.diag(n ** 2)
    # orthonormal basis of the zero-sum hyperplane
    Q, _ = np.linalg.qr(np.vstack([np.ones(2 * K + 1), np.eye(2 * K + 1)[:-1]]).T)
    B = Q[:, 1:]
    return float(np.linalg.eigvalsh(B.T @ D2 @ B).min())


def m73(kmax):
    mass_err = 0.0
    for K in range(1, kmax + 1):
        mass = sum(1 / (n * n - 0.25) for n in range(-K, K + 1) if n != 0)
        mass_err = max(mass_err, abs(mass - (4 - 4 / (2 * K + 1))))
    consts = {K: poincare_constant(K) for K in (1, 2, 3, 5, 10, 20, 40, 80)}
    above = all(v > 0.25 for v in consts.values())
    decreasing = all(consts[a] >= consts[b] for a, b in zip(list(consts)[:-1], list(consts)[1:]))
    control_fails = consts[80] < 0.25 + 0.01
    ok = mass_err < 1e-12 and above and decreasing and control_fails
    return {"package": "M73_QUARTER_POINCARE",
            "telescoped_mass_max_error": mass_err,
            "optimal_constant_by_K": consts,
            "control_quarter_plus_0p01_fails_at_K80": control_fails,
            "sharpness_status": "NUMERICAL_SIGNAL_ONLY",
            "disposition": "EXACT_THEOREM_REGRESSION_PASS" if ok else "FAIL"}


def m75(rng, trials, kmax, grid):
    worst_deriv_ratio = 0.0
    window_ok = True
    width_ratios = []
    for _ in range(trials):
        K = int(rng.integers(1, kmax + 1))
        # entry derivative bound by central differences
        h = 1e-6
        for w in np.linspace(h, 1 - h, 25):
            dS = (source_matrix(w + h, K) - source_matrix(w - h, K)) / (2 * h)
            worst_deriv_ratio = max(worst_deriv_ratio, np.abs(dS).max() / (2 + 4 * np.pi * K))
        z = random_zero_sum(rng, K)
        c = float(np.sum(np.abs(z) ** 2))
        MK = (2 + 4 * np.pi * K) * (2 * K + 1) * K ** 2
        eta = 1 / (2 * np.pi ** 2 * MK)
        ws = np.linspace(0, 1, grid)
        es = np.array([energy(z, w) for w in ws])
        cand = ws[es < -c / np.pi ** 2]
        if len(cand) == 0:
            window_ok = False
            continue
        wm = float(cand[0])
        pts = np.linspace(wm - eta, wm + eta, 9)
        window_ok &= bool(pts.min() > 0 and pts.max() < 1)
        window_ok &= all(energy(z, w) <= -c / (2 * np.pi ** 2) + 1e-12 for w in pts)
        # crude-ness signal: width of the negative run containing wm vs 2 eta
        idx = int(np.searchsorted(ws, wm))
        lo = idx
        while lo > 0 and es[lo - 1] < 0:
            lo -= 1
        hi = idx
        while hi < grid - 1 and es[hi + 1] < 0:
            hi += 1
        width_ratios.append(float((ws[hi] - ws[lo]) / (2 * eta)))
    ok = worst_deriv_ratio <= 1 + 1e-6 and window_ok
    return {"package": "M75_NEGATIVE_WINDOW",
            "worst_entry_derivative_over_bound": worst_deriv_ratio,
            "window_inside_and_negative": window_ok,
            "negative_run_width_over_2eta_min": min(width_ratios),
            "crudeness_status": "NUMERICAL_SIGNAL_ONLY",
            "disposition": "EXACT_THEOREM_REGRESSION_PASS" if ok else "FAIL"}


def m75_prime_threshold(kmax):
    rows = []
    for K in range(2, kmax + 1):
        MK = (2 + 4 * math.pi * K) * (2 * K + 1) * K ** 2
        rows.append({"K": K, "M_K": MK, "L_threshold": math.pi ** 2 * MK * math.log(2)})
    return {"package": "M75_PRIME_THRESHOLD_TABLE", "rows": rows,
            "note": "individual prime summands only; threshold far beyond any computed L",
            "disposition": "INFORMATIONAL"}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=40)
    ap.add_argument("--kmax", type=int, default=6)
    ap.add_argument("--grid", type=int, default=2001)
    ap.add_argument("--seed", type=int, default=20261010)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    results = [m70(rng, args.trials, args.kmax, args.grid),
               m73(60),
               m75(rng, args.trials, args.kmax, args.grid),
               m75_prime_threshold(args.kmax)]
    report = {"terminal_claim": "RH_OPEN", "authority": "REGRESSION_EVIDENCE_ONLY",
              "results": results}
    text = json.dumps(report, indent=2, default=float)
    if args.output:
        with open(args.output, "w") as f:
            f.write(text)
    print(text)
    bad = [r["package"] for r in results if r["disposition"] == "FAIL"]
    if bad:
        raise SystemExit(f"POST285 gate A/D falsifier failures: {bad}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
