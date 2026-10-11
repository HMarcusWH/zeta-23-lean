"""POST285 M55/M38 regression: weighted Chebyshev partial summation (Step 96)
and exact finite extrema of the weighted remainder (Step 75).

Checks the statement proved in `Zeta23/CCM/CanonicalWeightedChebyshevAbel.lean`:

    psi(x) - x = 1 + sqrt(x) R(x) - (1/2) int_1^x R(t)/sqrt(t) dt,   x >= 1,
    R(x) = sum_{n <= x} Lambda(n)/sqrt(n) - 2 sqrt(x),

with the right-continuous floor convention (n <= floor x).  R is a step
function minus 2 sqrt(t), so the integral is evaluated exactly cell by cell:
on [n, n+1) the sum A is constant and
int (A - 2 sqrt t)/sqrt t dt = 2A (sqrt b - sqrt a) - 2 (b - a).

Also checks the transfer bound |psi(x) - x - 1| <= 2 M sqrt(x) with
M = max_{[1,x]} |R| (the claim firewall: R = O(x^eps) for all eps would be
RH-strength; this script only evaluates finite x).

Left limits taken on both sides at an integer x = n also satisfy the identity
(psi and sqrt(n) R(n) both drop by Lambda(n)).  Negative control (must FAIL):
mixing conventions, psi(n-) against R(n), misses by exactly Lambda(n), which is
positive at prime powers and zero elsewhere.

M38: on [1, X], sup R = max_{1<=m<=floor X} R(m) (attained at an integer) and
inf R = min_{1<=m<=floor X} (W_m - 2 sqrt(min(m+1, X))) (possibly only a left
limit).  Checked against dense sampling for X just below, at and just after
prime powers.  Negative control (must FAIL): replacing min(m+1, X) by m + 1
(ignoring the cut at X) undershoots the true infimum when X is not an integer.

Regression evidence only; no sign or size of R is claimed.
"""
from __future__ import annotations

import argparse
import json
import math


def von_mangoldt_table(N: int) -> list[float]:
    lam = [0.0] * (N + 1)
    sieve = list(range(N + 1))
    for p in range(2, N + 1):
        if sieve[p] == p:
            for m in range(p, N + 1, p):
                if sieve[m] == m:
                    sieve[m] = p
    for n in range(2, N + 1):
        p = sieve[n]
        m = n
        while m % p == 0:
            m //= p
        if m == 1:
            lam[n] = math.log(p)
    return lam


def check(N: int, tol: float):
    lam = von_mangoldt_table(N + 1)
    # prefix sums A(n) = sum_{k <= n} Lambda(k)/sqrt(k), psi(n) = sum_{k <= n} Lambda(k)
    A = [0.0] * (N + 2)
    psi = [0.0] * (N + 2)
    for n in range(1, N + 2):
        A[n] = A[n - 1] + lam[n] / math.sqrt(n)
        psi[n] = psi[n - 1] + lam[n]

    def R(t: float) -> float:
        return A[math.floor(t)] - 2 * math.sqrt(t)

    # cumulative exact integral I(n) = int_1^n R/sqrt t
    I = [0.0] * (N + 2)
    for n in range(1, N + 1):
        a, b = n, n + 1
        I[n + 1] = I[n] + 2 * A[n] * (math.sqrt(b) - math.sqrt(a)) - 2 * (b - a)

    def integral(x: float) -> float:
        n = math.floor(x)
        return I[n] + 2 * A[n] * (math.sqrt(x) - math.sqrt(n)) - 2 * (x - n)

    xs = [1.0] + [float(n) for n in range(2, N + 1)] + [n + f for n in range(1, N) for f in (0.25, 0.5, 0.999)]
    worst = 0.0
    worst_bound_ratio = 0.0
    runmax = 0.0
    xs_sorted = sorted(xs)
    for x in xs_sorted:
        lhs = psi[math.floor(x)] - x
        rhs = 1 + math.sqrt(x) * R(x) - 0.5 * integral(x)
        worst = max(worst, abs(lhs - rhs) / max(1.0, abs(lhs)))
        # running sup of |R| on [1, x]: R is maximal in |.| at cell ends or left ends
        n = math.floor(x)
        runmax = max(runmax, abs(R(x)), abs(A[n] - 2 * math.sqrt(n)))
        bound = 2 * runmax * math.sqrt(x)
        if bound > 0:
            worst_bound_ratio = max(worst_bound_ratio, abs(lhs - 1) / bound)
    # sanity at x = 1
    sanity = {"psi(1)-1": psi[1] - 1, "R(1)": R(1.0)}
    # left limits on both sides at integer x = n: psi drops by Lambda(n) and so
    # does sqrt(n) R(n); the integral is unchanged.  The identity must still hold.
    left = []
    # negative control (must FAIL): mixed conventions, psi(n-) against R(n).
    mixed = []
    for n in (2, 3, 4, 5, 7, 8, 9, 16, 27, 32, 6, 10):
        if n > N:
            continue
        x = float(n)
        lhs_left = psi[n - 1] - x
        rhs_left = 1 + math.sqrt(x) * (A[n - 1] - 2 * math.sqrt(x)) - 0.5 * integral(x)
        rhs_right = 1 + math.sqrt(x) * R(x) - 0.5 * integral(x)
        left.append({"x": n, "residual": lhs_left - rhs_left})
        mixed.append({"x": n, "miss": rhs_right - lhs_left, "Lambda": lam[n]})
    left_ok = all(abs(c["residual"]) < tol * max(1.0, n) for c in left)
    mixed_fails = (all(abs(c["miss"] - c["Lambda"]) < 1e-8 for c in mixed)
                   and any(c["miss"] > 0.5 for c in mixed))
    # M38 exact extrema
    def sup_formula(X):
        return max(A[m] - 2 * math.sqrt(m) for m in range(1, math.floor(X) + 1))

    def inf_formula(X, cut=True):
        return min(A[m] - 2 * math.sqrt(min(m + 1, X) if cut else m + 1)
                   for m in range(1, math.floor(X) + 1))

    m38 = []
    m38_ok = True
    ctrl38 = False
    for base in (2, 3, 4, 5, 8, 9, 16, 25, 27, 32, 49, 97, 128, 500):
        if base + 1 > N:
            continue
        for X in (base - 1e-6, float(base), base + 1e-6, base + 0.5):
            if X < 1:
                continue
            samples = []
            for m in range(1, math.floor(X) + 1):
                hi = min(m + 1, X)
                for f in (0.0, 0.3, 0.7, 1 - 1e-9):
                    t = m + f * (hi - m)
                    if t <= X:
                        samples.append(R(t))
                if X < m + 1:
                    samples.append(R(X))
            s_sup, s_inf = max(samples), min(samples)
            f_sup, f_inf = sup_formula(X), inf_formula(X)
            ok = (abs(s_sup - f_sup) < 1e-12 and s_inf >= f_inf - 1e-12
                  and s_inf - f_inf < 1e-6)
            m38_ok &= ok
            if X != math.floor(X) and inf_formula(X, cut=False) < f_inf - 1e-9:
                ctrl38 = True
            m38.append({"X": X, "sup": f_sup, "inf": f_inf, "sample_sup": s_sup,
                        "sample_inf": s_inf, "ok": ok})
    return {
        "N": N,
        "points": len(xs_sorted),
        "worst_relative_residual": worst,
        "identity_pass": worst < tol,
        "sanity": sanity,
        "sanity_pass": abs(sanity["psi(1)-1"] + 1) < 1e-15 and abs(sanity["R(1)"] + 2) < 1e-15,
        "transfer_bound_worst_ratio": worst_bound_ratio,
        "transfer_bound_pass": worst_bound_ratio <= 1 + 1e-12,
        "left_limits_both_sides": left,
        "left_limits_both_sides_pass": left_ok,
        "control_mixed_conventions": mixed,
        "control_mixed_conventions_fails_as_predicted": mixed_fails,
        "m38_extrema": m38,
        "m38_extrema_pass": m38_ok,
        "control_m38_uncut_infimum_fails": ctrl38,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--nmax", type=int, default=20000)
    ap.add_argument("--tol", type=float, default=1e-9)
    ap.add_argument("--output")
    args = ap.parse_args()
    res = check(args.nmax, args.tol)
    ok = (res["identity_pass"] and res["sanity_pass"] and res["transfer_bound_pass"]
          and res["left_limits_both_sides_pass"]
          and res["control_mixed_conventions_fails_as_predicted"]
          and res["m38_extrema_pass"] and res["control_m38_uncut_infimum_fails"])
    res["verdict"] = "PASS_REGRESSION" if ok else "FAIL"
    text = json.dumps(res, indent=2)
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text + "\n")
    print(json.dumps({k: v for k, v in res.items()
                      if k not in ("left_limits_both_sides", "control_mixed_conventions",
                                   "m38_extrema")}, indent=2))
    print("verdict:", res["verdict"])
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
