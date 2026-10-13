"""POST285 M51 research certificate: the K = 2 even bottom on [1/400, log 16] (Step 92).

Experiment 1 of the M51 plan asks, for K = 2 and 0 < L <= log 16, whether the
physical balance P(L) + F(L) = 0 can occur at an actual canonical even zero
eigenvalue.  For K = 2 the legal even carrier (z_{-n} = z_n, M_0 = M_2 = 0) is
spanned by the single vector z = (1, -4, 6, -4, 1), so the even compressed
canonical operator is the scalar

    lambda(L) = <z, S_L z>/<z, z>,

and an even contact at L is exactly lambda(L) = 0.  By the F04 identity
(canonicalFixedSecondEuler_eq_physical_of_pos, M65) the physical second test of z
is V(L) = P - sum_q beta_q e_{Dz}(omega_q) = -(L^4/(4 pi^2))(lambda'' + 2 lambda'/L),
and at a K = 2 stationary contact the response cost vanishes, so a contact
would need lambda = lambda' = lambda'' = 0.

Certificate (Arb, python-flint, 128 bits; canonical_source_arb and the fixed-Q
jets of post194_fb05_q14_fixed_unit_second_derivative):

  For every L in [1/400, log 16], lambda(L) > 0.

Each closed cutoff cell [log Q, log(Q + 1)] (Q = 1..15; the prime sum is the
fixed-Q sum there, and the entering atom vanishes at both ends) is covered by
rational intervals [c - r, c + r] around rational centres c.  On each interval

    lambda(L) >= lambda(c) - |lambda'(c)| r + (1/2) min(0, inf lambda''([c - r, c + r])) r^2,

with lambda(c), lambda'(c) Arb point enclosures and inf lambda'' the lower end of
the Arb ball enclosure of lambda'' over the whole interval.  An interval is
accepted when this lower bound is > 0, and bisected otherwise.  The fixed-Q
formula is analytic in L, so an interval reaching slightly past a cell end still
bounds the true lambda on the part inside the cell.

Also reported (research evidence):
  * the local minima of lambda on (1.2, log 16] (Arb point values at refined
    minimizers): about 1.4e-6, 4.5e-9, 8.8e-9, 3.2e-10, near L = 1.334, 1.778,
    2.223, 2.668; lambda never reaches 0, but comes within 3.2e-10;
  * the F04 identity at those minima: V computed from the pole/archimedean
    integral and the prime samples (50-digit quadrature) against
    -(L^4/(4 pi^2))(lambda'' + 2 lambda'/L) from the Arb jets;
  * lambda(L) ~ -log L as L -> 0+ (lambda' ~ -1/L), shown at L = 1e-3 .. 2.5e-3;
    the interval (0, 1/400) is not certified here;
  * zero side: at L = 1, 2 and the four minima, lambda against the sum over the
    first 100 zeta zeros 1/2 + i gamma_k of the single-zero terms
    c_L(gamma) = -<z, E_gamma z>/<z, z>, E_gamma = exp_weight_sprime(i gamma L, -2/(i gamma))
    (the #249 planted-zero matrix for one zero); every c_L(gamma_k) is >= 0, and
    the minima sit at L = 2 pi k/gamma_1 (k = 3..6), where c_L(gamma_1) nearly
    vanishes, so the closest approach is the higher-zero remainder.  This uses the
    known zeros and is not independent of them.

Negative controls (each must FAIL as predicted):
  C1  the von Mangoldt weights scaled by 1 + 1e-6 (every prime atom heavier by one
      part in a million): lambda < 0 at the deepest minimizer (certified), so the
      closest approach is an arithmetic near-cancellation (the prime atoms
      contribute about -0.645 to lambda there, against lambda = 3.2e-10);
  C2  the same covering applied to lambda - 5e-10 on the cell of the deepest
      minimum is rejected, and lambda - 5e-10 < 0 is certified at the minimizer:
      the covering resolves the closest approach;
  C3  the weights scaled by 1 - 1e-6 instead: lambda stays positive there, as it
      must, since the prime part is negative (positive control for C1).

Interval evidence for K = 2 only: no statement for K >= 3, no exclusion of a
contact at other K, and not RH evidence beyond this finite instance.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from flint import acb, arb, arb_mat, ctx, fmpq

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

import canonical_source_arb as C  # noqa: E402
from post194_fb05_q14_fixed_unit_second_derivative import (  # noqa: E402
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb as jets,
)
from post247_remainder_budget_ratio_scout import exp_weight_sprime  # noqa: E402

PREC = 128
Z = (1, -4, 6, -4, 1)
ZZ = sum(c * c for c in Z)
L_MIN = Fraction(1, 400)
LOG16_UP = Fraction(2772588722239781, 10 ** 15)  # >= log 16 = 2.77258872223978...
MAX_DEPTH = 40


def quad(M, v=Z, norm=ZZ) -> arb:
    return sum(v[i] * M[i, j] * v[j] for i in range(5) for j in range(5)) / norm


def ball(c: Fraction, r: Fraction = Fraction(0)) -> arb:
    """Arb ball containing the rational interval [c - r, c + r]."""
    lo, hi = c - r, c + r
    a = arb(fmpq(lo.numerator, lo.denominator))
    return a if not r else a.union(arb(fmpq(hi.numerator, hi.denominator)))


def legal_even_carrier() -> list[list[int]]:
    """Exact basis of {z even, sum z = 0, sum n^2 z = 0} for K = 2 (sympy)."""
    import sympy as sp
    a, b, c = sp.symbols("a b c")
    z = [a, b, c, b, a]
    n = range(-2, 3)
    sol = sp.solve([sum(z), sum(k * k * zi for k, zi in zip(n, z))], [b, c], dict=True)[0]
    v = [sp.simplify(x.subs(sol).subs(a, 1)) for x in z]
    return [[int(x) for x in v]]


def cell_bounds(Q: int) -> tuple[Fraction, Fraction]:
    """Rational a <= log Q and b >= log(Q + 1), clipped to [L_MIN, LOG16_UP]."""
    lo = Fraction(0) if Q == 1 else Fraction(math.floor(math.log(Q) * 10 ** 12) - 1, 10 ** 12)
    hi = Fraction(math.ceil(math.log(Q + 1) * 10 ** 12) + 1, 10 ** 12)
    assert ball(lo) < arb(Q).log() or Q == 1
    assert ball(hi) > arb(Q + 1).log()
    return max(lo, L_MIN), min(hi, LOG16_UP)


def lower_bound(c: Fraction, r: Fraction, Q: int, offset: arb = arb(0)) -> arb:
    """Arb lower bound for lambda - offset on [c - r, c + r] (cell-Q formula)."""
    M, Mp, _ = jets(ball(c), 2, Q)
    _, _, Mpp = jets(ball(c, r), 2, Q)
    lam, lam1, lam2 = quad(M), quad(Mp), quad(Mpp)
    rr = ball(r)
    return C.finite_second_order_lower(lam-offset,lam1,lam2,rr)


def cover(Q: int, a: Fraction, b: Fraction, stats: dict, offset: arb = arb(0),
          max_depth: int = MAX_DEPTH):
    """Cover [a, b]; return None, or the interval where bisection gave up."""
    stack = [(a, b, 0)]
    while stack:
        lo, hi, depth = stack.pop()
        c, r = (lo + hi) / 2, (hi - lo) / 2
        lb = lower_bound(c, r, Q, offset)
        stats["evaluations"] += 1
        if C.definitely_positive(lb):
            stats["intervals"] += 1
            stats["min_lower_bound"] = min(stats["min_lower_bound"], float(lb))
            stats["min_radius"] = min(stats["min_radius"], float(r))
            continue
        if depth >= max_depth:
            return (float(lo), float(hi))
        stack.append((c, hi, depth + 1))
        stack.append((lo, c, depth + 1))
    return None


def lam_point(L: Fraction, Q: int, v=Z, norm=ZZ):
    M, Mp, Mpp = jets(ball(L), 2, Q)
    return quad(M, v, norm), quad(Mp, v, norm), quad(Mpp, v, norm)


def refine_minimum(c0: float) -> Fraction:
    g = (math.sqrt(5) - 1) / 2
    a, b = c0 - 0.004, c0 + 0.004
    Q = int(math.floor(math.exp(c0)))
    f = lambda x: float(lam_point(Fraction(round(x * 10 ** 12), 10 ** 12), Q)[0].mid())
    x1, x2 = b - g * (b - a), a + g * (b - a)
    f1, f2 = f(x1), f(x2)
    for _ in range(45):
        if f1 < f2:
            b, x2, f2 = x2, x1, f1
            x1 = b - g * (b - a)
            f1 = f(x1)
        else:
            a, x1, f1 = x1, x2, f2
            x2 = a + g * (b - a)
            f2 = f(x2)
    return Fraction(round(x1 * 10 ** 12), 10 ** 12)


def physical_V(L: float) -> float:
    """V = P - sum_q beta_q e_{Dz}(omega_q) at 50 digits, z normalized."""
    with mp.workdps(50):
        Lm = mp.mpf(L)
        n = list(range(-2, 3))
        u = [k * zi / mp.sqrt(ZZ) for k, zi in zip(n, Z)]

        def energy(w):
            a = 2 * mp.pi * w
            tot = mp.mpf(0)
            for i, ni in enumerate(n):
                for j, nj in enumerate(n):
                    s = 2 * w * mp.cos(ni * a) if i == j else (mp.sin(ni * a) - mp.sin(nj * a)) / ((ni - nj) * mp.pi)
                    tot += u[i] * s * u[j]
            return tot

        kern = lambda t: mp.exp(-t / 2) + mp.exp(t / 2) - mp.exp(t / 2) / (mp.exp(t) - mp.exp(-t))
        P = mp.quad(lambda t: t ** 2 * energy(1 - t / Lm) * kern(t), [0, Lm / 2, Lm])
        F = mp.mpf(0)
        for q in range(2, int(mp.floor(mp.exp(Lm))) + 1):
            vm = float(C.von_mangoldt(q).mid())
            if vm == 0:
                continue
            w = 1 - mp.log(q) / Lm
            F -= mp.mpf(vm) * mp.log(q) ** 2 / mp.sqrt(q) * energy(w)
        return float(P + F)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", default=None)
    ap.add_argument("--cells", default="1-15",
                    help="cutoff cells to cover, e.g. 14 or 1-15 (the certificate is 1-15)")
    args = ap.parse_args()
    C.set_precision(PREC)
    ctx.prec = PREC
    t0 = time.time()
    carrier = legal_even_carrier()
    assert carrier == [list(Z)], carrier

    stats = {"evaluations": 0, "intervals": 0, "min_lower_bound": math.inf, "min_radius": math.inf}
    cells = []
    lo_c, _, hi_c = args.cells.partition("-")
    chosen = range(int(lo_c), int(hi_c or lo_c) + 1)
    for Q in chosen:
        a, b = cell_bounds(Q)
        before = dict(stats)
        failed = cover(Q, a, b, stats)
        cells.append({"Q": Q, "from": float(a), "to": float(b),
                      "intervals": stats["intervals"] - before["intervals"], "failed": failed})
    certified = all(c["failed"] is None for c in cells)

    minima = []
    for c0 in (1.334, 1.778, 2.223, 2.668):
        Lm = refine_minimum(c0)
        Q = int(math.floor(math.exp(float(Lm))))
        lam, lam1, lam2 = lam_point(Lm, Q)
        pred = -(float(Lm) ** 4 / (4 * math.pi ** 2)) * (float(lam2.mid()) + 2 * float(lam1.mid()) / float(Lm))
        V = physical_V(float(Lm))
        minima.append({"L": float(Lm), "Q": Q, "lambda": lam.str(6, radius=True),
                       "lambda_positive_certified": bool(lam > 0),
                       "lambda1": float(lam1.mid()), "lambda2": float(lam2.mid()),
                       "V_physical": V, "V_from_F04": pred,
                       "F04_rel_error": abs(V - pred) / max(abs(V), abs(pred), 1e-30)})
    small = []
    for Lf in (Fraction(1, 1000), Fraction(1, 400)):
        lam, lam1, _ = lam_point(Lf, 1)
        small.append({"L": float(Lf), "lambda": float(lam.mid()), "lambda_plus_log_L": float(lam.mid()) + math.log(float(Lf)),
                      "L_lambda1": float(lam1.mid()) * float(Lf)})

    gammas = [mp.zetazero(k).imag for k in range(1, 101)]
    zero_side = []
    for Lf in [Fraction(1), Fraction(2)] + [Fraction(round(m["L"] * 10 ** 12), 10 ** 12) for m in minima]:
        Q = int(math.floor(math.exp(float(Lf))))
        lam = lam_point(Lf, Q)[0]
        terms = []
        for g in gammas:
            s_ = acb(0, arb(mp.nstr(g, 30)))
            terms.append(-quad(exp_weight_sprime(s_ * ball(Lf), -2 / s_, 2)))
        total = sum(terms, arb(0))
        zero_side.append({"L": float(Lf), "L_gamma1_over_2pi": float(Lf) * float(gammas[0]) / (2 * math.pi),
                          "lambda": lam.str(6, radius=True), "zero_sum_100": total.str(6, radius=True),
                          "rel_diff": float(abs(lam - total).upper() / abs(lam).lower()),
                          "first_terms": [float(t.mid()) for t in terms[:3]],
                          "all_terms_nonnegative": all(bool(t > 0) or bool(t.contains(0)) for t in terms)})
    # C1/C3: the prime weights scaled by 1 +- 1e-6 at the deepest minimizer
    Lm = Fraction(round(minima[-1]["L"] * 10 ** 12), 10 ** 12)
    Qm = minima[-1]["Q"]
    lam_m = lam_point(Lm, Qm)[0]
    prime = quad(arb_mat([[C.prime_component(n, m, ball(Lm), Qm) for m in range(-2, 3)]
                          for n in range(-2, 3)]))
    eps = arb(fmpq(1, 10 ** 6))
    c1_value, c3_value = lam_m - eps * prime, lam_m + eps * prime
    c1 = {"prime_part": prime.str(6, radius=True), "lambda_heavier_primes": c1_value.str(6, radius=True),
          "negative": bool(c1_value < 0)}
    c3 = {"lambda_lighter_primes": c3_value.str(6, radius=True), "positive": bool(c3_value > 0)}
    # C2: the same covering must reject lambda - 5e-10 on the cell of the deepest minimum
    a, b = cell_bounds(Qm)
    off = arb(fmpq(5, 10 ** 10))
    c2_fail_at = cover(Qm, a, b, {"evaluations": 0, "intervals": 0, "min_lower_bound": math.inf,
                                  "min_radius": math.inf}, offset=off, max_depth=30)
    c2_point_negative = bool(lam_point(Lm, Qm)[0] - off < 0)
    c2_fails = c2_fail_at is not None and c2_point_negative
    zero_ok = all(r["rel_diff"] <= 1e-4 and r["all_terms_nonnegative"] for r in zero_side)
    f04_ok = all(m["F04_rel_error"] <= 1e-6 or abs(m["V_physical"] - m["V_from_F04"]) <= 1e-12 for m in minima)
    controls_ok = c1["negative"] and c2_fails and c3["positive"]
    passed = (certified and all(m["lambda_positive_certified"] for m in minima) and f04_ok
              and zero_ok and controls_ok)
    report = {
        "terminal_claim": "RH_OPEN", "authority": "INTERVAL_CERTIFICATE_RESEARCH_EVIDENCE",
        "package": "M51_K2_EVEN_BOTTOM", "verdict": "PASS" if passed else "FAIL",
        "statement": ("lambda_even(L) > 0 for K = 2 and every L in [1/400, log 16]"
                      if list(chosen) == list(range(1, 16))
                      else f"partial covering: cutoff cells {args.cells} of 1-15"),
        "precision_bits": PREC, "legal_even_carrier": carrier, "cells": cells,
        "covering": {k: (v if not isinstance(v, float) else float(v)) for k, v in stats.items()},
        "minima": minima, "small_L": small, "zero_side": zero_side,
        "controls": {"C1_prime_weights_times_1_plus_1e-6": c1,
                     "C2_offset_covering_rejected_at": c2_fail_at,
                     "C2_offset_negative_at_minimizer": c2_point_negative,
                     "C3_prime_weights_times_1_minus_1e-6": c3},
        "seconds": round(time.time() - t0, 1),
    }
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k not in ("rows", "cells")}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
