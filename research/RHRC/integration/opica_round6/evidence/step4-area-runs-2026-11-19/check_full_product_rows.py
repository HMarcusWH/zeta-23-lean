"""Finite Arb audit of the two distributed prime filters, including every ordered row pair."""
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path

import flint
from flint import acb, arb, arb_mat, ctx, fmpz


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def agree(a, b, label):
    delta = a - b
    check(delta.contains(0) and abs(delta) < arb(2) ** -90, label)


def ball(z):
    return z.str(24)


def eta(s):
    return (1 - arb(2) ** (1 - s)) * s.zeta()


def filter_data(x, L, new):
    # Exact coefficients h from all representations a*b²*d³, then independent
    # triangular inversion of h*c=delta. The first filter has h(j)=1.
    h = [0] + [1] * x
    if new:
        h = [0] * (x + 1)
        for d in range(1, int(fmpz(x).root(3)) + 1):
            for b in range(1, isqrt(x // d**3) + 1):
                k = d**3 * b**2
                for n in range(k, x + 1, k):
                    h[n] += 1 if (b + d) % 2 == 0 else -1
    c = [0] * (2 * L + 1)
    c[1] = 1
    for m in range(1, len(c)):
        for k in range(2, (len(c) - 1) // m + 1):
            c[m * k] -= c[m] * h[k]
    a = {m: -arb(c[m]) / m for m in range(2, L + 1)}
    half = arb(1) / 2
    target = ([arb(1), 1 / (eta(arb(2)) * eta(arb(3))),
               1 / (half.zeta() * arb(2).log() * eta(3 * half)), arb(0)]
              if new else [arb(1), arb(1), 1 / half.zeta(), arb(2)])

    def moments(m):
        z = arb(m)
        return [arb(1), z.log(), 1 - z.sqrt(),
                1 - z ** (arb(2) / 3) if new else z - 1]

    rhs = [target[k] - sum(value * moments(m)[k] for m, value in a.items())
           for k in range(4)]
    for R in range(2 * L + 1, 3 * L + 1):
        nodes = [R * 4**i for i in range(4)]
        matrix = arb_mat([[moments(m)[k] for m in nodes] for k in range(4)])
        sol = matrix.solve(arb_mat([[v] for v in rhs]))
        for i, m in enumerate(nodes):
            a[m] = a.get(m, arb(0)) + sol[i, 0] / L
    actual = [sum(v * moments(m)[k] for m, v in a.items()) for k in range(4)]
    for v, expected in zip(actual, target):
        agree(v, expected, "full distributed moment normalization")

    # Compute the residual coefficient via exact prefix inversion and the
    # *certified* first moment sum(a_m)=1, avoiding balls at structural zeros.
    r = [arb(-v) for v in h]
    r[1] += 1
    for m, v in a.items():
        for j in range(m, x + 1, m):
            r[j] += m * v * h[j // m]
    for j in range(1, 2 * L + 1):
        expected = 0 if j <= L else c[j]
        agree(r[j], arb(expected), "inverse coefficient including first remaining band")
    pref, first = [0], [0]
    for j in range(1, x + 1):
        pref.append(pref[-1] + h[j])
        first.append(first[-1] + j * h[j])
    return a, r, pref, first, {"L": L, "average_base_count": L, "coefficient_count": len(a),
            "moment_values": [ball(v) for v in actual], "first_band": c[L + 1:]}


def rows(x, primes, L, new):
    a, r, pref, first, info = filter_data(x, L, new)
    low = (arb(x) ** (arb(1) / 40) if new else
           arb(x) ** (arb(3) / 4) / (L * arb(2 * L).log()**2))
    # Integer endpoint comparison avoids ambiguity at p=x/(L+1).
    check(all(not low.contains(p) for p in primes), "ambiguous lower endpoint")
    ps = [p for p in primes if low < p and (L + 1) * p < x]
    f = [arb(0) for _ in range(x + 1)]
    direct = arb(0)
    for p in ps:
        lp = arb(p).log()
        for j in range(1, x // p + 1):
            f[p * j] += (x - p * j) * lp * r[j]

        # Direct native K evaluation, without residual coefficients or product rows.
        def base(step):
            n = x // step
            return x * pref[n] - step * first[n]

        raw = base(p)
        direct += lp * (x - p - sum(v * (raw - m * base(m * p)) for m, v in a.items()))
    total = sum(f)
    agree(direct, total, "regrouped and native prime sums")
    energy = sum(v * v for v in f)
    check(energy > 0, "empty source row energy")
    # The terminal ramp is zero. Residues 0,...,x-1 therefore represent every
    # row with its true index when sampling the additive phases at k/x.
    spectrum = acb.dft(f[:x])
    agree(spectrum[0].real, direct, "additive phase zero")
    agree(spectrum[0].imag, arb(0), "imaginary phase-zero part")
    fourier_energy = sum(z.real**2 + z.imag**2 for z in spectrum) / x
    agree(fourier_energy, energy, "full additive Parseval")
    info.update(prime_labels=len(ps), lower_cutoff=ball(low), upper_cutoff=ball(arb(x)/(L+1)),
                native=ball(direct), regrouped=ball(total), energy_over_x_cubed=ball(energy/x**3),
                parseval_over_x_cubed=ball(fourier_energy/x**3), additive_phases_checked=x)
    return f, total, energy, ps, info


def partition(x, f, g):
    h_real = arb(x).log().sqrt().exp()
    H = int(h_real.floor().unique_fmpz())
    U = int((x * h_real).floor().unique_fmpz())
    # Every row index 1..x is counted (including zeros and the terminal ramp).
    # Enumerating the rarer small-lcm pairs allows the far-large class by exact
    # complementation, without materializing x² Arb products.
    pf, pg = [arb(0)], [arb(0)]
    for v in g[1:]:
        pf.append(pf[-1] + v)
        pg.append(pg[-1] + abs(v))
    divisors = [[] for _ in range(U + 1)]
    for n in range(1, x + 1):
        for w in range(n, U + 1, n):
            divisors[w].append(n)
    small = [[] for _ in range(x + 1)]
    for w, dd in enumerate(divisors):
        for n in dd:
            for m in dd:
                if n * m == w * gcd(n, m):
                    small[n].append(m)
    names = ["equal", "unequal_near_small_lcm", "near_large_lcm", "far_small_lcm", "far_large_lcm"]
    counts = [0] * 5
    signed = [arb(0) for _ in names]
    absolute = [arb(0) for _ in names]
    for n in range(1, x + 1):
        lo, hi = max(1, n - H), min(x, n + H)
        ns = [m for m in small[n] if 0 < abs(m-n) <= H]
        fs = [m for m in small[n] if abs(m-n) > H]
        sizes = [1, len(ns), hi-lo-len(ns), len(fs), x-(hi-lo+1)-len(fs)]
        for i, s in enumerate(sizes):
            check(s >= 0, "negative class count")
            counts[i] += s
        for pref, fn, aggregate in [(pf, lambda v: v, signed), (pg, abs, absolute)]:
            near = pref[hi] - pref[lo-1]
            a, b, d = fn(g[n]), sum((fn(g[m]) for m in ns), arb(0)), sum((fn(g[m]) for m in fs), arb(0))
            for i, subtotal in enumerate([a, b, near-a-b, d, pref[x]-near-d]):
                aggregate[i] += fn(f[n]) * subtotal
    agree(sum(signed), sum(f) * sum(g), "all signed pair families")
    agree(sum(absolute), sum(abs(v) for v in f) * sum(abs(v) for v in g), "all absolute pair families")
    agree(signed[0], sum(v*w for v, w in zip(f, g)), "direct equal-row subtotal")
    check(sum(counts) == x*x and min(counts) > 0, "incomplete integer partition")
    check(all(v > 0 for v in absolute), "an actual arithmetic family was never exercised")
    return {"shift_floor": H, "lcm_floor": U, "n_ordered_pairs": x*x,
            "families": {name: {"pairs": counts[i], "signed_over_x_cubed": ball(signed[i]/x**3),
                                 "absolute_over_x_cubed": ball(absolute[i]/x**3)}
                         for i, name in enumerate(names)}}


def main():
    ctx.prec = 224
    results = []
    for x in (2048, 4096):
        primes = [p for p in range(2, x+1) if fmpz(p).is_prime()]
        L1, L2 = [int(fmpz(x**p).root(100)) for p in (11, 37)]
        f, s, ef, p, fi = rows(x, primes, L1, False)
        g, t, eg, q, gi = rows(x, primes, L2, True)
        part = partition(x, f, g)
        check(sum(v*w for v, w in zip(f, g))**2 < ef*eg, "Cauchy check")
        results.append({"x": x, "factorial": fi, "eta": gi, "overlapping_outer_primes": len(set(p) & set(q)),
                        "native_product_over_x_cubed": ball(s*t/x**3), "partition": part})
    path = Path(__file__).resolve()
    out = {"status": "FINITE_ARITHMETIC_PASS", "precision_bits": ctx.prec, "flint_version": flint.__version__,
           "source_sha256": sha256(path.read_bytes()).hexdigest(),
           "scope": "True finite outer-prime sets, separately distributed calibrations, all ordered product indices. These small cases can have overlapping outer-prime ranges. No asymptotic signed bound is tested.", "cases": results}
    path.with_name("FULL_PRODUCT_ROWS_CHECK.json").write_text(json.dumps(out, indent=2)+"\n", encoding="utf8")
    print("PASS", [(v["x"], v["overlapping_outer_primes"], v["partition"]["n_ordered_pairs"]) for v in results])


if __name__ == "__main__":
    main()
