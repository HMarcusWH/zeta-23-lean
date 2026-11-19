"""Check the Abel endpoint, positive kernel and transfer constants with Arb balls."""

import json
from math import isqrt
from pathlib import Path

from flint import acb, arb, ctx


def li(x):
    return arb(x).log().ei()


def primes_up_to(x):
    return [p for p in range(2, x + 1) if all(p % d for d in range(2, isqrt(p) + 1))]


def compare_areas(x, c0):
    primes = primes_up_to(x)
    theta, prime_moment, integral = arb(0), arb(0), acb(0)
    for p, right in zip(primes, primes[1:] + [x]):
        theta += arb(p).log()
        prime_moment += p * arb(p).log()
        if p == right:
            continue

        def weighted_area(t, analytic):
            log_t = t.log(analytic=analytic)
            minus_derivative = ((t + x) / (t**2 * log_t**2)
                                + 2 * (x - t) / (t**2 * log_t**3))
            return minus_derivative * (t * theta - prime_moment - (t**2 - 4) / 2)

        integral += acb.integral(weighted_area, p, right)

    area_theta = x * theta - prime_moment - arb(x*x - 4) / 2
    area_pi = (sum(x - p for p in primes) - x * li(x) + li(x*x)
               + 2 * li(2) - li(4))
    reconstructed = c0 * (x - 2) + area_theta / arb(x).log() + integral
    difference = reconstructed - area_pi
    assert difference.contains(0) and abs(difference) < arb("1e-40")
    return {"x": x, "prime_count": len(primes),
            "direct_area_pi": str(area_pi), "direct_area_theta": str(area_theta),
            "abel_minus_direct": str(difference)}


ctx.prec = 224
c0 = 2 / arb(2).log() - li(2)
start = arb(10**19)
relative_cost = 3 * start.log() / start.sqrt()
assert 0 < c0 < 3 and relative_cost < arb("0.001")
ceilings = [10**46, 10**48, 121 * 10**46]
quartic_limits = {}
for ceiling in ceilings:
    m = isqrt(isqrt(ceiling))
    assert m**4 <= ceiling < (m + 1)**4
    quartic_limits[str(ceiling)] = m
results = {"precision_bits": ctx.prec, "c0": str(c0),
           "upper_for_normalized_endpoint_cost": str(relative_cost),
           "last_fourth_root_at_each_ceiling": quartic_limits,
           "comparisons": [compare_areas(x, c0) for x in (16, 81, 256)],
           "scope": "Exact prime enumeration and rigorous balls for three finite integrals. "
                    "The finite-range sign deduction also requires the complete analytic "
                    "bound for the Chebyshev area."}
Path(__file__).with_name("ORDINARY_AREA_CHECK.json").write_text(
    json.dumps(results, indent=2) + "\n", encoding="utf-8")
print("Validated positive-kernel reconstruction and endpoint constants.", m)
