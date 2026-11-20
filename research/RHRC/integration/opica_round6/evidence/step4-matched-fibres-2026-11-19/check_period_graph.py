"""Check whole residue periods and the rational three-moment calibration exactly."""
from fractions import Fraction as F
import json
from math import gcd, lcm
from pathlib import Path


def kernel(n, m):
    t = n % m
    return t * (m - t)


def mobius(n):
    value = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


def calibration(L):
    low = {m: F(-mobius(m), m) for m in range(2, L + 1)}
    a = 1 - sum(low.values())
    missing_linear = 3 - sum(m * v for m, v in low.items())
    missing_square = 13 - sum(m * m * v for m, v in low.items())
    coeff = low.copy()
    centers = [R for R in range(2 * L + 1, 3 * L + 1) if R % 9 == 0]
    assert centers
    for R in centers:
        b, c = missing_linear / R, missing_square / R**2
        z = (c - 3 * b + 2 * a) / 6
        y = b - a - 3 * z
        for m, v in [(R, a-y-z), (2*R, y), (4*R, z)]:
            coeff[m] = coeff.get(m, 0) + v / len(centers)
    assert [sum(m**k * v for m, v in coeff.items()) for k in range(3)] == [1, 3, 13]
    return {m: v for m, v in coeff.items() if v}


def covariance_numerator(m, k):
    g = gcd(m, k)
    return g**4 + 10 * g**2 - 11


def direct_controls(L):
    coeff = calibration(L)
    period = lcm(*coeff)
    scale = lcm(*(a.denominator for a in coeff.values()))
    scaled = {m: int(a * scale) for m, a in coeff.items()}

    def twice_scaled_value(n):
        return -2*scale + sum(a * kernel(n, m) for m, a in scaled.items())

    assert all(twice_scaled_value(n) == 0 for n in range(1, L+2))
    predicted = sum(a*b*covariance_numerator(m, k) for m, a in coeff.items()
                    for k, b in coeff.items()) / 720
    out = {"L": L, "nonzero_moduli": len(coeff), "period": period,
           "variance_from_gcd_graph": str(predicted)}
    if period <= 100000:
        values = [twice_scaled_value(n) for n in range(period)]
        assert sum(values) == 0
        assert F(sum(v*v for v in values), 4*scale**2*period) == predicted
        out["full_period_sites_directly_checked"] = period
    return out


def main():
    for m in range(1, 33):
        for k in range(1, 33):
            period = lcm(m, k)
            covariance = F(sum(kernel(n, m)*kernel(n, k) for n in range(period)), period)
            covariance -= F((m*m-1)*(k*k-1), 36)
            assert covariance * 180 == covariance_numerator(m, k)
    controls = [direct_controls(L) for L in [3, 6, 9, 12, 36, 72]]
    result = {"modulus_pair_checks": 32**2, "rational_source_checks": controls,
              "qualification": "Exact finite checks of CRT, calibration, native initial zeroes and the complete-period variance at the explicitly enumerated cutoffs."}
    Path(__file__).with_name("PERIOD_GRAPH_CHECK.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf8")
    print([(c["L"], c.get("full_period_sites_directly_checked")) for c in controls])


if __name__ == "__main__":
    main()
