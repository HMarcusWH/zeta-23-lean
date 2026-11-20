"""Finite checks for the K5 prime-side aperture calculation. Requires mpmath."""

from fractions import Fraction
from math import factorial, isqrt
import json

import mpmath as mp


def prime_exponents(n):
    terms = {}
    for p in range(2, isqrt(n) + 1):
        while n % p == 0:
            terms[p] = terms.get(p, 0) + 1
            n //= p
    if n > 1:
        terms[n] = 1
    return terms


def divisor_check(limit):
    factors = [None] + [prime_exponents(n) for n in range(1, limit + 1)]
    total = [{} for _ in range(limit + 1)]
    for d in range(1, limit + 1):
        if any(e > 1 for e in factors[d].values()):
            continue
        mu = (-1) ** len(factors[d])
        for m in range(1, limit // d + 1):
            for p, exponent in factors[m].items():
                bucket = total[d*m]
                bucket[p] = bucket.get(p, 0) + mu * exponent
    for n in range(1, limit + 1):
        actual = {p: e for p, e in total[n].items() if e}
        expected = {next(iter(factors[n])): 1} if len(factors[n]) == 1 else {}
        assert actual == expected


def f(y):
    s = mp.sin(mp.pi * y)
    return s**8 - mp.mpf(10)/9 * s**10


def f2(y):
    s = mp.sin(mp.pi * y)
    def derivative(n):
        return n * mp.pi**2 * ((n-1) * s**(n-2) - n * s**n)
    return derivative(8) - mp.mpf(10)/9 * derivative(10)


def kernels(u):
    def form(a, b):
        return mp.quad(lambda y: a(y) * b(y + u), [0, 1-u])
    return {13: form(f2, f2), 15: -(form(f2, f) + form(f, f2))/4,
            17: form(f, f)/16}


def residue_checks():
    coefficients = {13: Fraction(1), 15: Fraction(-1, 2), 17: Fraction(1, 16)}
    for z in [Fraction(1, 3), Fraction(2, 5), Fraction(3, 2)]:
        combined = sum(c / z**(m+1) for m, c in coefficients.items())
        assert combined == (z*z-Fraction(1, 4))**2/z**18
    for m in coefficients:
        e = mp.mpf('0.025')
        lhs = e * mp.quad(lambda v: v**m / (e + v)**(m+2), [0, e, 1])
        rhs = 1 / ((m+1) * (1+e)**(m+1))
        assert abs(lhs - rhs) < mp.mpf('1e-45')
    for v, sign in [(1, 1), (30, -1), (50, 1)]:
        poly = sum(c * Fraction(v**(m+1), factorial(m+1))
                   for m, c in coefficients.items())
        assert ((poly > 0) - (poly < 0)) == sign
    # Integrate h^j exp(-h/2) times the endpoint primitive, divided by K.
    moments = [
        sum(c * Fraction(factorial(m+1+j) * 2**(m+2+j), factorial(m+1))
            for m, c in coefficients.items())
        for j in range(3)
    ]
    assert moments == [0, 0, 2**20]


def main():
    mp.mp.dps = 55
    divisor_check(4096)
    residue_checks()
    differences = []
    moments = []
    for length in [3, 8, 23]:
        L = mp.mpf(length)
        g = lambda y: f2(y) / L**2 - f(y) / 4
        for u in [mp.mpf('0.1'), mp.mpf('0.47'), mp.mpf('0.88')]:
            direct = L**17 * mp.quad(lambda y: g(y)*g(y+u), [0, 1-u])
            expanded = sum(L**m * k for m, k in kernels(u).items())
            differences.append(abs(expanded-direct)/(1+abs(direct)))
        for s in [-mp.mpf('0.5'), mp.mpf('0.5')]:
            moments.append(abs(mp.quad(lambda y: mp.exp(s*L*y)*g(y), [0, 1])))
    assert max(differences) < mp.mpf('1e-45')
    assert max(moments) < mp.mpf('1e-45')
    print(json.dumps({
        "status": "PASS_BOUNDED_ALGEBRA_AND_NUMERICS",
        "mobius_log_coefficient_identities": 4096,
        "kernel_comparisons": len(differences),
        "max_relative_kernel_residual": mp.nstr(max(differences), 5),
        "max_weighted_carrier_moment_residual": mp.nstr(max(moments), 5),
        "primitive_endpoint_signs_at_1_30_50": [1, -1, 1],
        "exact_endpoint_moments_divided_by_K": [0, 0, 2**20],
        "scope": "No uniform arithmetic upper and no Lean proof."
    }, indent=2))


if __name__ == "__main__":
    main()
