"""Finite independent arithmetic checks for the Step 4 rough-squarefree report."""
import json
import math
from fractions import Fraction
from pathlib import Path

LIMIT = 32768
CUTOFFS = (2, 5, 11, 17)
PREFIXES = (1, 2, 6, 30, 210, 1001, 8191, LIMIT)


def factor_table(bound):
    factors = [{} for _ in range(bound + 1)]
    for prime in range(2, bound + 1):
        if factors[prime]:
            continue
        for n in range(prime, bound + 1, prime):
            rem, power = n, 0
            while rem % prime == 0:
                power += 1
                rem //= prime
            factors[n][prime] = power
    return factors


def mobius_divisors(primes):
    rows = [(1, 1)]
    for p in primes:
        rows += [(p * d, -mu) for d, mu in rows]
    return rows


def sieve_coefficients(factors, cutoff):
    kernel = []
    for n, fac in enumerate(factors):
        supported = n and all(k == (1 if p <= cutoff else 2) for p, k in fac.items())
        kernel.append((-1) ** len(fac) if supported else 0)
    return kernel


def log_vector_add(dest, fac, scalar):
    for p, exp in fac.items():
        dest[p] = dest.get(p, 0) + exp * scalar


def check(cutoff, factors):
    kernel = sieve_coefficients(factors, cutoff)
    counts = [0] * (LIMIT + 1)
    for d, coeff in enumerate(kernel):
        if coeff:
            for n in range(d, LIMIT + 1, d):
                counts[n] += coeff
    seen = dict(unit=0, prime=0, pair=0, higher=0)
    residual, background = {}, {}
    for n in range(1, LIMIT + 1):
        fac = factors[n]
        small = {p: k for p, k in fac.items() if p <= cutoff}
        large = {p: k for p, k in fac.items() if p > cutoff}
        is_in = not small and all(k == 1 for k in large.values())
        assert counts[n] == int(is_in), (cutoff, n, "sieve")
        # Expand the actual integer drive after retaining the rough Möbius action.
        # Compare as prime exponents of rational products, with no logarithm rounding.
        got = {}
        for d, mu in mobius_divisors(large):
            log_vector_add(got, factors[n // d], mu)
        want = (small if not large else
                {next(iter(large)): 1} if len(large) == 1 else {})
        assert {p: e for p, e in got.items() if e} == want, (cutoff, n, "drive")
        if is_in:
            key = ("unit" if n == 1 else "prime" if len(large) == 1 else
                   "pair" if len(large) == 2 else "higher")
            seen[key] += 1
        # A signed integer probe exposes exact coefficient/multiplicity errors.
        weight = (7 * n % 31) - 15
        if len(fac) == 1:
            p, k = next(iter(fac.items()))
            residual[p] = residual.get(p, 0) + weight  # full Mangoldt atom
            if p <= cutoff or k > 1:
                residual[p] -= weight  # paid prime and proper-power terms
        if is_in and len(fac) >= 2:
            log_vector_add(residual, fac, weight)
        if counts[n]:
            log_vector_add(background, fac, weight)
    assert {p: e for p, e in residual.items() if e} == {p: e for p, e in background.items() if e}
    assert seen["higher"] and seen["pair"]
    prefix_counts = []
    for x in PREFIXES:
        direct = sum(counts[1:x+1])
        with_floors = sum(coeff * (x // d) for d, coeff in enumerate(kernel[:x+1]) if coeff)
        assert direct == with_floors
        prefix_counts.append(direct)
    return {"cutoff": cutoff, "sector_counts": seen, "prefix_squarefree_rough_counts": prefix_counts}


def main():
    facts = factor_table(LIMIT)
    # Laplace moments of the explicit endpoint polynomial, in units of K.
    moments = []
    for j in range(3):
        moment = sum(c * Fraction(math.factorial(k + j), math.factorial(k)) *
                     2 ** (k + j + 1) for k, c in
                     [(14, Fraction(1)), (16, Fraction(-1, 2)), (18, Fraction(1, 16))])
        assert moment.denominator == 1
        moments.append(int(moment))
    assert moments == [0, 0, 2 ** 20]
    receipt = {
        "integer_range": [1, LIMIT], "inclusive_cutoffs": CUTOFFS, "prefixes": PREFIXES,
        "integer_cutoff_pairs": LIMIT * len(CUTOFFS), "laplace_moments_in_units_of_K": moments,
        "runs": [check(y, facts) for y in CUTOFFS],
        "scope": "Exact finite sieve, signed logarithmic coefficients and endpoint polynomial moments."
    }
    Path(__file__).with_name("finite-checks.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"checks": "passed", "integer_cutoff_pairs": receipt["integer_cutoff_pairs"],
                      "moments": moments}))


if __name__ == "__main__":
    main()
