"""Exact integer and rational checks on specified native squarefree rough vertices."""
from fractions import Fraction
from itertools import combinations
from math import isqrt, prod

from receipt import replay


def proth_primes(count):
    primes = []
    exponent = 190
    k = 1025
    while len(primes) < count:
        n = (k << exponent) + 1
        for witness in (3, 5, 7, 11, 13, 17, 19):
            if pow(witness, (n - 1) // 2, n) == n - 1:
                if not (k < 1 << exponent and k % 2 == 1):
                    raise ArithmeticError("invalid Proth parameters for the primality certificate")
                primes.append((n, k, exponent, witness))
                break
        k += 2
    return primes


def small_primes(count):
    result = []
    n = 500001
    while len(result) < count:
        if all(n % t != 0 for t in range(2, isqrt(n) + 1)):
            result.append(n)
        n += 2
    return result


def subsets(primes):
    return [(prod(sub), (-1) ** len(sub), frozenset(sub))
            for size in range(len(primes)+1) for sub in combinations(primes,size)]


def check(small, large, should_pass):
    primes = small + large
    a, n = prod(small), prod(primes)
    upper = 1 << n.bit_length()
    lower = upper // 2
    y = (upper.bit_length()-1)**2
    if not (lower < n < upper and lower**100 > upper**99):
        raise ArithmeticError("vertex is outside a whole terminal shell")
    if len(set(primes)) != len(primes) or min(primes) <= y:
        raise ArithmeticError("vertex fails the native rough squarefree conditions")
    ds = subsets(primes)
    low = [(d, m, t) for d,m,t in ds if d*d < n]
    high = [(d, m, t) for d,m,t in ds if d*d > n]
    near = [d for d,m,t in ds if n <= (a*d)**2 and d*d <= n*a*a]
    cubed = all((b*b<n)==((a*b)**2<n) for b,_,_ in subsets(large))
    if (not near) != should_pass or cubed != should_pass:
        raise ArithmeticError("divisor gap and complete cube classification disagree")
    moments = []
    for j in range(len(small)):
        moments.append([max(abs(sum(m for d,m,t in half if set(term)<=t))
                            for term in combinations(primes,j)) for half in (low,high)])
    direct = sum(Fraction(m,d) for d,m,t in low)
    factored = prod(1-Fraction(1,p) for p in small) * sum(
        Fraction(m,b) for b,m,t in subsets(large) if b*b<n)
    full_sign = (-1)**len(primes)
    punctured = sum(m for d,m,t in high if d<n)
    if should_pass:
        if any(pair != [0, 0] for pair in moments):
            raise ArithmeticError("a complete divisor half retained a low-order moment")
        if direct != factored or punctured != -full_sign:
            raise ArithmeticError("exact factorization or signed punctured endpoint failed")
    else:
        if sum(m for _, m, _ in low) != -2 or direct == factored:
            raise ArithmeticError("the missing-gap negative control falsely passed")
    return dict(n=str(n),native_cutoff=str(upper),whole_shell_start=str(lower),
                roughness=y,small_primes=small,large_primes=[str(p) for p in large],
                mobius=full_sign,half_divisors=len(low),middle_divisors=len(near),
                both_halves_are_unions_of_cubes=cubed,
                max_absolute_monomials_by_degree_for_each_half=moments,
                lower_mobius_sum=sum(m for d,m,t in low),
                upper_punctured_sum=punctured,exact_rational_factorization=direct==factored)


def calculate():
    """Check two genuine complete divisor cubes and a vertex where the gap fails."""
    certificates = proth_primes(3)
    large = [p for p, _, _, _ in certificates]
    small = small_primes(3)
    cases = [check(small[:2], large, True), check(small, large, True),
             check(small[:1], large[:2], False)]
    return dict(scope="Three individual genuine rough labels in whole terminal shells. The chosen "
                      "small primes test the finite cube identity. No execution of the asymptotic "
                      "selector or uniform theorem.",
                prime_certificates=[dict(prime=str(p), k=k, m=m, witness=w)
                                    for p, k, m, w in certificates],
                cases=cases)


if __name__ == "__main__":
    replay("DIVISOR_HALVES_EXACT.json", calculate)
