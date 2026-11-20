"""Exact pair accounting on two native base cells before any adaptive matching."""

from collections import Counter
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from math import gcd, isqrt
from pathlib import Path

from receipt import replay

NATIVE_SOURCE = Path(__file__).resolve().parents[2] / "cone_parity.py"
module_spec = spec_from_file_location("native_cone", NATIVE_SOURCE)
native = module_from_spec(module_spec)
module_spec.loader.exec_module(native)


def native_source_digest():
    """SHA-256 of the exact native vertex-generator source with LF line endings."""
    return sha256(NATIVE_SOURCE.read_text(encoding="utf-8").encode("utf-8")).hexdigest()


def complete_cell(x):
    """First full base in the highest occupied dyadic shell with a full base."""
    jx = x.bit_length() - 1
    s = isqrt(jx) + (isqrt(jx)**2 < jx)
    for j in range(jx, s - 1, -1):
        h = 1 << (j - s)
        low = max(native.first_terminal(x), 1 << j)
        start = ((low + h - 1) // h) * h
        if start + h <= min(x + 1, 1 << (j + 1)):
            return start, start + h
    raise ValueError("no complete base cell")


def independently_factor(n):
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def pair_accounting(rows, x):
    """Compare signed ordered incidence with cofactor counts and divisor inversion."""
    fibre = Counter()
    divisor_charge = Counter()
    divisor_size = Counter()
    divisor_sign = {}
    for n, sign, m, factors in rows:
        fibre[m] += 1
        terms = [(1, 1)]
        for p in factors:
            terms += [(d*p, -v) for d, v in terms]
        for d, mu in terms:
            divisor_charge[d] += sign
            divisor_size[d] += 1
            divisor_sign[d] = mu

    total = sum(sign for _, sign, _, _ in rows)**2 - len(rows)
    if not 1 < x < 2**100:
        raise ValueError("the divisor-inversion verification is for native D<2")
    primitive_total = sum(mu * (divisor_charge[d]**2 - divisor_size[d])
                          for d, mu in divisor_sign.items())
    same = sum(k*(k-1) for k in fibre.values())
    same_primitive = sum(k*(k-1) for m, k in fibre.items() if m**100 < x)
    direct = Counter()
    for i, (n, sign, m, _) in enumerate(rows):
        for r, other_sign, other_m, _ in rows[:i]:
            g = gcd(n, r)
            if m == other_m and (g != m or sign * other_sign != 1):
                raise ArithmeticError("same-cofactor Möbius sign or GCD failed")
            # g^100<x iff g=1 over these explicitly checked horizons.
            direct["same" if m == other_m else "different"] += 2*sign*other_sign
            if g == 1:
                key = "same_primitive" if m == other_m else "different_primitive"
                direct[key] += 2*sign*other_sign
    expected = dict(same=same, different=total-same, same_primitive=same_primitive,
                    different_primitive=primitive_total-same_primitive)
    if any(direct[k] != v for k, v in expected.items()):
        raise ArithmeticError("direct pair enumeration disagrees with inversion")
    return dict(labels=len(rows), cofactor_fibres=len(fibre),
                positive_labels=sum(row[1] > 0 for row in rows),
                ordered_pairs=len(rows)*(len(rows)-1), **expected)


def check(x):
    lo, hi = complete_cell(x)
    y = (x-1).bit_length()**2
    rows = []
    for n, sign, cone, *_ in native.vertex_rows(x, 1):
        if lo <= n < hi:
            factors = independently_factor(n)
            m = n // factors[-1]
            if (min(factors) <= y or len(set(factors)) != len(factors)
                    or sign != (-1)**len(factors) or cone != (m == 1)):
                raise ArithmeticError("factorization disagrees with source vertex")
            rows.append((n, sign, m, factors))
    nonprime = [r for r in rows if r[2] > 1]
    return dict(X=x, y=y, base_cell=[lo, hi], base_right_open=True,
                full_rough_source=pair_accounting(rows, x),
                deterministic_composite_only=pair_accounting(nonprime, x))


def calculate():
    """Enumerate all ordered pairs on two genuine preselection cells."""
    return dict(scope="Finite exact preselection. The composite-only restriction excludes "
                      "ordinary primes without matching. These horizons have D<2 and are "
                      "outside the asymptotic protected-cofactor regime.",
                native_generator_sha256_lf=native_source_digest(),
                results=[check(x) for x in (1049155, 1656575)])


if __name__ == "__main__":
    replay("SURVIVOR_COFACTOR_PAIRS_CHECK.json", calculate)
