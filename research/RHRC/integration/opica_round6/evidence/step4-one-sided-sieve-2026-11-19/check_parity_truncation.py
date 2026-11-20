"""Check the truncated native divisor polynomial and its full node accounting."""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations
import json
from math import comb, isqrt, prod
from pathlib import Path


def factor_squarefree(n):
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            if n % d == 0:
                return None
            factors.append(d)
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append(n)
    return factors


def check_polynomial(primes, m):
    n = prod(primes)
    divisors = {prod(block): len(block) for k in range(len(primes) + 1)
                for block in combinations(primes, k)}
    assert len(divisors) == 2 ** len(primes) and all(n % d == 0 for d in divisors)
    value = sum((-2) ** degree for degree in divisors.values() if degree <= m)
    r = len(primes)
    assert value == sum((-2) ** k * comb(r, k) for k in range(min(r, m) + 1))
    exact = (-1) ** r
    assert value >= exact
    if m >= r:
        assert value == exact
    if r == m + 1:
        assert value - exact == 2 ** (m + 1)
    return value - exact


def native_graph(x):
    jmax = x.bit_length() - 1
    s = isqrt(jmax) + (isqrt(jmax) ** 2 < jmax)
    y = (x - 1).bit_length() ** 2
    denominator = 1 << (jmax + max(jmax - s, 0))
    nodes = defaultdict(int)
    labels = []
    for n in range(2, x + 1):
        if n**100 <= x**99:
            continue
        factors = factor_squarefree(n)
        if not factors or factors[0] <= y:
            continue
        j = n.bit_length() - 1
        depth = max(0, j - s)
        excess = check_polynomial(factors, 0)
        assert check_polynomial(factors, 2) == 0
        labels.append((n, excess))
        for k in range(depth + 1):
            nodes[j, k, n >> (depth - k)] += excess
    node_total = sum((v*v) * (denominator >> (j + k)) for (j, k, _), v in nodes.items())
    edge_total = 0
    for n, en in labels:
        j = n.bit_length() - 1
        depth = max(0, j - s)
        for q, eq in labels:
            if n >> depth != q >> depth or q.bit_length() - 1 != j:
                continue
            same = depth + 1 - (n ^ q).bit_length()
            edge_total += en * eq * sum(denominator >> (j + k) for k in range(same))
    assert node_total == edge_total
    return {"cutoff": x, "native_y": y, "full_native_nonzero_labels": len(labels),
            "m0_weighted_squared_excess": str(Fraction(node_total, denominator)),
            "m2_weighted_squared_excess": "0", "independent_ordered_pair_check": True}


def constructed():
    # An exact genuine row at each cutoff, without enumerating its entire shell.
    pool = []
    p = 100003
    while len(pool) < 9:
        if factor_squarefree(p) == [p]:
            pool.append(p)
        p += 2
    rows = []
    for r in (1, 3, 5, 7, 9):
        primes = pool[:r]
        n = prod(primes)
        y = (n - 1).bit_length() ** 2
        assert min(primes) > y and n**100 > n**99
        rows.append({"native_cutoff_and_row": str(n), "native_y": y, "prime_factors": primes,
                     "m": r - 1, "exact_majorant_excess": check_polynomial(primes, r - 1)})
    return rows


if __name__ == "__main__":
    result = {"scope": "Exact finite divisor/direct-pair checks. Complete graphs for the two small "
                       "cutoffs; individual certified native rough rows for the large cutoffs. "
                       "The finite calculations do not establish an asymptotic estimate.",
              "complete_graphs": [native_graph(x) for x in (8192, 16384)],
              "large_individual_rows": constructed()}
    Path(__file__).with_name("PARITY_TRUNCATION_CHECK.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
