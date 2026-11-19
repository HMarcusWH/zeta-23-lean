"""Check signed rough-Möbius interval counts where the first squarefree composite enters."""
import json
from math import isqrt
from pathlib import Path


def sieve(end):
    flags = bytearray([1]) * (end + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(end) + 1):
        if flags[p]:
            flags[p * p::p] = bytes((end - p * p) // p + 1)
    return flags


def primes_between(low, high, flags):
    # low < k <= high. In both intervals low exceeds sqrt(high).
    assert 1 < isqrt(high) < low and isqrt(high) < len(flags)
    cells = bytearray([1]) * (high - low)
    for p in range(2, isqrt(high) + 1):
        if flags[p]:
            offset = -(low + 1) % p
            if offset < len(cells):
                cells[offset::p] = bytes((len(cells) - offset - 1) // p + 1)
    return sum(cells)


cutoff = 10**7
flags = sieve(cutoff + 100)
p, q = [k for k in range(cutoff + 1, len(flags)) if flags[k]][:2]
center = p * q
window = 50000
assert center - window - 1 > p*p
assert center + window < min(q*q, p*(q+1), p**3)
rows = []
for low, high in [(center-window-1, center-1), (center-1, center+window)]:
    primes = primes_between(low, high, flags)
    semiprimes = int(low < center <= high)
    rows.append(dict(low_exclusive=low, high_inclusive=high, primes=primes,
                     squarefree_composites=semiprimes, signed_count=semiprimes-primes))
assert [r["signed_count"] for r in rows] == [-1499, -1532]
data = dict(qualification="Exact finite rough-Mobius counts on two short intervals at "
            "the first squarefree composite above the fixed cutoff. No cofinal bound.",
            least_prime_factor_strictly_above=cutoff, first_two_primes=[p,q],
            first_squarefree_composite=center, intervals=rows)
Path(__file__).with_name("FIRST_ROUGH_COMPOSITE.json").write_text(
    json.dumps(data,indent=2)+"\n", encoding="utf8")
print(rows)
