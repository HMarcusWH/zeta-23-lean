"""Certify finite Schoenfeld comparisons at m^4 using exact counts and Arb balls.

Run with Python 3.10+ and python-flint 0.9.0. The JSON is written next to this file.
"""

import hashlib
import json
from math import isqrt
from pathlib import Path

import flint
from flint import arb, ctx


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def segmented_counts(points):
    """Count primes <= each sorted integer endpoint, including the prime 2."""
    limit = points[-1]
    root = isqrt(limit)
    base = bytearray([1]) * (root + 1)
    base[:2] = bytes(2)
    for p in range(2, isqrt(root) + 1):
        if base[p]:
            base[p * p::p] = bytes((root - p * p) // p + 1)
    primes = [p for p in range(3, root + 1, 2) if base[p]]
    next_point = 0
    total = 1
    result = {}
    # Each segment contains consecutive odd candidates, starting at low.
    for low in range(3, limit + 1, 2**21):
        high = min(limit, low + 2**21 - 1)
        size = (high - low) // 2 + 1
        odd = bytearray([1]) * size
        for p in primes:
            if p * p > high:
                break
            first = max(p * p, low + (-low) % p)
            if first % 2 == 0:
                first += p
            if first <= high:
                start = (first - low) // 2
                odd[start::p] = bytes((size - start - 1) // p + 1)
        offset = 0
        while next_point < len(points) and points[next_point] <= high:
            end = max(0, (points[next_point] - low) // 2 + 1)
            total += odd.count(1, offset, end)
            result[points[next_point]] = total
            offset = end
            next_point += 1
        total += odd.count(1, offset)
    require(next_point == len(points), 'incomplete sieve')
    return result


def quotient_prime_count(n):
    """Independent count by the Legendre sieve on distinct floor(n/i) values."""
    root = isqrt(n)
    large = [n // i for i in range(1, root + 1)]
    values = large + list(range(large[-1] - 1, 0, -1))
    count = {v: v - 1 for v in values}
    for p in range(2, root + 1):
        previous = count[p - 1]
        if count[p] == previous:
            continue
        for v in values:
            if v < p * p:
                break
            count[v] -= count[v // p] - previous
    return count[n]


def unique_extreme(pairs, *, maximum):
    key, value = pairs[0]
    for candidate, other in pairs[1:]:
        if (other > value) if maximum else (other < value):
            key, value = candidate, other
        else:
            require((other < value) if maximum else (other > value), 'overlapping comparison balls')
    return {'m': key, 'certified_ball': value.str(24)}


def compute():
    ctx.prec = 256
    first, last = 8, 128
    # These standard decimal values exercise endpoints unrelated to the quartic sequence.
    decimal = {10: 4, 100: 25, 1000: 168, 10000: 1229, 100000: 9592,
               1000000: 78498, 10000000: 664579, 100000000: 5761455}
    points = sorted(set(decimal) | {m**4 for m in range(first, last + 1)})
    counts = segmented_counts(points)
    require(all(counts[n] == count for n, count in decimal.items()), 'decimal count mismatch')
    independent = {m: quotient_prime_count(m**4) for m in (8, 9, 16, 32, 64, 100, 127, 128)}
    require(all(counts[m**4] == c for m, c in independent.items()), 'independent count mismatch')
    signed_ratios, lower_slacks, upper_slacks, rows = [], [], [], []
    for m in range(first, last + 1):
        x = m**4
        ax = arb(x)
        li = ax.li(offset=False)
        require(li.overlaps(ax.log().ei()), 'li and Ei(log x) disagree')
        difference = arb(counts[x]) - li
        bound = arb(m*m) * ax.log() / (8 * arb.pi())
        ratio = difference / bound
        lower, upper = bound + difference, bound - difference
        require(lower > 0 and upper > 0, f'uncertified Schoenfeld bound at {m}')
        signed_ratios.append((m, ratio))
        lower_slacks.append((m, lower))
        upper_slacks.append((m, upper))
        rows.append({'m': m, 'x': x, 'prime_count': counts[x], 'pi_minus_li': difference.str(24),
                     'schoenfeld_bound': bound.str(24), 'signed_ratio': ratio.str(24)})
    theorem_lower = 2657
    theorem_upper = 1101 * 10**23
    end = isqrt(isqrt(theorem_upper))
    require((first-1)**4 < theorem_lower <= first**4, 'invalid lower theorem breakpoint')
    require(end**4 <= theorem_upper < (end+1)**4, 'invalid upper theorem breakpoint')
    return {
        'qualification': 'Finite numerical certificate; the published finite interval is cited separately. The infinite tail and Step 4 are open.',
        'definition': 'Difference = pi(m^4)-li(m^4), li(x)=Ei(log(x)); bound = m^2 log(m^4)/(8 pi). Both strict one-sided inequalities certified by Arb.',
        'method': 'Integer segmented odd sieve. 256-bit Arb ball comparisons. Printed [midpoint +/- radius] values enclose the internal balls.',
        'python_flint': flint.__version__, 'arb_precision_bits': ctx.prec,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'first_m': first, 'last_m': last, 'quartic_counts_checked': len(rows),
        'decimal_crosschecks': decimal, 'independent_quotient_counts_by_m': independent,
        'min_signed_ratio': unique_extreme(signed_ratios, maximum=False),
        'max_signed_ratio': unique_extreme(signed_ratios, maximum=True),
        'min_lower_bound_slack': unique_extreme(lower_slacks, maximum=False),
        'min_upper_bound_slack': unique_extreme(upper_slacks, maximum=False),
        'johnston_corollary_3_3': {
            'source': 'https://doi.org/10.1007/s11139-022-00616-x',
            'x_lower_inclusive': theorem_lower, 'x_upper_inclusive': theorem_upper,
            'm_lower_inclusive': first, 'm_upper_inclusive': end,
            'last_grid_x': end**4, 'next_grid_m': end+1, 'next_grid_x': (end+1)**4,
            'qualification': 'External unconditional finite-range theorem. The finite computation here stops at last_m.'},
        'rows': rows}


if __name__ == '__main__':
    payload = compute()
    path = Path(__file__).with_name('QUARTIC_COUNTS.json')
    path.write_text(json.dumps(payload, indent=2) + '\n', encoding='utf-8')
    print(f"{payload['quartic_counts_checked']} strict two-sided tests passed; wrote {path.name}")
