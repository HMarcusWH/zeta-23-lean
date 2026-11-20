"""Exact finite checks of the smooth-divisor convolution for rough Möbius sums."""

import hashlib
import json
from math import isqrt
from pathlib import Path

import flint
from flint import fmpz


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def primes_through(limit):
    cells = bytearray([1]) * (limit + 1)
    cells[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if cells[p]:
            cells[p*p::p] = bytes((limit - p*p)//p + 1)
    return [i for i in range(2, limit + 1) if cells[i]]


def rough_mask(low, high, primes):
    mask = bytearray([1]) * (high - low)
    for p in primes:
        start = (-low-1) % p
        if start < len(mask):
            mask[start::p] = bytes((len(mask)-start-1)//p + 1)
    return mask


def scaled_sieve():
    limit = 32768
    primes = primes_through(limit)
    mu = [1] * (limit + 1)
    for p in primes:
        for n in range(p, limit + 1, p):
            mu[n] *= -1
        for n in range(p*p, limit + 1, p*p):
            mu[n] = 0
    results = []
    last = None
    for cutoff in (1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 22, 23, 24, 28, 29):
        small = [p for p in primes if p <= cutoff]
        mask = rough_mask(0, limit, small)
        direct = [0] + [mask[n-1]*mu[n] for n in range(1, limit+1)]
        smooth = [1]
        for p in small:
            previous = smooth.copy()
            power = p
            while power <= limit:
                smooth.extend(d*power for d in previous if d <= limit//power)
                power *= p
        convolution = [0] * (limit + 1)
        squarefree_only = [0] * (limit + 1)
        for d in smooth:
            squarefree = mu[d] != 0
            for k in range(1, limit//d + 1):
                convolution[k*d] += mu[k]
                if squarefree:
                    squarefree_only[k*d] += mu[k]
        require(direct == convolution, f'scaled coefficient mismatch at cutoff {cutoff}')
        wrong = [n for n in range(1, limit+1) if squarefree_only[n] != direct[n]]
        if cutoff >= 2:
            require(wrong and wrong[0] == 4, 'missing repeated-factor negative control')
        results.append({'cutoff': cutoff, 'tested_integers': limit, 'smooth_divisors': len(smooth),
                        'signed_sum': sum(direct), 'squarefree_only_wrong': len(wrong),
                        'first_squarefree_only_wrong': wrong[0] if wrong else None,
                        'changed_since_previous_cutoff': None if last is None else
                        sum(a != b for a,b in zip(last,direct))})
        last = direct
    return results


def literal_divisor_sum(r, cutoff):
    factors = [(int(p), int(e)) for p,e in fmpz(r).factor() if p <= cutoff]
    divisors = [1]
    for p,e in factors:
        divisors = [d*p**j for d in divisors for j in range(e+1)]
    return sum(int(fmpz(r//d).moebius_mu()) for d in divisors)


def actual_window():
    cutoff = 10**7
    primes = primes_through(cutoff + 100)
    initial = [p for p in primes if p > cutoff][:2]
    p,q = initial
    small = [v for v in primes if v <= cutoff]
    center = p*q
    rows = []
    for low,high in [(center-50001,center-1), (center-1,center+50000)]:
        mask = rough_mask(low,high,small)
        values = bytearray()
        for i,kept in enumerate(mask, start=low+1):
            direct = int(fmpz(i).moebius_mu()) if kept else 0
            convolution = literal_divisor_sum(i, cutoff)
            require(direct == convolution, f'actual coefficient mismatch at {i}')
            values.append(direct+1)
        pos, zero, neg = values.count(2), values.count(1), values.count(0)
        rows.append({'low_exclusive': low, 'high_inclusive': high, 'positive': pos,
                     'negative': neg, 'zero': zero, 'total': high-low, 'signed_sum': pos-neg,
                     'sha256_coefficient_plus_one_bytes': hashlib.sha256(values).hexdigest()})
    require([r['signed_sum'] for r in rows] == [-1499, -1532], 'historical window disagreement')
    # Points actually at a cutoff or a repeated factor; masks use the strict > convention.
    points = [1, p, q, p*p, p*q, q*q, 2*p*q, p*p*q]
    grid = {}
    for bound in [cutoff, p-1, p, q-1, q]:
        signs = [literal_divisor_sum(r,bound) for r in points]
        expected = [1, -int(p>bound), -int(q>bound), 0, int(p>bound and q>bound), 0, 0, 0]
        require(signs == expected, f'actual threshold control failed at {bound}')
        grid[bound] = signs
    return {'cutoff': cutoff, 'first_primes_after_cutoff': initial, 'first_rough_squarefree_composite': center,
            'windows': rows, 'edge_case_integers': points, 'signs_by_cutoff': grid}


if __name__ == '__main__':
    receipt = {
        'qualification': 'Finite exact checks of coefficients and interval sums. These are not evidence for a uniform asymptotic estimate.',
        'identity': 'mu(r)*1[Pminus(r)>Q] = sum_{d|r, Pplus(d)<=Q} mu(r/d); Pminus(1)=infinity; d=1 is included.',
        'scaled': scaled_sieve(), 'actual_fixed_Y': actual_window(),
        'scopes': 'Scaled rows use fixed small integer cutoffs; actual rows use the native fixed cutoff 10000000 plus strict-boundary spot controls. Neither substitutes a finite cutoff for the growing sequence in the proof.',
        'python_flint': flint.__version__, 'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    destination = Path(__file__).with_name('ROUGH_CONVOLUTION_CHECKS.json')
    destination.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print('All exact coefficient and cutoff checks passed.')
