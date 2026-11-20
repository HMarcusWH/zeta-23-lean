"""Check the finite grouping identity exactly and sample genuine finite Euler resonances."""

from hashlib import sha256
import json
from math import cos, isqrt, log, pi
from pathlib import Path

import numpy as np


def prime_table(limit):
    table = bytearray([1]) * (limit + 1)
    table[:2] = b"\0\0"
    for m in range(2, isqrt(limit) + 1):
        if table[m]:
            table[m * m::m] = bytes((limit - m * m) // m + 1)
    return table


def check_pairings():
    # At one time use U(t-log k) = sqrt(k) g(k), so all grouped energies
    # and cross terms are integers. This part checks algebra, not the source.
    cap = 853
    primes = [i for i, flag in enumerate(prime_table(cap)) if flag]
    mu = [1] * (cap + 1)
    for p in primes:
        for k in range(p, cap + 1, p):
            mu[k] *= -1
        for k in range(p*p, cap + 1, p*p):
            mu[k] = 0
    g = lambda k: (k*k + 5*k + 3) % 23 - 11 if k <= cap else 0

    def components(mask):
        divisors = [(1, 1)]
        for q in mask:
            divisors += [(d*q, -sgn) for d, sgn in divisors if d*q <= cap]
        return [0] + [mu[k] * sum(sgn*g(k*d) for d, sgn in divisors)
                      if all(k % q for q in mask) else 0
                      for k in range(1, cap + 1)]

    count = 0
    for mask in [(), (2,), (3, 7), (2, 3, 5, 7), (2, 13, 19)]:
        old = components(mask)
        for p in [q for q in primes[:13] if q not in mask]:
            new = components((*mask, p))
            assert sum(old) == sum(new)
            diff = sum(c*c for c in new) - sum(c*c for c in old)
            edge = 2*sum(old[k]*old[p*k] for k in range(1, cap//p + 1) if k % p)
            assert diff == edge
            count += 1
    return count


def local_max(logprimes, z, lo, hi):
    def score(t):
        return float(np.sum(np.log1p(z*z - 2*z*np.cos(t*logprimes))))/2
    # First sample a grid within the requested band, then refine only
    # its highest sampled cell. This supplies no all-frequency bound.
    grid = np.linspace(lo, hi, 25)
    best = max(range(25), key=lambda i: score(grid[i]))
    a, b = grid[max(0, best-1)], grid[min(24, best+1)]
    for _ in range(28):
        t, w = (2*a+b)/3, (a+2*b)/3
        if score(t) < score(w):
            a = t
        else:
            b = w
    t = (a+b)/2
    return t, score(t)


def sample(p, table):
    assert table[p]
    qs = np.flatnonzero(np.frombuffer(table, dtype=np.uint8)[:p]).astype(float)
    ell = log(p)
    lp = np.log(qs)
    z = 1/np.sqrt(qs)
    avg = float(np.sum(z*(ell - lp))/np.sum(z))
    peaks = []
    for k in (1, 3):
        left = (k-0.75)*pi/ell
        right = (k+0.75)*pi/ell
        peaks.append(local_max(lp, z, left, right))
    first, third = peaks
    assert first[1] > third[1]
    assert cos(first[0]*ell) < 0 < cos(first[0]*2*ell)
    return dict(p=p, prime_count=len(qs), h=0.5, first_peak=first[0],
                first_log_euler=first[1], third_log_euler=third[1],
                weighted_mean_log_p_over_q=avg,
                phase_at_first_peak=first[0]*ell,
                phase_prediction=pi*ell/(ell-avg),
                cosine_at_log_p=cos(first[0]*ell),
                cosine_at_log_p_squared=cos(2*first[0]*ell))


if __name__ == "__main__":
    cases = (100_003, 1_000_003, 10_000_019)
    table = prime_table(max(cases))
    results = dict(exact_algebraic_cases=check_pairings(),
                   samples=[sample(p, table) for p in cases],
                   sample_scope="Undamped finite Euler products sampled in two positive frequency bands. No source-weighted frequency integration or cofinal verification.",
                   script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    print(json.dumps(results, indent=2))
