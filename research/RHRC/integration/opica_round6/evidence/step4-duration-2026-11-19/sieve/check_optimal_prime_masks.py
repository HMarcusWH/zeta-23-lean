"""Finite extremal and genuine-mask checks; the asymptotic all-mask proof is analytic."""

import json
from hashlib import sha256
from math import cos, isqrt, pi
from pathlib import Path

import numpy as np


def coefficients(k):
    omega = pi/(k+2)
    v = np.sin(omega*np.arange(1, k+2))
    r = np.correlate(v, v, "full")[k:]
    return r[1:]/r[1], omega, v, r[1]


def extremal_checks():
    errors = []
    for k in range(1, 31):
        a, omega, v, r1 = coefficients(k)
        # The sine polynomial vanishes at exp(3 i omega), including k=1.
        windows = np.array([3*omega, 0, omega, 0.79, 6.1])
        square = abs(np.exp(1j*np.outer(windows, np.arange(k+1))) @ v)**2/(2*r1)
        poly = 1/(2*cos(omega)) + np.cos(np.outer(windows, np.arange(1, k+1))) @ a
        err = max(float(max(abs(poly-square))), float(abs(poly[0])))
        assert err < 1e-12
        errors.append(err)
    return max(errors)


def prime_table(top):
    bits = bytearray([1])*(top+1)
    bits[:2] = b"\0\0"
    for q in range(2, isqrt(top)+1):
        if bits[q]:
            bits[q*q::q] = bytes((top-q*q)//q+1)
    return np.flatnonzero(np.frombuffer(bits, dtype=np.uint8))


def mask_check(p, primes):
    base = primes[primes < p].astype(float)
    assert p in primes
    slab = primes[(primes >= p**1.75) & (primes <= p*p)]
    a, _, _, _ = coefficients(2)
    weights = a[1]*slab.astype(float)**(-0.25)
    weights_sum = np.cumsum(weights)
    counts = np.floor(weights_sum)
    selected = slab[np.diff(counts, prepend=0) > 0]
    assert int(counts[-1]) == len(selected)
    assert np.min(counts-weights_sum) >= -1
    assert np.max(counts-weights_sum) <= 0
    ell = np.log(p)
    base_mass = sum(base**(-0.5))
    extra_mass = sum(selected.astype(float)**(-0.5))
    # Evaluate the actual modulus at finitely many scaled frequencies.
    grid = np.linspace(0, 6*pi, 257)
    def scores(qs):
        logs = np.log(qs)
        z = qs.astype(float)**(-0.5)
        return np.array([np.sum(np.log1p(z*z - 2*z*np.cos(x*logs/ell)))/2
                         for x in grid])
    base_scores = scores(base)
    added_scores = scores(selected)
    return dict(p=p, selected=len(selected),
                normalization_A=base_mass, extra_mass_over_A=extra_mass/base_mass,
                base_grid_max_at=float(grid[np.argmax(base_scores)]),
                new_grid_max_at=float(grid[np.argmax(base_scores+added_scores)]),
                sampled_base_log_modulus_over_A=max(base_scores)/base_mass,
                sampled_new_log_modulus_over_A=max(base_scores+added_scores)/base_mass)


if __name__ == "__main__":
    cases = (503, 1009, 3163)
    primes = prime_table(max(cases)**2)
    result = dict(degrees_checked=30, max_extremal_identity_error=extremal_checks(),
                  cases=[mask_check(p, primes) for p in cases],
                  scope="Floating-point finite diagnostics of deterministic layer-2 masks and sine polynomial identities. No global integration, rigorous rounding certificate, or independent Step 4 closure.",
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    print(json.dumps(result, indent=2))
