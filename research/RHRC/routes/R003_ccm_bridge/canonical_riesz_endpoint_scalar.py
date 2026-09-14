#!/usr/bin/env python3
"""Exact Lean-normalized executable for the FB-05 Riesz endpoint scalar.

The Lean object is

    canonicalPolePrimeRieszEndpointScalar L r
      = (1 / L)^(r+1) * canonicalPolePrimeRieszPrimitive L (r+1) L.

For a fixed cutoff cell log(Q) < L < log(Q+1), the endpoint primitive has
the finite convolution form

    P_n(L) = P_n^pole(L)
      - sum_{q <= Q} Lambda(q)/sqrt(q) * (L-log(q))^n / n!,

where q runs over every integer with nonzero von Mangoldt weight, hence over
prime powers, not only primes.

This module is discovery/certification infrastructure.  It has no theorem or
RH-promotion authority.
"""
from __future__ import annotations

import math
from functools import lru_cache

import mpmath as mp
import sympy as sp
from flint import arb

from canonical_source_arb import (
    ball_record,
    definitely_negative,
    definitely_positive,
    fixed_cell_membership,
    set_precision,
    to_arb_rational,
)


@lru_cache(maxsize=None)
def prime_power_events(Q: int) -> tuple[tuple[int, int], ...]:
    """Return sorted (q,p) with q=p^k<=Q and Lambda(q)=log(p)."""
    if Q < 1:
        raise ValueError("require Q>=1")
    out: list[tuple[int, int]] = []
    for p in sp.primerange(2, Q + 1):
        q = int(p)
        while q <= Q:
            out.append((q, int(p)))
            q *= int(p)
    out.sort()
    return tuple(out)


def cell_bounds_mp(Q: int) -> tuple[mp.mpf, mp.mpf]:
    if Q < 1:
        raise ValueError("require Q>=1")
    return mp.log(Q), mp.log(Q + 1)


def dyadic_inside_cell(
    Q: int,
    position: float | mp.mpf,
    bits: int = 48,
) -> tuple[int, int]:
    """Deterministic exact dyadic at relative position 0<position<1 in a cell."""
    pos = mp.mpf(position)
    if not (0 < pos < 1):
        raise ValueError("require 0<position<1")
    lo, hi = cell_bounds_mp(Q)
    target = lo + pos * (hi - lo)
    den = 1 << bits
    num = int(mp.nint(target * den))
    while mp.mpf(num) / den <= lo:
        num += 1
    while mp.mpf(num) / den >= hi:
        num -= 1
    return num, den


def _mp_taylor_partial_even(z: mp.mpf, m: int) -> mp.mpf:
    return mp.fsum(z ** (2 * j) / mp.factorial(2 * j) for j in range(m + 1))


def _mp_taylor_partial_odd(z: mp.mpf, m: int) -> mp.mpf:
    return mp.fsum(z ** (2 * j + 1) / mp.factorial(2 * j + 1) for j in range(m))


def pole_endpoint_primitive_mp(primitive_order: int, L: mp.mpf) -> mp.mpf:
    """n-fold left-anchored primitive of 4*sinh(t/2), evaluated at L."""
    n = int(primitive_order)
    if n < 1:
        raise ValueError("primitive_order must be >=1")
    L = mp.mpf(L)
    z = L / 2
    scale = mp.mpf(2) ** (n + 2)
    if n % 2:
        m = (n - 1) // 2
        return scale * (mp.cosh(z) - _mp_taylor_partial_even(z, m))
    m = n // 2
    return scale * (mp.sinh(z) - _mp_taylor_partial_odd(z, m))


def prime_endpoint_primitive_mp(
    primitive_order: int,
    Q: int,
    L: mp.mpf,
) -> mp.mpf:
    """n-fold endpoint primitive of the finite von-Mangoldt staircase."""
    n = int(primitive_order)
    if n < 1:
        raise ValueError("primitive_order must be >=1")
    L = mp.mpf(L)
    fact = mp.factorial(n)
    return mp.fsum(
        (mp.log(p) / mp.sqrt(q)) * (L - mp.log(q)) ** n / fact
        for q, p in prime_power_events(Q)
    )


def pole_prime_endpoint_primitive_mp(
    primitive_order: int,
    Q: int,
    L: mp.mpf,
) -> mp.mpf:
    return pole_endpoint_primitive_mp(primitive_order, L) - prime_endpoint_primitive_mp(
        primitive_order, Q, L
    )


def canonical_riesz_endpoint_scalar_mp(
    riesz_order: int,
    Q: int,
    L: mp.mpf,
) -> mp.mpf:
    """Exact fixed-cell arithmetic normal form of the Lean endpoint scalar."""
    r = int(riesz_order)
    if r < 0:
        raise ValueError("riesz_order must be nonnegative")
    L = mp.mpf(L)
    if not L > 0:
        raise ValueError("require L>0")
    n = r + 1
    return pole_prime_endpoint_primitive_mp(n, Q, L) / (L ** n)


def canonical_riesz_eight_endpoint_scalar_mp(Q: int, L: mp.mpf) -> mp.mpf:
    return canonical_riesz_endpoint_scalar_mp(8, Q, L)


def pole_endpoint_primitive_nine_expanded_mp(L: mp.mpf) -> mp.mpf:
    """Independent expanded order-nine pole formula used by the plumbing check."""
    L = mp.mpf(L)
    return (
        2048 * (mp.cosh(L / 2) - 1)
        - 256 * L**2
        - mp.mpf(16) / 3 * L**4
        - mp.mpf(2) / 45 * L**6
        - L**8 / 5040
    )


def _arb_taylor_partial_even(z: arb, m: int) -> arb:
    total = arb(0)
    for j in range(m + 1):
        total += z ** (2 * j) / math.factorial(2 * j)
    return total


def _arb_taylor_partial_odd(z: arb, m: int) -> arb:
    total = arb(0)
    for j in range(m):
        total += z ** (2 * j + 1) / math.factorial(2 * j + 1)
    return total


def pole_endpoint_primitive_arb(primitive_order: int, L: arb) -> arb:
    n = int(primitive_order)
    if n < 1:
        raise ValueError("primitive_order must be >=1")
    z = L / 2
    scale = arb(2) ** (n + 2)
    if n % 2:
        m = (n - 1) // 2
        return scale * (z.cosh() - _arb_taylor_partial_even(z, m))
    m = n // 2
    return scale * (z.sinh() - _arb_taylor_partial_odd(z, m))


def prime_endpoint_primitive_arb(primitive_order: int, Q: int, L: arb) -> arb:
    n = int(primitive_order)
    if n < 1:
        raise ValueError("primitive_order must be >=1")
    total = arb(0)
    fact = math.factorial(n)
    for q, p in prime_power_events(Q):
        logp = arb(p).log()
        logq = arb(q).log()
        total += (logp / arb(q).sqrt()) * (L - logq) ** n / fact
    return total


def pole_prime_endpoint_primitive_arb(
    primitive_order: int,
    Q: int,
    L: arb,
) -> arb:
    return pole_endpoint_primitive_arb(primitive_order, L) - prime_endpoint_primitive_arb(
        primitive_order, Q, L
    )


def canonical_riesz_endpoint_scalar_arb(
    riesz_order: int,
    Q: int,
    L: arb,
) -> arb:
    r = int(riesz_order)
    if r < 0:
        raise ValueError("riesz_order must be nonnegative")
    n = r + 1
    return (arb(1) / L) ** n * pole_prime_endpoint_primitive_arb(n, Q, L)


def sign_classification_arb(x: arb) -> str:
    if definitely_positive(x):
        return "POSITIVE"
    if definitely_negative(x):
        return "NEGATIVE"
    return "CONTAINS_ZERO"


def endpoint_record_mp(riesz_order: int, Q: int, L: mp.mpf) -> dict:
    r = int(riesz_order)
    n = r + 1
    pole = pole_endpoint_primitive_mp(n, L)
    prime = prime_endpoint_primitive_mp(n, Q, L)
    margin = pole - prime
    scalar = margin / mp.mpf(L) ** n
    cancellation = mp.inf if margin == 0 else (abs(pole) + abs(prime)) / abs(margin)
    return {
        "Q": int(Q),
        "riesz_order": r,
        "primitive_order": n,
        "L": mp.nstr(L, 50),
        "pole_primitive": mp.nstr(pole, 50),
        "prime_primitive": mp.nstr(prime, 50),
        "pole_prime_primitive": mp.nstr(margin, 50),
        "endpoint_scalar": mp.nstr(scalar, 50),
        "endpoint_scalar_float": float(scalar),
        "cancellation_ratio": "inf" if mp.isinf(cancellation) else mp.nstr(cancellation, 30),
        "sign": "POSITIVE" if scalar > 0 else ("NEGATIVE" if scalar < 0 else "ZERO"),
    }


def endpoint_record_arb(
    riesz_order: int,
    Q: int,
    L_num: int,
    L_den: int,
    precision_bits: int = 320,
) -> dict:
    set_precision(precision_bits)
    L = to_arb_rational(int(L_num), int(L_den))
    cell = fixed_cell_membership(int(Q), L)
    n = int(riesz_order) + 1
    pole = pole_endpoint_primitive_arb(n, L)
    prime = prime_endpoint_primitive_arb(n, int(Q), L)
    margin = pole - prime
    scale = (arb(1) / L) ** n
    scalar = scale * margin
    return {
        "Q": int(Q),
        "L_num": int(L_num),
        "L_den": int(L_den),
        "riesz_order": int(riesz_order),
        "primitive_order": n,
        "precision_bits": int(precision_bits),
        "cell": cell,
        "pole_primitive": ball_record(pole),
        "prime_primitive": ball_record(prime),
        "pole_prime_primitive": ball_record(margin),
        "normalization_scale": ball_record(scale),
        "endpoint_scalar": ball_record(scalar),
        "sign_classification": sign_classification_arb(scalar),
    }
