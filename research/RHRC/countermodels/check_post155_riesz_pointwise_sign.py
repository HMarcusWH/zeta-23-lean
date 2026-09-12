#!/usr/bin/env python3
"""Exact regression for the post-#155 Riesz pointwise-sign countermodels.

This checker uses only integer/rational arithmetic.  It evaluates the odd
source-coordinate derivatives directly from the production real source-entry
formula in `Zeta23/CCM/DictionaryAnalysis.lean` at omega = 0 and omega = 1/4.

For odd k we normalize by the positive factor

    2 * (2*pi)^(k-1).

At omega = 1/4 the remaining exact value has the form a + b*pi.  We represent
that form as a pair of `Fraction`s; no floating-point trigonometry or numerical
approximation is used.

These fixtures falsify only the proposed pointwise fixed-sign smoothed-integrand
mechanism.  They are not zeta counterexamples and do not contradict the #155
Riesz identity.  RH remains OPEN.
"""

from __future__ import annotations

from fractions import Fraction

Pair = tuple[Fraction, Fraction]  # a + b*pi


def sin_pi_over_2_multiple(q: int) -> int:
    """Exact sin(q*pi/2) in {0, +/-1}."""
    return (0, 1, 0, -1)[q % 4]


def cos_pi_over_2_multiple(q: int) -> int:
    """Exact cos(q*pi/2) in {0, +/-1}."""
    return (1, 0, -1, 0)[q % 4]


def pair_add(x: Pair, y: Pair) -> Pair:
    return (x[0] + y[0], x[1] + y[1])


def pair_scale(q: Fraction, x: Pair) -> Pair:
    return (q * x[0], q * x[1])


def normalized_entry_odd_derivative(n: int, m: int, k: int, *, quarter: bool) -> Pair:
    """Return D^k sourceEntryReal / (2*(2*pi)^(k-1)) for odd k.

    Production source entry:

      n != m:
        [sin(2*pi*n*w)-sin(2*pi*m*w)] / [pi*(n-m)]

      n == m:
        2*w*cos(2*pi*n*w).

    At w=0 or 1/4 and odd k, exact trig values are rational.  The diagonal
    product-rule term at w=1/4 contributes the optional pi coefficient.
    """
    if k <= 0 or k % 2 == 0:
        raise ValueError("k must be a positive odd derivative order")

    if n != m:
        if quarter:
            sn = sin_pi_over_2_multiple(n + k)
            sm = sin_pi_over_2_multiple(m + k)
        else:
            sn = sin_pi_over_2_multiple(k)
            sm = sin_pi_over_2_multiple(k)
        return (Fraction(n**k * sn - m**k * sm, n - m), Fraction(0))

    if quarter:
        ck = cos_pi_over_2_multiple(n + k)
        ckm1 = cos_pi_over_2_multiple(n + k - 1)
        # [d^k 2*w*cos(2*pi*n*w)] / [2*(2*pi)^(k-1)]
        # = k*n^(k-1)*cos((n+k-1)pi/2)
        #   + (pi/2)*n^k*cos((n+k)pi/2).
        return (
            Fraction(k * n ** (k - 1) * ckm1),
            Fraction(n**k * ck, 2),
        )

    ckm1 = cos_pi_over_2_multiple(k - 1)
    return (Fraction(k * n ** (k - 1) * ckm1), Fraction(0))


def normalized_energy_odd_derivative(u: tuple[int, ...], k: int, *, quarter: bool) -> Pair:
    """Exact normalized kth derivative of the quadratic source energy."""
    if len(u) % 2 != 1:
        raise ValueError("fixture must use a centered odd-length grid")
    N = (len(u) - 1) // 2
    ns = range(-N, N + 1)
    total: Pair = (Fraction(0), Fraction(0))
    for i, n in enumerate(ns):
        for j, m in enumerate(ns):
            entry = normalized_entry_odd_derivative(n, m, k, quarter=quarter)
            total = pair_add(total, pair_scale(Fraction(u[i] * u[j]), entry))
    return total


def moment(u: tuple[int, ...], r: int) -> int:
    N = (len(u) - 1) // 2
    return sum(coeff * (n**r) for coeff, n in zip(u, range(-N, N + 1)))


def assert_boundary_flat(u: tuple[int, ...]) -> None:
    assert moment(u, 0) == 0
    assert moment(u, 1) == 0
    assert moment(u, 2) == 0


def main() -> int:
    even = (1, -4, 6, -4, 1)
    odd = (1, -2, 0, 2, -1)

    assert even == tuple(reversed(even))
    assert odd == tuple(-x for x in reversed(odd))
    assert_boundary_flat(even)
    assert_boundary_flat(odd)
    assert moment(even, 3) == 0

    even_zero = normalized_energy_odd_derivative(even, 9, quarter=False)
    even_quarter = normalized_energy_odd_derivative(even, 9, quarter=True)
    odd_zero = normalized_energy_odd_derivative(odd, 7, quarter=False)
    odd_quarter = normalized_energy_odd_derivative(odd, 7, quarter=True)

    # Exact identities for g^(k) / [2*(2*pi)^(k-1)].
    assert even_zero == (Fraction(576), Fraction(0))
    assert even_quarter == (Fraction(-1024, 3), Fraction(-16))
    assert odd_zero == (Fraction(-144), Fraction(0))
    assert odd_quarter == (Fraction(256, 3), Fraction(4))

    # Signs are exact and need only pi > 0.
    assert even_zero[0] > 0 and even_zero[1] == 0
    assert even_quarter[0] < 0 and even_quarter[1] < 0
    assert odd_zero[0] < 0 and odd_zero[1] == 0
    assert odd_quarter[0] > 0 and odd_quarter[1] > 0

    print("post-155 exact Riesz pointwise-sign regression: PASS")
    print("even: g^9(0) / [2(2pi)^8] = 576")
    print("even: g^9(1/4) / [2(2pi)^8] = -1024/3 - 16*pi")
    print("odd:  g^7(0) / [2(2pi)^6] = -144")
    print("odd:  g^7(1/4) / [2(2pi)^6] = 256/3 + 4*pi")
    print("RH remains OPEN")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
