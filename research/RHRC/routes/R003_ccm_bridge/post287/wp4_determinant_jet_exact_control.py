#!/usr/bin/env python3
"""WP4 exact-rational determinant Taylor identities (no Arb dependency).

Verifies the formula Δ'' = a''d+2a'd'+ad''-2(b')²-2bb''
and the coefficient-convolution formula for the fourth-order Taylor jet
of Δ=ad-b² over rational polynomials. This tests the algebraic *shape* of
the matrix method and is not a proof of correct interval enclosure or
source formula normalization.

The old unsound method froze a,b,d,a',b',d' at the centre when forming
a whole-interval Δ''. That method is explicitly rejected here.
"""
from __future__ import annotations

from fractions import Fraction
from math import factorial


def val(coeffs: tuple[Fraction, ...], x: Fraction, deriv: int = 0) -> Fraction:
    return sum(
        c * Fraction(factorial(j), factorial(j - deriv)) * x ** (j - deriv)
        for j, c in enumerate(coeffs)
        if j >= deriv
    )


def mul(u: tuple[Fraction, ...], v: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    n = len(u) + len(v) - 1
    return tuple(
        sum(u[j] * v[k - j]
            for j in range(max(0, k - len(v) + 1), min(k, len(u) - 1) + 1))
        for k in range(n)
    )


def sub(u: tuple[Fraction, ...], v: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    n = max(len(u), len(v))
    return tuple(
        (u[k] if k < len(u) else Fraction(0)) -
        (v[k] if k < len(v) else Fraction(0))
        for k in range(n)
    )


def check():
    rows = [
        ((1, 2, 3, 4, 5), (-1, 1, 0, -2, 5), (3, -1, 7, 1, -3)),
        ((-3, 0, 2, 1, 3), (0, -2, 1, 1, -1), (4, 3, -2, 2, 1)),
        ((1, -3, 0, 1, 1), (2, -1, 2, 3, 0), (2, 1, 3, -1, 3)),
    ]
    checked = 0
    old_centre_only_is_wrong = False
    for ra, rb, rd in rows:
        a, b, d = (tuple(Fraction(v) for v in row) for row in (ra, rb, rd))
        det = sub(mul(a, d), mul(b, b))
        for t in [Fraction(0), Fraction(1, 3), Fraction(-2, 5), Fraction(2)]:
            ap, bp, dp = (val(poly, t, 1) for poly in (a, b, d))
            app, bpp, dpp = (val(poly, t, 2) for poly in (a, b, d))
            aa, bb, dd = (val(poly, t) for poly in (a, b, d))
            exact = val(det, t, 2)
            composed = app * dd + 2 * ap * dp + aa * dpp - 2 * (bp * bp + bb * bpp)
            assert composed == exact, (t, exact, composed)
            # Wrong historical centre-only formula is NOT constant in t.
            old = (app * val(d, 0) + 2 * val(a, 0, 1) * val(d, 0, 1) +
                   val(a, 0) * dpp -
                   2 * (val(b, 0, 1) ** 2 + val(b, 0) * bpp))
            if t and old != exact:
                old_centre_only_is_wrong = True
            checked += 1
        # Δ^(4)(0)/4! has precisely the coefficient convolution shape.
        fourth = sum(
            a[j] * d[4 - j] - b[j] * b[4 - j]
            for j in range(5)
        )
        assert val(det, Fraction(0), 4) == factorial(4) * fourth
    assert old_centre_only_is_wrong, "negative control failed to detect old bug"
    print({
        "status": "EXACT_RATIONAL_REGRESSION_PASS",
        "determinant_second_derivative_cases": checked,
        "fourth_order_coefficient_cases": len(rows),
        "old_centre_only_method": "FALSIFIED",
        "terminal_claim": "RH_OPEN",
    })


if __name__ == "__main__":
    check()
