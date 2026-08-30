#!/usr/bin/env python3
"""D0-R falsifier: compare R002-style tapered characters with the CCM qBasis.

This script is an EXPERIMENTAL / algebraic-oracle check, not theorem authority.

It verifies three things:

1. The CCM qBasis is exactly the closed-form real symmetrization of the
   normalized shifted correlation of hard-window Fourier characters on [0,L].
2. Direct quadrature of that hard-window correlation reproduces qBasis.
3. Replacing the hard window by the smooth plateau/ramp geometry used by R002
   changes the correlation entries, so the hard-window identification is a
   specialization, not an identity for the generic tapered production family.

The common R002 carrier T is intentionally not erased here; the Lean D0-R file
records tau_k = T + k*2*pi/L separately as an additional map obligation.
"""

from __future__ import annotations

import cmath
import math


def q_basis(n: int, m: int, y: float, L: float) -> float:
    if n == m:
        return 2.0 * (1.0 - y / L) * math.cos(2.0 * math.pi * n * y / L)
    return (
        math.sin(2.0 * math.pi * n * y / L)
        - math.sin(2.0 * math.pi * m * y / L)
    ) / (math.pi * (m - n))


def hard_character_correlation_closed(n: int, m: int, y: float, L: float) -> float:
    """2 Re of the normalized shifted hard-window character correlation."""
    t = y / L
    if n == m:
        c = (1.0 - t) * cmath.exp(-2j * math.pi * m * t)
    else:
        c = (
            cmath.exp(-2j * math.pi * n * t)
            - cmath.exp(-2j * math.pi * m * t)
        ) / (2j * math.pi * (n - m))
    return 2.0 * c.real


def smootherstep01(x: float) -> float:
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    return x**3 * (10.0 + x * (-15.0 + 6.0 * x))


def plateau_taper(x: float, L: float, w: float) -> float:
    """[0,L] version of rho((L/2-|u|)/w), u=x-L/2."""
    return smootherstep01(min(x, L - x) / w)


def shifted_correlation_numeric(
    n: int,
    m: int,
    y: float,
    L: float,
    *,
    taper_width: float | None,
    steps: int = 20000,
) -> float:
    if not (0.0 <= y <= L):
        raise ValueError("diagnostic expects 0 <= y <= L")
    if steps <= 0:
        raise ValueError("steps must be positive")

    upper = L - y
    if upper == 0.0:
        return 0.0

    def window(x: float) -> float:
        if taper_width is None:
            return 1.0
        return plateau_taper(x, L, taper_width)

    def integrand(x: float) -> complex:
        left = window(x) * cmath.exp(2j * math.pi * n * x / L)
        right = window(x + y) * cmath.exp(2j * math.pi * m * (x + y) / L)
        return left * right.conjugate()

    h = upper / steps
    total = 0.5 * (integrand(0.0) + integrand(upper))
    for r in range(1, steps):
        total += integrand(r * h)
    integral = h * total
    return 2.0 * (integral / L).real


def main() -> int:
    L = 3.7
    cases = [
        (0, 0, 0.23 * L),
        (1, 0, 0.31 * L),
        (1, 1, 0.19 * L),
        (2, -1, 0.41 * L),
        (-2, 1, 0.67 * L),
    ]

    closed_residuals: list[float] = []
    quadrature_residuals: list[float] = []
    smooth_residuals: list[float] = []

    for n, m, y in cases:
        q = q_basis(n, m, y, L)
        closed = hard_character_correlation_closed(n, m, y, L)
        box_num = shifted_correlation_numeric(
            n, m, y, L, taper_width=None, steps=12000
        )
        smooth_num = shifted_correlation_numeric(
            n, m, y, L, taper_width=0.17 * L, steps=12000
        )

        closed_residuals.append(abs(q - closed))
        quadrature_residuals.append(abs(q - box_num))
        smooth_residuals.append(abs(q - smooth_num))

    max_closed = max(closed_residuals)
    max_box = max(quadrature_residuals)
    max_smooth = max(smooth_residuals)

    if max_closed > 5e-13:
        raise AssertionError(f"closed-form hard-window mismatch: {max_closed:.3e}")
    if max_box > 2e-6:
        raise AssertionError(f"hard-window quadrature mismatch: {max_box:.3e}")
    if max_smooth < 1e-3:
        raise AssertionError(
            "smooth taper unexpectedly indistinguishable from hard-window qBasis"
        )

    print("D0-R R002/CCM probe-family falsifier")
    print(f"hard closed-form max residual : {max_closed:.3e}")
    print(f"hard quadrature max residual  : {max_box:.3e}")
    print(f"smooth-taper max residual     : {max_smooth:.3e}")
    print("CLASSIFICATION: SPECIALIZATION_ONLY")
    print(
        "Interpretation: qBasis matches the hard-window character correlation; "
        "the generic smooth R002 taper does not share that exact entry formula."
    )
    print(
        "Additional obligations remain: the R002 carrier T, dynamic dimension "
        "d(T), finite-window Az versus global Gz, and current lambda<=1 validity."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
