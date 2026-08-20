from __future__ import annotations

"""Symbolic derivation of the finite CCM index-displacement identity.

This is an implementation-level algebraic certificate, not a finite-to-infinite theorem and not RH
evidence.  It proves the closed-form identity for the matrix formula used by R004-v2.
"""

import sympy as sp


def main() -> int:
    n, m, L, C, kappa = sp.symbols("n m L C kappa", nonzero=True)
    alpha_n, alpha_m, prime_n, prime_m = sp.symbols(
        "alpha_n alpha_m prime_n prime_m"
    )

    den_n = L**2 + kappa * n**2
    den_m = L**2 + kappa * m**2

    pole_nm = C * (L**2 - kappa * m * n) / (den_m * den_n)
    arch_nm = (alpha_m - alpha_n) / (n - m)
    prime_nm = (prime_m - prime_n) / (n - m)

    matrix_nm = pole_nm - arch_nm - prime_nm

    g_n = C * n / den_n + alpha_n + prime_n
    g_m = C * m / den_m + alpha_m + prime_m

    pole_identity = sp.factor(
        (n - m) * pole_nm - C * (n / den_n - m / den_m)
    )
    full_identity = sp.factor((n - m) * matrix_nm - (g_n - g_m))

    assert pole_identity == 0
    assert full_identity == 0

    print("R004 exact displacement derivation: PASS")
    print("For n != m:")
    print("  (n-m) M_nm = g_n - g_m")
    print("with")
    print("  g_n = C*n/(L^2+kappa*n^2) + alpha_n + prime_n")
    print("Therefore [D,M] = g*1^T - 1*g^T and rank([D,M]) <= 2.")
    print("The diagonal identity is 0=0, so the formula extends to all entries.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
