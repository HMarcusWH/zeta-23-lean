"""Exact rational coordinate implementation of the audited finite geometry.

This evaluator does not replace canonicalSourceMatrix or assert a zeta state.
Its parameter a is the rational stand-in for (L/(4*pi))^2 in finite controls.
"""
from __future__ import annotations

import sympy as s


def geometry(cutoff: int, a: s.Rational) -> dict:
    if cutoff < 3 or a <= 0:
        raise ValueError("nonempty geometry requires K >= 3 and a > 0")
    n = s.Matrix(range(-cutoff, cutoff + 1))
    size = len(n)
    one = s.ones(size, 1)
    reversal = s.zeros(size)
    for i in range(size):
        reversal[i, size - i - 1] = 1
    D = s.diag(*n)
    N2 = n.applyfunc(lambda t: t**2) - one * sum(t**2 for t in n) / size
    nu = N2.dot(N2)
    E = (s.eye(size) + reversal) / 2 - one * one.T / size - N2 * N2.T / nu
    O = (s.eye(size) - reversal) / 2 - n * n.T / n.dot(n)
    h = n.applyfunc(lambda t: 1 / (a + t**2))
    ve = E * h
    vo = O * D * h
    Qe = E - ve * ve.T / ve.dot(ve)
    Qo = O - vo * vo.T / vo.dot(vo)
    g = O * n.applyfunc(lambda t: t**3)
    g0 = Qo * g
    b = h.dot(N2) / nu
    return {k: v for k, v in locals().items() if k != "cutoff"} | {"K": cutoff}


def is_zero(matrix: s.Matrix) -> bool:
    return all(s.simplify(x) == 0 for x in matrix)


def require_checks(checks: dict[str, bool]) -> None:
    failed = [name for name, value in checks.items() if not value]
    if failed:
        raise AssertionError(failed)
