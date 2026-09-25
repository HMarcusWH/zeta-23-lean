"""Entire Fourier transform of the finite even CCM test; numerical tools only.

The sinc form removes both cancellation at zero and the apparent poles at
Fourier nodes. It is checked against independent direct mpmath integration.
The SciPy finite-interval integral is NOT an enclosure of an infinite integral.
"""
from __future__ import annotations
import math
import warnings
import mpmath as mp
import numpy as np
from scipy.integrate import IntegrationWarning, quad
from scipy.special import digamma


def h_mp(n: int, m: int, r, L):
    r, L = mp.mpmathify(r), mp.mpmathify(L)
    if not L > 0:
        raise ValueError("positive aperture required")
    a, b = 2 * mp.pi * n / L, 2 * mp.pi * m / L
    if n == m:
        return L * (mp.sinc((r - a) * L / 2)**2 + mp.sinc((r + a) * L / 2)**2)
    def F(z):
        return L**2 * z / 2 * mp.sinc(z * L / 2)**2
    return (F(a + r) + F(a - r) - F(b + r) - F(b - r)) / (mp.pi * (m - n))


def h_float(n: int, m: int, r: float, L: float) -> float:
    if not math.isfinite(L) or L <= 0 or not math.isfinite(r):
        raise ValueError("finite real frequency and positive finite aperture required")
    a, b = 2 * math.pi * n / L, 2 * math.pi * m / L
    if n == m:
        return float(L * (np.sinc((r - a) * L / (2*math.pi))**2
                          + np.sinc((r + a) * L / (2*math.pi))**2))
    def F(z):
        return L**2 * z / 2 * np.sinc(z * L / (2*math.pi))**2
    return float((F(a+r) + F(a-r) - F(b+r) - F(b-r)) / (math.pi*(m-n)))


def h_direct(n: int, m: int, r, L):
    """Independent integration of the original trigonometric test."""
    L, r = mp.mpmathify(L), mp.mpmathify(r)
    def q(y):
        if n == m:
            return 2 * (1-y/L) * mp.cos(2*mp.pi*n*y/L)
        return (mp.sin(2*mp.pi*n*y/L)-mp.sin(2*mp.pi*m*y/L))/(mp.pi*(m-n))
    return mp.quad(lambda y: 2*q(y)*mp.cos(r*y), [0, L/2, L])


def finite_arch_integral(n: int, m: int, L: float, R: float, panels: int) -> tuple[float, float]:
    """Return finite [-R,R] integral / (2*pi), plus QUADPACK error estimate.

    The error estimate is diagnostic, not certified. No tail is included.
    Integration warnings and nonfinite outputs are failures, not passes.
    """
    if R <= 0 or panels < 1 or L <= 0:
        raise ValueError("R,L positive and panels >= 1 required")
    nodes = list(np.linspace(0, R, panels+1))
    nodes += [c for c in (2*math.pi*abs(n)/L, 2*math.pi*abs(m)/L) if 0 < c < R]
    nodes = sorted(set(nodes))
    value, error = 0., 0.
    def f(r):
        return h_float(n,m,r,L) * (float(digamma(.25+.5j*r).real)-math.log(math.pi))
    with warnings.catch_warnings():
        warnings.simplefilter("error", IntegrationWarning)
        for a,b in zip(nodes,nodes[1:]):
            v,e = quad(f,a,b,epsabs=1e-11,epsrel=1e-10,limit=250)
            value += v
            error += e
    if not math.isfinite(value) or not math.isfinite(error):
        raise ArithmeticError("nonfinite quadrature result")
    return value/math.pi, error/math.pi


def validate_transform(L: float) -> dict:
    """Exercise regular, zero, exact Fourier-node and near-node cases."""
    records = []
    with mp.workdps(55):
        for n,m in [(0,0),(1,1),(1,0),(2,-1),(-2,2)]:
            node = 2*mp.pi*abs(n)/mp.mpf(L)
            for r in [mp.mpf(0),mp.mpf('.7'),mp.mpf('3.3'),node,node+mp.mpf('1e-20')]:
                exact = h_mp(n,m,r,L)
                direct = h_direct(n,m,r,L)
                error = abs(exact-direct)
                if error > mp.mpf('1e-40')*max(1,abs(direct)):
                    raise AssertionError(f"entire transform mismatch {(n,m,r,error)}")
                fast_error = abs(h_float(n,m,float(r),L)-float(exact))
                if fast_error > 2e-12*max(1,float(abs(exact))):
                    raise AssertionError(f"float transform mismatch {(n,m,r,fast_error)}")
                records.append({"n":n,"m":m,"r":str(r),"mp_error":str(error),"float_error":fast_error})
    return {"status":"PASS","claim_cap":"FINITE_NUMERICAL_TRANSFORM_REGRESSION_ONLY","cases":records}
