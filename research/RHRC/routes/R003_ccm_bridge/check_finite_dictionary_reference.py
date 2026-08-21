#!/usr/bin/env python3
"""Regression guard for the PR #35 external finite-dictionary oracle.

This is diagnostic/reference validation only.  It does not enter the Lean graph
and cannot promote an RHRC mathematical claim.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[2]
ORACLE = ROOT / "external" / "connes_cvs" / "finite_dictionary_reference.py"


def load_oracle():
    before = mp.mp.dps
    spec = importlib.util.spec_from_file_location("finite_dictionary_reference", ORACLE)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load oracle at {ORACLE}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    if mp.mp.dps != before:
        raise AssertionError(
            f"oracle import changed global mpmath precision: {before} -> {mp.mp.dps}"
        )
    return module


def expect_value_error(fn, label: str) -> None:
    try:
        fn()
    except ValueError:
        return
    raise AssertionError(f"expected ValueError for {label}")


def expect_arithmetic_error(fn, label: str) -> None:
    try:
        fn()
    except ArithmeticError:
        return
    raise AssertionError(f"expected ArithmeticError for {label}")


def is_finite(value) -> bool:
    """Fail-closed finiteness predicate for real or complex mpmath values."""
    return bool(mp.isfinite(mp.re(value)) and mp.isfinite(mp.im(value)))


def require_finite_within(value, tol, label: str) -> None:
    """Require a finite residual inside tolerance; NaN/Inf can never pass."""
    if not is_finite(value) or not (abs(value) <= tol):
        raise AssertionError(f"{label} residual {value} is non-finite or exceeds {tol}")


def main() -> None:
    mp.mp.dps = 70
    oracle = load_oracle()

    # Domain/band guards: these prevent plausible but internally inconsistent
    # reference values from being produced outside the paper's c>1, N>=0,
    # len(v)=N+1 domain.
    expect_value_error(lambda: oracle.TestFn(1, 1, [1, 2]), "c = 1")
    expect_value_error(lambda: oracle.TestFn(mp.mpf("0.5"), 1, [1, 2]), "c < 1")
    expect_value_error(lambda: oracle.TestFn(13, -1, []), "negative N")
    expect_value_error(lambda: oracle.TestFn(13, 2, [1, 2]), "short coefficient vector")
    expect_value_error(lambda: oracle.TestFn(13, 1, [1, 2, 3]), "long coefficient vector")

    # Python's max can mask a later NaN.  Exercise the oracle's own aggregation
    # helper directly so every probe must be finite before a maximum is formed.
    expect_arithmetic_error(
        lambda: oracle._max_finite_residual(
            [mp.mpf("1e-80"), mp.nan], "synthetic non-finite residual"
        ),
        "per-probe NaN rejection before max",
    )
    expect_arithmetic_error(
        lambda: oracle._max_finite_residual(
            [mp.mpf("1e-80"), mp.inf], "synthetic non-finite residual"
        ),
        "per-probe Inf rejection before max",
    )

    # Exact finite dictionary regression: source closed form vs independent
    # Volterra / physical-space quadrature, at higher caller-selected precision.
    residuals = oracle.regression_guards(13, 4, [1, 2, -1, 3, 2])
    tol = mp.mpf("1e-50")
    for name, value in residuals.items():
        require_finite_within(value, tol, name)

    # The closed-form transform must preserve the complex value arbitrarily
    # close to, but not on, the real axis.  Also check Schwarz reflection for
    # the real/even finite test at a genuinely complex point.
    tf = oracle.TestFn(13, 4, [1, 2, -1, 3, 2])
    z = mp.mpc("0.9", "1e-40")
    gz = tf.g(z)
    if not isinstance(gz, mp.mpc):
        raise AssertionError("non-real transform input was projected to a real scalar")
    if not is_finite(gz):
        raise AssertionError(f"non-real transform returned non-finite value {gz}")
    if mp.im(gz) == 0:
        raise AssertionError("non-real transform input lost its imaginary part")
    reflection_error = abs(tf.g(mp.conj(z)) - mp.conj(gz))
    require_finite_within(reflection_error, tol, "complex transform reflection")

    # Exercise the removable-singularity path beyond the old fixed 25-term
    # precision ceiling.  The adaptive series must track caller precision.
    with mp.workdps(300):
        a = mp.mpf("9e-9")
        al = mp.mpc("1.2", "0.3")
        be = mp.mpc("-0.7", "0.2")
        series_value = oracle.TestFn._int_poly_exp(al, be, a)
        quad_value = mp.quad(
            lambda w: (al + be * w) * mp.exp(1j * a * w), [0, 1]
        )
        high_precision_error = abs(series_value - quad_value)
        require_finite_within(
            high_precision_error,
            mp.mpf("1e-280"),
            "300-dps removable-singularity series",
        )

    # The guard itself must leave caller precision untouched.
    if mp.mp.dps != 70:
        raise AssertionError(f"oracle/guard changed caller precision to {mp.mp.dps}")

    print("finite dictionary reference guard: PASS")
    for name, value in residuals.items():
        print(f"  {name}: {mp.nstr(value, 8)}")
    print(f"  complex reflection residual: {mp.nstr(reflection_error, 8)}")
    print(f"  300-dps series residual: {mp.nstr(high_precision_error, 8)}")


if __name__ == "__main__":
    main()
