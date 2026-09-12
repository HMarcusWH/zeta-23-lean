#!/usr/bin/env python3
"""Fast production-canonical CCM source matrix utilities.

This module deliberately does *not* change the historical R004
``build_ccm_matrix`` binding.  R004 remains the legacy printed normalization.
Here we import the fork-owned executable primitives and apply the exact
source-normalization repair

    canonicalSourceMatrix = legacyPrintedMatrix + 2*cCorrection(L) I.

The resulting floats are discovery/regression data only.  Rigorous sign
certification lives in ``canonical_source_arb.py``.
"""
from __future__ import annotations

import math
import sys
from functools import lru_cache
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
RHRC = HERE.parents[1]
R004 = RHRC / "routes" / "R004_prolate_v2"
sys.path.insert(0, str(R004))

from run_commutator_gauntlet_v2 import (  # noqa: E402
    arch_component,
    c_correction,
    pole_component,
    prime_component,
)


def fixed_cell_bounds(Q: int) -> tuple[float, float]:
    if Q < 1:
        raise ValueError("require Q>=1")
    return math.log(float(Q)), math.log(float(Q + 1))


def assert_in_fixed_cell(Q: int, L: float) -> None:
    lo, hi = fixed_cell_bounds(Q)
    if not (lo < L < hi):
        raise ValueError(f"L={L!r} is not in (log({Q}), log({Q + 1}))")


def centered_indices(N: int) -> list[int]:
    if N < 0:
        raise ValueError("require N>=0")
    return list(range(-N, N + 1))


def legacy_source_entry_L(n: int, m: int, L: float) -> float:
    if not L > 0:
        raise ValueError("require L>0")
    return (
        pole_component(n, m, L)
        - arch_component(n, m, L)
        - prime_component(n, m, L)
    )


def canonical_source_entry_L(n: int, m: int, L: float) -> float:
    """Production canonical source entry at native aperture L."""
    value = legacy_source_entry_L(n, m, L)
    if n == m:
        value += 2.0 * c_correction(L)
    return float(value)


@lru_cache(maxsize=None)
def canonical_source_matrix_L(L: float, N: int) -> np.ndarray:
    if not L > 0 or N < 0:
        raise ValueError("require L>0 and N>=0")
    idx = centered_indices(N)
    M = np.empty((len(idx), len(idx)), dtype=float)
    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            value = canonical_source_entry_L(n, m, L)
            M[r, c] = value
            M[c, r] = value
    return M


@lru_cache(maxsize=None)
def legacy_source_matrix_L(L: float, N: int) -> np.ndarray:
    if not L > 0 or N < 0:
        raise ValueError("require L>0 and N>=0")
    idx = centered_indices(N)
    M = np.empty((len(idx), len(idx)), dtype=float)
    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            value = legacy_source_entry_L(n, m, L)
            M[r, c] = value
            M[c, r] = value
    return M


def signed_channel_matrices_L(L: float, N: int) -> dict[str, np.ndarray]:
    """Return the exact executable channel split used by the repaired matrix.

    The returned matrices already carry their sign in the canonical sum:

        canonical = pole + arch_signed + prime_signed + scalar_shift.
    """
    if not L > 0 or N < 0:
        raise ValueError("require L>0 and N>=0")
    idx = centered_indices(N)
    dim = len(idx)
    pole = np.empty((dim, dim), dtype=float)
    arch_signed = np.empty((dim, dim), dtype=float)
    prime_signed = np.empty((dim, dim), dtype=float)
    for r, n in enumerate(idx):
        for c in range(r, dim):
            m = idx[c]
            p = float(pole_component(n, m, L))
            a = -float(arch_component(n, m, L))
            q = -float(prime_component(n, m, L))
            pole[r, c] = pole[c, r] = p
            arch_signed[r, c] = arch_signed[c, r] = a
            prime_signed[r, c] = prime_signed[c, r] = q
    scalar = 2.0 * c_correction(L) * np.eye(dim)
    return {
        "pole": pole,
        "arch_signed": arch_signed,
        "prime_signed": prime_signed,
        "scalar_shift": scalar,
    }


def canonical_channel_energies_L(L: float, N: int, u: np.ndarray) -> dict[str, float]:
    u = np.asarray(u, dtype=float).reshape(-1)
    expected = 2 * N + 1
    if len(u) != expected:
        raise ValueError(f"expected vector length {expected}, got {len(u)}")
    channels = signed_channel_matrices_L(L, N)
    out = {name: float(u @ A @ u) for name, A in channels.items()}
    out["total_from_channels"] = float(sum(out.values()))
    out["total_direct"] = float(u @ canonical_source_matrix_L(L, N) @ u)
    out["reconstruction_error"] = abs(out["total_from_channels"] - out["total_direct"])
    return out


def dyadic_inside_fixed_cell(Q: int, t: float, bits: int = 40) -> tuple[int, int]:
    """Return a deterministic exact dyadic point inside the Q cutoff cell."""
    if not (0.0 < t < 1.0):
        raise ValueError("require 0<t<1")
    lo, hi = fixed_cell_bounds(Q)
    target = lo + t * (hi - lo)
    den = 1 << bits
    num = int(round(target * den))
    while num / den <= lo:
        num += 1
    while num / den >= hi:
        num -= 1
    L = num / den
    if not (lo < L < hi):
        raise RuntimeError("failed to construct an interior dyadic aperture")
    return num, den
