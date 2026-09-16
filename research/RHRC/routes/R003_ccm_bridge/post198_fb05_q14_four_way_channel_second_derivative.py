#!/usr/bin/env python3
"""Fixed-unit four-way canonical source jets through second aperture order.

Extends the established source convention

    canonical = pole + arch_signed + prime_signed + scalar_shift

to second aperture derivatives in the fixed-unit representation used by the
post-#195/#197 Q14 trajectory.  The independently validated post-#194 total
M'' remains authoritative; this module only exposes and reconstructs a channel
split.  Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

from flint import arb, arb_mat

from canonical_source_arb import c_correction, direct_arch_component, signed_channel_matrices
from post175_fb05_q13_fixed_unit_enclosure import fixed_unit_primitive_caches
from post187_fb05_q14_mixed_drift_selector import four_way_channel_derivative_matrices
from post194_fb05_q14_fixed_unit_second_derivative import (
    direct_arch_component_second,
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb,
    fixed_unit_primitive_second_derivative_caches,
    pole_component_second,
    prime_component_second,
)

CHANNEL_NAMES = ("pole", "arch_signed", "prime_signed", "scalar_shift")


def _scalar_identity(dim: int, scalar: arb) -> arb_mat:
    return arb_mat([[scalar if r == c else arb(0) for c in range(dim)] for r in range(dim)])


def matrix_sum(matrices: list[arb_mat]) -> arb_mat:
    if not matrices:
        raise ValueError("matrix_sum requires at least one matrix")
    out = matrices[0]
    for matrix in matrices[1:]:
        out = out + matrix
    return out


def matrix_all_entries_overlap(left: arb_mat, right: arb_mat) -> bool:
    if left.nrows() != right.nrows() or left.ncols() != right.ncols():
        return False
    return all(
        bool((left[r, c] - right[r, c]).contains(0))
        for r in range(left.nrows())
        for c in range(left.ncols())
    )


def c_correction_second_derivative(L: arb) -> arb:
    """Exact derivative of cCorrection'(L) on positive-aperture cells."""
    ep = L.exp()
    em = (-L).exp()
    emh = (-L / 2).exp()
    numerator = arb(1) - emh
    numerator_prime = emh / 2
    denominator = ep - em
    denominator_prime = ep + em
    return (numerator_prime * denominator - numerator * denominator_prime) / (denominator * denominator)


def fixed_unit_four_way_value_matrices(L: arb, N: int, Q: int) -> dict[str, arb_mat]:
    """Four-way values in the fixed-unit trajectory representation."""
    if N < 0 or Q < 1:
        raise ValueError("require N>=0 and Q>=1")
    from canonical_source_arb import pole_component, prime_component

    idx = list(range(-N, N + 1))
    dim = len(idx)
    values = fixed_unit_primitive_caches(L, N)
    scalar = 2 * c_correction(L)
    pole_rows = [[arb(0) for _ in idx] for _ in idx]
    arch_rows = [[arb(0) for _ in idx] for _ in idx]
    prime_rows = [[arb(0) for _ in idx] for _ in idx]

    for r, n in enumerate(idx):
        for c in range(r, dim):
            m = idx[c]
            pole = pole_component(n, m, L)
            direct_arch = direct_arch_component(
                n, m, L, values["alpha"], values["beta"], values["gamma"]
            )
            prime = prime_component(n, m, L, Q)
            scalar_entry = scalar if n == m else arb(0)
            pole_rows[r][c] = pole_rows[c][r] = pole
            arch_rows[r][c] = arch_rows[c][r] = -direct_arch - scalar_entry
            prime_rows[r][c] = prime_rows[c][r] = -prime

    return {
        "pole": arb_mat(pole_rows),
        "arch_signed": arb_mat(arch_rows),
        "prime_signed": arb_mat(prime_rows),
        "scalar_shift": _scalar_identity(dim, scalar),
    }


def fixed_unit_four_way_second_derivative_matrices(L: arb, N: int, Q: int) -> dict[str, arb_mat]:
    """Four-way split of the already-validated total M''."""
    if N < 0 or Q < 1:
        raise ValueError("require N>=0 and Q>=1")
    idx = list(range(-N, N + 1))
    dim = len(idx)
    seconds = fixed_unit_primitive_second_derivative_caches(L, N)
    scalar_second = 2 * c_correction_second_derivative(L)
    pole_rows = [[arb(0) for _ in idx] for _ in idx]
    arch_rows = [[arb(0) for _ in idx] for _ in idx]
    prime_rows = [[arb(0) for _ in idx] for _ in idx]

    for r, n in enumerate(idx):
        for c in range(r, dim):
            m = idx[c]
            pole_second = pole_component_second(n, m, L)
            direct_arch_second = direct_arch_component_second(
                n, m, seconds["alpha"], seconds["beta"], seconds["gamma"]
            )
            prime_second = prime_component_second(n, m, L, Q)
            scalar_entry = scalar_second if n == m else arb(0)
            pole_rows[r][c] = pole_rows[c][r] = pole_second
            arch_rows[r][c] = arch_rows[c][r] = -direct_arch_second - scalar_entry
            prime_rows[r][c] = prime_rows[c][r] = -prime_second

    return {
        "pole": arb_mat(pole_rows),
        "arch_signed": arb_mat(arch_rows),
        "prime_signed": arb_mat(prime_rows),
        "scalar_shift": _scalar_identity(dim, scalar_second),
    }


def fixed_unit_four_way_channel_jets(L: arb, N: int, Q: int) -> dict:
    value = fixed_unit_four_way_value_matrices(L, N, Q)
    first = four_way_channel_derivative_matrices(L, N, Q)
    second = fixed_unit_four_way_second_derivative_matrices(L, N, Q)
    direct_M, direct_Mp, direct_Mpp = fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb(L, N, Q)
    rebuilt_M = matrix_sum([value[name] for name in CHANNEL_NAMES])
    rebuilt_Mp = matrix_sum([first[name] for name in CHANNEL_NAMES])
    rebuilt_Mpp = matrix_sum([second[name] for name in CHANNEL_NAMES])
    return {
        "channels": {
            name: {
                "matrix": value[name],
                "matrix_prime": first[name],
                "matrix_second": second[name],
            }
            for name in CHANNEL_NAMES
        },
        "direct": {"matrix": direct_M, "matrix_prime": direct_Mp, "matrix_second": direct_Mpp},
        "reconstruction": {
            "matrix_overlap": matrix_all_entries_overlap(rebuilt_M, direct_M),
            "matrix_prime_overlap": matrix_all_entries_overlap(rebuilt_Mp, direct_Mp),
            "matrix_second_overlap": matrix_all_entries_overlap(rebuilt_Mpp, direct_Mpp),
        },
    }


def direct_baseline_value_channel_overlaps(L: arb, N: int, Q: int) -> dict:
    fixed = fixed_unit_four_way_value_matrices(L, N, Q)
    direct = signed_channel_matrices(L, N, Q)
    return {name: matrix_all_entries_overlap(fixed[name], direct[name]) for name in CHANNEL_NAMES}


def collapse_direct_arch_channel_jets(jets: dict) -> dict:
    channels = jets["channels"]
    arch = channels["arch_signed"]
    scalar = channels["scalar_shift"]
    return {
        "pole": channels["pole"],
        "direct_arch_signed": {
            "matrix": arch["matrix"] + scalar["matrix"],
            "matrix_prime": arch["matrix_prime"] + scalar["matrix_prime"],
            "matrix_second": arch["matrix_second"] + scalar["matrix_second"],
        },
        "prime_signed": channels["prime_signed"],
    }


def four_way_second_derivative_seam_overlap_record(k: int, N: int) -> dict:
    if k not in (14, 15):
        raise ValueError("four-way second-derivative seam check only valid at 14 or 15")
    L = arb(k).log()
    left = fixed_unit_four_way_second_derivative_matrices(L, N, k - 1)
    right = fixed_unit_four_way_second_derivative_matrices(L, N, k)
    overlaps = {name: matrix_all_entries_overlap(left[name], right[name]) for name in CHANNEL_NAMES}
    return {
        "k": int(k),
        "left_Q": int(k - 1),
        "right_Q": int(k),
        "channel_overlaps": overlaps,
        "all_overlap": all(overlaps.values()),
    }
