#!/usr/bin/env python3
"""Cancellation-preserving two-channel canonical source jets.

This module changes only the representation used by the post-#199 mechanism
experiment.  It starts from the validated four-way fixed-unit source jets and
forms the pole-prime discrepancy at matrix M/M'/M'' level *before* parity
restriction or trajectory transport:

    D = pole + prime_signed
    A = direct_arch_signed
    M = D + A

Because ``prime_signed`` already carries the production minus sign, D is the
production pole-minus-prime channel.  The theorem-backed Lean discrepancy
identity motivates this pairing but does not prove any aperture-derivative or
parity-orientation sign law here.  Research/audit tooling only.  RH remains
OPEN.
"""
from __future__ import annotations

from flint import arb_mat

from post198_fb05_q14_four_way_channel_second_derivative import (
    collapse_direct_arch_channel_jets,
    fixed_unit_four_way_channel_jets,
    matrix_all_entries_overlap,
)

PAIRED_CHANNELS = ("pole_prime_discrepancy", "direct_arch_signed")


def _add_jet_rows(left: dict, right: dict) -> dict:
    return {
        "matrix": left["matrix"] + right["matrix"],
        "matrix_prime": left["matrix_prime"] + right["matrix_prime"],
        "matrix_second": left["matrix_second"] + right["matrix_second"],
    }


def _sum_two(left: arb_mat, right: arb_mat) -> arb_mat:
    return left + right


def paired_discrepancy_channel_jets(L, N: int, Q: int) -> dict:
    """Build D/A matrix jets before parity restriction or interval transport."""
    four = fixed_unit_four_way_channel_jets(L, N, Q)
    channels = four["channels"]
    collapsed = collapse_direct_arch_channel_jets(four)

    discrepancy = _add_jet_rows(channels["pole"], channels["prime_signed"])
    arch = collapsed["direct_arch_signed"]
    paired = {
        "pole_prime_discrepancy": discrepancy,
        "direct_arch_signed": arch,
    }

    direct = four["direct"]
    rebuilt_M = _sum_two(discrepancy["matrix"], arch["matrix"])
    rebuilt_Mp = _sum_two(discrepancy["matrix_prime"], arch["matrix_prime"])
    rebuilt_Mpp = _sum_two(discrepancy["matrix_second"], arch["matrix_second"])

    return {
        "channels": paired,
        "direct": direct,
        "inherited_four_way_reconstruction": four["reconstruction"],
        "paired_reconstruction": {
            "matrix_overlap": matrix_all_entries_overlap(rebuilt_M, direct["matrix"]),
            "matrix_prime_overlap": matrix_all_entries_overlap(rebuilt_Mp, direct["matrix_prime"]),
            "matrix_second_overlap": matrix_all_entries_overlap(rebuilt_Mpp, direct["matrix_second"]),
        },
    }


def paired_reconstruction_ok(record: dict) -> bool:
    return all(record["inherited_four_way_reconstruction"].values()) and all(
        record["paired_reconstruction"].values()
    )
