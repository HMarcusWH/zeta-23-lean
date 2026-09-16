#!/usr/bin/env python3
"""Discrepancy-first mechanism audit for the complete post-#197 Q14 trajectory.

The experiment differs from PR #199 in exactly one structural way: pole and
prime_signed are paired at matrix M/M'/M'' level before parity restriction and
second-order interval transport.  The resulting two-channel representation is

    D = pole + prime_signed
    A = direct_arch_signed
    M = D + A

The generic normalized predecessor and Method-C transport machinery from the
post-#199 audit is reused unchanged.  Research/audit tooling only.  RH remains
OPEN.
"""
from __future__ import annotations

from flint import arb

from canonical_source_arb import set_precision
from post166_fb05_cell_interval import arb_unit_interval, cell_coordinate_L_arb
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR
from post198_fb05_q14_parity_source_mechanism import (
    _direct_normalized_method_c,
    _json_interaction,
    _overlap,
    interaction_transport,
    normalized_predecessor_channel_jets,
)
from post200_fb05_q14_discrepancy_channel_jets import (
    PAIRED_CHANNELS,
    paired_discrepancy_channel_jets,
    paired_reconstruction_ok,
)

DISCREPANCY_GROUP = "pole_prime_discrepancy"
ARCH_GROUP = "direct_arch_signed"
CROSS_GROUP = "pole_prime_discrepancy__x__direct_arch_signed"


def paired_mechanism_cell_record(cell: dict) -> dict:
    Q = int(cell["Q"])
    lo = int(cell["lo_num"])
    hi = int(cell["hi_num"])
    den = int(cell["den"])
    center_num = int(cell.get("center_num", (lo + hi) // 2))
    L_interval = cell_coordinate_L_arb(Q, arb_unit_interval(lo, hi, den))
    L_center = cell_coordinate_L_arb(Q, arb(center_num) / den)

    center_jets = paired_discrepancy_channel_jets(L_center, TARGET_KSTAR, Q)
    interval_jets = paired_discrepancy_channel_jets(L_interval, TARGET_KSTAR, Q)
    if not paired_reconstruction_ok(center_jets) or not paired_reconstruction_ok(interval_jets):
        raise AssertionError("paired discrepancy matrix-jet reconstruction failed")

    center = normalized_predecessor_channel_jets(center_jets)
    interval = normalized_predecessor_channel_jets(interval_jets)
    paired = interaction_transport(center, interval, L_interval, L_center)
    direct = _direct_normalized_method_c(Q, L_center, L_interval)

    paired_direct_overlap = _overlap(paired["source_sum"], direct["J_transport"])
    if not paired_direct_overlap:
        raise AssertionError("paired discrepancy transport failed to reconstruct direct Method C")

    expected_groups = {DISCREPANCY_GROUP, ARCH_GROUP, CROSS_GROUP}
    if set(paired["groups"]) != expected_groups:
        raise AssertionError("paired Wronskian group surface drift")

    return {
        "label": cell.get("label"),
        "role": cell.get("role"),
        "primary": cell.get("primary"),
        "Q": Q,
        "depth": int(cell.get("depth", 0)),
        "lo_num": lo,
        "hi_num": hi,
        "center_num": center_num,
        "den": den,
        "direct": {
            "J_transport_positive": bool(direct["J_transport"] > 0),
        },
        "paired": _json_interaction(paired),
        "checks": {
            "paired_direct_transport_overlap": paired_direct_overlap,
            "center_inherited_four_way_reconstruction": center_jets["inherited_four_way_reconstruction"],
            "center_paired_reconstruction": center_jets["paired_reconstruction"],
            "interval_inherited_four_way_reconstruction": interval_jets["inherited_four_way_reconstruction"],
            "interval_paired_reconstruction": interval_jets["paired_reconstruction"],
            "pairing_before_parity_restriction": True,
        },
    }


def summarize_paired_representation(rows: list[dict]) -> dict:
    if not rows:
        raise ValueError("paired mechanism summary requires cells")
    lock_sets = [set(row["paired"]["dominance_locks"]) for row in rows]
    common = set.intersection(*lock_sets) if lock_sets else set()
    every_locked = all(bool(s) for s in lock_sets)
    all_source_positive = all(bool(row["paired"]["source_sum_positive"]) for row in rows)
    all_nonnegative = all(bool(row["paired"]["all_groups_nonnegative"]) for row in rows)

    if not all_source_positive:
        classification = "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED"
    elif common:
        if len(common) != 1:
            raise AssertionError("multiple strict uniform dominance locks are inconsistent")
        group = next(iter(common))
        mapping = {
            DISCREPANCY_GROUP: "DISCREPANCY_UNIFORM_LOCK",
            ARCH_GROUP: "DIRECT_ARCH_UNIFORM_LOCK",
            CROSS_GROUP: "CROSS_UNIFORM_LOCK",
        }
        if group not in mapping:
            raise AssertionError(f"unknown paired uniform lock group: {group}")
        classification = mapping[group]
    elif every_locked:
        classification = "REGIME_SWITCHING_LOCK"
    elif all_nonnegative:
        classification = "COOPERATIVE_NONNEGATIVE"
    else:
        classification = "MIXED_SIGN_RECONSTRUCTABLE"

    return {
        "classification": classification,
        "uniform_lock_groups": sorted(common),
        "every_leaf_has_some_lock": every_locked,
        "all_source_sums_positive": all_source_positive,
        "all_groups_nonnegative_on_every_leaf": all_nonnegative,
        "positive_source_sum_leaf_count": sum(bool(row["paired"]["source_sum_positive"]) for row in rows),
        "unresolved_source_sum_leaf_count": sum(not bool(row["paired"]["source_sum_positive"]) for row in rows),
        "leaf_lock_histogram": {
            name: sum(name in row["paired"]["dominance_locks"] for row in rows)
            for name in sorted({g for row in rows for g in row["paired"]["dominance_locks"]})
        },
    }


def audit_discrepancy_mechanism(schedule: dict, completed_cover: dict, *, precision_bits: int) -> dict:
    set_precision(precision_bits)
    leaves = completed_cover["leaves"]
    primary_rows = [paired_mechanism_cell_record(row) for row in leaves]
    if not all(row["direct"]["J_transport_positive"] for row in primary_rows):
        raise AssertionError("post-#197 direct Method C positivity failed to replay")

    summary = summarize_paired_representation(primary_rows)
    selected = None
    if len(summary["uniform_lock_groups"]) == 1:
        selected = summary["uniform_lock_groups"][0]

    controls = []
    for box in schedule["boxes"]:
        if bool(box["primary"]):
            continue
        row = paired_mechanism_cell_record(box)
        locks = row["paired"]["dominance_locks"]
        row["falsification"] = {
            "selected_primary_lock_group": selected,
            "selected_group_locks_control": None if selected is None else selected in locks,
            "control_class": "ADJACENT_Q_TRANSFER" if int(box["Q"]) != 14 else "Q14_INTERNAL",
        }
        controls.append(row)

    if selected is None:
        transfer_status = "NO_UNIQUE_PRIMARY_LOCK"
    else:
        adjacent = [
            row for row in controls
            if row["falsification"]["control_class"] == "ADJACENT_Q_TRANSFER"
        ]
        transfer_status = (
            "SELECTED_LOCK_SURVIVES_Q13_Q15_CONTROLS"
            if adjacent and all(row["falsification"]["selected_group_locks_control"] for row in adjacent)
            else "Q14_LOCAL_MECHANISM_ONLY"
        )

    return {
        "status": "PASS",
        "scope": "Q14_POST200_CANCELLATION_PRESERVING_DISCREPANCY_MECHANISM_RESEARCH_ONLY",
        "paired_channels": list(PAIRED_CHANNELS),
        "completed_leaf_count": len(primary_rows),
        "mechanism_classification": summary["classification"],
        "summary": summary,
        "selected_uniform_lock_group": selected,
        "control_transfer_status": transfer_status,
        "primary_cells": primary_rows,
        "control_rows": controls,
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
