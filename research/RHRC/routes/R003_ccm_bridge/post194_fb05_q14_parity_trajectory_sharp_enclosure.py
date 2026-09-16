#!/usr/bin/env python3
"""Sharper post-#193 Q14 parity-trajectory enclosure using canonical second derivatives.

The mathematical object is unchanged.  On the exact inherited Q14 hull this
module compares, on the same evaluated cells:

  A. the frozen #193 first-order Wronskian enclosure;
  B. a direct parity log-slope enclosure using centered second-order transport;
  C. a centered Wronskian transport using J' = o''e - e''o.

No new selector, Q/N/parity search, threshold, or target label is introduced.
Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

from flint import arb

from canonical_source_arb import ball_record, definitely_negative, definitely_positive, set_precision
from post166_fb05_cell_interval import arb_unit_interval, cell_coordinate_L_arb
from post192_fb05_q14_parity_trajectory_rigidity import (
    H1_UNRESOLVED,
    J_NEGATIVE,
    J_POSITIVE,
    J_UNRESOLVED,
    _classify_cover,
    audit_parity_trajectory,
    primary_hull,
    trajectory_cell_record,
)
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_second_derivative_scalar_record_arb_at_L,
)


def overlap(x: arb, y: arb) -> bool:
    return bool((x - y).contains(0))


def _orientation(x: arb) -> str:
    if definitely_positive(x):
        return J_POSITIVE
    if definitely_negative(x):
        return J_NEGATIVE
    return J_UNRESOLVED


def centered_second_order_enclosure(
    value_center: arb,
    first_center: arb,
    second_interval: arb,
    L_interval: arb,
    L_center: arb,
) -> arb:
    """Taylor enclosure f(c)+f'(c)δ+1/2 f''(I)δ²."""
    delta = L_interval - L_center
    return value_center + first_center * delta + (second_interval * delta * delta) / 2


def centered_first_derivative_enclosure(
    first_center: arb,
    second_interval: arb,
    L_interval: arb,
    L_center: arb,
) -> arb:
    """Mean-value enclosure f'(I) subset f'(c)+f''(I)(I-c)."""
    return first_center + second_interval * (L_interval - L_center)


def _signed_orientation_values(*values: str) -> tuple[set[str], bool]:
    signed = {value for value in values if value in (J_POSITIVE, J_NEGATIVE)}
    return signed, J_POSITIVE in signed and J_NEGATIVE in signed


def resolve_method_orientations(
    method_a: str,
    method_b: str,
    method_c: str,
    *,
    second_order_h1: bool,
) -> dict:
    """Predeclared resolution rule: any certified sign may resolve, conflicts are fatal."""
    signed, conflict = _signed_orientation_values(method_a, method_b, method_c)
    if conflict:
        return {
            "orientation": J_UNRESOLVED,
            "representation_conflict": True,
            "resolving_methods": [],
        }
    if signed == {J_POSITIVE}:
        orientation = J_POSITIVE
    elif signed == {J_NEGATIVE}:
        orientation = J_NEGATIVE
    elif method_a == H1_UNRESOLVED and not second_order_h1:
        orientation = H1_UNRESOLVED
    else:
        orientation = J_UNRESOLVED
    resolving = [
        name
        for name, value in (("A", method_a), ("B", method_b), ("C", method_c))
        if value == orientation and orientation in (J_POSITIVE, J_NEGATIVE)
    ]
    return {
        "orientation": orientation,
        "representation_conflict": False,
        "resolving_methods": resolving,
    }


def sharp_trajectory_cell_record(
    Q: int,
    lo_num: int,
    hi_num: int,
    den: int,
    depth: int,
) -> dict:
    """Evaluate A/B/C on one exact shared dyadic cell."""
    baseline = trajectory_cell_record(Q, lo_num, hi_num, den, depth)

    center_num = (lo_num + hi_num) // 2
    t_interval = arb_unit_interval(lo_num, hi_num, den)
    L_interval = cell_coordinate_L_arb(Q, t_interval)
    L_center = cell_coordinate_L_arb(Q, arb(center_num) / den)

    center = fixed_unit_second_derivative_scalar_record_arb_at_L(Q, L_center)
    interval = fixed_unit_second_derivative_scalar_record_arb_at_L(Q, L_interval)

    e0 = center["even"]["a"]
    ep0 = center["even"]["a_prime"]
    eppI = interval["even"]["a_second"]
    o0 = center["odd_N2_predecessor"]
    op0 = center["odd_N2_predecessor_prime"]
    oppI = interval["odd_N2_predecessor_second"]

    e_taylor = centered_second_order_enclosure(e0, ep0, eppI, L_interval, L_center)
    o_taylor = centered_second_order_enclosure(o0, op0, oppI, L_interval, L_center)
    ep_taylor = centered_first_derivative_enclosure(ep0, eppI, L_interval, L_center)
    op_taylor = centered_first_derivative_enclosure(op0, oppI, L_interval, L_center)

    second_order_h1 = definitely_positive(e_taylor) and definitely_positive(o_taylor)
    method_b = H1_UNRESOLVED
    method_c = H1_UNRESOLVED
    direct_log_slope = None
    direct_P2 = None
    J_center = op0 * e0 - ep0 * o0
    J_prime_interval = oppI * e_taylor - eppI * o_taylor
    J_taylor = J_center + J_prime_interval * (L_interval - L_center)
    P2_from_J = None
    identity_overlap = None

    if second_order_h1:
        direct_log_slope = op_taylor / o_taylor - ep_taylor / e_taylor
        direct_P2 = L_interval * direct_log_slope
        method_b = _orientation(direct_log_slope)
        method_c = _orientation(J_taylor)
        P2_from_J = L_interval * J_taylor / (o_taylor * e_taylor)
        identity_overlap = overlap(direct_P2, P2_from_J)
        if not identity_overlap:
            raise AssertionError("direct P2 and transported-J enclosures are disjoint")

    resolution = resolve_method_orientations(
        baseline["orientation"],
        method_b,
        method_c,
        second_order_h1=second_order_h1,
    )
    if resolution["representation_conflict"]:
        raise AssertionError("equivalent trajectory representations certified opposite signs")

    return {
        "Q": int(Q),
        "depth": int(depth),
        "lo_num": int(lo_num),
        "hi_num": int(hi_num),
        "center_num": int(center_num),
        "den": int(den),
        "orientation": resolution["orientation"],
        "representation_conflict": False,
        "resolving_methods": resolution["resolving_methods"],
        "method_A_orientation": baseline["orientation"],
        "method_B_orientation": method_b,
        "method_C_orientation": method_c,
        "first_order_h1": bool(
            baseline.get("centered_e_positive") and baseline.get("centered_o_positive")
        ),
        "second_order_h1": bool(second_order_h1),
        "L_interval": ball_record(L_interval),
        "L_center": ball_record(L_center),
        "e_center": ball_record(e0),
        "e_prime_center": ball_record(ep0),
        "e_second_interval": ball_record(eppI),
        "o_center": ball_record(o0),
        "o_prime_center": ball_record(op0),
        "o_second_interval": ball_record(oppI),
        "e_second_order_enclosure": ball_record(e_taylor),
        "o_second_order_enclosure": ball_record(o_taylor),
        "e_prime_centered_enclosure": ball_record(ep_taylor),
        "o_prime_centered_enclosure": ball_record(op_taylor),
        "J_center": ball_record(J_center),
        "J_prime_interval": ball_record(J_prime_interval),
        "J_second_order_enclosure": ball_record(J_taylor),
        "direct_log_slope": None if direct_log_slope is None else ball_record(direct_log_slope),
        "direct_P2": None if direct_P2 is None else ball_record(direct_P2),
        "P2_from_J": None if P2_from_J is None else ball_record(P2_from_J),
        "P2_identity_overlap": identity_overlap,
    }


def localize_sharp_trajectory(
    hull: dict,
    *,
    max_depth: int,
    max_cells: int,
) -> dict:
    """One shared adaptive cover: every visited cell is evaluated by A/B/C."""
    queue = [(int(hull["lo_num"]), int(hull["hi_num"]), 0)]
    leaves: list[dict] = []
    evaluated = 0
    max_evaluated_depth = 0
    budget_exhausted_leaf_count = 0
    resolved_counts = {
        J_NEGATIVE: 0,
        J_POSITIVE: 0,
        J_UNRESOLVED: 0,
        H1_UNRESOLVED: 0,
    }
    method_counts = {
        name: {J_NEGATIVE: 0, J_POSITIVE: 0, J_UNRESOLVED: 0, H1_UNRESOLVED: 0}
        for name in ("A", "B", "C")
    }
    second_order_h1_recovery_count = 0

    while queue:
        lo, hi, depth = queue.pop(0)
        if evaluated >= max_cells:
            budget_exhausted_leaf_count += 1
            leaves.append(
                {
                    "Q": int(hull["Q"]),
                    "depth": depth,
                    "lo_num": lo,
                    "hi_num": hi,
                    "den": int(hull["den"]),
                    "orientation": J_UNRESOLVED,
                    "reason": "MAX_CELL_BUDGET",
                }
            )
            continue

        row = sharp_trajectory_cell_record(
            int(hull["Q"]), lo, hi, int(hull["den"]), depth
        )
        evaluated += 1
        max_evaluated_depth = max(max_evaluated_depth, depth)
        resolved_counts[row["orientation"]] += 1
        for name in ("A", "B", "C"):
            method_counts[name][row[f"method_{name}_orientation"]] += 1
        if row["second_order_h1"] and not row["first_order_h1"]:
            second_order_h1_recovery_count += 1

        if (
            row["orientation"] in (J_NEGATIVE, J_POSITIVE)
            or depth >= max_depth
            or hi - lo <= 2
        ):
            leaves.append(row)
            continue

        mid = (lo + hi) // 2
        if not lo < mid < hi:
            leaves.append(row)
            continue
        queue.append((lo, mid, depth + 1))
        queue.append((mid, hi, depth + 1))

    leaves.sort(key=lambda row: row["lo_num"])
    if not leaves:
        raise AssertionError("sharp trajectory localization produced no leaves")
    if leaves[0]["lo_num"] != int(hull["lo_num"]) or leaves[-1]["hi_num"] != int(
        hull["hi_num"]
    ):
        raise AssertionError("sharp trajectory cover does not span inherited hull")
    for left, right in zip(leaves, leaves[1:]):
        if left["hi_num"] != right["lo_num"]:
            raise AssertionError("sharp trajectory cover has a gap or overlap")

    classification = _classify_cover(leaves)
    signed_leaf_orientations = {
        row["orientation"]
        for row in leaves
        if row["orientation"] in (J_POSITIVE, J_NEGATIVE)
    }
    uniform_orientation = (
        next(iter(signed_leaf_orientations))
        if not classification["unresolved_spans"] and len(signed_leaf_orientations) == 1
        else None
    )

    return {
        "hull": dict(hull),
        "evaluated_cell_count": evaluated,
        "leaf_count": len(leaves),
        "max_depth": int(max_depth),
        "max_cells": int(max_cells),
        "max_evaluated_depth": int(max_evaluated_depth),
        "evaluated_orientation_counts": resolved_counts,
        "method_orientation_counts": method_counts,
        "second_order_h1_recovery_count": int(second_order_h1_recovery_count),
        "budget_exhausted_leaf_count": int(budget_exhausted_leaf_count),
        "representation_conflict_count": 0,
        "uniform_orientation": uniform_orientation,
        "leaves": leaves,
        **classification,
    }


def synthetic_second_order_controls() -> dict:
    """Controls for orientation resolution and a true fold crossing."""
    positive = resolve_method_orientations(
        J_UNRESOLVED, J_POSITIVE, J_POSITIVE, second_order_h1=True
    )
    negative = resolve_method_orientations(
        J_NEGATIVE, J_UNRESOLVED, J_NEGATIVE, second_order_h1=True
    )
    conflict = resolve_method_orientations(
        J_POSITIVE, J_NEGATIVE, J_UNRESOLVED, second_order_h1=True
    )

    x = arb("0", "1")
    fold_J = 2 * x
    fold_orientation = _orientation(fold_J)

    passed = (
        positive["orientation"] == J_POSITIVE
        and negative["orientation"] == J_NEGATIVE
        and conflict["representation_conflict"]
        and fold_orientation == J_UNRESOLVED
    )
    return {
        "status": "PASS" if passed else "FAIL",
        "positive_resolution": positive,
        "negative_resolution": negative,
        "conflict_detected": conflict["representation_conflict"],
        "fold_interval_orientation": fold_orientation,
    }


def audit_sharp_parity_trajectory(
    schedule: dict,
    *,
    precision_bits: int,
    max_depth: int,
    max_cells: int,
) -> dict:
    set_precision(precision_bits)

    baseline = audit_parity_trajectory(
        schedule,
        precision_bits=precision_bits,
        max_depth=max_depth,
        max_cells=max_cells,
    )
    hull = primary_hull(schedule["boxes"])
    sharp = localize_sharp_trajectory(
        hull,
        max_depth=max_depth,
        max_cells=max_cells,
    )
    controls = synthetic_second_order_controls()

    return {
        "status": "PASS",
        "scope": "Q14_FIXED_TRAJECTORY_SECOND_ORDER_RESEARCH_ONLY",
        "precision_bits": int(precision_bits),
        "baseline_post193": baseline,
        "sharp_localization": sharp,
        "synthetic_second_order_controls": controls,
        "interpretation": {
            "method_A": "FROZEN_POST193_FIRST_ORDER_WRONSKIAN",
            "method_B": "DIRECT_P2_LOG_SLOPE_WITH_SECOND_ORDER_CENTERING",
            "method_C": "CENTERED_WRONSKIAN_TRANSPORT_USING_J_PRIME",
            "J_prime_identity": "o_second*e - e_second*o",
            "new_selector": False,
        },
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
