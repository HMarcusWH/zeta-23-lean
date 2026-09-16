#!/usr/bin/env python3
"""Source-mechanism audit for the complete post-#197 Q14 parity orientation.

The audit works on normalized even/odd predecessor levels, decomposes both the
repository four-way source convention and the collapsed direct-production
three-way convention, reconstructs J and J', and transports every interaction
through the same centered second-order finite-width graph used by Method C.
Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

from itertools import combinations

from flint import arb

from canonical_source_arb import ball_record, definitely_negative, definitely_positive, set_precision
from post166_fb05_cell_interval import _arb_matrix_from_sympy, arb_unit_interval, cell_coordinate_L_arb
from post169_fb05_schur_visibility import one_step_geometry
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR, TARGET_N, scalar_geometry
from post194_fb05_q14_fixed_unit_second_derivative import fixed_unit_second_derivative_scalar_record_arb_at_L
from post194_fb05_q14_parity_trajectory_sharp_enclosure import centered_second_order_enclosure
from post198_fb05_q14_four_way_channel_second_derivative import (
    CHANNEL_NAMES,
    collapse_direct_arch_channel_jets,
    fixed_unit_four_way_channel_jets,
)

FOUR_WAY_CHANNELS = CHANNEL_NAMES
COLLAPSED_CHANNELS = ("pole", "direct_arch_signed", "prime_signed")


def _overlap(x: arb, y: arb) -> bool:
    return bool((x - y).contains(0))


def _nonnegative(x: arb) -> bool:
    return bool(x >= 0)


def _restrict_normalized_predecessor(matrix, parity: str) -> arb:
    geom = one_step_geometry(TARGET_N, parity)
    B = _arb_matrix_from_sympy(geom.step_basis_exact)
    H = B.transpose() * matrix * B
    norms = scalar_geometry(parity)
    return H[0, 0] / arb(norms.W_norm_sq)


def normalized_predecessor_channel_jets(jets: dict, *, collapsed: bool = False) -> dict:
    channels = collapse_direct_arch_channel_jets(jets) if collapsed else jets["channels"]
    out = {}
    for name, row in channels.items():
        out[name] = {
            "E": _restrict_normalized_predecessor(row["matrix"], "even"),
            "Ep": _restrict_normalized_predecessor(row["matrix_prime"], "even"),
            "Epp": _restrict_normalized_predecessor(row["matrix_second"], "even"),
            "O": _restrict_normalized_predecessor(row["matrix"], "odd"),
            "Op": _restrict_normalized_predecessor(row["matrix_prime"], "odd"),
            "Opp": _restrict_normalized_predecessor(row["matrix_second"], "odd"),
        }
    return out


def _group_name(left: str, right: str | None = None) -> str:
    return left if right is None else f"{left}__x__{right}"


def interaction_transport(
    center: dict,
    interval: dict,
    L_interval: arb,
    L_center: arb,
) -> dict:
    names = tuple(center)
    if set(names) != set(interval):
        raise AssertionError("channel name drift between center and interval")
    taylor = {}
    for name in names:
        c = center[name]
        i = interval[name]
        taylor[name] = {
            "E": centered_second_order_enclosure(c["E"], c["Ep"], i["Epp"], L_interval, L_center),
            "O": centered_second_order_enclosure(c["O"], c["Op"], i["Opp"], L_interval, L_center),
            "Epp": i["Epp"],
            "Opp": i["Opp"],
        }

    group_center = {}
    group_prime = {}
    for name in names:
        c = center[name]
        t = taylor[name]
        g = _group_name(name)
        group_center[g] = c["Op"] * c["E"] - c["Ep"] * c["O"]
        group_prime[g] = t["Opp"] * t["E"] - t["Epp"] * t["O"]

    for left, right in combinations(names, 2):
        a = center[left]
        b = center[right]
        ta = taylor[left]
        tb = taylor[right]
        g = _group_name(left, right)
        group_center[g] = (
            a["Op"] * b["E"] + b["Op"] * a["E"]
            - a["Ep"] * b["O"] - b["Ep"] * a["O"]
        )
        group_prime[g] = (
            ta["Opp"] * tb["E"] + tb["Opp"] * ta["E"]
            - ta["Epp"] * tb["O"] - tb["Epp"] * ta["O"]
        )

    delta = L_interval - L_center
    transported = {name: group_center[name] + group_prime[name] * delta for name in group_center}
    source_sum = sum(transported.values(), arb(0))
    dominance = {}
    for name, value in transported.items():
        remainder = sum((abs(other) for key, other in transported.items() if key != name), arb(0))
        dominance[name] = value - remainder
    locks = sorted(name for name, margin in dominance.items() if definitely_positive(margin))
    return {
        "groups": transported,
        "group_centers": group_center,
        "group_prime_intervals": group_prime,
        "dominance_margins": dominance,
        "dominance_locks": locks,
        "source_sum": source_sum,
        "source_sum_positive": definitely_positive(source_sum),
        "all_groups_nonnegative": all(_nonnegative(value) for value in transported.values()),
        "has_positive_group": any(definitely_positive(value) for value in transported.values()),
        "has_negative_group": any(definitely_negative(value) for value in transported.values()),
    }


def _direct_normalized_method_c(Q: int, L_center: arb, L_interval: arb) -> dict:
    center = fixed_unit_second_derivative_scalar_record_arb_at_L(Q, L_center)
    interval = fixed_unit_second_derivative_scalar_record_arb_at_L(Q, L_interval)
    we = arb(scalar_geometry("even").W_norm_sq)
    wo = arb(scalar_geometry("odd").W_norm_sq)
    E0 = center["even"]["a"] / we
    Ep0 = center["even"]["a_prime"] / we
    EppI = interval["even"]["a_second"] / we
    O0 = center["odd_N2_predecessor"] / wo
    Op0 = center["odd_N2_predecessor_prime"] / wo
    OppI = interval["odd_N2_predecessor_second"] / wo
    E = centered_second_order_enclosure(E0, Ep0, EppI, L_interval, L_center)
    O = centered_second_order_enclosure(O0, Op0, OppI, L_interval, L_center)
    J0 = Op0 * E0 - Ep0 * O0
    Jp = OppI * E - EppI * O
    J = J0 + Jp * (L_interval - L_center)
    raw_scale = we * wo
    return {
        "E": E,
        "O": O,
        "J_center": J0,
        "J_prime_interval": Jp,
        "J_transport": J,
        "raw_scale": raw_scale,
    }


def _json_interaction(record: dict) -> dict:
    return {
        "groups": {name: ball_record(value) for name, value in record["groups"].items()},
        "group_centers": {name: ball_record(value) for name, value in record["group_centers"].items()},
        "group_prime_intervals": {name: ball_record(value) for name, value in record["group_prime_intervals"].items()},
        "dominance_margins": {name: ball_record(value) for name, value in record["dominance_margins"].items()},
        "dominance_locks": record["dominance_locks"],
        "source_sum": ball_record(record["source_sum"]),
        "source_sum_positive": record["source_sum_positive"],
        "all_groups_nonnegative": record["all_groups_nonnegative"],
        "has_positive_group": record["has_positive_group"],
        "has_negative_group": record["has_negative_group"],
    }


def source_mechanism_cell_record(cell: dict) -> dict:
    Q = int(cell["Q"])
    lo = int(cell["lo_num"])
    hi = int(cell["hi_num"])
    den = int(cell["den"])
    center_num = int(cell.get("center_num", (lo + hi) // 2))
    L_interval = cell_coordinate_L_arb(Q, arb_unit_interval(lo, hi, den))
    L_center = cell_coordinate_L_arb(Q, arb(center_num) / den)

    center_jets = fixed_unit_four_way_channel_jets(L_center, TARGET_KSTAR, Q)
    interval_jets = fixed_unit_four_way_channel_jets(L_interval, TARGET_KSTAR, Q)
    if not all(center_jets["reconstruction"].values()) or not all(interval_jets["reconstruction"].values()):
        raise AssertionError("four-way source-jet reconstruction failed")

    four_center = normalized_predecessor_channel_jets(center_jets)
    four_interval = normalized_predecessor_channel_jets(interval_jets)
    three_center = normalized_predecessor_channel_jets(center_jets, collapsed=True)
    three_interval = normalized_predecessor_channel_jets(interval_jets, collapsed=True)
    four = interaction_transport(four_center, four_interval, L_interval, L_center)
    three = interaction_transport(three_center, three_interval, L_interval, L_center)
    direct = _direct_normalized_method_c(Q, L_center, L_interval)

    four_direct_overlap = _overlap(four["source_sum"], direct["J_transport"])
    three_direct_overlap = _overlap(three["source_sum"], direct["J_transport"])
    four_three_overlap = _overlap(four["source_sum"], three["source_sum"])
    if not (four_direct_overlap and three_direct_overlap and four_three_overlap):
        raise AssertionError("source interaction transport failed to reconstruct direct Method C")

    scalar_self = _group_name("scalar_shift")
    scalar_self_zero = bool(four["groups"][scalar_self].contains(0))
    if not scalar_self_zero:
        raise AssertionError("normalized scalar-shift self-Wronskian lost its zero identity")

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
        "L_center": ball_record(L_center),
        "L_interval": ball_record(L_interval),
        "direct": {
            "J_center": ball_record(direct["J_center"]),
            "J_prime_interval": ball_record(direct["J_prime_interval"]),
            "J_transport": ball_record(direct["J_transport"]),
            "J_transport_positive": definitely_positive(direct["J_transport"]),
        },
        "four_way": _json_interaction(four),
        "collapsed_three_way": _json_interaction(three),
        "checks": {
            "four_way_direct_transport_overlap": four_direct_overlap,
            "collapsed_direct_transport_overlap": three_direct_overlap,
            "four_way_collapsed_transport_overlap": four_three_overlap,
            "scalar_shift_self_wronskian_contains_zero": scalar_self_zero,
            "center_matrix_reconstruction": center_jets["reconstruction"],
            "interval_matrix_reconstruction": interval_jets["reconstruction"],
        },
    }


def summarize_representation(rows: list[dict], key: str) -> dict:
    if not rows:
        raise ValueError("mechanism summary requires cells")
    lock_sets = [set(row[key]["dominance_locks"]) for row in rows]
    common = set.intersection(*lock_sets) if lock_sets else set()
    every_locked = all(bool(s) for s in lock_sets)
    all_source_positive = all(bool(row[key]["source_sum_positive"]) for row in rows)
    all_nonnegative = all(bool(row[key]["all_groups_nonnegative"]) for row in rows)
    if not all_source_positive:
        classification = "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED"
    elif common:
        classification = "UNIFORM_LOCK"
    elif every_locked:
        classification = "REGIME_SWITCHING_LOCK"
    elif all_nonnegative:
        classification = "COOPERATIVE_NONNEGATIVE"
    else:
        classification = "MIXED_SIGN_NO_SINGLE_LOCK"
    return {
        "classification": classification,
        "uniform_lock_groups": sorted(common),
        "every_leaf_has_some_lock": every_locked,
        "all_source_sums_positive": all_source_positive,
        "all_groups_nonnegative_on_every_leaf": all_nonnegative,
        "leaf_lock_histogram": {
            name: sum(name in row[key]["dominance_locks"] for row in rows)
            for name in sorted({g for row in rows for g in row[key]["dominance_locks"]})
        },
    }


def joint_mechanism_classification(four: dict, three: dict) -> str:
    if "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED" in (four["classification"], three["classification"]):
        return "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED"
    if three["classification"] == "UNIFORM_LOCK" and four["classification"] == "UNIFORM_LOCK":
        return "REPRESENTATION_STABLE_UNIFORM_LOCK"
    if three["classification"] == "UNIFORM_LOCK":
        return "DIRECT_ARCH_COLLAPSE_LOCK"
    if four["classification"] == "UNIFORM_LOCK":
        return "FOUR_WAY_ONLY_LOCK"
    if "REGIME_SWITCHING_LOCK" in (four["classification"], three["classification"]):
        return "REGIME_SWITCHING_LOCK"
    if four["classification"] == three["classification"] == "COOPERATIVE_NONNEGATIVE":
        return "COOPERATIVE_NONNEGATIVE"
    return "MIXED_SIGN_NO_SINGLE_LOCK"


def audit_source_mechanism(schedule: dict, completed_cover: dict, *, precision_bits: int) -> dict:
    set_precision(precision_bits)
    leaves = completed_cover["leaves"]
    primary_rows = [source_mechanism_cell_record(row) for row in leaves]
    if not all(row["direct"]["J_transport_positive"] for row in primary_rows):
        raise AssertionError("post-#197 direct Method C positivity failed to replay")
    four_summary = summarize_representation(primary_rows, "four_way")
    three_summary = summarize_representation(primary_rows, "collapsed_three_way")
    joint = joint_mechanism_classification(four_summary, three_summary)

    selected = None
    if len(three_summary["uniform_lock_groups"]) == 1:
        selected = three_summary["uniform_lock_groups"][0]

    controls = []
    for box in schedule["boxes"]:
        if bool(box["primary"]):
            continue
        row = source_mechanism_cell_record(box)
        locks = row["collapsed_three_way"]["dominance_locks"]
        row["falsification"] = {
            "selected_collapsed_lock_group": selected,
            "selected_group_locks_control": None if selected is None else selected in locks,
            "control_class": "ADJACENT_Q_TRANSFER" if int(box["Q"]) != 14 else "Q14_INTERNAL",
        }
        controls.append(row)

    if selected is None:
        transfer_status = "NO_UNIQUE_COLLAPSED_UNIFORM_LOCK"
    else:
        adjacent = [row for row in controls if row["falsification"]["control_class"] == "ADJACENT_Q_TRANSFER"]
        transfer_status = (
            "SELECTED_LOCK_SURVIVES_Q13_Q15_CONTROLS"
            if adjacent and all(row["falsification"]["selected_group_locks_control"] for row in adjacent)
            else "Q14_LOCAL_MECHANISM_ONLY"
        )

    return {
        "status": "PASS",
        "scope": "Q14_POST197_PARITY_SOURCE_MECHANISM_RESEARCH_ONLY",
        "completed_leaf_count": len(leaves),
        "primary_cells": primary_rows,
        "four_way_summary": four_summary,
        "collapsed_three_way_summary": three_summary,
        "mechanism_classification": joint,
        "selected_collapsed_uniform_lock_group": selected,
        "control_rows": controls,
        "control_transfer_status": transfer_status,
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
