#!/usr/bin/env python3
"""Full-composite parity-gap mechanism audit for the post-#202 FB-05 frontier.

The experiment does not split the source into selectable channels.  It keeps the
assembled normalized even predecessor E and the trace-zero full-composite gap

    G = O - E

with the exact algebraic identity

    Jbar = O' E - E' O = E G' - E' G.

A predeclared six-center kill-switch tests E>0, G>0, G'>=0, E'<=0 before the
completed 49-leaf #197 partition is evaluated.  If the pattern fails at any
frozen primary center, the full-cover mechanism audit is not run.

Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

from flint import arb

from canonical_source_arb import ball_record, definitely_positive, set_precision
from post166_fb05_cell_interval import arb_unit_interval, cell_coordinate_L_arb
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR, scalar_geometry
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_second_derivative_scalar_record_arb_at_L,
)
from post194_fb05_q14_parity_trajectory_sharp_enclosure import (
    centered_first_derivative_enclosure,
    centered_second_order_enclosure,
)
from post198_fb05_q14_parity_source_mechanism import _direct_normalized_method_c
from post202_fb05_q14_parity_contrast_jets import (
    parity_gap_contrast_jets,
    parity_gap_contrast_json,
)

PATTERN_FALSIFIED = "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED"
PATTERN_LOCK = "COMPOSITE_PARITY_GAP_LOCK"
COOPERATIVE_LOCK = "COOPERATIVE_COMPOSITE_LOCK"
MIXED_RECONSTRUCTABLE = "MIXED_COMPOSITE_RECONSTRUCTABLE"
DEPENDENCY_UNRESOLVED = "COMPOSITE_PARITY_GAP_DEPENDENCY_UNRESOLVED"


def _overlap(left: arb, right: arb) -> bool:
    return bool((left - right).contains(0))


def _nonnegative(value: arb) -> bool:
    return bool(value >= 0)


def _nonpositive(value: arb) -> bool:
    return bool(value <= 0)


def _normalized_levels(Q: int, L: arb) -> dict:
    rec = fixed_unit_second_derivative_scalar_record_arb_at_L(Q, L)
    we = arb(scalar_geometry("even").W_norm_sq)
    wo = arb(scalar_geometry("odd").W_norm_sq)
    return {
        "E": rec["even"]["a"] / we,
        "E_prime": rec["even"]["a_prime"] / we,
        "E_second": rec["even"]["a_second"] / we,
        "O": rec["odd_N2_predecessor"] / wo,
        "O_prime": rec["odd_N2_predecessor_prime"] / wo,
        "O_second": rec["odd_N2_predecessor_second"] / wo,
    }


def _cell_coordinates(cell: dict) -> tuple[int, int, int, int, arb, arb]:
    Q = int(cell["Q"])
    lo = int(cell["lo_num"])
    hi = int(cell["hi_num"])
    den = int(cell["den"])
    center_num = int(cell.get("center_num", (lo + hi) // 2))
    L_interval = cell_coordinate_L_arb(Q, arb_unit_interval(lo, hi, den))
    L_center = cell_coordinate_L_arb(Q, arb(center_num) / den)
    return Q, lo, hi, den, L_center, L_interval


def _contrast_reconstructs_level_difference(levels: dict, gap: dict) -> dict:
    return {
        "G_matches_O_minus_E": _overlap(gap["G"], levels["O"] - levels["E"]),
        "G_prime_matches_O_prime_minus_E_prime": _overlap(
            gap["G_prime"], levels["O_prime"] - levels["E_prime"]
        ),
        "G_second_matches_O_second_minus_E_second": _overlap(
            gap["G_second"], levels["O_second"] - levels["E_second"]
        ),
    }


def center_pattern_record(cell: dict) -> dict:
    Q, lo, hi, den, L_center, _ = _cell_coordinates(cell)
    center_num = int(cell.get("center_num", (lo + hi) // 2))
    levels = _normalized_levels(Q, L_center)
    gap = parity_gap_contrast_jets(L_center, TARGET_KSTAR, Q)
    reconstruction = _contrast_reconstructs_level_difference(levels, gap)
    if not all(reconstruction.values()):
        raise AssertionError("center parity-gap contrast failed O-E reconstruction")

    checks = {
        "E_strict_positive": definitely_positive(levels["E"]),
        "G_strict_positive": definitely_positive(gap["G"]),
        "G_prime_nonnegative": _nonnegative(gap["G_prime"]),
        "E_prime_nonpositive": _nonpositive(levels["E_prime"]),
    }
    return {
        "label": cell.get("label"),
        "Q": Q,
        "lo_num": lo,
        "hi_num": hi,
        "center_num": center_num,
        "den": den,
        "L_center": ball_record(L_center),
        "E": ball_record(levels["E"]),
        "E_prime": ball_record(levels["E_prime"]),
        "G": ball_record(gap["G"]),
        "G_prime": ball_record(gap["G_prime"]),
        "pattern_checks": checks,
        "pattern_passes": all(checks.values()),
        "reconstruction": reconstruction,
    }


def exact_center_kill_switch(schedule: dict) -> dict:
    primaries = [box for box in schedule["boxes"] if bool(box["primary"])]
    if len(primaries) != 6:
        raise AssertionError("post-#202 kill-switch requires the exact six inherited primary boxes")
    rows = [center_pattern_record(box) for box in primaries]
    return {
        "primary_center_count": len(rows),
        "survives": all(row["pattern_passes"] for row in rows),
        "rows": rows,
    }


def composite_gap_cell_record(cell: dict, *, require_direct_positive: bool) -> dict:
    Q, lo, hi, den, L_center, L_interval = _cell_coordinates(cell)
    center_num = int(cell.get("center_num", (lo + hi) // 2))
    center_levels = _normalized_levels(Q, L_center)
    interval_levels = _normalized_levels(Q, L_interval)
    center_gap = parity_gap_contrast_jets(L_center, TARGET_KSTAR, Q)
    interval_gap = parity_gap_contrast_jets(L_interval, TARGET_KSTAR, Q)

    center_reconstruction = _contrast_reconstructs_level_difference(center_levels, center_gap)
    interval_reconstruction = _contrast_reconstructs_level_difference(interval_levels, interval_gap)
    if not all(center_reconstruction.values()) or not all(interval_reconstruction.values()):
        raise AssertionError("parity-gap contrast failed normalized O-E reconstruction")

    E0 = center_levels["E"]
    Ep0 = center_levels["E_prime"]
    EppI = interval_levels["E_second"]
    G0 = center_gap["G"]
    Gp0 = center_gap["G_prime"]
    GppI = interval_gap["G_second"]

    E = centered_second_order_enclosure(E0, Ep0, EppI, L_interval, L_center)
    Ep = centered_first_derivative_enclosure(Ep0, EppI, L_interval, L_center)
    G = centered_second_order_enclosure(G0, Gp0, GppI, L_interval, L_center)
    Gp = centered_first_derivative_enclosure(Gp0, GppI, L_interval, L_center)

    J_center = E0 * Gp0 - Ep0 * G0
    J_prime_interval = E * GppI - EppI * G
    J_transport = J_center + J_prime_interval * (L_interval - L_center)
    direct = _direct_normalized_method_c(Q, L_center, L_interval)
    direct_overlap = _overlap(J_transport, direct["J_transport"])
    if not direct_overlap:
        raise AssertionError("parity-gap J transport failed independent direct Method-C reconstruction")
    direct_positive = definitely_positive(direct["J_transport"])
    if require_direct_positive and not direct_positive:
        raise AssertionError("post-#197 direct Method-C positivity failed to replay")

    T1 = E * Gp
    T2 = -Ep * G
    factor_sum = T1 + T2
    factor_transport_overlap = _overlap(factor_sum, J_transport)
    if not factor_transport_overlap:
        raise AssertionError("composite factor interval and transported J enclosures are disjoint")

    pattern_checks = {
        "E_strict_positive": definitely_positive(E),
        "G_strict_positive": definitely_positive(G),
        "G_prime_nonnegative": _nonnegative(Gp),
        "E_prime_nonpositive": _nonpositive(Ep),
    }
    factor_checks = {
        "T1_nonnegative": _nonnegative(T1),
        "T2_nonnegative": _nonnegative(T2),
        "factor_sum_strict_positive": definitely_positive(factor_sum),
        "gap_transport_strict_positive": definitely_positive(J_transport),
    }
    pattern_lock = all(pattern_checks.values()) and factor_checks["factor_sum_strict_positive"]
    cooperative_lock = (
        factor_checks["T1_nonnegative"]
        and factor_checks["T2_nonnegative"]
        and factor_checks["factor_sum_strict_positive"]
    )

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
        "E": ball_record(E),
        "E_prime": ball_record(Ep),
        "G": ball_record(G),
        "G_prime": ball_record(Gp),
        "G_second_interval": ball_record(GppI),
        "J_center": ball_record(J_center),
        "J_prime_interval": ball_record(J_prime_interval),
        "J_transport": ball_record(J_transport),
        "T1_E_times_G_prime": ball_record(T1),
        "T2_neg_E_prime_times_G": ball_record(T2),
        "factor_sum": ball_record(factor_sum),
        "pattern_checks": pattern_checks,
        "factor_checks": factor_checks,
        "pattern_lock": pattern_lock,
        "cooperative_lock": cooperative_lock,
        "direct_method_c_positive": direct_positive,
        "checks": {
            "center_gap_reconstruction": center_reconstruction,
            "interval_gap_reconstruction": interval_reconstruction,
            "gap_transport_direct_method_c_overlap": direct_overlap,
            "factor_sum_gap_transport_overlap": factor_transport_overlap,
            "scalar_cancellation_before_interval_transport": True,
        },
        "center_gap": parity_gap_contrast_json(center_gap),
    }


def summarize_composite_rows(rows: list[dict]) -> dict:
    if not rows:
        raise ValueError("composite summary requires completed-cover rows")
    all_gap_positive = all(row["factor_checks"]["gap_transport_strict_positive"] for row in rows)
    all_pattern = all(bool(row["pattern_lock"]) for row in rows)
    all_cooperative = all(bool(row["cooperative_lock"]) for row in rows)
    if not all_gap_positive:
        classification = DEPENDENCY_UNRESOLVED
    elif all_pattern:
        classification = PATTERN_LOCK
    elif all_cooperative:
        classification = COOPERATIVE_LOCK
    else:
        classification = MIXED_RECONSTRUCTABLE
    return {
        "classification": classification,
        "all_gap_transports_positive": all_gap_positive,
        "all_leaves_pattern_lock": all_pattern,
        "all_leaves_cooperative_lock": all_cooperative,
        "pattern_lock_leaf_count": sum(bool(row["pattern_lock"]) for row in rows),
        "cooperative_lock_leaf_count": sum(bool(row["cooperative_lock"]) for row in rows),
        "gap_positive_leaf_count": sum(
            bool(row["factor_checks"]["gap_transport_strict_positive"]) for row in rows
        ),
        "gap_unresolved_leaf_count": sum(
            not bool(row["factor_checks"]["gap_transport_strict_positive"]) for row in rows
        ),
    }


def audit_composite_parity_gap(schedule: dict, completed_cover: dict, *, precision_bits: int) -> dict:
    set_precision(precision_bits)
    gate = exact_center_kill_switch(schedule)
    if not gate["survives"]:
        return {
            "status": "PASS",
            "scope": "Q14_POST202_FULL_COMPOSITE_PARITY_GAP_RESEARCH_ONLY",
            "center_kill_switch": gate,
            "full_cover_executed": False,
            "completed_leaf_count": 0,
            "mechanism_classification": PATTERN_FALSIFIED,
            "summary": None,
            "control_transfer_status": "PATTERN_FALSIFIED_BEFORE_FULL_COVER",
            "primary_cells": [],
            "control_rows": [],
            "theorem_promotion": False,
            "fb05_closed": False,
            "negative_root_exclusion": False,
            "rh_claim": False,
        }

    leaves = completed_cover["leaves"]
    primary_rows = [
        composite_gap_cell_record(row, require_direct_positive=True) for row in leaves
    ]
    summary = summarize_composite_rows(primary_rows)
    classification = summary["classification"]

    controls = []
    selected_kind = classification if classification in (PATTERN_LOCK, COOPERATIVE_LOCK) else None
    for box in schedule["boxes"]:
        if bool(box["primary"]):
            continue
        row = composite_gap_cell_record(box, require_direct_positive=False)
        if selected_kind == PATTERN_LOCK:
            selected_survives = bool(row["pattern_lock"])
        elif selected_kind == COOPERATIVE_LOCK:
            selected_survives = bool(row["cooperative_lock"])
        else:
            selected_survives = None
        row["falsification"] = {
            "selected_primary_mechanism": selected_kind,
            "selected_mechanism_survives_control": selected_survives,
            "control_class": "ADJACENT_Q_TRANSFER" if int(box["Q"]) != 14 else "Q14_INTERNAL",
        }
        controls.append(row)

    if selected_kind is None:
        transfer_status = "NO_UNIQUE_COMPOSITE_LOCK"
    else:
        adjacent = [
            row for row in controls
            if row["falsification"]["control_class"] == "ADJACENT_Q_TRANSFER"
        ]
        transfer_status = (
            "COMPOSITE_LOCK_SURVIVES_Q13_Q15_CONTROLS"
            if adjacent and all(row["falsification"]["selected_mechanism_survives_control"] for row in adjacent)
            else "Q14_LOCAL_COMPOSITE_ONLY"
        )

    return {
        "status": "PASS",
        "scope": "Q14_POST202_FULL_COMPOSITE_PARITY_GAP_RESEARCH_ONLY",
        "center_kill_switch": gate,
        "full_cover_executed": True,
        "completed_leaf_count": len(primary_rows),
        "mechanism_classification": classification,
        "summary": summary,
        "control_transfer_status": transfer_status,
        "primary_cells": primary_rows,
        "control_rows": controls,
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
