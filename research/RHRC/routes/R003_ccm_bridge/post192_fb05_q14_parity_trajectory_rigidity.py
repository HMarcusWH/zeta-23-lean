#!/usr/bin/env python3
"""Post-#192 Q14 parity-trajectory rigidity audit.

The post-#190 ambient reflected twin survives the frozen selector algebra, while
PR #192 showed that its specific negative-scalar realization is not canonical
and that the bounded canonical replay still leaves the general twin question
UNRESOLVED.  This module attacks the surviving mechanism along the actual
fixed-Q aperture trajectory.

No new selector is introduced.  The only trajectory coordinates used here are
the already-frozen post-#188 parity quantities

    P1 = (o / ||W_o||^2) / (e / ||W_e||^2)
    P2 = L * (o'/o - e'/e),

where e is the even N2 predecessor and o the odd N2 predecessor produced from
the *same* canonical M(L), M'(L) evaluation.  Their common derivative graph is
controlled by

    J = o' e - e' o,

so, whenever L,e,o are positive,

    sign(P1') = sign(P2) = sign(J).

Finite-width H1 recovery uses a centered mean-value enclosure rather than raw
wide-box values.  Deterministic dyadic subdivision is only a localizer for the
remaining J=0/fold region; bounded non-resolution never counts as nonexistence.

Research/audit tooling only.  No output here is Lean theorem authority.
FB-05, negative-root exclusion, and RH remain OPEN.
"""
from __future__ import annotations

from fractions import Fraction

from flint import arb

from canonical_source_arb import ball_record, definitely_negative, definitely_positive, set_precision
from post166_fb05_cell_interval import arb_unit_interval, cell_coordinate_L_arb
from post173_fb05_q13_scalar_barrier import scalar_geometry
from post177_fb05_q13_fixed_unit_derivative import fixed_unit_derivative_scalar_record_arb_at_L
from post187_fb05_q14_mixed_drift_selector import selector_record_from_box

J_NEGATIVE = "J_NEGATIVE"
J_POSITIVE = "J_POSITIVE"
J_UNRESOLVED = "J_UNRESOLVED"
H1_UNRESOLVED = "H1_UNRESOLVED"

GLOBAL_MONOTONE_ORIENTATION = "GLOBAL_MONOTONE_ORIENTATION"
SINGLE_FOLD_REGION_LOCALIZED = "SINGLE_FOLD_REGION_LOCALIZED"
MULTIPLE_FOLD_REGIONS = "MULTIPLE_FOLD_REGIONS"
PARTIAL_TRAJECTORY_ORIENTATION = "PARTIAL_TRAJECTORY_ORIENTATION"
TRAJECTORY_RIGIDITY_UNRESOLVED = "TRAJECTORY_RIGIDITY_UNRESOLVED"


def overlap(x: arb, y: arb) -> bool:
    return bool((x - y).contains(0))


def centered_predecessor_enclosure(
    center_value: arb,
    derivative_interval: arb,
    L_interval: arb,
    L_center: arb,
) -> arb:
    """Mean-value enclosure f(I) subset f(c)+f'(I)(I-c)."""
    return center_value + derivative_interval * (L_interval - L_center)


def parity_coordinates_from_same_state(record: dict) -> dict:
    """Reconstruct frozen P1/P2 and the Wronskian J from one canonical state."""
    even = record["even"]
    e = even["a"]
    ep = even["a_prime"]
    o = record["odd_N2_predecessor"]
    op = record["odd_N2_predecessor_prime"]
    L = record["L"]
    even_norm = arb(scalar_geometry("even").W_norm_sq)
    odd_norm = arb(scalar_geometry("odd").W_norm_sq)
    J = op * e - ep * o
    p1 = (o / odd_norm) / (e / even_norm)
    p2 = L * (op / o - ep / e)
    p2_from_J = L * J / (o * e)
    p1_prime_from_J = (even_norm / odd_norm) * J / (e * e)
    return {
        "e": e,
        "e_prime": ep,
        "o": o,
        "o_prime": op,
        "J": J,
        "P1": p1,
        "P2": p2,
        "P2_from_J": p2_from_J,
        "P1_prime_from_J": p1_prime_from_J,
    }


def inherited_center_crosscheck(box: dict) -> dict:
    """Cross-check reconstructed P1/P2 against the frozen #188 selector graph."""
    den = int(box["den"])
    L = cell_coordinate_L_arb(int(box["Q"]), arb(int(box["center_num"])) / den)
    state = fixed_unit_derivative_scalar_record_arb_at_L(int(box["Q"]), L)
    ours = parity_coordinates_from_same_state(state)
    inherited = selector_record_from_box(box)
    if inherited["scope"] != "CERTIFIED_H1_SCOPE":
        return {
            "label": box["label"],
            "scope": inherited["scope"],
            "P1_overlap": False,
            "P2_overlap": False,
            "P2_J_identity_overlap": overlap(ours["P2"], ours["P2_from_J"]),
        }
    p1_existing = inherited["candidates"]["parity_predecessor_ratio"]
    p2_existing = inherited["candidates"]["parity_log_slope_gap"]
    return {
        "label": box["label"],
        "scope": inherited["scope"],
        "P1_overlap": overlap(ours["P1"], p1_existing),
        "P2_overlap": overlap(ours["P2"], p2_existing),
        "P2_J_identity_overlap": overlap(ours["P2"], ours["P2_from_J"]),
        "P1": ball_record(ours["P1"]),
        "P2": ball_record(ours["P2"]),
        "J": ball_record(ours["J"]),
    }


def primary_hull(boxes: list[dict]) -> dict:
    primaries = [box for box in boxes if bool(box["primary"])]
    if not primaries:
        raise ValueError("trajectory audit requires inherited primary boxes")
    qs = {int(box["Q"]) for box in primaries}
    dens = {int(box["den"]) for box in primaries}
    if len(qs) != 1 or len(dens) != 1:
        raise AssertionError("primary trajectory hull requires one Q and one dyadic denominator")
    Q = next(iter(qs))
    den = next(iter(dens))
    lo = min(int(box["lo_num"]) for box in primaries)
    hi = max(int(box["hi_num"]) for box in primaries)
    if not 0 <= lo < hi <= den:
        raise AssertionError("invalid inherited primary hull")
    return {"Q": Q, "lo_num": lo, "hi_num": hi, "den": den}


def _orientation(J: arb) -> str:
    if definitely_negative(J):
        return J_NEGATIVE
    if definitely_positive(J):
        return J_POSITIVE
    return J_UNRESOLVED


def trajectory_cell_record(Q: int, lo_num: int, hi_num: int, den: int, depth: int) -> dict:
    if not 0 <= lo_num < hi_num <= den:
        raise ValueError("invalid trajectory cell")
    center_num = (lo_num + hi_num) // 2
    if not lo_num < center_num < hi_num:
        raise ValueError("trajectory cell too narrow to bisect at inherited denominator")

    t_interval = arb_unit_interval(lo_num, hi_num, den)
    L_interval = cell_coordinate_L_arb(Q, t_interval)
    L_center = cell_coordinate_L_arb(Q, arb(center_num) / den)

    center = fixed_unit_derivative_scalar_record_arb_at_L(Q, L_center)
    interval = fixed_unit_derivative_scalar_record_arb_at_L(Q, L_interval)

    e0 = center["even"]["a"]
    o0 = center["odd_N2_predecessor"]
    epI = interval["even"]["a_prime"]
    opI = interval["odd_N2_predecessor_prime"]

    e_mvt = centered_predecessor_enclosure(e0, epI, L_interval, L_center)
    o_mvt = centered_predecessor_enclosure(o0, opI, L_interval, L_center)
    e_positive = definitely_positive(e_mvt)
    o_positive = definitely_positive(o_mvt)

    J = opI * e_mvt - epI * o_mvt
    orientation = _orientation(J) if e_positive and o_positive else H1_UNRESOLVED
    P2_from_J = None
    P1_prime_from_J = None
    if e_positive and o_positive:
        even_norm = arb(scalar_geometry("even").W_norm_sq)
        odd_norm = arb(scalar_geometry("odd").W_norm_sq)
        P2_from_J = L_interval * J / (o_mvt * e_mvt)
        P1_prime_from_J = (even_norm / odd_norm) * J / (e_mvt * e_mvt)

    return {
        "Q": int(Q),
        "depth": int(depth),
        "lo_num": int(lo_num),
        "hi_num": int(hi_num),
        "center_num": int(center_num),
        "den": int(den),
        "orientation": orientation,
        "center_e_positive": definitely_positive(e0),
        "center_o_positive": definitely_positive(o0),
        "centered_e_positive": e_positive,
        "centered_o_positive": o_positive,
        "L_interval": ball_record(L_interval),
        "L_center": ball_record(L_center),
        "e_center": ball_record(e0),
        "o_center": ball_record(o0),
        "e_prime_interval": ball_record(epI),
        "o_prime_interval": ball_record(opI),
        "e_centered_enclosure": ball_record(e_mvt),
        "o_centered_enclosure": ball_record(o_mvt),
        "J": ball_record(J),
        "P2_from_J": None if P2_from_J is None else ball_record(P2_from_J),
        "P1_prime_from_J": None if P1_prime_from_J is None else ball_record(P1_prime_from_J),
    }


def _merge_spans(cells: list[dict]) -> list[dict]:
    if not cells:
        return []
    ordered = sorted(cells, key=lambda row: (row["lo_num"], row["hi_num"]))
    spans = [{"lo_num": ordered[0]["lo_num"], "hi_num": ordered[0]["hi_num"], "den": ordered[0]["den"]}]
    for row in ordered[1:]:
        cur = spans[-1]
        if row["lo_num"] <= cur["hi_num"] and row["den"] == cur["den"]:
            cur["hi_num"] = max(cur["hi_num"], row["hi_num"])
        else:
            spans.append({"lo_num": row["lo_num"], "hi_num": row["hi_num"], "den": row["den"]})
    return spans


def _classify_cover(leaves: list[dict]) -> dict:
    ordered = sorted(leaves, key=lambda row: row["lo_num"])
    signs = [row["orientation"] for row in ordered if row["orientation"] in (J_NEGATIVE, J_POSITIVE)]
    unresolved = [row for row in ordered if row["orientation"] not in (J_NEGATIVE, J_POSITIVE)]
    spans = _merge_spans(unresolved)

    compressed_signs = []
    for sign in signs:
        if not compressed_signs or compressed_signs[-1] != sign:
            compressed_signs.append(sign)

    if not unresolved and len(compressed_signs) == 1 and compressed_signs:
        classification = GLOBAL_MONOTONE_ORIENTATION
        excluded_outside_fold = True
    elif len(spans) == 1 and compressed_signs in ([J_NEGATIVE, J_POSITIVE], [J_POSITIVE, J_NEGATIVE]):
        classification = SINGLE_FOLD_REGION_LOCALIZED
        excluded_outside_fold = True
    elif len(compressed_signs) > 2:
        classification = MULTIPLE_FOLD_REGIONS
        excluded_outside_fold = False
    elif signs:
        classification = PARTIAL_TRAJECTORY_ORIENTATION
        excluded_outside_fold = False
    else:
        classification = TRAJECTORY_RIGIDITY_UNRESOLVED
        excluded_outside_fold = False

    return {
        "classification": classification,
        "compressed_certified_orientation_sequence": compressed_signs,
        "unresolved_span_count": len(spans),
        "unresolved_spans": spans,
        "distinct_aperture_twin_excluded_outside_reported_fold_region": excluded_outside_fold,
    }


def localize_trajectory(
    hull: dict,
    *,
    max_depth: int,
    max_cells: int,
) -> dict:
    """Deterministically bisect only cells whose J/H1 orientation is unresolved."""
    queue = [(int(hull["lo_num"]), int(hull["hi_num"]), 0)]
    leaves: list[dict] = []
    evaluated = 0
    while queue:
        lo, hi, depth = queue.pop(0)
        if evaluated >= max_cells:
            leaves.append({
                "Q": int(hull["Q"]), "depth": depth, "lo_num": lo, "hi_num": hi,
                "den": int(hull["den"]), "orientation": J_UNRESOLVED,
                "reason": "MAX_CELL_BUDGET",
            })
            continue
        row = trajectory_cell_record(int(hull["Q"]), lo, hi, int(hull["den"]), depth)
        evaluated += 1
        if row["orientation"] in (J_NEGATIVE, J_POSITIVE) or depth >= max_depth or hi - lo <= 2:
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
        raise AssertionError("trajectory localization produced no leaves")
    if leaves[0]["lo_num"] != int(hull["lo_num"]) or leaves[-1]["hi_num"] != int(hull["hi_num"]):
        raise AssertionError("trajectory cover does not span inherited hull")
    for left, right in zip(leaves, leaves[1:]):
        if left["hi_num"] != right["lo_num"]:
            raise AssertionError("trajectory cover has a gap or overlap")

    classification = _classify_cover(leaves)
    return {
        "hull": dict(hull),
        "evaluated_cell_count": evaluated,
        "leaf_count": len(leaves),
        "max_depth": int(max_depth),
        "max_cells": int(max_cells),
        "leaves": leaves,
        **classification,
    }


def synthetic_orientation_controls() -> dict:
    """Exact algebra controls for the sign graph; no canonical claim is made."""
    L = Fraction(1, 1)
    e = Fraction(1, 1)
    ep = Fraction(0, 1)

    o_up = Fraction(2, 1)
    op_up = Fraction(1, 1)
    J_up = op_up * e - ep * o_up
    P2_up = L * J_up / (o_up * e)

    o_down = Fraction(2, 1)
    op_down = Fraction(-1, 1)
    J_down = op_down * e - ep * o_down
    P2_down = L * J_down / (o_down * e)

    passed = J_up > 0 and P2_up > 0 and J_down < 0 and P2_down < 0
    return {
        "status": "PASS" if passed else "FAIL",
        "positive_control": {"J": str(J_up), "P2": str(P2_up)},
        "negative_control": {"J": str(J_down), "P2": str(P2_down)},
    }


def audit_parity_trajectory(schedule: dict, *, precision_bits: int, max_depth: int, max_cells: int) -> dict:
    set_precision(precision_bits)
    primary = [box for box in schedule["boxes"] if bool(box["primary"])]
    crosschecks = [inherited_center_crosscheck(box) for box in primary]
    hull = primary_hull(schedule["boxes"])
    localization = localize_trajectory(hull, max_depth=max_depth, max_cells=max_cells)
    all_crosschecks = all(
        row["scope"] == "CERTIFIED_H1_SCOPE"
        and row["P1_overlap"]
        and row["P2_overlap"]
        and row["P2_J_identity_overlap"]
        for row in crosschecks
    )
    controls = synthetic_orientation_controls()
    return {
        "status": "PASS",
        "scope": "Q14_FIXED_TRAJECTORY_RESEARCH_ONLY",
        "precision_bits": int(precision_bits),
        "primary_center_crosschecks": crosschecks,
        "all_inherited_P1_P2_crosschecks_pass": all_crosschecks,
        "synthetic_orientation_controls": controls,
        "localization": localization,
        "interpretation": {
            "P1_P2_status": "REUSED_FROZEN_POST188_COORDINATES",
            "J_status": "DERIVED_EVALUATION_GRAPH_NOT_NEW_SELECTOR",
            "centered_H1_status": "FINITE_ARB_MEAN_VALUE_ENCLOSURE",
            "twin_exclusion_status": (
                "DERIVED_OUTSIDE_REPORTED_FOLD_REGION"
                if localization["distinct_aperture_twin_excluded_outside_reported_fold_region"]
                else "UNRESOLVED"
            ),
        },
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
