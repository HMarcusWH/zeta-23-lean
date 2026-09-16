#!/usr/bin/env python3
"""Replay the unique post-#195 Q14 cell skipped by the frozen 96-cell budget.

This is a post-hoc one-cell follow-up to the exact frozen #195 experiment.  It
first reruns #195 unchanged, identifies the unique leaf emitted solely because
``MAX_CELL_BUDGET`` was reached, evaluates that exact cell once with the
unchanged #195 shared A/B/C evaluator, and reclassifies the completed leaf
cover.  It does not increase the inherited adaptive budget and it does not
recursively subdivide the replayed cell.

Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

from post192_fb05_q14_parity_trajectory_rigidity import (
    J_NEGATIVE,
    J_POSITIVE,
    _classify_cover,
)
from post194_fb05_q14_parity_trajectory_sharp_enclosure import (
    audit_sharp_parity_trajectory,
    sharp_trajectory_cell_record,
)


def unique_budget_leaf(localization: dict) -> dict:
    """Return the unique leaf that #195 emitted without evaluating it."""
    budget = [
        row
        for row in localization["leaves"]
        if row.get("reason") == "MAX_CELL_BUDGET"
    ]
    if int(localization.get("budget_exhausted_leaf_count", -1)) != len(budget):
        raise AssertionError("post-#195 budget-leaf accounting mismatch")
    if len(budget) != 1:
        raise AssertionError(f"expected one post-#195 budget leaf, found {len(budget)}")
    return dict(budget[0])


def _same_cell(left: dict, right: dict) -> bool:
    return all(
        int(left[key]) == int(right[key])
        for key in ("Q", "depth", "lo_num", "hi_num", "den")
    )


def _validated_completed_cover(localization: dict, budget_leaf: dict, replayed: dict) -> list[dict]:
    if not _same_cell(budget_leaf, replayed):
        raise AssertionError("residual replay moved off the inherited budget leaf")
    if replayed.get("reason") == "MAX_CELL_BUDGET":
        raise AssertionError("residual replay returned a budget sentinel instead of an evaluation")
    if replayed.get("representation_conflict"):
        raise AssertionError("residual replay found an A/B/C representation conflict")

    replaced = 0
    leaves: list[dict] = []
    for row in localization["leaves"]:
        if row.get("reason") == "MAX_CELL_BUDGET":
            if not _same_cell(row, budget_leaf):
                raise AssertionError("unexpected second budget leaf in inherited cover")
            leaves.append(dict(replayed))
            replaced += 1
        else:
            leaves.append(dict(row))
    if replaced != 1:
        raise AssertionError("residual replay did not replace exactly one inherited sentinel")

    leaves.sort(key=lambda row: row["lo_num"])
    hull = localization["hull"]
    if not leaves:
        raise AssertionError("completed residual cover is empty")
    if leaves[0]["lo_num"] != int(hull["lo_num"]) or leaves[-1]["hi_num"] != int(hull["hi_num"]):
        raise AssertionError("completed residual cover does not span the inherited hull")
    for left, right in zip(leaves, leaves[1:]):
        if left["hi_num"] != right["lo_num"]:
            raise AssertionError("completed residual cover has a gap or overlap")
    return leaves


def replay_post195_budget_leaf(
    schedule: dict,
    *,
    precision_bits: int,
    max_depth: int,
    max_cells: int,
) -> dict:
    """Rerun frozen #195, then evaluate its one skipped leaf exactly once."""
    inherited = audit_sharp_parity_trajectory(
        schedule,
        precision_bits=precision_bits,
        max_depth=max_depth,
        max_cells=max_cells,
    )
    localization = inherited["sharp_localization"]
    budget_leaf = unique_budget_leaf(localization)

    replayed = sharp_trajectory_cell_record(
        int(budget_leaf["Q"]),
        int(budget_leaf["lo_num"]),
        int(budget_leaf["hi_num"]),
        int(budget_leaf["den"]),
        int(budget_leaf["depth"]),
    )
    completed_leaves = _validated_completed_cover(localization, budget_leaf, replayed)
    classification = _classify_cover(completed_leaves)

    signed = {
        row["orientation"]
        for row in completed_leaves
        if row["orientation"] in (J_POSITIVE, J_NEGATIVE)
    }
    uniform_orientation = (
        next(iter(signed))
        if not classification["unresolved_spans"] and len(signed) == 1
        else None
    )

    return {
        "status": "PASS",
        "scope": "Q14_POST195_UNIQUE_BUDGET_LEAF_REPLAY_RESEARCH_ONLY",
        "precision_bits": int(precision_bits),
        "inherited_max_refinement_depth": int(max_depth),
        "inherited_max_evaluated_cells": int(max_cells),
        "post195_audit": inherited,
        "residual_budget_leaf": budget_leaf,
        "replayed_cell": replayed,
        "followup_evaluated_cell_count": 1,
        "recursive_followup_subdivision": False,
        "completed_cover": {
            "hull": dict(localization["hull"]),
            "leaf_count": len(completed_leaves),
            "uniform_orientation": uniform_orientation,
            "leaves": completed_leaves,
            **classification,
        },
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
