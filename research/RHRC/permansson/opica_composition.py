"""Authenticated finite-menu policy, separate from provider theorem authority.

The pure selector validates an entire menu and history. Journal.dispatch obtains
both from one durable transaction; candidate records never supply their counts.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Mapping
from research.RHRC.integration.opica_composition.canonical import (
    require, digest, digest_text, nonempty_text, closed_keys)

PROVIDER_REPO = "HMarcusWH/PermanssonLean"
PROVIDER_COMMIT = "17c315f7df7abf457eb94d393bd526d46da6f6f4"
PROVIDER_LEAN = "leanprover/lean4:v4.34.0"
SELECTED_APIS = (
    "PermanssonResearch.ReverseSolver.FiniteMonitor.computedValue_eq_value",
    "PermanssonResearch.ReverseSolver.FiniteMonitor.leastMaximizingControl_spec",
    "PermanssonResearch.ReverseSolver.FiniteMonitor.computedMaximizer_attains",
)

@dataclass(frozen=True)
class Action:
    action_id: str
    source: str
    priority: int
    cost: int

    def __post_init__(self):
        nonempty_text(self.action_id, "action ID")
        digest_text(self.source, "action source")
        require(len(self.action_id) <= 4096, "action ID budget exceeded")
        require(type(self.priority) is int and self.priority >= 0, "invalid priority")
        require(type(self.cost) is int and self.cost > 0, "invalid action cost")

def select_action(actions, *, source: str, allowed_ids: frozenset[str],
                  attempt_counts: Mapping[str, int], budget: int) -> dict:
    digest_text(source)
    require(type(budget) is int and budget >= 0, "nonnegative integer budget required")
    require(type(allowed_ids) is frozenset and len(allowed_ids) <= 4096,
            "complete bounded eligible menu required")
    require(isinstance(attempt_counts, Mapping), "trusted history mapping required")
    counts = dict(attempt_counts)
    require(set(counts) == set(allowed_ids), "history/eligible inventory differs")
    require(all(type(n) is int and n >= 0 for n in counts.values()), "invalid dispatch counts")
    require(type(actions) in (list, tuple) and len(actions) <= 4096, "finite action list required")
    rows = tuple(actions)
    require(all(type(r) is Action and r.source == source for r in rows), "stale/untyped action")
    ids = [r.action_id for r in rows]
    require(len(ids) == len(set(ids)) and set(ids) == set(allowed_ids),
            "missing, duplicate or unauthorized action")
    base = {"schema": "OPICA_POLICY_CHOICE_V1", "source": source,
            "mode": "POLICY_ADAPTER_ONLY"}
    feasible = [r for r in rows if r.cost <= budget]
    if not feasible:
        return {**base, "kind": "STOP", "reason":
                "EMPTY_ELIGIBLE_MENU" if not rows else "NO_FEASIBLE_ACTION"}
    chosen = min(feasible, key=lambda r: (counts[r.action_id], -r.priority, r.cost, r.action_id))
    return {**base, "kind": "SELECT", "action_id": chosen.action_id}

def validate_intervention(before: dict, after: dict) -> None:
    """Strategy changes do not authorize changes to the mathematical world."""
    for field in ("source", "checker", "profile", "grammar", "target_inventory"):
        require(field in before and after.get(field) == before[field],
                "world-changing intervention: " + field)

def qualify_provider(record: dict, *, expected_environment: dict,
                     replay) -> dict:
    """Replay exact independent consumers; registry labels alone do not admit APIs."""
    closed_keys(record, {"repository", "commit", "toolchain", "environment",
                         "apis", "raw_evidence", "mode"})
    require(record["repository"] == PROVIDER_REPO and record["commit"] == PROVIDER_COMMIT,
            "wrong provider source")
    require(record["toolchain"] == PROVIDER_LEAN and record["environment"] == expected_environment,
            "wrong provider compiler/packages")
    require(record["mode"] == "POLICY_ADAPTER_ONLY", "unqualified model-relative policy")
    require(type(record["apis"]) is list and len(record["apis"]) == 3 and
            set(record["apis"]) == set(SELECTED_APIS), "selected API inventory differs")
    require(type(record["raw_evidence"]) is dict and set(record["raw_evidence"]) == set(SELECTED_APIS),
            "missing raw provider consumers")
    require(callable(replay), "independent provider replay required")
    for name in SELECTED_APIS:
        require(replay(name, record["raw_evidence"][name]) is True,
                "provider consumer replay failed: " + name)
    return {"status": "ADMITTED_SELECTED_APIS_ONLY", "mode": "POLICY_ADAPTER_ONLY",
            "provider_digest": digest(record, domain="OPICA_PROVIDER_V1"),
            "host_theorem_authority": False, "model_optimality": "NOT_ESTABLISHED"}

def require_comparable_experiments(left: dict, right: dict) -> None:
    for key in ("source", "checker", "menu", "budget", "population", "phase"):
        require(key in left and left[key] == right.get(key), "uncontrolled policy comparison: " + key)

def count_information_gain(results: list[dict]) -> int:
    """Aliases and repeated origins do not increase the discharged obligation set."""
    require(type(results) is list, "result inventory required")
    return len({(r["source"], r["obligation"])
                for r in results if r.get("status") == "PROVED_CONDITIONAL"})

def validate_policy_claim(record: dict) -> None:
    closed_keys(record, {"mode", "claim", "world", "menu", "history_revision", "budget"})
    require(record["mode"] == "POLICY_ADAPTER_ONLY", "model-relative policy not qualified in v1")
    require(record["claim"] in {"DETERMINISTIC_SELECTION", "CONDITIONAL_FINITE_MENU_FAIRNESS"},
            "unsupported optimality/probability claim")
    digest_text(record["world"]); digest_text(record["menu"])
    require(type(record["history_revision"]) is int and record["history_revision"] >= 0,
            "invalid policy history revision")
    require(type(record["budget"]) is int and record["budget"] >= 0, "invalid policy budget")
