"""Read one stored constraint query and exercise the real finite-menu selector.

This read-only example uses stdlib Python and existing repository code. It does
not rebuild the graph, dispatch a theorem attempt, compile Lean, validate the
selected external provider, or issue an acceptance receipt.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from research.RHRC.integration.opica_composition.canonical import ContractError, digest, require
from research.RHRC.integration.opica_round6.constraint_graph import explain
from research.RHRC.permansson.opica_composition import Action, select_action, validate_intervention


def graph_query():
    path = ROOT / "research/RHRC/integration/opica_round6/CONSTRAINT_GRAPH.json"
    if not path.is_file():
        raise SystemExit("Missing CONSTRAINT_GRAPH.json. Materialize this tracked file in your sparse checkout; "
                         "see docs/REPRODUCIBILITY.md. No generated state has been written.")
    data = path.read_bytes()
    graph = json.loads(data)
    require(graph["RH"] == graph["Step4"] == "OPEN", "terminal state changed: review this example")
    result = explain(graph, "SURVIVOR_ROUTE")
    require(result["status"] == "OPEN", "survivor disposition changed: review this example")
    require(set(result["open_on_joint_edges_only"]) == {"ACTUAL_UPPER", "PAPER_ROUTE_VALIDATION"},
            "survivor premises changed: review this example")
    return {"scope": "QUERY_OF_STORED_GRAPH_ONLY", "graph_sha256": sha256(data).hexdigest(),
            "target": result["target"], "status": result["status"],
            "joint_open_premises": result["open_on_joint_edges_only"],
            "context_only": result["context"], "routes": result["shortest_open_routes"]}


def policy_fixture():
    # This identifies only the displayed example menu; it is not a project source lock.
    menu = [{"id": "read", "priority": 1, "cost": 1},
            {"id": "replay", "priority": 8, "cost": 2},
            {"id": "compile", "priority": 9, "cost": 5}]
    source = digest({"example": "documentation-policy-v1", "menu": menu}, domain="DOCS_EXAMPLE_V1")
    actions = [Action(row["id"], source, row["priority"], row["cost"]) for row in menu]
    ids = frozenset(row["id"] for row in menu)
    history = {"read": 0, "replay": 1, "compile": 0}
    choose = lambda budget: select_action(actions, source=source, allowed_ids=ids,
                                         attempt_counts=history, budget=budget)
    first, second, stopped = choose(2), choose(5), choose(0)
    require(first["action_id"] == "read", "attempt counts did not take precedence")
    require(second["action_id"] == "compile", "priority tie break differs")
    require(stopped["reason"] == "NO_FEASIBLE_ACTION", "budget stop differs")
    world = {"source": source, "checker": "example-checker", "profile": "example-profile",
             "grammar": "example-grammar", "target_inventory": "example-targets"}
    validate_intervention(world, {**world, "strategy": "another policy"})
    try:
        validate_intervention(world, {**world, "target_inventory": "changed-targets"})
    except ContractError:
        changed_target_rejected = True
    else:
        raise ArithmeticError("a policy intervention changed the target inventory")
    return {"scope": "REAL_SELECTOR_ON_DOCUMENTATION_FIXTURE", "menu": menu,
            "attempt_counts": history, "budget_2": first, "budget_5": second,
            "budget_0": stopped, "changed_target_rejected": changed_target_rejected}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", choices=("all", "graph", "policy"), default="all")
    args = parser.parse_args()
    result = {}
    if args.part in ("all", "graph"):
        result["stored_graph"] = graph_query()
    if args.part in ("all", "policy"):
        result["finite_menu"] = policy_fixture()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
