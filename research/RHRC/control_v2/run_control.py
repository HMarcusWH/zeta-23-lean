from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
sys.path.insert(0, str(RHRC))

from control_v2.adapters.ffbbp import load_ffbbp_snapshot
from control_v2.adapters.ool import load_ool_snapshot
from control_v2.first_break import FirstBreak, rank_first_breaks
from control_v2.regime_monitor import RouteHistoryRecord, assess_regime
from control_v2.retro.search import search_concept
from control_v2.retro.summary import summarize_receipt
from control_v2.router import load_actions, recommend
from control_v2.state import load_research_state


def _action_registry() -> dict:
    return json.loads((RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8"))


def _first_break_counts(registry: dict) -> dict[str, int]:
    return {
        action_id: len(raw.get("first_breaks", []))
        for action_id, raw in registry["actions"].items()
    }


def _selected_first_break(registry: dict, action_id: str | None) -> dict | None:
    if action_id is None:
        return None
    raw_breaks = registry["actions"].get(action_id, {}).get("first_breaks", [])
    candidates = [
        FirstBreak(
            break_id=str(raw["id"]),
            route_id=action_id,
            statement=str(raw["statement"]),
            test_id=str(raw["test_id"]),
            estimated_cost=float(raw["estimated_cost"]),
            decisive_if_failed=bool(raw.get("decisive_if_failed", False)),
            decisive_if_passed=bool(raw.get("decisive_if_passed", False)),
        )
        for raw in raw_breaks
    ]
    if not candidates:
        return None
    selected = rank_first_breaks(candidates)[0]
    return {
        "break_id": selected.break_id,
        "statement": selected.statement,
        "test_id": selected.test_id,
        "estimated_cost": selected.estimated_cost,
        "decisive_if_failed": selected.decisive_if_failed,
        "decisive_if_passed": selected.decisive_if_passed,
    }


def _load_history(path: Path | None) -> tuple[RouteHistoryRecord, ...]:
    if path is None:
        return ()
    records: list[RouteHistoryRecord] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        raw = json.loads(line)
        records.append(RouteHistoryRecord(
            action_id=str(raw["action_id"]),
            evaluator_id=str(raw["evaluator_id"]),
            benchmark_id=raw.get("benchmark_id"),
            complexity=int(raw.get("complexity", 0)),
            outcome=str(raw.get("outcome", "OPEN")),
        ))
    return tuple(records)


def main() -> int:
    parser = argparse.ArgumentParser(description="RHRC Control v2 diagnostic research router")
    parser.add_argument("--archive-root", type=Path)
    parser.add_argument("--history-jsonl", type=Path,
                        help="Optional prior route history for read-only PIRE-style regime monitoring")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--quick-retro", action="store_true",
                        help="Bound retro search for interactive use; incomplete receipts cannot admit history-sensitive routes")
    args = parser.parse_args()

    state = load_research_state()
    actions = load_actions()
    registry = _action_registry()

    receipt_ids: dict[str, str] = {}
    receipt_complete: dict[str, bool] = {}
    receipt_summaries: list[dict] = []
    for action in actions:
        if not action.retro_search_required:
            continue
        receipt = search_concept(
            repo_root=REPO,
            concept_id=action.concept_id,
            as_of_ref=state.anchor.merge_commit,
            archive_root=args.archive_root,
            exhaustive=not args.quick_retro,
        )
        receipt_ids[action.action_id] = receipt.receipt_id
        receipt_complete[action.action_id] = receipt.search_complete
        summary = summarize_receipt(receipt)
        summary["action_id"] = action.action_id
        summary["searched_sources"] = list(receipt.searched_sources)
        receipt_summaries.append(summary)

    cert = recommend(
        state,
        actions,
        retro_receipts=receipt_ids,
        retro_complete=receipt_complete,
        first_break_counts=_first_break_counts(registry),
    )

    ffbbp = load_ffbbp_snapshot(RHRC)
    ool = load_ool_snapshot(RHRC)
    regime = assess_regime(_load_history(args.history_jsonl))

    payload = {
        "schema_version": "RHRC-control-run-1.3",
        "terminal_claim": state.terminal_claim,
        "theorem_anchor": {
            "pr": state.anchor.pr,
            "merge_commit": state.anchor.merge_commit,
            "tree": state.anchor.tree,
        },
        "control_anchor": {
            "pr": state.control_anchor.pr,
            "merge_commit": state.control_anchor.merge_commit,
            "tree": state.control_anchor.tree,
        },
        "supporting_stack": {
            "ffbbp": {
                "qualified_reference_version": ffbbp.qualified_reference_version,
                "qualified_profile": ffbbp.qualified_profile,
                "v16_theory_version": ffbbp.v16_theory_version,
                "v16_inherits_qualification": ffbbp.v16_inherits_qualification,
            },
            "ool": {
                "kernel_version": ool.kernel_version,
                "registered_route_count": ool.registered_route_count,
            },
            "research_regime": {
                "regime": regime.regime.value,
                "reasons": list(regime.reasons),
                "authorization": regime.authorization,
            },
        },
        "retro_receipts": sorted(receipt_summaries, key=lambda x: x["action_id"]),
        "route_certificate": cert.to_dict(),
        "selected_first_break": _selected_first_break(registry, cert.selected_action),
        "claim_firewall": "CONTROL_V2_HAS_NO_THEOREM_OR_RH_PROMOTION_AUTHORITY",
    }
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
