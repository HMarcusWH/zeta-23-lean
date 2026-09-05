from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
sys.path.insert(0, str(RHRC))

from control_v2.retro.search import search_concept
from control_v2.router import load_actions, recommend
from control_v2.state import load_research_state


def _first_break_counts() -> dict[str, int]:
    data = json.loads((RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8"))
    return {
        action_id: len(raw.get("first_breaks", []))
        for action_id, raw in data["actions"].items()
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="RHRC Control v2 diagnostic research router")
    parser.add_argument("--archive-root", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    state = load_research_state()
    actions = load_actions()

    receipt_ids: dict[str, str] = {}
    receipt_summaries: list[dict] = []
    for action in actions:
        if not action.retro_search_required:
            continue
        receipt = search_concept(
            repo_root=REPO,
            concept_id=action.concept_id,
            as_of_ref=state.anchor.merge_commit,
            archive_root=args.archive_root,
        )
        receipt_ids[action.action_id] = receipt.receipt_id
        receipt_summaries.append({
            "action_id": action.action_id,
            "receipt_id": receipt.receipt_id,
            "hit_count": len(receipt.hits),
            "searched_sources": list(receipt.searched_sources),
        })

    cert = recommend(
        state,
        actions,
        retro_receipts=receipt_ids,
        first_break_counts=_first_break_counts(),
    )

    payload = {
        "schema_version": "RHRC-control-run-1.0",
        "terminal_claim": state.terminal_claim,
        "theorem_anchor": {
            "pr": state.anchor.pr,
            "merge_commit": state.anchor.merge_commit,
            "tree": state.anchor.tree,
        },
        "retro_receipts": sorted(receipt_summaries, key=lambda x: x["action_id"]),
        "route_certificate": cert.to_dict(),
        "claim_firewall": "CONTROL_V2_HAS_NO_THEOREM_OR_RH_PROMOTION_AUTHORITY"
    }
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
