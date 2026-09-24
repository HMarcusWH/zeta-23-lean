from __future__ import annotations

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "graph" / "generated"


def load(name: str) -> dict:
    return json.loads((GENERATED / name).read_text(encoding="utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description="Query RHKG Phase-2C dependency products")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--claim")
    group.add_argument("--compare", nargs=2, metavar=("LEFT", "RIGHT"))
    group.add_argument("--intersect")
    args = parser.parse_args()

    closure = load("THEOREM_DEPENDENCY_CLOSURE.json")
    overlap = load("DEPENDENCY_COHORT_OVERLAP.json")
    by_claim = {row["claim_id"]: row for row in closure["entries"]}
    by_cohort = {row["cohort_id"]: row for row in overlap["cohorts"]}

    if args.claim:
        row = by_claim.get(args.claim)
        if row is None:
            raise SystemExit(f"unknown proved registered claim: {args.claim}")
        print(json.dumps(row, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    if args.compare:
        left_id, right_id = args.compare
        if left_id not in by_claim or right_id not in by_claim:
            missing = [x for x in args.compare if x not in by_claim]
            raise SystemExit(f"unknown proved registered claim(s): {missing}")
        left = set(by_claim[left_id]["transitive_local_dependencies"])
        right = set(by_claim[right_id]["transitive_local_dependencies"])
        out = {
            "left_claim_id": left_id,
            "right_claim_id": right_id,
            "left_count": len(left),
            "right_count": len(right),
            "shared_count": len(left & right),
            "left_only_count": len(left - right),
            "right_only_count": len(right - left),
            "shared": sorted(left & right),
            "left_only": sorted(left - right),
            "right_only": sorted(right - left),
            "interpretation": "Exact local dependency-set comparison only; not theorem equivalence or implication.",
            "terminal_claim": "RH_OPEN",
            "graph_theorem_promotion": False,
        }
        print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    row = by_cohort.get(args.intersect)
    if row is None:
        raise SystemExit(f"unknown dependency cohort: {args.intersect}")
    out = {
        "cohort_id": row["cohort_id"],
        "claim_ids": row["claim_ids"],
        "intersection_count": row["local_dependency_intersection_count"],
        "intersection_excluding_registered_roots_count": row[
            "local_dependency_intersection_excluding_registered_roots_count"
        ],
        "intersection": row["local_dependency_intersection"],
        "intersection_excluding_registered_roots": row[
            "local_dependency_intersection_excluding_registered_roots"
        ],
        "member_shells": row["member_shells"],
        "interpretation": "Exact cohort dependency intersection and subtraction shells; discovery-only.",
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }
    print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
