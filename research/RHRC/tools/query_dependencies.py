from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "graph" / "generated"
COMPILER_RECEIPT = ROOT / "graph" / "compiler" / "REGISTERED_DECLARATION_DEPENDENCIES.jsonl"


def load(name: str) -> dict:
    return json.loads((GENERATED / name).read_text(encoding="utf-8"))


def load_compiler_receipt() -> list[dict]:
    return [
        json.loads(line)
        for line in COMPILER_RECEIPT.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def shortest_local_dependency_path(
    receipt: list[dict], start: str, target: str
) -> list[str] | None:
    by_name = {row["declaration"]: row for row in receipt}
    if start not in by_name or target not in by_name:
        return None
    if by_name[start]["repository_scope"] != "LOCAL":
        return None
    if by_name[target]["repository_scope"] != "LOCAL":
        return None
    if start == target:
        return [start]

    parent: dict[str, str | None] = {start: None}
    queue: deque[str] = deque([start])
    while queue:
        current = queue.popleft()
        neighbors = sorted(
            dep["constant"]
            for dep in by_name[current]["dependencies"]
            if dep["constant"] in by_name
            and by_name[dep["constant"]]["repository_scope"] == "LOCAL"
        )
        for neighbor in neighbors:
            if neighbor in parent:
                continue
            parent[neighbor] = current
            if neighbor == target:
                path = [target]
                cursor = target
                while parent[cursor] is not None:
                    cursor = parent[cursor]  # type: ignore[index]
                    path.append(cursor)
                return list(reversed(path))
            queue.append(neighbor)
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description="Query RHKG Phase-2D dependency products")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--claim")
    group.add_argument("--compare", nargs=2, metavar=("LEFT", "RIGHT"))
    group.add_argument("--intersect")
    group.add_argument("--atoms", metavar="COHORT")
    group.add_argument("--frontier", metavar="COHORT")
    group.add_argument("--path", nargs=2, metavar=("ROOT_CLAIM", "TARGET_DECLARATION"))
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

    if args.intersect:
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

    if args.atoms:
        atoms = load("DEPENDENCY_COHORT_ATOMS.json")
        if args.atoms != atoms["target_cohort_id"]:
            raise SystemExit(
                f"Phase 2D atom view is configured for {atoms['target_cohort_id']}, "
                f"not {args.atoms}"
            )
        print(json.dumps(atoms, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    if args.frontier:
        frontiers = load("DEPENDENCY_BRIDGE_FRONTIERS.json")
        if args.frontier != frontiers["target_cohort_id"]:
            raise SystemExit(
                f"Phase 2D frontier view is configured for {frontiers['target_cohort_id']}, "
                f"not {args.frontier}"
            )
        print(json.dumps(frontiers, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    root_claim, target = args.path
    entry = by_claim.get(root_claim)
    if entry is None:
        raise SystemExit(f"unknown proved registered root claim: {root_claim}")
    receipt = load_compiler_receipt()
    path = shortest_local_dependency_path(receipt, entry["root_theorem"], target)
    if path is None:
        raise SystemExit(
            f"no project-local compiler dependency path from {root_claim} to {target}"
        )
    by_name = {row["declaration"]: row for row in receipt}
    edges = []
    for source, dest in zip(path, path[1:]):
        dep = next(
            dep for dep in by_name[source]["dependencies"] if dep["constant"] == dest
        )
        edges.append(
            {
                "source": source,
                "target": dest,
                "used_in_type": dep["used_in_type"],
                "used_in_value": dep["used_in_value"],
                "used_in_structure": dep["used_in_structure"],
            }
        )
    out = {
        "root_claim_id": root_claim,
        "root_theorem": entry["root_theorem"],
        "target_declaration": target,
        "path_length": len(path) - 1,
        "path": path,
        "edges": edges,
        "edge_direction": "SOURCE_DECLARATION_TO_COMPILER_USED_CONSTANT",
        "interpretation": "Deterministic shortest path in the exact local compiler dependency graph; not logical implication.",
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }
    print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
