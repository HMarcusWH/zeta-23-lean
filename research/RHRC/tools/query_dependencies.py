from __future__ import annotations

import argparse
import importlib.util
import json
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "graph" / "generated"
COMPILER_RECEIPT = ROOT / "graph" / "compiler" / "REGISTERED_DECLARATION_DEPENDENCIES.jsonl"

SPEC = importlib.util.spec_from_file_location("rhkg_views", ROOT / "graph" / "views.py")
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load RHKG views.py")
views = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(views)


def load(name: str) -> dict:
    return json.loads((GENERATED / name).read_text(encoding="utf-8"))


def load_compiler_receipt() -> list[dict]:
    return [
        json.loads(line)
        for line in COMPILER_RECEIPT.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def projected_claim_entry(
    receipt: list[dict],
    old_entry: dict,
    projection: str,
) -> dict:
    if projection == "ANY":
        return old_entry
    row = views.dependency_projection_closure_entry(
        receipt, old_entry["root_theorem"], projection
    )
    row["claim_id"] = old_entry["claim_id"]
    row["interpretation"] = (
        "Exact compiler-support projection only; not logical implication, "
        "mathematical necessity, or theorem equivalence."
    )
    row["terminal_claim"] = "RH_OPEN"
    row["graph_theorem_promotion"] = False
    return row


def shortest_local_dependency_path(
    receipt: list[dict], start: str, target: str, projection: str = "ANY"
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
        current_row = by_name[current]
        neighbors = sorted(
            dep["constant"]
            for dep in current_row["dependencies"]
            if views.dependency_edge_allowed(current_row, dep, projection)
            and dep["constant"] in by_name
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
    parser = argparse.ArgumentParser(
        description="Query RHKG compiler-derived dependency products"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--claim")
    group.add_argument("--compare", nargs=2, metavar=("LEFT", "RIGHT"))
    group.add_argument("--intersect")
    group.add_argument("--atoms", metavar="COHORT")
    group.add_argument("--frontier", metavar="COHORT")
    group.add_argument("--path", nargs=2, metavar=("ROOT_CLAIM", "TARGET_DECLARATION"))
    parser.add_argument(
        "--projection",
        choices=views.DEPENDENCY_PROJECTIONS,
        default="ANY",
        help=(
            "Dependency traversal projection. ANY preserves the sealed Phase-2D "
            "semantics; THEOREM_VALUE_ERASED_SUPPORT removes theorem VALUE traversal "
            "while retaining TYPE, STRUCTURE, and non-theorem VALUE traversal."
        ),
    )
    args = parser.parse_args()

    closure = load("THEOREM_DEPENDENCY_CLOSURE.json")
    overlap = load("DEPENDENCY_COHORT_OVERLAP.json")
    by_claim = {row["claim_id"]: row for row in closure["entries"]}
    by_cohort = {row["cohort_id"]: row for row in overlap["cohorts"]}
    receipt = load_compiler_receipt()

    if args.claim:
        row = by_claim.get(args.claim)
        if row is None:
            raise SystemExit(f"unknown proved registered claim: {args.claim}")
        out = projected_claim_entry(receipt, row, args.projection)
        print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    if args.compare:
        left_id, right_id = args.compare
        if left_id not in by_claim or right_id not in by_claim:
            missing = [x for x in args.compare if x not in by_claim]
            raise SystemExit(f"unknown proved registered claim(s): {missing}")
        left_row = projected_claim_entry(receipt, by_claim[left_id], args.projection)
        right_row = projected_claim_entry(receipt, by_claim[right_id], args.projection)
        left = set(left_row["transitive_local_dependencies"])
        right = set(right_row["transitive_local_dependencies"])
        if left == right:
            relation = "EQUAL"
        elif left < right:
            relation = "LEFT_STRICT_SUBSET"
        elif right < left:
            relation = "RIGHT_STRICT_SUBSET"
        else:
            relation = "INCOMPARABLE"
        out = {
            "projection": args.projection,
            "left_claim_id": left_id,
            "right_claim_id": right_id,
            "relation": relation,
            "left_count": len(left),
            "right_count": len(right),
            "shared_count": len(left & right),
            "left_only_count": len(left - right),
            "right_only_count": len(right - left),
            "shared": sorted(left & right),
            "left_only": sorted(left - right),
            "right_only": sorted(right - left),
            "interpretation": (
                "Exact project-local compiler-support set comparison only; "
                "not theorem equivalence or logical implication."
            ),
            "terminal_claim": "RH_OPEN",
            "graph_theorem_promotion": False,
        }
        print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    if args.intersect:
        row = by_cohort.get(args.intersect)
        if row is None:
            raise SystemExit(f"unknown dependency cohort: {args.intersect}")
        if args.projection == "ANY":
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
                "interpretation": (
                    "Exact cohort dependency intersection and subtraction shells; "
                    "discovery-only."
                ),
                "terminal_claim": "RH_OPEN",
                "graph_theorem_promotion": False,
            }
        else:
            sets = []
            for claim_id in row["claim_ids"]:
                old_entry = by_claim[claim_id]
                projected = projected_claim_entry(receipt, old_entry, args.projection)
                sets.append(set(projected["transitive_local_dependencies"]))
            intersection = set(sets[0])
            for current in sets[1:]:
                intersection &= current
            out = {
                "cohort_id": row["cohort_id"],
                "projection": args.projection,
                "claim_ids": row["claim_ids"],
                "intersection_count": len(intersection),
                "intersection": sorted(intersection),
                "interpretation": (
                    "Exact projected cohort intersection; compiler-support discovery only."
                ),
                "terminal_claim": "RH_OPEN",
                "graph_theorem_promotion": False,
            }
        print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    if args.atoms:
        if args.projection == "ANY":
            atoms = load("DEPENDENCY_COHORT_ATOMS.json")
            if args.atoms != atoms["target_cohort_id"]:
                raise SystemExit(
                    f"Phase 2D atom view is configured for {atoms['target_cohort_id']}, "
                    f"not {args.atoms}"
                )
            out = atoms
        else:
            product = load("DEPENDENCY_PROJECTION_QUOTIENTS.json")
            if args.atoms != product["target_cohort_id"]:
                raise SystemExit(
                    f"Phase 2E projection quotient is configured for "
                    f"{product['target_cohort_id']}, not {args.atoms}"
                )
            out = next(
                row
                for row in product["projections"]
                if row["projection"] == args.projection
            )
        print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    if args.frontier:
        if args.projection == "ANY":
            frontiers = load("DEPENDENCY_BRIDGE_FRONTIERS.json")
            if args.frontier != frontiers["target_cohort_id"]:
                raise SystemExit(
                    f"Phase 2D frontier view is configured for "
                    f"{frontiers['target_cohort_id']}, not {args.frontier}"
                )
            out = frontiers
        else:
            product = load("DEPENDENCY_PROJECTION_FRONTIERS.json")
            if args.frontier != product["target_cohort_id"]:
                raise SystemExit(
                    f"Phase 2E projection frontier is configured for "
                    f"{product['target_cohort_id']}, not {args.frontier}"
                )
            out = next(
                row
                for row in product["projections"]
                if row["projection"] == args.projection
            )
        print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    root_claim, target = args.path
    entry = by_claim.get(root_claim)
    if entry is None:
        raise SystemExit(f"unknown proved registered root claim: {root_claim}")
    path = shortest_local_dependency_path(
        receipt, entry["root_theorem"], target, projection=args.projection
    )
    if path is None:
        raise SystemExit(
            f"no project-local {args.projection} compiler dependency path "
            f"from {root_claim} to {target}"
        )
    by_name = {row["declaration"]: row for row in receipt}
    edges = []
    for source, dest in zip(path, path[1:]):
        source_row = by_name[source]
        dep = next(
            dep
            for dep in source_row["dependencies"]
            if dep["constant"] == dest
            and views.dependency_edge_allowed(source_row, dep, args.projection)
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
        "projection": args.projection,
        "target_declaration": target,
        "path_length": len(path) - 1,
        "path": path,
        "edges": edges,
        "edge_direction": "SOURCE_DECLARATION_TO_COMPILER_USED_CONSTANT",
        "interpretation": (
            "Deterministic shortest path in the exact projected local compiler "
            "dependency graph; not logical implication or semantic necessity."
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }
    print(json.dumps(out, sort_keys=True, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
