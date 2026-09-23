from __future__ import annotations

import json
from pathlib import Path

import build as graph_build

GRAPH = Path(__file__).resolve().parent
RHRC = GRAPH.parent
REPO = RHRC.parents[1]
GENERATED = GRAPH / "generated"

FORBIDDEN_PHASE1_RELATIONS = {
    "PROVES",
    "USES_CONSTANT",
    "DEPENDS_ON",
    "KILLS_ROUTE",
    "REOPENS",
    "SUPERSEDES",
}


def read_jsonl(name: str) -> list[dict]:
    path = GENERATED / name
    rows: list[dict] = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError as exc:
            raise ValueError(f"{path}:{number}: invalid JSON: {exc}") from exc
    return rows


def main() -> int:
    errors: list[str] = []

    repo_files = read_jsonl("repository_files.jsonl")
    lean_modules = read_jsonl("lean_modules.jsonl")
    registry_nodes = read_jsonl("registry_nodes.jsonl")
    relations = read_jsonl("relations.jsonl")

    all_nodes = repo_files + lean_modules + registry_nodes
    ids: set[str] = set()
    duplicates: set[str] = set()
    for row in all_nodes:
        rid = row.get("id")
        if not rid:
            errors.append(f"node missing id: {row}")
            continue
        if rid in ids:
            duplicates.add(rid)
        ids.add(rid)
    if duplicates:
        errors.append(f"duplicate graph IDs: {sorted(duplicates)}")

    tracked = set(graph_build.tracked_files())
    indexed = {row["path"] for row in repo_files}
    if tracked != indexed:
        errors.append(
            "repository coverage mismatch: "
            f"unindexed={sorted(tracked - indexed)} "
            f"phantom={sorted(indexed - tracked)}"
        )

    unknown = sorted(
        row["path"] for row in repo_files if row["file_class"] == "UNKNOWN_FILE_CLASS"
    )
    if unknown:
        errors.append(f"unclassified tracked files: {unknown}")

    declared_generated = set(graph_build.DECLARED_GENERATED_PRODUCTS)
    actual_generated = {row["path"] for row in repo_files if row["generated_product"]}
    if actual_generated != declared_generated:
        errors.append(
            "generated-product declaration mismatch: "
            f"missing={sorted(declared_generated - actual_generated)} "
            f"extra={sorted(actual_generated - declared_generated)}"
        )

    for row in repo_files:
        if not (REPO / row["path"]).exists():
            errors.append(f"missing source path: {row['path']}")
        if row["generated_product"] and row.get("git_blob") is not None:
            errors.append(f"generated product recursively carries git_blob: {row['path']}")
        if not row["generated_product"] and not row.get("git_blob"):
            errors.append(f"subject file missing git_blob: {row['path']}")

    local_modules = [m for m in lean_modules if m["repository_scope"] == "LOCAL"]
    external_modules = [m for m in lean_modules if m["repository_scope"] == "EXTERNAL"]
    expected_lean_paths = {
        row["path"]
        for row in repo_files
        if row["file_class"] in {"LEAN_SOURCE", "LEAN_ROOT"}
    }
    actual_lean_paths = {m["path"] for m in local_modules}
    if expected_lean_paths != actual_lean_paths:
        errors.append(
            "Lean file/module coverage mismatch: "
            f"missing_modules={sorted(expected_lean_paths - actual_lean_paths)} "
            f"phantom_modules={sorted(actual_lean_paths - expected_lean_paths)}"
        )

    module_ids = {m["id"] for m in lean_modules}
    local_module_ids = {m["id"] for m in local_modules}
    for rel in relations:
        if rel.get("source") not in ids:
            errors.append(f"missing relation source endpoint: {rel}")
        if rel.get("target") not in ids:
            errors.append(f"missing relation target endpoint: {rel}")
        if rel.get("kind") in FORBIDDEN_PHASE1_RELATIONS:
            errors.append(f"forbidden Phase-1 claim-bearing relation: {rel['kind']}")
        if rel.get("kind") == "IMPORTS":
            if rel["source"] not in local_module_ids:
                errors.append(f"IMPORTS source is not a local module: {rel}")
            if rel["target"] not in module_ids:
                errors.append(f"IMPORTS target is not an explicit module node: {rel}")

    claim_source = json.loads((REPO / graph_build.CLAIM_REGISTRY).read_text(encoding="utf-8"))
    route_source = json.loads((REPO / graph_build.ROUTE_REGISTRY).read_text(encoding="utf-8"))
    claim_nodes = [n for n in registry_nodes if n["type"] == "RegisteredClaim"]
    route_nodes = [n for n in registry_nodes if n["type"] == "Route"]

    claim_projection = sorted((n["projection"] for n in claim_nodes), key=lambda x: x["id"])
    source_claims = sorted(claim_source["claims"], key=lambda x: x["id"])
    if claim_projection != source_claims:
        errors.append("CLAIM_REGISTRY projection is not exact")

    route_projection = sorted((n["projection"] for n in route_nodes), key=lambda x: x["route_id"])
    source_routes = sorted(route_source["routes"], key=lambda x: x["route_id"])
    if route_projection != source_routes:
        errors.append("ROUTE_REGISTRY projection is not exact")

    boundary = json.loads((REPO / graph_build.BOUNDARY).read_text(encoding="utf-8"))
    if boundary.get("terminal_claim_id") != "C_RH":
        errors.append(f"unexpected terminal claim id: {boundary.get('terminal_claim_id')!r}")
    terminal = next((c for c in claim_source["claims"] if c["id"] == "C_RH"), None)
    if terminal is None or terminal.get("status") != "OPEN":
        errors.append("terminal claim is not OPEN")

    coverage = json.loads((GENERATED / "REPOSITORY_COVERAGE.json").read_text(encoding="utf-8"))
    if coverage.get("terminal_claim") != "RH_OPEN":
        errors.append("coverage view does not preserve RH_OPEN")
    if coverage.get("graph_theorem_promotion") is not False:
        errors.append("coverage view permits graph theorem promotion")
    if coverage.get("unindexed_files") != []:
        errors.append("coverage view reports unindexed files")
    if coverage.get("unclassified_files") != []:
        errors.append("coverage view reports unclassified files")

    if errors:
        print("RHKG VALIDATION: FAIL")
        for error in errors:
            print(" -", error)
        return 1

    print(
        "RHKG VALIDATION: PASS "
        f"({len(repo_files)} files; {len(local_modules)} local Lean modules; "
        f"{len(external_modules)} external import targets; "
        f"{len(claim_nodes)} claim mirrors; {len(route_nodes)} route mirrors; "
        f"{len(relations)} relations; terminal claim RH_OPEN)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
