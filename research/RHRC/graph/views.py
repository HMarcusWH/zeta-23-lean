from __future__ import annotations

from collections import Counter


def _closure(graph: dict[str, list[str]], start: str) -> list[str]:
    if start not in graph:
        return []
    seen: set[str] = set()
    stack = [start]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        for dep in graph.get(current, []):
            if dep in graph and dep not in seen:
                stack.append(dep)
    return sorted(seen)


def coverage_view(
    repo_files: list[dict],
    lean_modules: list[dict],
    registry_nodes: list[dict],
    relations: list[dict],
    subject_digest: str,
    declared_generated_products: list[str],
) -> dict:
    local_modules = [m for m in lean_modules if m["repository_scope"] == "LOCAL"]
    external_modules = [m for m in lean_modules if m["repository_scope"] == "EXTERNAL"]
    claims = [n for n in registry_nodes if n["type"] == "RegisteredClaim"]
    routes = [n for n in registry_nodes if n["type"] == "Route"]
    return {
        "schema_version": "RHKG-phase1-coverage-0.1",
        "tracked_file_count": len(repo_files),
        "subject_file_count": sum(not row["generated_product"] for row in repo_files),
        "generated_product_count": sum(row["generated_product"] for row in repo_files),
        "file_class_counts": dict(sorted(Counter(r["file_class"] for r in repo_files).items())),
        "trust_zone_counts": dict(sorted(Counter(r["trust_zone"] for r in repo_files).items())),
        "local_lean_module_count": len(local_modules),
        "external_lean_module_count": len(external_modules),
        "registered_claim_count": len(claims),
        "route_count": len(routes),
        "relation_count": len(relations),
        "subject_digest_sha256": subject_digest,
        "declared_generated_products": sorted(declared_generated_products),
        "unindexed_files": [],
        "unclassified_files": sorted(
            r["path"] for r in repo_files if r["file_class"] == "UNKNOWN_FILE_CLASS"
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }


def reachability_view(local_import_graph: dict[str, list[str]]) -> dict:
    comparator_candidates = ("Challenge", "ChallengeDeps", "Solution", "PrintAxioms")
    comparator_roots = [m for m in comparator_candidates if m in local_import_graph]
    zeta = _closure(local_import_graph, "Zeta23")
    ccm = _closure(local_import_graph, "Zeta23.CCM")
    exceptional = _closure(local_import_graph, "Zeta23.ExceptionalZero")
    comparator: set[str] = set()
    for root in comparator_roots:
        comparator.update(_closure(local_import_graph, root))
    all_reached = set(zeta) | set(ccm) | set(exceptional) | comparator
    standalone = sorted(set(local_import_graph) - all_reached)
    return {
        "schema_version": "RHKG-phase1-reachability-0.1",
        "entrypoints": {
            "Zeta23": "present" if "Zeta23" in local_import_graph else "missing",
            "Zeta23.CCM": "present" if "Zeta23.CCM" in local_import_graph else "missing",
            "Zeta23.ExceptionalZero": (
                "present" if "Zeta23.ExceptionalZero" in local_import_graph else "missing"
            ),
            "comparator_roots": comparator_roots,
        },
        "reachable_from_Zeta23_root": zeta,
        "reachable_from_CCM_root": ccm,
        "reachable_from_ExceptionalZero_root": exceptional,
        "reachable_from_comparator_roots": sorted(comparator),
        "standalone_or_auxiliary": standalone,
        "interpretation": (
            "Reachability is descriptive only. standalone_or_auxiliary does not imply "
            "invalidity, irrelevance, or absence from formal authority."
        ),
    }
