from __future__ import annotations

from collections import Counter, deque


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
    lean_declarations: list[dict],
    registry_nodes: list[dict],
    relations: list[dict],
    subject_digest: str,
    declared_generated_products: list[str],
) -> dict:
    local_modules = [m for m in lean_modules if m["repository_scope"] == "LOCAL"]
    external_modules = [m for m in lean_modules if m["repository_scope"] == "EXTERNAL"]
    claims = [n for n in registry_nodes if n["type"] == "RegisteredClaim"]
    routes = [n for n in registry_nodes if n["type"] == "Route"]
    roots = [d for d in lean_declarations if d["graph_role"] == "REGISTERED_CLAIM_ROOT"]
    local_deps = [d for d in lean_declarations if d["graph_role"] == "LOCAL_DEPENDENCY"]
    external_deps = [d for d in lean_declarations if d["graph_role"] == "EXTERNAL_BOUNDARY"]
    return {
        "schema_version": "RHKG-phase2b-coverage-0.4",
        "tracked_file_count": len(repo_files),
        "subject_file_count": sum(not row["generated_product"] for row in repo_files),
        "generated_product_count": sum(row["generated_product"] for row in repo_files),
        "file_class_counts": dict(sorted(Counter(r["file_class"] for r in repo_files).items())),
        "trust_zone_counts": dict(sorted(Counter(r["trust_zone"] for r in repo_files).items())),
        "local_lean_module_count": len(local_modules),
        "external_lean_module_count": len(external_modules),
        "registered_claim_count": len(claims),
        "registered_proved_lean_declaration_count": len(roots),
        "local_dependency_lean_declaration_count": len(local_deps),
        "external_boundary_lean_declaration_count": len(external_deps),
        "lean_declaration_count": len(lean_declarations),
        "route_count": len(routes),
        "node_type_counts": dict(
            sorted(
                Counter(
                    r["type"]
                    for r in (
                        repo_files + lean_modules + lean_declarations + registry_nodes
                    )
                ).items()
            )
        ),
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


def reachability_view(
    local_import_graph: dict[str, list[str]], comparator_roots: list[str]
) -> dict:
    comparator_roots = sorted(m for m in comparator_roots if m in local_import_graph)
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


def theorem_claim_view(
    lean_declarations: list[dict],
    claims_data: dict,
    binding_data: dict,
    compiler_binding_source: str,
) -> dict:
    claim_by_id = {claim["id"]: claim for claim in claims_data["claims"]}
    declaration_by_name = {
        declaration["declaration"]: declaration
        for declaration in lean_declarations
        if declaration["graph_role"] == "REGISTERED_CLAIM_ROOT"
    }
    entries: list[dict] = []
    bound_claim_ids: set[str] = set()
    for binding in binding_data["bindings"]:
        claim = claim_by_id[binding["id"]]
        declaration = declaration_by_name[binding["theorem"]]
        bound_claim_ids.add(binding["id"])
        entries.append(
            {
                "claim_id": binding["id"],
                "claim_node_id": "rh:claim:" + binding["id"],
                "claim_status": claim["status"],
                "route": claim.get("route"),
                "theorem": binding["theorem"],
                "declaration_id": declaration["id"],
                "module": declaration["module"],
                "module_id": declaration["module_id"],
                "source_path": declaration["source_path"],
                "source_file_id": declaration["source_file_id"],
                "binding_source": declaration["binding_source"],
                "compiler_binding_source": compiler_binding_source,
                "historical_r003_promoted": declaration["historical_r003_promoted"],
                "provenance": "REGISTRY_EXACT",
            }
        )
    entries.sort(key=lambda row: row["claim_id"])
    return {
        "schema_version": "RHKG-phase2b-theorem-claim-map-0.4",
        "scope": "ALL_PROVED_UNCONDITIONAL_REGISTERED_CLAIMS",
        "binding_authority": "research/RHRC/REGISTERED_THEOREM_BINDINGS.json",
        "compiler_binding_surface": compiler_binding_source,
        "registered_proved_binding_count": len(entries),
        "entries": entries,
        "unlinked_registered_claim_ids": sorted(set(claim_by_id) - bound_claim_ids),
        "unlinked_interpretation": (
            "Unlinked means not PROVED_UNCONDITIONAL under the complete registered "
            "theorem binding surface; RHKG does not infer proof status."
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }


def theorem_dependency_closure_view(
    compiler_receipt: list[dict],
    binding_data: dict,
) -> dict:
    row_by_name = {row["declaration"]: row for row in compiler_receipt}
    entries: list[dict] = []

    for binding in sorted(binding_data["bindings"], key=lambda row: row["id"]):
        root = binding["theorem"]
        root_row = row_by_name[root]
        direct_local = sorted(
            dep["constant"]
            for dep in root_row["dependencies"]
            if row_by_name[dep["constant"]]["repository_scope"] == "LOCAL"
        )
        direct_external = sorted(
            dep["constant"]
            for dep in root_row["dependencies"]
            if row_by_name[dep["constant"]]["repository_scope"] == "EXTERNAL"
        )

        depths: dict[str, int] = {root: 0}
        external: set[str] = set(direct_external)
        queue: deque[str] = deque([root])
        while queue:
            current = queue.popleft()
            depth = depths[current]
            for dep in row_by_name[current]["dependencies"]:
                target = dep["constant"]
                target_row = row_by_name[target]
                if target_row["repository_scope"] == "EXTERNAL":
                    external.add(target)
                    continue
                if target not in depths:
                    depths[target] = depth + 1
                    queue.append(target)

        entries.append(
            {
                "claim_id": binding["id"],
                "root_theorem": root,
                "direct_local_dependencies": direct_local,
                "transitive_local_dependencies": sorted(name for name in depths if name != root),
                "direct_external_boundaries": direct_external,
                "transitive_external_boundaries": sorted(external),
                "minimum_local_depth": {
                    name: depths[name] for name in sorted(depths) if name != root
                },
            }
        )

    return {
        "schema_version": "RHKG-phase2b-theorem-dependency-closure-0.4",
        "scope": "ALL_PROVED_UNCONDITIONAL_REGISTERED_CLAIMS",
        "entries": entries,
        "interpretation": (
            "Compiler-derived dependency reachability is descriptive. Shared dependencies "
            "are not automatically mathematically decisive and do not promote claims."
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }
