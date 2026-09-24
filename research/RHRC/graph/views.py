from __future__ import annotations

import hashlib
from collections import Counter, deque
from itertools import combinations


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


def _sha256_names(names: set[str] | list[str]) -> str:
    h = hashlib.sha256()
    for name in sorted(names):
        h.update(name.encode("utf-8"))
        h.update(b"\0")
    return h.hexdigest()


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
        "schema_version": "RHKG-phase2c-coverage-0.5",
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


def resolve_dependency_farming_cohorts(
    claims_data: dict,
    binding_data: dict,
    routes_data: dict,
    cohort_config: dict,
) -> list[dict]:
    if cohort_config.get("schema_version") != "RHKG-phase2c-farming-cohorts-0.5":
        raise ValueError("dependency farming cohort config schema drift")

    claim_by_id = {claim["id"]: claim for claim in claims_data["claims"]}
    binding_ids = {binding["id"] for binding in binding_data["bindings"]}
    known_routes = {route["route_id"] for route in routes_data["routes"]}
    open_ids = {
        claim["id"] for claim in claims_data["claims"] if claim.get("status") == "OPEN"
    }

    result: list[dict] = []
    seen_ids: set[str] = set()

    for spec in cohort_config.get("route_cohorts", []):
        cohort_id = spec["id"]
        route_id = spec["route_id"]
        if cohort_id in seen_ids:
            raise ValueError(f"duplicate dependency farming cohort id: {cohort_id}")
        if route_id not in known_routes:
            raise ValueError(f"unknown route cohort selector: {route_id}")
        members = sorted(
            binding_id
            for binding_id in binding_ids
            if claim_by_id[binding_id].get("route") == route_id
        )
        if not members:
            raise ValueError(f"route cohort {cohort_id} resolved to no proved roots")
        result.append(
            {
                "cohort_id": cohort_id,
                "kind": "ROUTE_SELECTOR",
                "route_id": route_id,
                "claim_ids": members,
            }
        )
        seen_ids.add(cohort_id)

    for spec in cohort_config.get("explicit_cohorts", []):
        cohort_id = spec["id"]
        if cohort_id in seen_ids:
            raise ValueError(f"duplicate dependency farming cohort id: {cohort_id}")
        members = spec.get("claim_ids", [])
        if not members or len(set(members)) != len(members):
            raise ValueError(f"explicit cohort {cohort_id} must contain unique members")
        unknown = sorted(set(members) - set(claim_by_id))
        if unknown:
            raise ValueError(f"explicit cohort {cohort_id} has unknown claims: {unknown}")
        unbound = sorted(set(members) - binding_ids)
        if unbound:
            raise ValueError(
                f"explicit cohort {cohort_id} contains non-proved/unbound claims: {unbound}"
            )
        open_members = sorted(set(members) & open_ids)
        if open_members:
            raise ValueError(
                f"explicit cohort {cohort_id} contains OPEN claims: {open_members}"
            )
        result.append(
            {
                "cohort_id": cohort_id,
                "kind": "EXPLICIT",
                "claim_ids": sorted(members),
            }
        )
        seen_ids.add(cohort_id)

    return sorted(result, key=lambda row: row["cohort_id"])


def dependency_kernel_atlas_view(
    compiler_receipt: list[dict],
    dependency_closure: dict,
    cohorts: list[dict],
) -> dict:
    row_by_name = {row["declaration"]: row for row in compiler_receipt}
    entry_by_claim = {row["claim_id"]: row for row in dependency_closure["entries"]}
    root_claim_by_theorem = {
        row["root_theorem"]: row["claim_id"] for row in dependency_closure["entries"]
    }

    closure_by_claim: dict[str, set[str]] = {}
    direct_by_claim: dict[str, set[str]] = {}
    depth_by_claim: dict[str, dict[str, int]] = {}
    for claim_id, entry in entry_by_claim.items():
        closure_by_claim[claim_id] = {
            entry["root_theorem"],
            *entry["transitive_local_dependencies"],
        }
        direct_by_claim[claim_id] = set(entry["direct_local_dependencies"])
        depth_by_claim[claim_id] = {
            entry["root_theorem"]: 0,
            **entry["minimum_local_depth"],
        }

    incoming: dict[str, dict[str, int]] = {}
    for source in compiler_receipt:
        if source["repository_scope"] != "LOCAL":
            continue
        for dep in source["dependencies"]:
            target = dep["constant"]
            target_row = row_by_name[target]
            if target_row["repository_scope"] != "LOCAL":
                continue
            counts = incoming.setdefault(
                target,
                {"type": 0, "value": 0, "structure": 0, "edge": 0},
            )
            counts["edge"] += 1
            counts["type"] += int(dep["used_in_type"])
            counts["value"] += int(dep["used_in_value"])
            counts["structure"] += int(dep["used_in_structure"])

    cohort_members = {
        cohort["cohort_id"]: set(cohort["claim_ids"]) for cohort in cohorts
    }
    entries: list[dict] = []
    for decl in sorted(
        row["declaration"]
        for row in compiler_receipt
        if row["repository_scope"] == "LOCAL"
    ):
        row = row_by_name[decl]
        reaching = sorted(
            claim_id
            for claim_id, closure in closure_by_claim.items()
            if decl in closure
        )
        direct = sorted(
            claim_id
            for claim_id, direct_set in direct_by_claim.items()
            if decl in direct_set
        )
        own_root = [root_claim_by_theorem[decl]] if decl in root_claim_by_theorem else []
        reaching_cohorts = sorted(
            cohort_id
            for cohort_id, members in cohort_members.items()
            if any(claim_id in members for claim_id in reaching)
        )
        universal_cohorts = sorted(
            cohort_id
            for cohort_id, members in cohort_members.items()
            if members and all(decl in closure_by_claim[claim_id] for claim_id in members)
        )
        depths = [
            depth_by_claim[claim_id][decl]
            for claim_id in reaching
            if decl in depth_by_claim[claim_id]
        ]
        counts = incoming.get(
            decl,
            {"type": 0, "value": 0, "structure": 0, "edge": 0},
        )
        entries.append(
            {
                "declaration": decl,
                "module": row["module"],
                "graph_role": row["graph_role"],
                "private_or_internal": row["private_or_internal"],
                "root_claim_ids": own_root,
                "reaching_root_claim_ids": reaching,
                "root_reach_count": len(reaching),
                "direct_root_claim_ids": direct,
                "direct_root_count": len(direct),
                "reaching_cohort_ids": reaching_cohorts,
                "universal_cohort_ids": universal_cohorts,
                "minimum_depth_from_any_root": min(depths) if depths else None,
                "incoming_local_edge_count": counts["edge"],
                "incoming_type_edge_count": counts["type"],
                "incoming_value_edge_count": counts["value"],
                "incoming_structure_edge_count": counts["structure"],
            }
        )

    return {
        "schema_version": "RHKG-phase2c-dependency-kernel-atlas-0.5",
        "scope": "COMPILER_LOCAL_CLOSURE_OF_ALL_PROVED_REGISTERED_ROOTS",
        "local_declaration_count": len(entries),
        "registered_root_count": len(entry_by_claim),
        "cohort_ids": sorted(cohort_members),
        "entries": entries,
        "interpretation": (
            "Reach and overlap describe exact compiler dependency structure only. "
            "High reach, shared dependencies, or cohort universality do not establish "
            "mathematical importance or theorem equivalence."
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }


def dependency_cohort_overlap_view(
    compiler_receipt: list[dict],
    dependency_closure: dict,
    cohorts: list[dict],
) -> dict:
    entry_by_claim = {row["claim_id"]: row for row in dependency_closure["entries"]}
    registered_root_declarations = {
        row["declaration"]
        for row in compiler_receipt
        if row["graph_role"] == "REGISTERED_CLAIM_ROOT"
    }

    closure_by_claim = {
        claim_id: set(entry["transitive_local_dependencies"])
        for claim_id, entry in entry_by_claim.items()
    }

    cohort_rows: list[dict] = []
    union_by_cohort: dict[str, set[str]] = {}
    for cohort in cohorts:
        cohort_id = cohort["cohort_id"]
        members = cohort["claim_ids"]
        sets = [closure_by_claim[claim_id] for claim_id in members]
        union = set().union(*sets)
        intersection = set(sets[0])
        for current in sets[1:]:
            intersection &= current
        dependency_only_intersection = intersection - registered_root_declarations
        union_by_cohort[cohort_id] = union
        row = {
            "cohort_id": cohort_id,
            "kind": cohort["kind"],
            "claim_ids": members,
            "root_count": len(members),
            "local_dependency_union_count": len(union),
            "local_dependency_intersection_count": len(intersection),
            "local_dependency_intersection_excluding_registered_roots_count": len(
                dependency_only_intersection
            ),
            "local_dependency_union": sorted(union),
            "local_dependency_intersection": sorted(intersection),
            "local_dependency_intersection_excluding_registered_roots": sorted(
                dependency_only_intersection
            ),
            "union_sha256": _sha256_names(union),
            "intersection_sha256": _sha256_names(intersection),
        }
        if "route_id" in cohort:
            row["route_id"] = cohort["route_id"]
        cohort_rows.append(row)

    pairwise: list[dict] = []
    for left_id, right_id in combinations(sorted(union_by_cohort), 2):
        left = union_by_cohort[left_id]
        right = union_by_cohort[right_id]
        shared = left & right
        union = left | right
        left_only = left - right
        right_only = right - left
        if left == right:
            containment = "EQUAL"
        elif left < right:
            containment = "LEFT_STRICT_SUBSET"
        elif right < left:
            containment = "RIGHT_STRICT_SUBSET"
        else:
            containment = "NONE"
        pairwise.append(
            {
                "left_cohort_id": left_id,
                "right_cohort_id": right_id,
                "left_count": len(left),
                "right_count": len(right),
                "shared_count": len(shared),
                "union_count": len(union),
                "left_only_count": len(left_only),
                "right_only_count": len(right_only),
                "containment": containment,
                "jaccard_numerator": len(shared),
                "jaccard_denominator": len(union),
                "shared": sorted(shared),
                "left_only": sorted(left_only),
                "right_only": sorted(right_only),
            }
        )

    return {
        "schema_version": "RHKG-phase2c-dependency-cohort-overlap-0.5",
        "cohorts": sorted(cohort_rows, key=lambda row: row["cohort_id"]),
        "pairwise": pairwise,
        "interpretation": (
            "Cohort union/intersection and pairwise overlap are exact set relations over "
            "compiler-derived project-local dependency closures. They are discovery-only "
            "and do not imply logical implication, equivalence, or theorem promotion."
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }


def dependency_signature_classes_view(dependency_closure: dict) -> dict:
    entries: list[dict] = []
    closure_by_claim: dict[str, set[str]] = {}
    groups: dict[str, list[str]] = {}

    for row in dependency_closure["entries"]:
        claim_id = row["claim_id"]
        closure = set(row["transitive_local_dependencies"])
        digest = _sha256_names(closure)
        closure_by_claim[claim_id] = closure
        groups.setdefault(digest, []).append(claim_id)
        entries.append(
            {
                "claim_id": claim_id,
                "root_theorem": row["root_theorem"],
                "local_dependency_count": len(closure),
                "closure_sha256": digest,
            }
        )

    exact_equal_classes = [
        {
            "closure_sha256": digest,
            "claim_ids": sorted(claim_ids),
            "local_dependency_count": len(
                closure_by_claim[sorted(claim_ids)[0]]
            ),
        }
        for digest, claim_ids in sorted(groups.items())
        if len(claim_ids) > 1
    ]

    strict_containments: list[dict] = []
    claim_ids = sorted(closure_by_claim)
    for left_id in claim_ids:
        left = closure_by_claim[left_id]
        for right_id in claim_ids:
            if left_id == right_id:
                continue
            right = closure_by_claim[right_id]
            if left < right:
                strict_containments.append(
                    {
                        "subset_claim_id": left_id,
                        "superset_claim_id": right_id,
                        "subset_count": len(left),
                        "superset_count": len(right),
                        "difference_count": len(right - left),
                    }
                )

    repeated_claim_ids = {
        claim_id
        for group in exact_equal_classes
        for claim_id in group["claim_ids"]
    }
    return {
        "schema_version": "RHKG-phase2c-dependency-signature-classes-0.5",
        "entries": sorted(entries, key=lambda row: row["claim_id"]),
        "exact_equal_closure_classes": exact_equal_classes,
        "strict_local_closure_containments": strict_containments,
        "unique_signature_claim_ids": sorted(set(claim_ids) - repeated_claim_ids),
        "interpretation": (
            "Exact dependency signatures and strict set containments describe proof "
            "implementation structure only. Equal closure is not theorem equivalence, "
            "and closure containment is not logical implication."
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }
