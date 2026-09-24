from __future__ import annotations

import hashlib
import json
from pathlib import Path

import build as graph_build

GRAPH = Path(__file__).resolve().parent
RHRC = GRAPH.parent
REPO = RHRC.parents[1]
GENERATED = GRAPH / "generated"
GRAPH_SCHEMA = GRAPH / "GRAPH_SCHEMA.json"

FORBIDDEN_CURRENT_RELATIONS = {
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


SUPPORTED_SCHEMA_KEYS = {
    "$schema",
    "$id",
    "$defs",
    "$ref",
    "title",
    "type",
    "oneOf",
    "allOf",
    "required",
    "properties",
    "additionalProperties",
    "const",
    "enum",
    "minLength",
}


def schema_definition_errors(schema: dict, path: str = "$") -> list[str]:
    """Fail closed if GRAPH_SCHEMA starts using keywords this validator ignores."""
    errors: list[str] = []
    for key in schema:
        if key not in SUPPORTED_SCHEMA_KEYS:
            errors.append(f"{path}: unsupported schema keyword {key!r}")

    for key in ("allOf", "oneOf"):
        for index, child in enumerate(schema.get(key, [])):
            errors.extend(schema_definition_errors(child, f"{path}.{key}[{index}]"))

    for name, child in schema.get("$defs", {}).items():
        errors.extend(schema_definition_errors(child, f"{path}.$defs.{name}"))

    for name, child in schema.get("properties", {}).items():
        errors.extend(schema_definition_errors(child, f"{path}.properties.{name}"))

    return errors


def _resolve_ref(ref: str, root: dict) -> dict:
    prefix = "#/$defs/"
    if not ref.startswith(prefix):
        raise ValueError(f"unsupported local schema ref: {ref!r}")
    name = ref[len(prefix):]
    try:
        return root["$defs"][name]
    except KeyError as exc:
        raise ValueError(f"unknown local schema ref: {ref!r}") from exc


def _type_matches(value: object, expected: str) -> bool:
    if expected == "object":
        return isinstance(value, dict)
    if expected == "array":
        return isinstance(value, list)
    if expected == "string":
        return isinstance(value, str)
    if expected == "boolean":
        return isinstance(value, bool)
    if expected == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    if expected == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if expected == "null":
        return value is None
    raise ValueError(f"unsupported schema type: {expected!r}")


def validate_schema_value(
    value: object,
    schema: dict,
    root: dict,
    path: str = "$",
) -> list[str]:
    errors: list[str] = []

    if "$ref" in schema:
        return validate_schema_value(value, _resolve_ref(schema["$ref"], root), root, path)

    for child in schema.get("allOf", []):
        errors.extend(validate_schema_value(value, child, root, path))

    if "oneOf" in schema:
        matches = [
            index
            for index, child in enumerate(schema["oneOf"])
            if not validate_schema_value(value, child, root, path)
        ]
        if len(matches) != 1:
            errors.append(f"{path}: expected exactly one oneOf branch, matched {matches}")

    if "const" in schema and value != schema["const"]:
        errors.append(f"{path}: expected const {schema['const']!r}, got {value!r}")

    if "enum" in schema and value not in schema["enum"]:
        errors.append(f"{path}: value {value!r} not in enum {schema['enum']!r}")

    expected_type = schema.get("type")
    if expected_type is not None and not _type_matches(value, expected_type):
        errors.append(
            f"{path}: expected type {expected_type!r}, got {type(value).__name__}"
        )
        return errors

    if isinstance(value, str) and "minLength" in schema:
        if len(value) < schema["minLength"]:
            errors.append(
                f"{path}: string shorter than minLength {schema['minLength']}"
            )

    if isinstance(value, dict):
        for required in schema.get("required", []):
            if required not in value:
                errors.append(f"{path}: missing required property {required!r}")

        properties = schema.get("properties", {})
        for name, child in properties.items():
            if name in value:
                errors.extend(
                    validate_schema_value(value[name], child, root, f"{path}.{name}")
                )

        if schema.get("additionalProperties") is False:
            extras = sorted(set(value) - set(properties))
            if extras:
                errors.append(f"{path}: additional properties forbidden: {extras}")

    return errors


def main() -> int:
    errors: list[str] = []

    repo_files = read_jsonl("repository_files.jsonl")
    lean_modules = read_jsonl("lean_modules.jsonl")
    lean_declarations = read_jsonl("lean_declarations.jsonl")
    registry_nodes = read_jsonl("registry_nodes.jsonl")
    relations = read_jsonl("relations.jsonl")

    schema = json.loads(GRAPH_SCHEMA.read_text(encoding="utf-8"))
    for error in schema_definition_errors(schema):
        errors.append(f"GRAPH_SCHEMA invalid: {error}")
    if not errors:
        for collection_name, rows in (
            ("repository_files.jsonl", repo_files),
            ("lean_modules.jsonl", lean_modules),
            ("lean_declarations.jsonl", lean_declarations),
            ("registry_nodes.jsonl", registry_nodes),
            ("relations.jsonl", relations),
        ):
            for index, row in enumerate(rows, start=1):
                for error in validate_schema_value(row, schema, schema):
                    errors.append(
                        f"{collection_name}:{index}: schema validation failed: {error}"
                    )

    all_nodes = repo_files + lean_modules + lean_declarations + registry_nodes
    node_ids: set[str] = set()
    all_ids: set[str] = set()
    duplicates: set[str] = set()
    for row in all_nodes + relations:
        rid = row.get("id")
        if not rid:
            errors.append(f"node missing id: {row}")
            continue
        if rid in all_ids:
            duplicates.add(rid)
        all_ids.add(rid)
        if row.get("type") != "Relation":
            node_ids.add(rid)
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
    local_module_by_path = {m["path"]: m for m in local_modules}
    declaration_ids = {d["id"] for d in lean_declarations}
    declaration_by_id = {d["id"]: d for d in lean_declarations}
    claim_node_ids = {
        n["id"] for n in registry_nodes if n["type"] == "RegisteredClaim"
    }
    for rel in relations:
        kind = rel.get("kind")
        source = rel.get("source")
        target = rel.get("target")
        if all(isinstance(value, str) for value in (kind, source, target)):
            expected_relation_id = "rh:rel:" + hashlib.sha256(
                f"{kind}|{source}|{target}".encode("utf-8")
            ).hexdigest()
            if rel.get("id") != expected_relation_id:
                errors.append(
                    "relation stable-ID mismatch: "
                    f"{rel.get('id')!r} != {expected_relation_id!r}"
                )
        if rel.get("source") not in node_ids:
            errors.append(f"missing relation source endpoint: {rel}")
        if rel.get("target") not in node_ids:
            errors.append(f"missing relation target endpoint: {rel}")
        if rel.get("kind") in FORBIDDEN_CURRENT_RELATIONS:
            errors.append(f"relation not authorized in Phase 2B: {rel['kind']}")
        if rel.get("kind") == "IMPORTS":
            if rel["source"] not in local_module_ids:
                errors.append(f"IMPORTS source is not a local module: {rel}")
            if rel["target"] not in module_ids:
                errors.append(f"IMPORTS target is not an explicit module node: {rel}")
        if rel.get("kind") == "DECLARES":
            if rel["source"] not in local_module_ids:
                errors.append(f"DECLARES source is not a local module: {rel}")
            if rel["target"] not in declaration_ids:
                errors.append(f"DECLARES target is not a LeanDeclaration: {rel}")
            target_decl = declaration_by_id.get(rel["target"])
            expected_provenance = (
                "REGISTRY_EXACT"
                if target_decl and target_decl.get("graph_role") == "REGISTERED_CLAIM_ROOT"
                else "LEAN_ENV_EXACT"
            )
            if rel.get("provenance") != expected_provenance:
                errors.append(
                    f"DECLARES provenance drift: {rel.get('provenance')} != "
                    f"{expected_provenance}: {rel}"
                )
        if rel.get("kind") == "PROVES":
            if rel["source"] not in declaration_ids:
                errors.append(f"PROVES source is not a LeanDeclaration: {rel}")
            if rel["target"] not in claim_node_ids:
                errors.append(f"PROVES target is not a RegisteredClaim: {rel}")
            source_decl = declaration_by_id.get(rel["source"])
            if source_decl and source_decl.get("graph_role") != "REGISTERED_CLAIM_ROOT":
                errors.append(f"non-root declaration has PROVES edge: {rel}")
            if rel.get("provenance") != "REGISTRY_EXACT":
                errors.append(f"PROVES provenance is not REGISTRY_EXACT: {rel}")
        if rel.get("kind") == "USES_CONSTANT":
            if rel["source"] not in declaration_ids or rel["target"] not in declaration_ids:
                errors.append(f"USES_CONSTANT endpoints are not declarations: {rel}")
            if rel.get("provenance") != "LEAN_ENV_EXACT":
                errors.append(f"USES_CONSTANT provenance is not LEAN_ENV_EXACT: {rel}")
            flags = [
                rel.get("used_in_type"),
                rel.get("used_in_value"),
                rel.get("used_in_structure"),
            ]
            if not all(isinstance(flag, bool) for flag in flags) or not any(flags):
                errors.append(f"USES_CONSTANT channel metadata invalid: {rel}")


    expected_artifact_classes = {
        "ControlObject": {"CONTROL_STATE"},
        "HistoricalDelta": {
            "FROZEN_RESEARCH_DELTA",
            "FROZEN_OBSTRUCTION_DELTA",
            "FROZEN_DEAD_ROUTE_DELTA",
        },
        "ResearchExecutable": {"RESEARCH_EXECUTABLE"},
        "Fixture": {"RESEARCH_FIXTURE"},
        "WorkflowDefinition": {"CI_WORKFLOW"},
    }
    file_by_id = {row["id"]: row for row in repo_files}
    for node in registry_nodes:
        allowed = expected_artifact_classes.get(node["type"])
        if allowed is None:
            continue
        source = file_by_id.get(node.get("file_id"))
        if source is None:
            errors.append(f"artifact node missing RepoFile endpoint: {node}")
        elif source["file_class"] not in allowed:
            errors.append(
                f"artifact node/file-class mismatch: {node['id']} -> {source['file_class']}"
            )

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


    registered_bindings = json.loads(
        (REPO / graph_build.REGISTERED_BINDINGS).read_text(encoding="utf-8")
    )
    promoted = json.loads(
        (REPO / graph_build.PROMOTED_BINDINGS).read_text(encoding="utf-8")
    )
    claim_by_id = {claim["id"]: claim for claim in claim_source["claims"]}
    proved_claims = {
        claim["id"]: claim
        for claim in claim_source["claims"]
        if claim.get("status") == "PROVED_UNCONDITIONAL"
    }
    open_claim_ids = {
        claim["id"]
        for claim in claim_source["claims"]
        if claim.get("status") == "OPEN"
    }
    expected_open_claim_ids = {
        "C_RH",
        "R001_PRIME_UPPER",
        "R002_WINDOWED_VISIBILITY",
    }
    if open_claim_ids != expected_open_claim_ids:
        errors.append(
            "OPEN registered-claim set drift: "
            f"expected={sorted(expected_open_claim_ids)} "
            f"actual={sorted(open_claim_ids)}"
        )

    if registered_bindings.get("scope") != "ALL_PROVED_UNCONDITIONAL_REGISTERED_CLAIMS":
        errors.append("registered theorem binding manifest scope drift")
    if registered_bindings.get("terminal_claim") != "RH_OPEN":
        errors.append("registered theorem binding manifest does not preserve RH_OPEN")

    binding_by_id = {row["id"]: row for row in registered_bindings["bindings"]}
    if len(binding_by_id) != len(registered_bindings["bindings"]):
        errors.append("duplicate claim IDs in registered theorem binding manifest")
    if set(binding_by_id) != set(proved_claims):
        errors.append(
            "registered theorem binding completeness mismatch: "
            f"missing={sorted(set(proved_claims) - set(binding_by_id))} "
            f"extra={sorted(set(binding_by_id) - set(proved_claims))}"
        )

    promoted_by_id = {row["id"]: row for row in promoted["bindings"]}
    for claim_id, row in promoted_by_id.items():
        registered = binding_by_id.get(claim_id)
        if registered is None:
            errors.append(f"historical R003 binding missing from complete manifest: {claim_id}")
        elif registered.get("theorem") != row.get("theorem"):
            errors.append(f"historical R003 theorem drift in complete manifest: {claim_id}")

    post259_receipt = json.loads(
        (REPO / graph_build.POST259_KERNEL_RECEIPT).read_text(encoding="utf-8")
    )
    if post259_receipt.get("schema_version") != "RHKG-post259-kernel-first-contact-1.0":
        errors.append("post-259 kernel first-contact receipt schema drift")
    authority = post259_receipt.get("authority", {})
    if authority.get("theorem_authority") is not False:
        errors.append("post-259 research receipt claims theorem authority")
    if authority.get("research_only") is not True:
        errors.append("post-259 research receipt lost research-only status")
    if authority.get("terminal_claim") != "RH_OPEN":
        errors.append("post-259 research receipt does not preserve RH_OPEN")
    if authority.get("graph_theorem_promotion") is not False:
        errors.append("post-259 research receipt permits theorem promotion")
    source = post259_receipt.get("source", {})
    if source.get("pull_request") != 259:
        errors.append("post-259 research receipt source PR drift")
    if source.get("merge_commit") != "6be76581362680fc0f43574c762ba7fd512bb3e7":
        errors.append("post-259 research receipt merge commit drift")
    if source.get("merge_tree") != "d2851f6c1b04d8b54a5d387acafe87b0803adc66":
        errors.append("post-259 research receipt merge tree drift")

    post260_receipt = json.loads(
        (REPO / graph_build.POST260_QUOTIENT_RECEIPT).read_text(encoding="utf-8")
    )
    if post260_receipt.get("schema_version") != "RHKG-post260-quotient-frontier-first-contact-1.0":
        errors.append("post-260 quotient/frontier receipt schema drift")
    post260_authority = post260_receipt.get("authority", {})
    if post260_authority.get("theorem_authority") is not False:
        errors.append("post-260 research receipt claims theorem authority")
    if post260_authority.get("research_only") is not True:
        errors.append("post-260 research receipt lost research-only status")
    if post260_authority.get("terminal_claim") != "RH_OPEN":
        errors.append("post-260 research receipt does not preserve RH_OPEN")
    if post260_authority.get("graph_theorem_promotion") is not False:
        errors.append("post-260 research receipt permits theorem promotion")
    post260_source = post260_receipt.get("source", {})
    if post260_source.get("pull_request") != 260:
        errors.append("post-260 research receipt source PR drift")
    if post260_source.get("final_head") != "91d8ea51409c4dc264a0a1a79493b39323d4fa10":
        errors.append("post-260 research receipt final head drift")
    if post260_source.get("merge_commit") != "7893126bb3b3291e37faf5ea0f8d8e3fa78cf882":
        errors.append("post-260 research receipt merge commit drift")
    if post260_source.get("merge_tree") != "ee0794c12da199bc4079499987c34a6deee624ed":
        errors.append("post-260 research receipt merge tree drift")
    if post260_source.get("workflow_disposition") != "FULLY_GREEN_FINAL_HEAD":
        errors.append("post-260 research receipt workflow disposition drift")
    if post260_source.get("completed_check_count") != 14 or post260_source.get(
        "successful_check_count"
    ) != 14:
        errors.append("post-260 research receipt final-head check count drift")

    compiler_receipt = graph_build.load_compiler_dependency_receipt()
    compiler_by_name = {row["declaration"]: row for row in compiler_receipt}
    declaration_by_name = {d["declaration"]: d for d in lean_declarations}
    if set(declaration_by_name) != set(compiler_by_name):
        errors.append(
            "compiler declaration population mismatch: "
            f"missing={sorted(set(compiler_by_name) - set(declaration_by_name))} "
            f"extra={sorted(set(declaration_by_name) - set(compiler_by_name))}"
        )

    expected_declares: set[tuple[str, str]] = set()
    expected_proves: set[tuple[str, str]] = set()
    expected_uses: dict[tuple[str, str], tuple[bool, bool, bool]] = {}
    binding_by_theorem = {row["theorem"]: row for row in registered_bindings["bindings"]}

    receipt_root_names = {
        row["declaration"]
        for row in compiler_receipt
        if row.get("graph_role") == "REGISTERED_CLAIM_ROOT"
    }
    if receipt_root_names != set(binding_by_theorem):
        errors.append(
            "compiler receipt registered-root set mismatch: "
            f"missing={sorted(set(binding_by_theorem) - receipt_root_names)} "
            f"extra={sorted(receipt_root_names - set(binding_by_theorem))}"
        )

    local_module_by_name = {m["module"]: m for m in local_modules}
    for compiler_row in compiler_receipt:
        theorem = compiler_row["declaration"]
        actual = declaration_by_name.get(theorem)
        if actual is None:
            continue
        for field in (
            "repository_scope",
            "graph_role",
            "declaration_kind",
            "private_or_internal",
            "module",
        ):
            if actual.get(field) != compiler_row.get(field):
                errors.append(
                    f"compiler declaration field drift for {theorem}: {field}"
                )

        scope = compiler_row["repository_scope"]
        role = compiler_row["graph_role"]
        module_name = compiler_row.get("module")
        decl_id = graph_build.declaration_id(theorem)

        if scope == "LOCAL":
            module = local_module_by_name.get(module_name)
            if module is None:
                errors.append(
                    f"compiler-local declaration module is not indexed: {theorem} -> {module_name}"
                )
            else:
                if actual.get("module_id") != module["id"]:
                    errors.append(f"compiler-local module_id drift for {theorem}")
                if actual.get("source_path") != module["path"]:
                    errors.append(f"compiler-local source_path drift for {theorem}")
                if actual.get("source_file_id") != module["file_id"]:
                    errors.append(f"compiler-local source_file_id drift for {theorem}")
                expected_declares.add((module["id"], decl_id))
        elif scope == "EXTERNAL":
            if role != "EXTERNAL_BOUNDARY":
                errors.append(f"external declaration has non-boundary role: {theorem}")
            if actual.get("source_path") is not None:
                errors.append(f"external declaration fabricates local source path: {theorem}")
        else:
            errors.append(f"unknown compiler declaration scope: {theorem} -> {scope}")

        if role == "REGISTERED_CLAIM_ROOT":
            binding = binding_by_theorem.get(theorem)
            if binding is None:
                errors.append(f"registered compiler root lacks binding: {theorem}")
            else:
                claim = claim_by_id[binding["id"]]
                if compiler_row.get("registered_claim_id") != binding["id"]:
                    errors.append(
                        f"compiler root registered_claim_id drift: {theorem} -> "
                        f"{compiler_row.get('registered_claim_id')!r}"
                    )
                if actual.get("binding_scope") != "REGISTERED_PROVED":
                    errors.append(f"registered root binding_scope drift: {theorem}")
                if actual.get("authority_role") != "REGISTERED_CLAIM_DECLARATION":
                    errors.append(f"registered root authority_role drift: {theorem}")
                if actual.get("binding_source") != graph_build.REGISTERED_BINDINGS:
                    errors.append(f"registered root binding_source drift: {theorem}")
                if actual.get("compiler_binding_source") != graph_build.REGISTERED_BINDINGS_LEAN:
                    errors.append(f"registered root compiler binding source drift: {theorem}")
                if actual.get("historical_r003_promoted") != (binding["id"] in promoted_by_id):
                    errors.append(f"registered root historical-R003 flag drift: {theorem}")
                expected_proves.add((decl_id, graph_build.claim_id(binding["id"])))
                if claim.get("status") != "PROVED_UNCONDITIONAL":
                    errors.append(f"registered root claim is not proved: {binding['id']}")
        elif role == "LOCAL_DEPENDENCY":
            if actual.get("authority_role") != "DEPENDENCY_DECLARATION":
                errors.append(f"local dependency authority_role drift: {theorem}")
        elif role == "EXTERNAL_BOUNDARY":
            if actual.get("authority_role") != "EXTERNAL_BOUNDARY_DECLARATION":
                errors.append(f"external boundary authority_role drift: {theorem}")
        else:
            errors.append(f"unknown compiler graph role: {theorem} -> {role}")

        for dep in compiler_row["dependencies"]:
            key = (decl_id, graph_build.declaration_id(dep["constant"]))
            expected_uses[key] = (
                dep["used_in_type"],
                dep["used_in_value"],
                dep["used_in_structure"],
            )

    actual_declares = {
        (rel["source"], rel["target"])
        for rel in relations
        if rel.get("kind") == "DECLARES"
    }
    actual_proves = {
        (rel["source"], rel["target"])
        for rel in relations
        if rel.get("kind") == "PROVES"
    }
    actual_uses = {
        (rel["source"], rel["target"]): (
            rel.get("used_in_type"),
            rel.get("used_in_value"),
            rel.get("used_in_structure"),
        )
        for rel in relations
        if rel.get("kind") == "USES_CONSTANT"
    }
    if actual_declares != expected_declares:
        errors.append(
            "DECLARES relation projection mismatch: "
            f"missing={sorted(expected_declares - actual_declares)} "
            f"extra={sorted(actual_declares - expected_declares)}"
        )
    if actual_proves != expected_proves:
        errors.append(
            "PROVES relation projection mismatch: "
            f"missing={sorted(expected_proves - actual_proves)} "
            f"extra={sorted(actual_proves - expected_proves)}"
        )
    if actual_uses != expected_uses:
        errors.append(
            "USES_CONSTANT relation projection does not exactly match compiler receipt"
        )

    theorem_claim_map = json.loads(
        (GENERATED / "THEOREM_CLAIM_MAP.json").read_text(encoding="utf-8")
    )
    if theorem_claim_map.get("scope") != "ALL_PROVED_UNCONDITIONAL_REGISTERED_CLAIMS":
        errors.append("THEOREM_CLAIM_MAP scope drift")
    if theorem_claim_map.get("registered_proved_binding_count") != len(proved_claims):
        errors.append("THEOREM_CLAIM_MAP proved-binding count drift")
    if set(theorem_claim_map.get("unlinked_registered_claim_ids", [])) != open_claim_ids:
        errors.append("THEOREM_CLAIM_MAP unlinked set is not exactly the OPEN claim set")
    if theorem_claim_map.get("terminal_claim") != "RH_OPEN":
        errors.append("THEOREM_CLAIM_MAP does not preserve RH_OPEN")
    if theorem_claim_map.get("graph_theorem_promotion") is not False:
        errors.append("THEOREM_CLAIM_MAP permits graph theorem promotion")

    dependency_closure = json.loads(
        (GENERATED / "THEOREM_DEPENDENCY_CLOSURE.json").read_text(encoding="utf-8")
    )
    if dependency_closure.get("scope") != "ALL_PROVED_UNCONDITIONAL_REGISTERED_CLAIMS":
        errors.append("THEOREM_DEPENDENCY_CLOSURE scope drift")
    if {row["claim_id"] for row in dependency_closure.get("entries", [])} != set(binding_by_id):
        errors.append("THEOREM_DEPENDENCY_CLOSURE registered-root coverage drift")
    if dependency_closure.get("terminal_claim") != "RH_OPEN":
        errors.append("THEOREM_DEPENDENCY_CLOSURE does not preserve RH_OPEN")
    if dependency_closure.get("graph_theorem_promotion") is not False:
        errors.append("THEOREM_DEPENDENCY_CLOSURE permits graph theorem promotion")

    cohort_config = json.loads(
        (REPO / graph_build.DEPENDENCY_FARMING_COHORTS).read_text(encoding="utf-8")
    )
    try:
        resolved_cohorts = graph_build.resolve_dependency_farming_cohorts(
            claim_source,
            registered_bindings,
            route_source,
            cohort_config,
        )
    except ValueError as exc:
        errors.append(f"dependency farming cohort configuration invalid: {exc}")
        resolved_cohorts = []

    if cohort_config.get("terminal_claim") != "RH_OPEN":
        errors.append("dependency farming cohorts do not preserve RH_OPEN")
    if cohort_config.get("graph_theorem_promotion") is not False:
        errors.append("dependency farming cohorts permit theorem promotion")

    expected_cohort_ids = {
        "ROUTE_R001",
        "ROUTE_R002",
        "ROUTE_R003",
        "ROUTE_R004",
        "RH_EQUIVALENCE_SURFACE",
        "GLOBAL_BOTTOM_CHAIN",
        "CANONICAL_ARITHMETIC_SURFACE",
    }
    if {row["cohort_id"] for row in resolved_cohorts} != expected_cohort_ids:
        errors.append("dependency farming cohort ID surface drift")

    if resolved_cohorts:
        expected_kernel_atlas = graph_build.dependency_kernel_atlas_view(
            compiler_receipt,
            dependency_closure,
            resolved_cohorts,
        )
        expected_overlap = graph_build.dependency_cohort_overlap_view(
            compiler_receipt,
            dependency_closure,
            resolved_cohorts,
        )
        expected_signatures = graph_build.dependency_signature_classes_view(
            dependency_closure
        )

        kernel_atlas = json.loads(
            (GENERATED / "DEPENDENCY_KERNEL_ATLAS.json").read_text(encoding="utf-8")
        )
        cohort_overlap = json.loads(
            (GENERATED / "DEPENDENCY_COHORT_OVERLAP.json").read_text(encoding="utf-8")
        )
        signature_classes = json.loads(
            (GENERATED / "DEPENDENCY_SIGNATURE_CLASSES.json").read_text(encoding="utf-8")
        )

        if kernel_atlas != expected_kernel_atlas:
            errors.append("DEPENDENCY_KERNEL_ATLAS exact projection drift")
        if cohort_overlap != expected_overlap:
            errors.append("DEPENDENCY_COHORT_OVERLAP exact projection drift")
        if signature_classes != expected_signatures:
            errors.append("DEPENDENCY_SIGNATURE_CLASSES exact projection drift")

        quotient_config = json.loads(
            (REPO / graph_build.DEPENDENCY_QUOTIENT_CONFIG).read_text(encoding="utf-8")
        )
        try:
            resolved_quotient = graph_build.resolve_dependency_quotient_config(
                registered_bindings,
                resolved_cohorts,
                quotient_config,
            )
            expected_atoms = graph_build.dependency_cohort_atoms_view(
                lean_declarations,
                dependency_closure,
                resolved_quotient,
            )
            expected_quotient = graph_build.dependency_kernel_quotient_view(
                expected_atoms
            )
            expected_frontiers = graph_build.dependency_bridge_frontiers_view(
                compiler_receipt,
                dependency_closure,
                expected_atoms,
                resolved_quotient,
            )
        except ValueError as exc:
            errors.append(f"dependency quotient configuration/view invalid: {exc}")
            expected_atoms = expected_quotient = expected_frontiers = None

        if expected_atoms is not None:
            dependency_atoms = json.loads(
                (GENERATED / "DEPENDENCY_COHORT_ATOMS.json").read_text(encoding="utf-8")
            )
            kernel_quotient = json.loads(
                (GENERATED / "DEPENDENCY_KERNEL_QUOTIENT.json").read_text(encoding="utf-8")
            )
            bridge_frontiers = json.loads(
                (GENERATED / "DEPENDENCY_BRIDGE_FRONTIERS.json").read_text(encoding="utf-8")
            )
            if dependency_atoms != expected_atoms:
                errors.append("DEPENDENCY_COHORT_ATOMS exact projection drift")
            if kernel_quotient != expected_quotient:
                errors.append("DEPENDENCY_KERNEL_QUOTIENT exact projection drift")
            if bridge_frontiers != expected_frontiers:
                errors.append("DEPENDENCY_BRIDGE_FRONTIERS exact projection drift")

            target_overlap = next(
                (
                    row
                    for row in cohort_overlap["cohorts"]
                    if row["cohort_id"] == resolved_quotient["target_cohort_id"]
                ),
                None,
            )
            if target_overlap is None:
                errors.append("Phase 2D target cohort missing from Phase 2C overlap")
            elif dependency_atoms.get("union_count") != target_overlap.get(
                "local_dependency_union_count"
            ):
                errors.append(
                    "Phase 2D atom union does not equal target cohort dependency union"
                )

            atom_rows = dependency_atoms.get("atoms", [])
            declaration_rows = dependency_atoms.get("declaration_atoms", [])
            if sum(row.get("count", 0) for row in atom_rows) != dependency_atoms.get(
                "union_count"
            ):
                errors.append("Phase 2D atom partition count does not sum to union")
            if len({row["declaration"] for row in declaration_rows}) != len(
                declaration_rows
            ):
                errors.append("Phase 2D atom declaration mapping contains duplicates")

            atom_label_sets = {
                row["signature"]: set(row["member_labels"])
                for row in dependency_atoms.get("atoms", [])
            }
            for edge in bridge_frontiers.get("cross_atom_edges", []):
                if edge["source_atom"] == edge["target_atom"]:
                    errors.append("Phase 2D frontier contains same-atom edge")
                source_labels = atom_label_sets.get(edge["source_atom"])
                target_labels = atom_label_sets.get(edge["target_atom"])
                if source_labels is None or target_labels is None:
                    errors.append("Phase 2D frontier references unknown atom signature")
                elif not source_labels < target_labels:
                    errors.append(
                        "Phase 2D cross-atom edge violates reachability monotonicity: "
                        f"{edge['source_atom']} -> {edge['target_atom']}"
                    )
                if edge.get("bridge_candidate_eligible") and (
                    edge.get("source_registered_root")
                    or edge.get("target_registered_root")
                ):
                    errors.append(
                        "Phase 2D bridge candidate includes registered-root endpoint"
                    )

            probe_edges = bridge_frontiers.get("containment_probe", {}).get(
                "cross_region_edges", []
            )
            if any(
                edge.get("transition") != "SUPERSET_ONLY->SHARED"
                for edge in probe_edges
            ):
                errors.append(
                    "Phase 2D containment probe has non-monotone cross-region direction"
                )

            for name, product in (
                ("DEPENDENCY_COHORT_ATOMS", dependency_atoms),
                ("DEPENDENCY_KERNEL_QUOTIENT", kernel_quotient),
                ("DEPENDENCY_BRIDGE_FRONTIERS", bridge_frontiers),
            ):
                if product.get("terminal_claim") != "RH_OPEN":
                    errors.append(f"{name} does not preserve RH_OPEN")
                if product.get("graph_theorem_promotion") is not False:
                    errors.append(f"{name} permits graph theorem promotion")

        for name, product in (
            ("DEPENDENCY_KERNEL_ATLAS", kernel_atlas),
            ("DEPENDENCY_COHORT_OVERLAP", cohort_overlap),
            ("DEPENDENCY_SIGNATURE_CLASSES", signature_classes),
        ):
            if product.get("terminal_claim") != "RH_OPEN":
                errors.append(f"{name} does not preserve RH_OPEN")
            if product.get("graph_theorem_promotion") is not False:
                errors.append(f"{name} permits graph theorem promotion")

        expected_projection_summary = graph_build.dependency_projection_summary_view(
            compiler_receipt,
            registered_bindings,
            resolved_cohorts,
        )
        expected_projection_quotients = graph_build.dependency_projection_quotients_view(
            compiler_receipt,
            lean_declarations,
            registered_bindings,
            resolved_quotient,
        )
        expected_projection_frontiers = graph_build.dependency_projection_frontiers_view(
            compiler_receipt,
            registered_bindings,
            resolved_quotient,
            expected_projection_quotients,
        )

        projection_summary = json.loads(
            (GENERATED / "DEPENDENCY_PROJECTION_SUMMARY.json").read_text(encoding="utf-8")
        )
        projection_quotients = json.loads(
            (GENERATED / "DEPENDENCY_PROJECTION_QUOTIENTS.json").read_text(encoding="utf-8")
        )
        projection_frontiers = json.loads(
            (GENERATED / "DEPENDENCY_PROJECTION_FRONTIERS.json").read_text(encoding="utf-8")
        )

        if projection_summary != expected_projection_summary:
            errors.append("DEPENDENCY_PROJECTION_SUMMARY exact projection drift")
        if projection_quotients != expected_projection_quotients:
            errors.append("DEPENDENCY_PROJECTION_QUOTIENTS exact projection drift")
        if projection_frontiers != expected_projection_frontiers:
            errors.append("DEPENDENCY_PROJECTION_FRONTIERS exact projection drift")

        expected_projection_names = set(graph_build.DEPENDENCY_PROJECTIONS)
        if {
            row.get("projection") for row in projection_summary.get("projections", [])
        } != expected_projection_names:
            errors.append("Phase 2E projection summary surface drift")
        if {
            row.get("projection") for row in projection_quotients.get("projections", [])
        } != expected_projection_names:
            errors.append("Phase 2E quotient projection surface drift")
        if {
            row.get("projection") for row in projection_frontiers.get("projections", [])
        } != expected_projection_names:
            errors.append("Phase 2E frontier projection surface drift")

        # ANY is a regression baseline, not a redefinition of Phase 2D.
        old_by_claim = {
            row["claim_id"]: row for row in dependency_closure.get("entries", [])
        }
        for binding in registered_bindings["bindings"]:
            root = binding["theorem"]
            any_entry = graph_build.dependency_projection_closure_entry(
                compiler_receipt, root, "ANY"
            )
            if set(any_entry["transitive_local_dependencies"]) != set(
                old_by_claim[binding["id"]]["transitive_local_dependencies"]
            ):
                errors.append(
                    f"Phase 2E ANY local closure drift for {binding['id']}"
                )
            any_local = set(any_entry["transitive_local_dependencies"])
            for projection in (
                "TYPE_ONLY",
                "VALUE_ONLY",
                "THEOREM_VALUE_ERASED_SUPPORT",
            ):
                projected = set(
                    graph_build.dependency_projection_closure_entry(
                        compiler_receipt, root, projection
                    )["transitive_local_dependencies"]
                )
                if not projected <= any_local:
                    errors.append(
                        f"Phase 2E {projection} is not a subset of ANY for {binding['id']}"
                    )

        any_quotient = next(
            row
            for row in projection_quotients["projections"]
            if row["projection"] == "ANY"
        )
        if any_quotient.get("union_count") != dependency_atoms.get("union_count"):
            errors.append("Phase 2E ANY quotient union drift from Phase 2D")
        old_atoms_by_sig = {
            row["signature"]: row for row in dependency_atoms.get("atoms", [])
        }
        new_atoms_by_sig = {
            row["signature"]: row for row in any_quotient.get("atoms", [])
        }
        if set(old_atoms_by_sig) != set(new_atoms_by_sig):
            errors.append("Phase 2E ANY atom signature surface drift")
        else:
            for signature in sorted(old_atoms_by_sig):
                old_atom = old_atoms_by_sig[signature]
                new_atom = new_atoms_by_sig[signature]
                if (
                    old_atom.get("count") != new_atom.get("count")
                    or old_atom.get("sha256") != new_atom.get("sha256")
                    or old_atom.get("declarations") != new_atom.get("declarations")
                ):
                    errors.append(
                        f"Phase 2E ANY atom drift from Phase 2D: {signature}"
                    )

        any_frontier = next(
            row
            for row in projection_frontiers["projections"]
            if row["projection"] == "ANY"
        )
        if any_frontier.get("cross_atom_edges") != bridge_frontiers.get(
            "cross_atom_edges"
        ):
            errors.append("Phase 2E ANY cross-atom frontier drift from Phase 2D")
        any_pair = any_frontier.get("pair_probe", {})
        if (
            any_pair.get("relation") != "LEFT_STRICT_SUBSET"
            or any_pair.get("left_count") != 224
            or any_pair.get("right_count") != 2659
            or any_pair.get("left_only_count") != 0
            or any_pair.get("right_only_count") != 2435
            or any_pair.get("cross_region_edge_count") != 972
            or any_pair.get("eligible_cross_region_edge_count") != 949
        ):
            errors.append("Phase 2E ANY pair probe does not reproduce Phase 2D baseline")

        quotient_by_projection = {
            row["projection"]: row
            for row in projection_quotients.get("projections", [])
        }
        pair_memberships = {
            "LEFT_ONLY": {"LEFT"},
            "RIGHT_ONLY": {"RIGHT"},
            "SHARED": {"LEFT", "RIGHT"},
        }
        for frontier in projection_frontiers.get("projections", []):
            projection = frontier["projection"]
            quotient_row = quotient_by_projection[projection]
            label_sets = {
                row["signature"]: set(row["member_labels"])
                for row in quotient_row["atoms"]
            }
            for edge in frontier.get("cross_atom_edges", []):
                source_labels = label_sets.get(edge["source_atom"])
                target_labels = label_sets.get(edge["target_atom"])
                if source_labels is None or target_labels is None:
                    errors.append(
                        f"Phase 2E {projection} frontier references unknown atom"
                    )
                elif not source_labels < target_labels:
                    errors.append(
                        f"Phase 2E {projection} cross-atom edge violates reachability monotonicity"
                    )
                if edge.get("bridge_candidate_eligible") and (
                    edge.get("source_registered_root")
                    or edge.get("target_registered_root")
                ):
                    errors.append(
                        f"Phase 2E {projection} bridge candidate includes registered root"
                    )

            for edge in frontier.get("pair_probe", {}).get("cross_region_edges", []):
                source_membership = pair_memberships.get(edge["source_atom"])
                target_membership = pair_memberships.get(edge["target_atom"])
                if source_membership is None or target_membership is None:
                    errors.append(
                        f"Phase 2E {projection} pair frontier references unknown region"
                    )
                elif not source_membership < target_membership:
                    errors.append(
                        f"Phase 2E {projection} pair frontier violates reachability monotonicity"
                    )

        for name, product in (
            ("DEPENDENCY_PROJECTION_SUMMARY", projection_summary),
            ("DEPENDENCY_PROJECTION_QUOTIENTS", projection_quotients),
            ("DEPENDENCY_PROJECTION_FRONTIERS", projection_frontiers),
        ):
            if product.get("terminal_claim") != "RH_OPEN":
                errors.append(f"{name} does not preserve RH_OPEN")
            if product.get("graph_theorem_promotion") is not False:
                errors.append(f"{name} permits graph theorem promotion")

        proved_ids = set(binding_by_id)
        open_in_cohorts = sorted(
            open_claim_ids
            & {
                claim_id
                for cohort in resolved_cohorts
                for claim_id in cohort["claim_ids"]
            }
        )
        if open_in_cohorts:
            errors.append(
                f"OPEN claims entered proved dependency farming cohorts: {open_in_cohorts}"
            )
        unknown_in_cohorts = sorted(
            {
                claim_id
                for cohort in resolved_cohorts
                for claim_id in cohort["claim_ids"]
            }
            - proved_ids
        )
        if unknown_in_cohorts:
            errors.append(
                f"non-proved claims entered dependency farming cohorts: {unknown_in_cohorts}"
            )

    unresolved = json.loads(
        (GENERATED / "UNRESOLVED_GRAPH_ITEMS.json").read_text(encoding="utf-8")
    )
    if unresolved.get("schema_version") != "RHKG-phase2e-unresolved-0.7":
        errors.append("UNRESOLVED_GRAPH_ITEMS is not Phase 2E current")
    if unresolved.get("semantic_coverage_status") != "PARTIAL_BY_DESIGN_PHASE_2E":
        errors.append("UNRESOLVED_GRAPH_ITEMS semantic coverage status drift")
    if unresolved.get("claim_firewall") != "RH_OPEN":
        errors.append("UNRESOLVED_GRAPH_ITEMS does not preserve RH_OPEN")

    local_module_names = {m["module"] for m in local_modules}
    expected_external_import_targets: set[str] = set()
    for module in local_modules:
        source_text = (REPO / module["path"]).read_text(encoding="utf-8")
        expected_external_import_targets.update(
            dep
            for dep in graph_build.IMPORT_MODULES(source_text)
            if dep not in local_module_names
        )
    if set(unresolved.get("external_import_targets", [])) != expected_external_import_targets:
        errors.append(
            "UNRESOLVED_GRAPH_ITEMS external_import_targets does not exactly match "
            "syntactic Lean imports"
        )

    expected_compiler_boundary_modules = {
        row["module"]
        for row in compiler_receipt
        if row.get("repository_scope") == "EXTERNAL" and row.get("module")
    }
    if set(unresolved.get("compiler_external_boundary_modules", [])) != expected_compiler_boundary_modules:
        errors.append(
            "UNRESOLVED_GRAPH_ITEMS compiler_external_boundary_modules does not exactly "
            "match compiler receipt"
        )

    expected_external_modules = (
        expected_external_import_targets | expected_compiler_boundary_modules
    )
    actual_external_modules = {m["module"] for m in external_modules}
    if actual_external_modules != expected_external_modules:
        errors.append(
            "external Lean module node set mismatch: "
            f"missing={sorted(expected_external_modules - actual_external_modules)} "
            f"extra={sorted(actual_external_modules - expected_external_modules)}"
        )
    for module in external_modules:
        name = module["module"]
        expected_role = (
            "EXPLICIT_EXTERNAL_IMPORT_TARGET"
            if name in expected_external_import_targets
            else "COMPILER_EXTERNAL_BOUNDARY_MODULE"
        )
        if module.get("authority_role") != expected_role:
            errors.append(
                f"external module authority-role drift for {name}: "
                f"{module.get('authority_role')!r} != {expected_role!r}"
            )

    boundary = json.loads((REPO / graph_build.BOUNDARY).read_text(encoding="utf-8"))
    if boundary.get("terminal_claim_id") != "C_RH":
        errors.append(f"unexpected terminal claim id: {boundary.get('terminal_claim_id')!r}")
    terminal = next((c for c in claim_source["claims"] if c["id"] == "C_RH"), None)
    if terminal is None or terminal.get("status") != "OPEN":
        errors.append("terminal claim is not OPEN")

    coverage = json.loads((GENERATED / "REPOSITORY_COVERAGE.json").read_text(encoding="utf-8"))
    if coverage.get("schema_version") != "RHKG-phase2e-coverage-0.7":
        errors.append("coverage view is not Phase 2E current")
    if coverage.get("registered_proved_lean_declaration_count") != len(binding_by_id):
        errors.append("coverage registered-root count drift")
    if coverage.get("lean_declaration_count") != len(lean_declarations):
        errors.append("coverage Lean-declaration count drift")
    if coverage.get("local_dependency_lean_declaration_count") != sum(
        d.get("graph_role") == "LOCAL_DEPENDENCY" for d in lean_declarations
    ):
        errors.append("coverage local-dependency declaration count drift")
    if coverage.get("external_boundary_lean_declaration_count") != sum(
        d.get("graph_role") == "EXTERNAL_BOUNDARY" for d in lean_declarations
    ):
        errors.append("coverage external-boundary declaration count drift")
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
        f"{len(external_modules)} external module nodes; "
        f"{sum(d.get('graph_role') == 'REGISTERED_CLAIM_ROOT' for d in lean_declarations)} registered roots; "
        f"{sum(d.get('graph_role') == 'LOCAL_DEPENDENCY' for d in lean_declarations)} local dependencies; "
        f"{sum(d.get('graph_role') == 'EXTERNAL_BOUNDARY' for d in lean_declarations)} external boundaries; "
        f"{len(claim_nodes)} claim mirrors; {len(route_nodes)} route mirrors; "
        f"{len(relations)} relations; terminal claim RH_OPEN)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
