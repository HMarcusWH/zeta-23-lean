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
            errors.append(f"relation not yet authorized in Phase 2A: {rel['kind']}")
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
            if rel.get("provenance") != "REGISTRY_EXACT":
                errors.append(f"Phase-2A DECLARES provenance is not REGISTRY_EXACT: {rel}")
        if rel.get("kind") == "PROVES":
            if rel["source"] not in declaration_ids:
                errors.append(f"PROVES source is not a LeanDeclaration: {rel}")
            if rel["target"] not in claim_node_ids:
                errors.append(f"PROVES target is not a RegisteredClaim: {rel}")
            if rel.get("provenance") != "REGISTRY_EXACT":
                errors.append(f"Phase-2A PROVES provenance is not REGISTRY_EXACT: {rel}")


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


    promoted = json.loads(
        (REPO / graph_build.PROMOTED_BINDINGS).read_text(encoding="utf-8")
    )
    claim_by_id = {claim["id"]: claim for claim in claim_source["claims"]}
    declaration_by_name = {d["declaration"]: d for d in lean_declarations}
    expected_declarations: dict[str, dict] = {}
    expected_declares: set[tuple[str, str]] = set()
    expected_proves: set[tuple[str, str]] = set()

    for binding in promoted["bindings"]:
        claim = claim_by_id.get(binding["id"])
        if claim is None:
            errors.append(f"promoted binding references unknown claim: {binding['id']}")
            continue
        if claim.get("route") != "R003_ccm_bridge":
            errors.append(f"promoted binding is outside R003_ccm_bridge: {binding['id']}")
        if claim.get("status") != "PROVED_UNCONDITIONAL":
            errors.append(f"promoted binding is not PROVED_UNCONDITIONAL: {binding['id']}")
        if claim.get("theorem") != binding["theorem"]:
            errors.append(
                f"promoted binding theorem mismatch for {binding['id']}: "
                f"{binding['theorem']!r} != {claim.get('theorem')!r}"
            )
            continue

        source_path = claim.get("source")
        module = local_module_by_path.get(source_path)
        if module is None:
            errors.append(
                f"promoted binding source is not an indexed local Lean module: "
                f"{binding['id']} -> {source_path!r}"
            )
            continue

        decl_id = graph_build.declaration_id(binding["theorem"])
        expected = {
            "id": decl_id,
            "type": "LeanDeclaration",
            "declaration": binding["theorem"],
            "module": module["module"],
            "module_id": module["id"],
            "source_path": source_path,
            "source_file_id": module["file_id"],
            "binding_scope": "R003_PROMOTED",
            "authority_role": "PROMOTED_CLAIM_DECLARATION",
            "binding_source": graph_build.PROMOTED_BINDINGS,
            "compiler_binding_source": graph_build.CLAIM_BINDINGS_LEAN,
            "source_locator": module["source_locator"],
        }
        expected_declarations[binding["theorem"]] = expected
        expected_declares.add((module["id"], decl_id))
        expected_proves.add((decl_id, graph_build.claim_id(binding["id"])))

    if set(declaration_by_name) != set(expected_declarations):
        errors.append(
            "promoted Lean declaration population mismatch: "
            f"missing={sorted(set(expected_declarations) - set(declaration_by_name))} "
            f"extra={sorted(set(declaration_by_name) - set(expected_declarations))}"
        )
    for theorem, expected in expected_declarations.items():
        if declaration_by_name.get(theorem) != expected:
            errors.append(f"LeanDeclaration record drift for {theorem}")

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

    theorem_claim_map = json.loads(
        (GENERATED / "THEOREM_CLAIM_MAP.json").read_text(encoding="utf-8")
    )
    if theorem_claim_map.get("scope") != "R003_PROMOTED_BINDINGS_ONLY":
        errors.append("THEOREM_CLAIM_MAP scope drift")
    if theorem_claim_map.get("promoted_binding_count") != len(promoted["bindings"]):
        errors.append("THEOREM_CLAIM_MAP promoted-binding count drift")
    if theorem_claim_map.get("terminal_claim") != "RH_OPEN":
        errors.append("THEOREM_CLAIM_MAP does not preserve RH_OPEN")
    if theorem_claim_map.get("graph_theorem_promotion") is not False:
        errors.append("THEOREM_CLAIM_MAP permits graph theorem promotion")

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
        f"{len(lean_declarations)} promoted Lean declarations; "
        f"{len(claim_nodes)} claim mirrors; {len(route_nodes)} route mirrors; "
        f"{len(relations)} relations; terminal claim RH_OPEN)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
