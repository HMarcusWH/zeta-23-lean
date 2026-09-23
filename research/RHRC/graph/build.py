from __future__ import annotations

import argparse
import base64
import hashlib
import importlib.util
import json
import os
import re
import subprocess
from pathlib import Path

from views import coverage_view, reachability_view

GRAPH = Path(__file__).resolve().parent
RHRC = GRAPH.parent
REPO = RHRC.parents[1]
GENERATED = GRAPH / "generated"
REPOSITORY_NAME = "HMarcusWH/zeta-23-lean"
REPOSITORY_ID = "rh:repository:" + REPOSITORY_NAME
FILE_CLASSES_PATH = GRAPH / "FILE_CLASSES.json"

DECLARED_GENERATED_PRODUCTS = [
    "research/RHRC/graph/generated/repository_files.jsonl",
    "research/RHRC/graph/generated/lean_modules.jsonl",
    "research/RHRC/graph/generated/registry_nodes.jsonl",
    "research/RHRC/graph/generated/relations.jsonl",
    "research/RHRC/graph/generated/REPOSITORY_COVERAGE.json",
    "research/RHRC/graph/generated/ENTRYPOINT_REACHABILITY.json",
    "research/RHRC/graph/generated/UNRESOLVED_GRAPH_ITEMS.json",
]

CLAIM_REGISTRY = "research/RHRC/CLAIM_REGISTRY.json"
ROUTE_REGISTRY = "research/RHRC/routes/ROUTE_REGISTRY.json"
BOUNDARY = "research/RHRC/BOUNDARY.json"


def _load_firewall_import_regex():
    path = RHRC / "tools" / "arithmetic_firewall_lint.py"
    spec = importlib.util.spec_from_file_location("rhrc_arithmetic_firewall", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load arithmetic firewall from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.IMPORT


IMPORT_RE = _load_firewall_import_regex()


def _git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()


def tracked_files() -> list[str]:
    raw = subprocess.check_output(["git", "ls-files", "-z"], cwd=REPO)
    tracked = {p.decode("utf-8") for p in raw.split(b"\0") if p}
    # Generated RHKG products belong to physical coverage even during the
    # first bootstrap before they have been added to Git.
    tracked.update(DECLARED_GENERATED_PRODUCTS)
    return sorted(tracked)


def load_classification_contract() -> dict:
    return json.loads(FILE_CLASSES_PATH.read_text(encoding="utf-8"))


def classify(path: str, contract: dict) -> tuple[str, str, str]:
    for rule in contract["rules"]:
        if re.search(rule["pattern"], path):
            return rule["file_class"], rule["trust_zone"], rule["id"]
    return contract["unknown_class"], contract["unknown_trust_zone"], "no_matching_rule"


def file_id(path: str) -> str:
    return "rh:file:" + path


def module_id(module: str) -> str:
    return "rh:module:" + module


def claim_id(claim: str) -> str:
    return "rh:claim:" + claim


def route_id(route: str) -> str:
    return "rh:route:" + route


def module_name(path: str) -> str:
    if path == "Zeta23.lean":
        return "Zeta23"
    if path.startswith("Zeta23/") and path.endswith(".lean"):
        return path[:-5].replace("/", ".")
    if path.startswith("comparator/") and path.endswith(".lean"):
        return path[len("comparator/"):-5].replace("/", ".")
    raise ValueError(f"no Lean module mapping for {path}")


def relation(kind: str, source: str, target: str, provenance: str) -> dict:
    digest = hashlib.sha256(f"{kind}|{source}|{target}".encode("utf-8")).hexdigest()
    return {
        "id": "rh:rel:" + digest,
        "type": "Relation",
        "kind": kind,
        "source": source,
        "target": target,
        "provenance": provenance,
    }


def _jsonl(rows: list[dict]) -> bytes:
    ordered = sorted(rows, key=lambda r: r["id"])
    text = "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"
        for row in ordered
    )
    return text.encode("utf-8")


def _pretty(obj: dict) -> bytes:
    return (json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def _subject_digest(repo_files: list[dict]) -> str:
    h = hashlib.sha256()
    for row in sorted(repo_files, key=lambda r: r["path"]):
        if row["generated_product"]:
            continue
        h.update(row["path"].encode("utf-8"))
        h.update(b"\0")
        h.update((row["git_blob"] or "").encode("ascii"))
        h.update(b"\n")
    return h.hexdigest()


def build_records() -> dict[str, object]:
    contract = load_classification_contract()
    paths = tracked_files()
    generated_set = set(DECLARED_GENERATED_PRODUCTS)

    repo_files: list[dict] = []
    for path in paths:
        cls, trust, rule_id = classify(path, contract)
        generated = path in generated_set
        blob = None if generated else _git("hash-object", path)
        locator = {"repository": REPOSITORY_NAME, "path": path}
        if blob is not None:
            locator["blob_sha"] = blob
        else:
            locator["generated_product"] = True
        repo_files.append(
            {
                "id": file_id(path),
                "type": "RepoFile",
                "path": path,
                "file_class": cls,
                "trust_zone": trust,
                "classification_rule": rule_id,
                "generated_product": generated,
                "git_blob": blob,
                "source_locator": locator,
            }
        )

    by_path = {row["path"]: row for row in repo_files}
    lean_paths = sorted(
        row["path"]
        for row in repo_files
        if row["file_class"] in {"LEAN_SOURCE", "LEAN_ROOT"}
    )
    local_by_module: dict[str, str] = {}
    for path in lean_paths:
        name = module_name(path)
        if name in local_by_module:
            raise RuntimeError(
                f"duplicate local Lean module {name}: {local_by_module[name]} and {path}"
            )
        local_by_module[name] = path

    import_map: dict[str, list[str]] = {}
    external_imports: set[str] = set()
    for name, path in sorted(local_by_module.items()):
        text = (REPO / path).read_text(encoding="utf-8")
        imports = IMPORT_RE.findall(text)
        import_map[name] = imports
        external_imports.update(dep for dep in imports if dep not in local_by_module)

    lean_modules: list[dict] = []
    for name, path in sorted(local_by_module.items()):
        source = by_path[path]
        lean_modules.append(
            {
                "id": module_id(name),
                "type": "LeanModule",
                "module": name,
                "repository_scope": "LOCAL",
                "file_id": source["id"],
                "path": path,
                "trust_zone": source["trust_zone"],
                "source_locator": source["source_locator"],
            }
        )
    for name in sorted(external_imports):
        lean_modules.append(
            {
                "id": module_id(name),
                "type": "LeanModule",
                "module": name,
                "repository_scope": "EXTERNAL",
                "authority_role": "EXPLICIT_EXTERNAL_IMPORT_TARGET",
            }
        )

    claims_data = json.loads((REPO / CLAIM_REGISTRY).read_text(encoding="utf-8"))
    routes_data = json.loads((REPO / ROUTE_REGISTRY).read_text(encoding="utf-8"))
    known_routes = {r["route_id"] for r in routes_data["routes"]}
    known_claims = {c["id"] for c in claims_data["claims"]}

    registry_nodes: list[dict] = [
        {
            "id": REPOSITORY_ID,
            "type": "Repository",
            "repository": REPOSITORY_NAME,
            "authority_role": "CONTAINER_ONLY",
        }
    ]
    for claim in claims_data["claims"]:
        registry_nodes.append(
            {
                "id": claim_id(claim["id"]),
                "type": "RegisteredClaim",
                "claim_id": claim["id"],
                "authority_role": "NORMALIZED_MIRROR",
                "source_authority": CLAIM_REGISTRY,
                "projection": claim,
            }
        )
    for route in routes_data["routes"]:
        registry_nodes.append(
            {
                "id": route_id(route["route_id"]),
                "type": "Route",
                "route_id": route["route_id"],
                "authority_role": "NORMALIZED_MIRROR",
                "source_authority": ROUTE_REGISTRY,
                "projection": route,
            }
        )

    relations_by_key: dict[tuple[str, str, str], dict] = {}

    def add_rel(kind: str, source: str, target: str, provenance: str) -> None:
        relations_by_key[(kind, source, target)] = relation(
            kind, source, target, provenance
        )

    for name, path in sorted(local_by_module.items()):
        add_rel("LOCATED_AT", module_id(name), file_id(path), "GIT_EXACT")
        for dep in import_map[name]:
            add_rel("IMPORTS", module_id(name), module_id(dep), "GIT_EXACT")

    for claim in claims_data["claims"]:
        cid = claim_id(claim["id"])
        add_rel("MIRRORS", cid, file_id(CLAIM_REGISTRY), "REGISTRY_EXACT")
        if claim.get("route") in known_routes:
            add_rel("PART_OF_ROUTE", cid, route_id(claim["route"]), "REGISTRY_EXACT")

    for route in routes_data["routes"]:
        rid = route_id(route["route_id"])
        add_rel("MIRRORS", rid, file_id(ROUTE_REGISTRY), "REGISTRY_EXACT")
        for cid_raw in route.get("claim_ids", []):
            if cid_raw in known_claims:
                add_rel("PART_OF_ROUTE", claim_id(cid_raw), rid, "REGISTRY_EXACT")

    relations = list(relations_by_key.values())

    local_import_graph = {
        name: sorted(dep for dep in deps if dep in local_by_module)
        for name, deps in import_map.items()
    }

    subject_digest = _subject_digest(repo_files)
    coverage = coverage_view(
        repo_files,
        lean_modules,
        registry_nodes,
        relations,
        subject_digest,
        DECLARED_GENERATED_PRODUCTS,
    )
    reachability = reachability_view(local_import_graph)
    unresolved = {
        "schema_version": "RHKG-phase1-unresolved-0.1",
        "semantic_coverage_status": "PARTIAL_BY_DESIGN_PHASE_1",
        "unknown_file_classes": sorted(
            row["path"] for row in repo_files if row["file_class"] == "UNKNOWN_FILE_CLASS"
        ),
        "external_import_targets": sorted(external_imports),
        "standalone_or_auxiliary_modules": reachability["standalone_or_auxiliary"],
        "deferred_to_later_phases": [
            "Lean declaration extraction",
            "declaration-level USES_CONSTANT dependencies",
            "PROVES claim bindings beyond exact registry projection",
            "multi-axis authority/current-state resolution",
            "Git/PR/workflow provenance graph",
            "dead-route/obstruction/revival semantic graph",
            "operational concept preflight",
        ],
        "claim_firewall": "RH_OPEN",
    }

    return {
        "repo_files": repo_files,
        "lean_modules": lean_modules,
        "registry_nodes": registry_nodes,
        "relations": relations,
        "coverage": coverage,
        "reachability": reachability,
        "unresolved": unresolved,
    }


def rendered_outputs() -> dict[str, bytes]:
    records = build_records()
    return {
        "research/RHRC/graph/generated/repository_files.jsonl": _jsonl(records["repo_files"]),
        "research/RHRC/graph/generated/lean_modules.jsonl": _jsonl(records["lean_modules"]),
        "research/RHRC/graph/generated/registry_nodes.jsonl": _jsonl(records["registry_nodes"]),
        "research/RHRC/graph/generated/relations.jsonl": _jsonl(records["relations"]),
        "research/RHRC/graph/generated/REPOSITORY_COVERAGE.json": _pretty(records["coverage"]),
        "research/RHRC/graph/generated/ENTRYPOINT_REACHABILITY.json": _pretty(records["reachability"]),
        "research/RHRC/graph/generated/UNRESOLVED_GRAPH_ITEMS.json": _pretty(records["unresolved"]),
    }


def write_outputs(outputs: dict[str, bytes]) -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    for path, data in outputs.items():
        target = REPO / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)


def check_outputs(outputs: dict[str, bytes]) -> list[str]:
    errors: list[str] = []
    expected_paths = set(DECLARED_GENERATED_PRODUCTS)
    actual_paths = (
        {
            str(p.relative_to(REPO)).replace("\\", "/")
            for p in GENERATED.rglob("*")
            if p.is_file()
        }
        if GENERATED.exists()
        else set()
    )
    if actual_paths != expected_paths:
        errors.append(
            "generated product set drift: "
            f"missing={sorted(expected_paths - actual_paths)} "
            f"extra={sorted(actual_paths - expected_paths)}"
        )
    for path, expected in outputs.items():
        target = REPO / path
        if not target.exists():
            errors.append(f"missing generated output: {path}")
            continue
        if target.read_bytes() != expected:
            errors.append(f"stale generated output: {path}")
    return errors


def emit_bootstrap_payload(outputs: dict[str, bytes]) -> None:
    """Emit repairable base64 chunks only when CI detects stale/missing products."""
    for path in sorted(outputs):
        encoded = base64.b64encode(outputs[path]).decode("ascii")
        for index in range(0, len(encoded), 3000):
            chunk = encoded[index:index + 3000]
            print(f"RHKG_BOOTSTRAP|{path}|{index // 3000:06d}|{chunk}", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build/check RHKG Phase-1 generated products")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true", help="regenerate checked-in products")
    group.add_argument("--check", action="store_true", help="verify checked-in products are byte-current")
    args = parser.parse_args()

    outputs = rendered_outputs()
    if args.write:
        pre_errors = check_outputs(outputs)
        write_outputs(outputs)
        if pre_errors and os.environ.get("RHKG_BOOTSTRAP_LOG") == "1":
            emit_bootstrap_payload(outputs)
        print(f"RHKG BUILD: WROTE {len(outputs)} deterministic products")
        return 0

    errors = check_outputs(outputs)
    if errors:
        print("RHKG BUILD CHECK: FAIL")
        for error in errors:
            print(" -", error)
        return 1
    print(f"RHKG BUILD CHECK: PASS ({len(outputs)} products byte-current)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
