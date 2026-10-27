"""Fail-closed Round 2 plan/source preflight and explicit acceptance boundary.

A preflight PASS proves no mathematics and grants no release or human approval.
The original compiler parser and current-tree ancestry gate remain separate.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable, Mapping
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
from typing import Any

try:
    from .certificate_io import (InvalidCertificate, canonical_sha256, failure_envelope,
        load_strict_json, require, validate_schema, validate_schema_definition)
    from .controls import check_control_bindings
except ImportError:
    from certificate_io import (InvalidCertificate, canonical_sha256, failure_envelope,
        load_strict_json, require, validate_schema, validate_schema_definition)
    from controls import check_control_bindings

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
FROZEN_COMMIT = "416aec21d4d6634675639b5397cc300d1f826e34"
FROZEN_TREE = "0506bca8ffe613e9cd9ab844650a1141d4494f66"
MERGED_BASE = "adab10a37207f75b9a8b415a0fe9eadca2e4c9aa"
MANDATORY = {f"OPICA2_P{k:02d}" for k in range(1, 24)} | {f"OPICA2_S{k:02d}" for k in range(1, 18)}
OPTIONAL = {"OPICA2_P24", "OPICA2_P25", "OPICA2_O_C2", "OPICA2_O_C3", "OPICA2_O_C4", "OPICA2_X01"}
SHA = re.compile(r"[0-9a-f]{64}\Z")
IMMUTABLE_INPUT_HASHES = {
    "paper/ROUND2_ORIGINAL_25.json": "2374df94db84eaeb2d97bd8b402ac86b267958cb159724445c1b8ced88da3c15",
    "paper/ROUND2_V2_1.json": "18d17ee9cc18c94e13293051f0744a5aacafc65110e99ea56f82cf13aef61a6c",
    "paper/ROUND2_RESEARCH.md": "84d39bdbb6bc9a56a6f6d6ef15958ff21e5e1dd03234dd498e5e50e2d3464e9c",
    "paper/DEEP_SEARCH.md": "84d05886eb1a7708732aa90262d5ccba3aa9c94fcf23ac9f8a4fcda4494f921b",
    "paper/ROUND2_POSTGREEN_V2_1.md": "8714a068beb490ae4f35f853e6723fc88d670d248f145ece84b83e3694dcd444",
}

# Explicit versioned child boundary. These pins are finalized after reviewed
# authored-source freeze; the original Round2 path policy/locks remain intact.
ROUND3_PROVIDER_SHA256 = "cf7091e77c22ccce43dcf685456de4ca98da0aba079000cc71ffbe140c8c4ec4"
ROUND3_PATH_POLICY_SHA256 = "1efef90366541653a42df027045ba317e52a664cdfcce7a305d6b5c5638538ad"


def round3_extension_context(repo: Path) -> dict[str, Any] | None:
    child = repo / "research/RHRC/integration/opica_round3"
    marker = child / "DESCENDANT_EXTENSION.json"
    if not marker.exists():
        return None
    provider = child / "validate_contract.py"
    require(SHA.fullmatch(ROUND3_PROVIDER_SHA256) is not None
            and SHA.fullmatch(ROUND3_PATH_POLICY_SHA256) is not None,
            "round3_unreviewed", "Round3 extension has not received its explicit source freeze")
    require(provider.is_file() and not provider.is_symlink()
            and digest(provider) == ROUND3_PROVIDER_SHA256,
            "round3_provider", "Round3 source-scope provider differs from the reviewed pin")
    spec = importlib.util.spec_from_file_location("_opica3_reviewed_extension", provider)
    require(spec is not None and spec.loader is not None, "round3_import", "Missing child provider")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    require(module.policy_digest(module.path_policy(repo)) == ROUND3_PATH_POLICY_SHA256,
            "round3_policy", "Round3 extension cannot enlarge its reviewed path authority")
    result = module.inspect_descendant(repo)
    require(result.get("status") == "PASS_SOURCE_SCOPE_ONLY"
            and result.get("path_policy_sha256") == ROUND3_PATH_POLICY_SHA256
            and result.get("full_release_accepted") is False,
            "round3_inspection", "Round3 source inspection failed")
    return result


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def actual_blob_identity(path: Path) -> tuple[int, str, str]:
    """Bind checked-out bytes to the independently obtained frozen Git object."""
    length = path.stat().st_size
    blob = hashlib.sha1(b"blob " + str(length).encode("ascii") + b"\0")
    sha256 = hashlib.sha256()
    read = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            read += len(block)
            blob.update(block)
            sha256.update(block)
    require(read == length, "source_read_race", "Source changed while its identity was inspected")
    return length, blob.hexdigest(), sha256.hexdigest()


def git(repo: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(repo), *args], check=False, capture_output=True,
                            encoding="utf-8", errors="strict", timeout=90)
    require(result.returncode == 0, "git_command", "Git inspection failed: " + " ".join(args))
    return result.stdout.strip()


def safe_relative(value: Any) -> str:
    require(type(value) is str and bool(value) and "\\" not in value and ":" not in value,
            "unsafe_path", "Canonical repository-relative POSIX path required")
    p = PurePosixPath(value)
    require(not p.is_absolute() and ".." not in p.parts and "." not in value.split("/")
            and p.as_posix() == value, "unsafe_path", "Unsafe or noncanonical relative path")
    return value


def file_at(root: Path, relative: str) -> Path:
    relative = safe_relative(relative)
    path = root / relative
    require(path.resolve().is_relative_to(root.resolve()), "path_escape", "Path escapes its root")
    require(not path.is_symlink(), "symlink_input", "Symlink source inputs are not accepted")
    return path


def validate_package_inventory(root: Path, manifest: Mapping[str, Any], *,
                               root_manifest: str = "PACKAGE_MANIFEST.json") -> None:
    """A15: root-only self exclusion; nested manifests remain ordinary files."""
    rows = manifest.get("files")
    require(type(rows) is list and bool(rows), "package_inventory", "Complete package inventory required")
    indexed: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        require(type(row) is dict, "package_record", "Malformed package inventory record")
        rel = safe_relative(row.get("path"))
        require(rel != root_manifest and rel not in indexed, "package_duplicate", "Self/duplicate package record")
        require(type(row.get("sha256")) is str and SHA.fullmatch(row["sha256"]) is not None,
                "package_hash", "Package digest is not canonical")
        path = file_at(root, rel)
        require(path.is_file(), "package_missing", "Missing package file: " + rel)
        length = row.get("bytes", row.get("size"))
        require(type(length) is int and length >= 0 and path.stat().st_size == length,
                "package_size", "Wrong package file size: " + rel)
        require(digest(path) == row["sha256"], "package_hash", "Changed package file: " + rel)
        indexed[rel] = row
    found = set()
    for path in root.rglob("*"):
        require(not path.is_symlink(), "package_symlink", "Package symlink is not allowed")
        if path.is_file():
            rel = path.relative_to(root).as_posix()
            if rel != root_manifest:
                found.add(rel)
    require(found == set(indexed), "package_census", "Missing or unlisted package paths")


def check_merged_base(repo: Path, lock: Mapping[str, Any]) -> dict[str, Any]:
    frozen, base = lock.get("frozen_ancestor"), lock.get("build_base")
    require(type(frozen) is dict and type(base) is dict, "ancestor_lock", "Both frozen and merged-base records required")
    require(frozen.get("commit") == FROZEN_COMMIT and frozen.get("tree") == FROZEN_TREE,
            "frozen_lock", "Original source identity changed")
    require(base.get("commit") == MERGED_BASE and base.get("tree") == FROZEN_TREE
            and base.get("merged") is True, "merged_lock", "Observed PR294 merged-base identity is required")
    require(git(repo, "rev-parse", MERGED_BASE + "^{tree}") == FROZEN_TREE,
            "merge_tree", "Merged Git tree differs from the audited source tree")
    parents = git(repo, "show", "-s", "--format=%P", MERGED_BASE).split()
    require(len(parents) == 2 and FROZEN_COMMIT in parents, "merge_parent", "Actual PR294 merge parents do not match")
    git(repo, "merge-base", "--is-ancestor", MERGED_BASE, "HEAD")
    return {"frozen_commit": FROZEN_COMMIT, "build_base": MERGED_BASE,
            "checked_head": git(repo, "rev-parse", "HEAD"),
            "checked_tree": git(repo, "rev-parse", "HEAD^{tree}")}


def check_dag(dag: Mapping[str, Any]) -> dict[str, Any]:
    rows = dag.get("modules")
    require(type(rows) is list and len(rows) == 21, "module_inventory", "Exactly 21 planned math modules required")
    modules = {r["module"]: r for r in rows}
    require(len(modules) == len(rows), "module_duplicate", "Duplicate module")
    required = {m for m, r in modules.items() if r.get("required_for_full_core") is True}
    require(len(required) == 16, "required_modules", "Required module scope changed")
    membership: dict[str, str] = {}
    for name, row in modules.items():
        require(row["path"] == name.replace(".", "/") + ".lean", "module_path", "Module/path mismatch")
        for cid in row["contract_ids"]:
            require(cid not in membership, "family_duplicate", "Family assigned more than once")
            membership[cid] = name
        deps = row["direct_round2_imports"]
        require(type(deps) is list and len(set(deps)) == len(deps)
                and set(deps) <= set(modules), "module_dependency", "Missing or duplicate dependency")
        require(name not in required or set(deps) <= required, "optional_import", "Core imports optional mathematics")
        require(not any(".Validation" in dep or dep.startswith("Zeta23.RHRC.")
                        for dep in deps + row.get("upstream_project_imports", [])),
                "audit_import", "Mathematical module imports an audit/exporter")
    require(set(membership) == MANDATORY | OPTIONAL
            and {cid for cid, m in membership.items() if m in required} == MANDATORY,
            "family_scope", "Original 40 required / six optional family scope changed")
    visited, active = set(), set()

    def visit(name):
        require(name not in active, "module_cycle", "Cycle in planned module DAG")
        if name in visited:
            return
        active.add(name)
        for dep in modules[name]["direct_round2_imports"]:
            visit(dep)
        active.remove(name)
        visited.add(name)

    for name in modules:
        visit(name)

    def closure(seeds):
        found = set()
        todo = list(seeds)
        while todo:
            name = todo.pop()
            require(name in modules, "umbrella_import", "Unknown umbrella module")
            if name not in found:
                found.add(name)
                todo.extend(modules[name]["direct_round2_imports"])
        return found

    umbrellas = {r["kind"]: r for r in dag["umbrellas"]}
    expected_minimal = {"Zeta23.OPICARound2." + s for s in (
        "CausalProbe", "ClassicalAdapter", "FixedFilter", "FilteredClassicalComparison", "FiniteFilteredBaseline")}
    require(closure(umbrellas["MATHEMATICAL_MINIMAL"]["imports"]) == expected_minimal,
            "minimal_scope", "Minimal facade gained general Gram or optional dependencies")
    require(closure(umbrellas["MATHEMATICAL_FULL_CORE"]["imports"]) == required,
            "full_core_scope", "Full facade omits required or imports optional modules")
    return {"modules": modules, "family_modules": membership, "required_modules": required}


def _strip_comments_and_strings(text: str) -> str:
    out = []
    i = 0
    nesting = 0
    while i < len(text):
        if nesting:
            if text.startswith("/-", i):
                nesting += 1; i += 2
            elif text.startswith("-/", i):
                nesting -= 1; i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("/-", i):
            nesting = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(" ")
            i += 1
            closed = False
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1; closed = True; break
                else:
                    out.append("\n" if text[i] == "\n" else " "); i += 1
            require(closed, "unterminated_string", "Unterminated Lean string")
        else:
            out.append(text[i]); i += 1
    require(nesting == 0, "unterminated_comment", "Unterminated Lean comment")
    return "".join(out)


def imports(text: str) -> list[str]:
    clean = _strip_comments_and_strings(text)
    return [name for line in re.findall(r"^\s*import\s+([^\n]+)", clean, flags=re.M)
            for name in line.split()]


def check_math_sources(repo: Path, dag_result: Mapping[str, Any]) -> None:
    for name, row in dag_result["modules"].items():
        path = file_at(repo, row["path"])
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        clean = _strip_comments_and_strings(text)
        require(not re.search(r"\b(?:sorry|admit|axiom|native_decide|ofReduceBool|unsafe|extern|implemented_by)\b", clean)
                and "debug.skipKernelTC" not in clean, "proof_escape", "Forbidden proof escape in " + row["path"])
        actual = imports(text)
        expected_project = set(row["direct_round2_imports"] + row.get("upstream_project_imports", []))
        require(not any(".Validation" in imp or imp.startswith("Zeta23.RHRC.") for imp in actual),
                "audit_import", "Actual mathematical import crosses audit boundary: " + name)
        require({imp for imp in actual if imp.startswith("Zeta23.")} == expected_project,
                "import_drift", "Actual direct project imports differ from the reviewed DAG: " + name)


def check_facade_sources(repo: Path, dag: Mapping[str, Any], public: Mapping[str, Any]) -> None:
    """Required facades import exactly their reviewed scope and add no declarations."""
    for row in dag["umbrellas"]:
        path=file_at(repo,row["path"])
        if not path.exists() and row.get("required") is False:
            continue
        require(path.is_file(),"facade_source","Required facade source absent: "+row["path"])
        text=path.read_text(encoding="utf-8")
        lines=[line.strip() for line in _strip_comments_and_strings(text).splitlines() if line.strip()]
        require(all(re.fullmatch(r"import [A-Za-z_][A-Za-z0-9_.]*(?:[ \t]+[A-Za-z_][A-Za-z0-9_.]*)*",line) for line in lines),
                "facade_declaration","Import facade gained a declaration or executable command: "+row["path"])
        actual=imports(text)
        require(len(actual)==len(set(actual)) and set(actual)==set(row["imports"]),
                "facade_import_drift","Actual facade imports differ from its reviewed scope: "+row["path"])
    binding=file_at(repo,"Zeta23/RHRC/OpicaRound2Bindings.lean")
    require(binding.is_file(),"binding_facade","Required compiler binding facade absent")
    lines=[line.strip() for line in _strip_comments_and_strings(binding.read_text(encoding="utf-8")).splitlines() if line.strip()]
    required={row["proposed_public_name"] for row in public["roots"] if row["required_for_full_core"]}
    imports_seen=[];checks=[];axioms=[]
    for line in lines:
        match=re.fullmatch(r"import ([A-Za-z_][A-Za-z0-9_.]*)",line)
        if match:imports_seen.append(match.group(1));continue
        match=re.fullmatch(r"#check ([A-Za-z_][A-Za-z0-9_.]*)",line)
        if match:checks.append(match.group(1));continue
        match=re.fullmatch(r"#print axioms ([A-Za-z_][A-Za-z0-9_.]*)",line)
        require(match is not None,"binding_command","Compiler binding facade gained an unreviewed command/declaration")
        axioms.append(match.group(1))
    require(imports_seen==["Zeta23.OPICARound2.Validation"]
            and len(checks)==len(set(checks))==len(required) and set(checks)==required
            and len(axioms)==len(set(axioms))==len(required) and set(axioms)==required,
            "binding_inventory","Compiler binding facade must check every required root and exactly its axiom surface")


def check_original_rows(current: Any, frozen: Any, array_name: str) -> None:
    require(type(current) is dict and type(frozen) is dict
            and type(current.get(array_name)) is list and type(frozen.get(array_name)) is list,
            "registry_shape", "Malformed claim/binding array")
    rows = current[array_name]
    ids = [r.get("id") for r in rows]
    require(len(set(ids)) == len(ids), "registry_duplicate", "Duplicate registry ID")
    current_by_id = {r["id"]: r for r in rows}
    for row in frozen[array_name]:
        require(current_by_id.get(row["id"]) == row, "ancestor_registry", "Original registry object changed: " + row["id"])


def check_source_lock(repo: Path, lock: Mapping[str, Any], manifest: Mapping[str, Any]) -> None:
    require(lock.get("commit") == FROZEN_COMMIT and lock.get("tree") == FROZEN_TREE,
            "source_lock", "Unexpected frozen source lock")
    rows = lock.get("files", lock.get("source_manifest"))
    require(type(rows) is list and len(rows) == 4780, "source_census", "Full original 4,780-source inventory required")
    paths = [safe_relative(r.get("path")) for r in rows]
    require(len(set(paths)) == len(paths), "source_duplicate", "Duplicate frozen source path")
    baseline_index = {}
    for line in git(repo, "ls-tree", "-r", FROZEN_COMMIT).splitlines():
        info, path = line.split("\t", 1)
        mode, kind, blob = info.split()
        require(kind == "blob", "source_kind", "Unexpected non-file baseline input")
        baseline_index[path] = (mode, blob)
    require(set(baseline_index) == set(paths), "source_census", "Frozen path set is not the actual Git tree")
    allowed_edits = {safe_relative(r["path"]) for key in ("edit", "generated") for r in manifest[key]}
    for row in rows:
        rel = row["path"]
        require(baseline_index[rel] == (row["mode"], row["git_blob"]), "source_object", "Wrong baseline mode/blob: " + rel)
        if rel not in allowed_edits:
            path = file_at(repo, rel)
            require(path.is_file(), "protected_source", "Protected ancestor source is missing: " + rel)
            length, blob, sha256 = actual_blob_identity(path)
            require(length == row["bytes"] and blob == baseline_index[rel][1] and sha256 == row["sha256"],
                    "protected_source", "Protected ancestor source changed or missing: " + rel)
    for manifest_path, key in (("research/RHRC/CLAIM_REGISTRY.json", "claims"),
                               ("research/RHRC/REGISTERED_THEOREM_BINDINGS.json", "bindings")):
        current = load_strict_json(repo / manifest_path)
        baseline = json.loads(git(repo, "show", FROZEN_COMMIT + ":" + manifest_path))
        check_original_rows(current, baseline, key)
        if key == "bindings":
            require(current.get("candidate_bindings", []) == baseline.get("candidate_bindings", []),
                    "candidate_drift", "Original candidate bindings changed")


def check_registered_inputs(here: Path, register: Mapping[str, Any], *, authored_paths: set[str] | None = None,
                            expected_inventory: Mapping[str, str] | None = None) -> None:
    candidates = [register[k] for k in ("files", "inputs", "input_files") if k in register]
    require(len(candidates) == 1 and type(candidates[0]) is list and bool(candidates[0]),
            "input_register", "One explicit immutable input inventory is required")
    if expected_inventory is not None:
        require({r.get("path"): r.get("sha256") for r in candidates[0]} == dict(expected_inventory),
                "approved_input_inventory", "Candidate cannot rewrite the approved immutable input inventory")
    seen = set()
    for row in candidates[0]:
        rel = safe_relative(row.get("path"))
        require(rel not in seen, "input_duplicate", "Duplicate registered input")
        seen.add(rel)
        path = file_at(here, rel)
        require(path.is_file() and type(row.get("sha256")) is str and SHA.fullmatch(row["sha256"]) is not None
                and digest(path) == row["sha256"], "input_hash", "Immutable input missing or changed: " + rel)
        if "bytes" in row:
            require(type(row["bytes"]) is int and path.stat().st_size == row["bytes"], "input_size", "Input size changed")
    input_root = here / "paper"
    require(input_root.is_dir(), "missing_inputs", "Original immutable paper inputs directory is absent")
    found = {p.relative_to(here).as_posix() for p in input_root.rglob("*") if p.is_file()}
    require(found <= seen | (authored_paths or set()), "input_census", "Unregistered immutable input file")


def check_root100(here: Path, repo: Path) -> None:
    original_path = "research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json"
    frozen = json.loads(git(repo, "show", FROZEN_COMMIT + ":" + original_path))
    actual = load_strict_json(repo / "research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json", 8*1024*1024)
    require(frozen == actual, "original100_contracts", "Original 100 frozen contracts differ from actual source")
    rows = actual["roots"]
    require(type(rows) is list and len(rows) == 100
            and len({r["id"] for r in rows}) == 100
            and len({r["full_name"] for r in rows}) == 100,
            "root100_population", "Original 100 root identity set changed")
    for row in rows:
        path = file_at(repo, row["path"])
        source = path.read_text(encoding="utf-8")
        short = row["full_name"].split(".")[-1]
        require(re.search(r"\b(?:theorem|lemma|def|abbrev)\s+" + re.escape(short) + r"\b", source) is not None,
                "root100_source", "Original required declaration is absent")


def check_upstream_symbols(repo: Path, register: Mapping[str, Any], dag_result: Mapping[str, Any]) -> None:
    rows = register.get("upstream_symbols")
    require(type(rows) is list and bool(rows), "upstream_inventory", "Actual upstream symbol inventory required")
    seen = set()
    for row in rows:
        key = (row["consumer_module"], row["module"], row["symbol"])
        require(key not in seen, "upstream_duplicate", "Duplicate upstream symbol record")
        seen.add(key)
        path = file_at(repo, row["path"])
        require(row["path"] == row["module"].replace(".", "/") + ".lean"
                and path.is_file() and digest(path) == row["sha256"],
                "upstream_source", "Upstream module/source hash changed")
        text = _strip_comments_and_strings(path.read_text(encoding="utf-8"))
        require(re.search(r"\b(?:theorem|lemma|def|abbrev)\s+" + re.escape(row["symbol"]) + r"\b", text) is not None,
                "upstream_symbol", "Required upstream declaration is absent")
        consumer = dag_result["modules"].get(row["consumer_module"])
        require(consumer is not None, "upstream_consumer", "Unknown upstream consumer")
        reachable, pending = set(), list(consumer.get("direct_round2_imports", [])) + list(consumer.get("upstream_project_imports", []))
        while pending:
            name = pending.pop()
            if name in reachable:
                continue
            reachable.add(name)
            source = repo / (name.replace(".", "/") + ".lean")
            if source.is_file():
                pending.extend(imp for imp in imports(source.read_text(encoding="utf-8"))
                               if imp.startswith("Zeta23."))
        require(row["module"] in reachable, "upstream_reachability", "Upstream symbol not reachable from declared imports")


def control_mapping(here: Path, crosswalk: Mapping[str, Any]) -> dict[str, Any]:
    registry = load_strict_json(here / "CONTROL_REGISTRY.json", 16*1024*1024)
    controls = []
    for key in ("inherited_controls", "runtime_mutations", "typed_semantic_guards"):
        require(type(registry.get(key)) is list, "control_registry", "Missing control population: " + key)
        controls.extend(registry[key])
    return {**crosswalk, "controls": controls}


def check_family_contracts(here: Path, public: Mapping[str, Any], crosswalk: Mapping[str, Any],
                          dag_result: Mapping[str, Any]) -> None:
    original = load_strict_json(here / "paper/ROUND2_ORIGINAL_25.json", 8*1024*1024)
    normative = load_strict_json(here / "paper/ROUND2_V2_1.json", 8*1024*1024)
    require(original["contracts"] == normative["contracts"] and len(original["contracts"]) == 25,
            "original25", "Original 25 contracts were rewritten")
    buckets = ("contracts", "supporting_amendments", "optional_extensions", "optional_external_transfer_lanes")
    records = [row for bucket in buckets for row in normative[bucket]]
    pointers = {row["id"]: bucket + "/" + row["id"] for bucket in buckets for row in normative[bucket]}
    source = {row["id"]: row for row in records}
    require(len(source) == len(records) == 46 and set(source) == MANDATORY | OPTIONAL,
            "normative_population", "Normative contract family set changed")
    rows = public.get("roots")
    require(type(rows) is list and len(rows) == 45
            and {row["id"] for row in rows} == set(source) - {"OPICA2_X01"},
            "public_population", "All original 45 public contract records must remain")
    require(public.get("external_optional") == normative["optional_external_transfer_lanes"],
            "external_scope", "The disabled external lane was silently changed")
    for row in rows:
        cid = row["id"]
        require(row.get("input_contract_sha256") == canonical_sha256(source[cid])
                and row.get("proposed_public_name") == source[cid].get("proposed_lean_name")
                and row.get("module") == dag_result["family_modules"][cid]
                and row.get("input_pointer") == pointers[cid]
                and row.get("dependencies") == source[cid].get("dependencies")
                and row.get("required_for_full_core") is (cid in MANDATORY)
                and row.get("all_clauses_required") is True,
                "public_contract", "Public contract binding changed: " + cid)
    families = crosswalk.get("family_bindings")
    require(type(families) is list and len(families) == 46
            and {f["family_id"] for f in families} == set(source),
            "crosswalk_population", "Family crosswalk population changed")
    for family in families:
        cid = family["family_id"]
        require(family.get("input_record_sha256") == canonical_sha256(source[cid])
                and family.get("module") == dag_result["family_modules"][cid],
                "crosswalk_contract", "Crosswalk no longer binds its exact normative record: " + cid)


def preflight(repo: Path = REPO, here: Path = HERE, *, scope: str = "full-core") -> dict[str, Any]:
    repo, here = repo.resolve(), here.resolve()
    require(scope in {"minimal", "full-core"}, "scope", "Unknown scope")
    checks = []
    missing = []
    def run(name, action):
        action()
        checks.append({"check": name, "pass": True})
    try:
        child = round3_extension_context(repo)
        if child is not None:
            return {"schema": "OPICA3_ROUND2_PARENT_STATIC_COMPATIBILITY_V1",
                    "status": "PASS_PARENT_SOURCE_SCOPE_ONLY", "scope": scope,
                    "round3_source_inspection": child,
                    "authority": "REVIEWED_CHILD_SOURCE_SCOPE_ONLY_NO_ROUND2_COMPILER_ACCEPTANCE",
                    "full_core_accepted": False, "full_release_accepted": False,
                    "human_review": "NOT_ESTABLISHED", "RH": "OPEN", "Step4": "OPEN"}
        manifest = load_strict_json(here / "BUILD_MANIFEST.json", 8*1024*1024)
        ancestor = load_strict_json(here / "ANCESTOR_LOCK.json", 16*1024*1024)
        register = load_strict_json(here / "SOURCE_REGISTER.json", 16*1024*1024)
        dag = register.get("module_dag")
        require(type(dag) is dict, "module_dag", "Reviewed inline module DAG is required")
        source_lock = ancestor["frozen_ancestor"]
        run("observed merged base and Git ancestry", lambda: check_merged_base(repo, ancestor))
        for key in ("create", "edit", "generated"):
            require(type(manifest.get(key)) is list, "manifest_shape", "Missing explicit delta path list")
        all_paths = [safe_relative(row["path"]) for key in ("create", "edit", "generated") for row in manifest[key]]
        require(len(all_paths) == len(set(all_paths)) and not manifest.get("deletions") and not manifest.get("renames"),
                "manifest_delta", "Duplicate, deletion or rename in allowed delta")
        allowed = set(all_paths)
        for line in git(repo, "diff", "--name-status", "--no-renames", MERGED_BASE, "--").splitlines():
            status, path = line.split("\t", 1)
            require(status in {"A", "M"} and path in allowed, "unauthorized_delta", "Unlisted/deleted source change: " + path)
        for path in git(repo, "ls-files", "--others", "--exclude-standard").splitlines():
            # Output artifacts are not silently admitted as source providers.
            if path.startswith(".opica2-artifacts/") or path.startswith(".opica2-inputs/"):
                require(Path(path).suffix not in {".lean", ".py"}, "untracked_provider", "Unlisted executable output provider")
            else:
                require(path in allowed, "untracked_input", "Unlisted untracked build input: " + path)
        run("frozen ancestor source and claim objects", lambda: check_source_lock(repo, source_lock, manifest))
        relative_here = here.relative_to(repo).as_posix() + "/"
        authored_paper = {row["path"][len(relative_here):] for row in manifest["create"]
                          if row["path"].startswith(relative_here + "paper/")}
        run("registered immutable inputs", lambda: check_registered_inputs(here, register, authored_paths=authored_paper,
                                                                           expected_inventory=IMMUTABLE_INPUT_HASHES))
        run("original 100 source/contract summaries", lambda: check_root100(here, repo))
        dag_result = check_dag(dag)
        checks.append({"check": "exact DAG and minimal/full/optional closures", "pass": True})
        run("actual upstream symbol identities and transitive imports", lambda: check_upstream_symbols(repo, register, dag_result))
        run("actual mathematical imports and proof-escape scan", lambda: check_math_sources(repo, dag_result))
        crosswalk = load_strict_json(here / "PAPER_CROSSWALK.json", 16*1024*1024)
        public = load_strict_json(here / "PUBLIC_ROOTS.json", 8*1024*1024)
        run("literal minimal/full/audit facade source scopes", lambda: check_facade_sources(repo, dag, public))
        run("original25 and exact45-plus-external public contract bindings",
            lambda: check_family_contracts(here, public, crosswalk, dag_result))
        run("46-family / 143-clause control binding plan", lambda: check_control_bindings(control_mapping(here, crosswalk)))
        for name in ("certificate.schema.json", "receipt.schema.json", "workflow_harvest.schema.json", "failure.schema.json"):
            run("closed supported schema " + name,
                lambda name=name: validate_schema_definition(load_strict_json(here/"schemas"/name)))
        selected = {r["path"] for r in manifest["create"] if r.get("required") is True}
        if scope == "minimal":
            minimal = {"Zeta23.OPICARound2." + x for x in (
                "CausalProbe", "ClassicalAdapter", "FixedFilter", "FilteredClassicalComparison", "FiniteFilteredBaseline")}
            math_paths = {r["path"] for r in dag["modules"]}
            consumer_paths = {r["independent_consumer"] for r in dag["modules"]}
            excluded = {r["path"] for r in dag["modules"] if r["module"] not in minimal}
            excluded |= {r["independent_consumer"] for r in dag["modules"] if r["module"] not in minimal}
            selected -= excluded
            selected.discard("Zeta23/OPICARound2/All.lean")
            selected.discard("Zeta23/OPICARound2/Validation.lean")
            selected.discard("Zeta23/RHRC/OpicaRound2Bindings.lean")
        missing = sorted(path for path in selected if not file_at(repo, path).is_file())
        require(not missing, "missing_implementation_files", "Required implementation files are absent")
        return {"schema": "OPICA2_PREFLIGHT_V1", "status": "PASS_PREFLIGHT_ONLY", "scope": scope,
                "checks": checks, "missing_files": [], "errors": [],
                "authority": "STATIC_SOURCE_PLAN_AND_INVENTORY_ONLY", "full_core_accepted": False,
                "full_release_accepted": False, "human_review": "NOT_ESTABLISHED", "RH": "OPEN", "Step4": "OPEN"}
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as exc:
        return {"schema": "OPICA2_PREFLIGHT_V1", "status": "FAIL_PREFLIGHT", "scope": scope,
                "checks": checks, "missing_files": missing, "errors": [
                    {"code": getattr(exc, "code", "preflight_error"), "message": str(exc)}],
                "authority": "NO_ACCEPTANCE", "full_core_accepted": False,
                "full_release_accepted": False, "human_review": "NOT_ESTABLISHED", "RH": "OPEN", "Step4": "OPEN"}


def acceptance(repo: Path = REPO, here: Path = HERE, *, formal_receipt: Path,
               receipt_verifier: Callable[[Mapping[str, Any], Path], bool] | None = None) -> dict[str, Any]:
    report = preflight(repo, here)
    require(report["status"] == "PASS_PREFLIGHT_ONLY", "preflight_failed", "Acceptance needs a complete source preflight")
    receipt = load_strict_json(formal_receipt, 32*1024*1024)
    validate_schema(receipt, load_strict_json(here/"schemas"/"receipt.schema.json"))
    require(receipt_verifier is not None, "compiler_reparse_required",
            "An independently configured raw compiler/source/object verifier is mandatory")
    require(receipt_verifier(receipt, repo) is True, "compiler_reparse_failed", "Compiler evidence did not revalidate")
    require(receipt["checked_commit"] == git(repo, "rev-parse", "HEAD")
            and receipt["checked_tree"] == git(repo, "rev-parse", "HEAD^{tree}")
            and receipt["requested_commit"] == receipt["checked_commit"],
            "receipt_source", "Compiler receipt checked another commit/tree")
    require(not git(repo, "status", "--porcelain", "--untracked-files=all"),
            "dirty_source", "Acceptance needs a clean checkout with no uncommitted source providers")
    require(receipt["implementation_state"] == "FULL_CORE_COMPILER_VERIFIED"
            and receipt["ancestor_baseline_replay"] is True
            and receipt["ancestor_current_compatibility"] is True
            and receipt["reparsed_records_match"] is True,
            "incomplete_receipt", "Required compiler/ancestry gates are incomplete")
    crosswalk = load_strict_json(here/"PAPER_CROSSWALK.json", 16*1024*1024)
    clauses = {c["clause_id"] for f in crosswalk["family_bindings"]
               if f["required_for_full_core"] for c in f["components"]}
    require(set(receipt["required_clauses"]) == clauses
            and clauses <= set(receipt["covered_clauses"]),
            "clause_coverage", "Missing or altered required component clause coverage")
    return {"schema": "OPICA2_COMPILER_ACCEPTANCE_V1", "status": "PASS_COMPILER_EVIDENCE_ONLY",
            "checked_commit": receipt["checked_commit"], "checked_tree": receipt["checked_tree"],
            "full_core_compiler_verified": True, "full_release_accepted": False,
            "human_review": "NOT_ESTABLISHED", "RH": "OPEN", "Step4": "OPEN"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--here", type=Path, default=HERE)
    parser.add_argument("--phase", choices=("preflight", "acceptance"), default="preflight")
    parser.add_argument("--scope", choices=("minimal", "full-core"), default="full-core")
    parser.add_argument("--formal-receipt", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.phase == "preflight":
            report = preflight(args.repo, args.here, scope=args.scope)
        else:
            require(args.formal_receipt is not None, "missing_receipt", "Acceptance requires actual compiler evidence")
            # CLI cannot turn an arbitrary JSON file into a trusted verifier.
            # The compiler owner integrates the independently implemented parser.
            report = acceptance(args.repo, args.here, formal_receipt=args.formal_receipt)
    except (OSError, ValueError, TypeError, KeyError) as exc:
        report = failure_envelope("contract_acceptance", exc)
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if report.get("status", "").startswith("PASS_") else 1


if __name__ == "__main__":
    raise SystemExit(main())

