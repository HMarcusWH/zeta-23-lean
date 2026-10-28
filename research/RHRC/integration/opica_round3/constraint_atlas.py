"""Current Lean statement atlas. Semantic annotations and compiler facts stay separate.

The committed rows contain no checkout/descriptor/receipt digest: their inputs are
the named upstream source bytes and the authored overlay. External execution
receipts bind those stable rows to an actual checkout. Nothing promotes RH.
"""
from __future__ import annotations

import argparse
import ast
import csv
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import subprocess
import sys
from typing import Any

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PREFIX = "research/RHRC/integration/opica_round3/"
EXPORTER = "Zeta23/RHRC/OpicaRound3AtlasExport.lean"
OVERLAY = PREFIX + "atlas/SEMANTIC_OVERLAY.json"
ATLAS = PREFIX + "atlas/CONSTRAINT_ATLAS.jsonl"
SCHEMA = PREFIX + "schemas/constraint_atlas.schema.json"
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
MAX_FILE = 128 * 1024 * 1024
MAX_ROW = 8 * 1024 * 1024
MAX_ROWS = 1024
AXES = ("object_identity", "aperture_cutoff_quantifiers", "parity", "normalization",
        "maps", "norms", "derivative_moment_order", "polarity")
CAPS = {"full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}


class InvalidAtlas(ValueError):
    pass


def need(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidAtlas(message)


def runtime(repo: Path = REPO):
    previous = list(sys.path)
    try:
        sys.path.insert(0, str(repo))
        from research.RHRC.integration.opica_round2 import build_receipt, certificate_io
        return build_receipt, certificate_io
    finally:
        sys.path[:] = previous


def canonical(data: Any) -> bytes:
    _, cio = runtime()
    value = cio.canonical_bytes(data, max_nodes=8_000_000)
    need(len(value) <= MAX_FILE, "Atlas canonical data exceeds finite byte budget")
    return value


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def safe_relative(name: Any) -> str:
    need(type(name) is str and name and "\\" not in name and ":" not in name, "Canonical relative path required")
    path = PurePosixPath(name)
    need(not path.is_absolute() and ".." not in path.parts and "." not in name.split("/")
         and path.as_posix() == name, "Unsafe atlas path")
    return name


def file_at(root: Path, name: str, budget: int = MAX_FILE) -> Path:
    safe_relative(name)
    path = root
    for part in PurePosixPath(name).parts:
        path = path / part
        need(not path.is_symlink() and not (hasattr(path, "is_junction") and path.is_junction()), "Linked atlas input")
    need(path.is_file() and path.resolve().is_relative_to(root.resolve()) and path.stat().st_size <= budget,
         "Missing, escaping or oversized atlas file: " + name)
    return path


def read_json(path: Path, budget: int = MAX_ROW) -> Any:
    _, cio = runtime()
    return cio.load_strict_json(path, budget, max_nodes=8_000_000)


def git(repo: Path, *args: str) -> str:
    env = {**os.environ, "GIT_OPTIONAL_LOCKS": "0", "GIT_NO_LAZY_FETCH": "1", "GIT_TERMINAL_PROMPT": "0"}
    run = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, check=False, timeout=120, env=env)
    need(type(run.returncode) is int and run.returncode == 0, "Read-only Git inspection failed")
    return run.stdout.decode("utf-8").strip()


def load_overlay(repo: Path) -> dict:
    overlay = read_json(file_at(repo, OVERLAY))
    need(type(overlay) is dict and set(overlay) == {"schema", "authority", "reference_inputs", "support_declarations",
         "reviews", "connections", "source_only_review", *CAPS}, "Closed authored atlas overlay required")
    need(overlay["schema"] == "OPICA3_ATLAS_SEMANTIC_OVERLAY_V1"
         and overlay["authority"] == "AUTHORED_SOURCE_CROSSWALK_NOT_COMPILER_OR_CLOSURE_AUTHORITY", "Wrong overlay authority")
    for key, value in CAPS.items():
        need(type(overlay[key]) is type(value) and overlay[key] == value, "Atlas cannot promote a terminal claim")
    refs = overlay["reference_inputs"]
    need(type(refs) is list and 3 <= len(refs) <= 16, "Finite historical source register required")
    seen = set()
    for row in refs:
        need(type(row) is dict and set(row) == {"kind", "reference_path", "sha256", "raw_utf8", "authority"}
             and type(row["kind"]) is str and row["kind"] not in seen
             and row["authority"] == "HISTORICAL_RESEARCH_INPUT_NOT_CURRENT_PROOF", "Historical reference fields differ")
        safe_relative(row["reference_path"])
        need(type(row["raw_utf8"]) is str and digest(row["raw_utf8"].encode("utf-8")) == row["sha256"],
             "Historical raw JSON/CSV bytes differ from their registered hash")
        seen.add(row["kind"])
    need({"ROOTS216_JSON", "ROOTS216_CSV", "CONTACTS185_JSON"} <= seen, "Missing root/contact historical inputs")
    need(type(overlay["reviews"]) is dict and type(overlay["support_declarations"]) is list,
         "Closed review/support containers required")
    for name, review in overlay["reviews"].items():
        need(NAME.fullmatch(name) and type(review) is dict and set(review) == {"status", "axes", "evidence_declarations", "source_anchors"}
             and review["status"] in {"REVIEWED_SOURCE_CROSSWALK", "UNREVIEWED"}
             and set(review["axes"]) == set(AXES), "Closed semantic review fields required")
        for axis in review["axes"].values():
            need(type(axis) is dict and set(axis) == {"status", "description", "constants"}
                 and axis["status"] in {"REVIEWED", "NOT_APPLICABLE", "UNREVIEWED"}
                 and type(axis["description"]) is str and bool(axis["description"])
                 and type(axis["constants"]) is list and all(type(n) is str and NAME.fullmatch(n) for n in axis["constants"]),
                 "Missing explicit reviewed/unreviewed/not-applicable axis")
        for anchor in review["source_anchors"]:
            need(type(anchor) is dict and set(anchor) == {"path", "sha256", "contains"}, "Closed source anchor required")
            path = file_at(repo, anchor["path"], MAX_ROW)
            need(sha(path) == anchor["sha256"] and type(anchor["contains"]) is list and anchor["contains"]
                 and all(type(part) is str and part and part in path.read_text(encoding="utf-8") for part in anchor["contains"]),
                 "Reviewed source anchor no longer matches actual source")
    connections = overlay["connections"]
    need(type(connections) is list and len({r["id"] for r in connections}) == len(connections), "Unique connection IDs required")
    allowed = {"PROVED_TARGET_WITH_REVIEWED_COMPOSITION", "PROVED_IDENTITY_ADAPTER", "DERIVED_COUNTERMODEL_GENERAL_INFERENCE",
               "UNSUPPORTED_STRENGTHENING_TYPE_REJECTED", "NOT_APPLICABLE", "OPEN_SOURCE_LEAF", "UNREVIEWED"}
    for row in connections:
        need(type(row) is dict and set(row) == {"id", "from", "to", "status", "description", "evidence_declarations",
             "evidence_tests", "scientific_scope", "terminal_progress"} and row["status"] in allowed
             and row["terminal_progress"] in {"SUPPORTING_ONLY", "EXCLUDES_GENERAL_INFERENCE", "UNREVIEWED", "OPEN"},
             "Connection is missing an honest explicit disposition")
        for test in row["evidence_tests"]:
            need(type(test) is dict and set(test) == {"path", "class", "method", "sha256"}, "Closed falsifier source reference required")
            path = file_at(repo, test["path"], MAX_ROW)
            tree = ast.parse(path.read_text(encoding="utf-8"))
            methods = [method for cls in tree.body if isinstance(cls, ast.ClassDef) and cls.name == test["class"]
                       for method in cls.body if isinstance(method, ast.FunctionDef) and method.name == test["method"]]
            need(len(methods) == 1 and digest(ast.get_source_segment(path.read_text(encoding="utf-8"), methods[0]).encode()) == test["sha256"],
                 "Falsifier method/source identity changed")
    return overlay


def reference(overlay: dict, kind: str) -> Any:
    _, cio = runtime()
    row = next(row for row in overlay["reference_inputs"] if row["kind"] == kind)
    return cio.loads_strict_json(row["raw_utf8"], MAX_ROW, max_nodes=8_000_000)


def query_inventory(repo: Path, overlay: dict | None = None) -> list[dict]:
    overlay = overlay if overlay is not None else load_overlay(repo)
    bindings = read_json(repo / "research/RHRC/REGISTERED_THEOREM_BINDINGS.json")["bindings"]
    binding_ids = {row["id"]: row for row in bindings}
    need(len(binding_ids) == len(bindings), "Duplicate registered binding ID")
    rows: dict[str, dict] = {}
    def add(name, module, path, cohort, identity, provenance, registered=False):
        need(type(name) is str and NAME.fullmatch(name) and module.startswith("Zeta23.")
             and NAME.fullmatch(module), "Invalid compiler declaration/module name")
        safe_relative(path)
        need(path == module.replace(".", "/") + ".lean", "Source path is not the exact originating module")
        if registered:
            need(identity in binding_ids and binding_ids[identity]["theorem"] == name
                 and binding_ids[identity]["source"] == path, "Cohort root differs from current registered theorem binding")
        record = rows.setdefault(name, {"declaration": name, "module": module, "source_path": path, "memberships": []})
        need(record["module"] == module and record["source_path"] == path, "Deduplicated declaration has conflicting source identities")
        membership = {"cohort": cohort, "identity": identity, "provenance": provenance}
        need(membership not in record["memberships"], "Duplicate identical cohort membership")
        record["memberships"].append(membership)
    originals = read_json(repo / "research/RHRC/integration/opica/PUBLIC_ROOTS.json")["primary_roots"]
    followup = read_json(repo / "research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json")["roots"]
    round2 = [row for row in read_json(repo / "research/RHRC/integration/opica_round2/PUBLIC_ROOTS.json")["roots"]
              if row.get("required_for_full_core") is True]
    round3 = read_json(repo / PREFIX / "PUBLIC_ROOTS.json")["roots"]
    need((len(originals), len(followup), len(round2), len(round3)) == (76, 100, 40, 5), "Mandatory76+100+40+5 cohort coverage required")
    for cohort, roots in (("OPICA_ORIGINAL76", originals), ("OPICA_FOLLOWUP100", followup)):
        for row in roots:
            add(row["full_name"], row["module"], row["path"], cohort, row["id"], "CURRENT_PUBLIC_ROOTS_AND_REGISTERED_BINDING", True)
    for row in round2:
        add(row["proposed_public_name"], row["module"], row["module"].replace(".", "/") + ".lean",
            "OPICA_ROUND2_40", row["id"], "CURRENT_PUBLIC_ROOTS_AND_REGISTERED_BINDING", True)
    for row in round3:
        add(row["theorem"], row["module"], row["source"], "OPICA_ROUND3_5", row["claim_id"], "CURRENT_PUBLIC_ROOTS_AND_REGISTERED_BINDING", True)
        add(row["consumer_declaration"], row["consumer_module"], row["consumer"], "ROUND3_INDEPENDENT_CONSUMERS5", row["id"], "CURRENT_PUBLIC_ROOTS")
    historical = reference(overlay, "ROOTS216_JSON")["roots"]
    need(len(historical) == 216 and len({r["name"] for r in historical}) == 216, "Exact historical216 declaration identities required")
    historical_names = {r["name"] for r in historical}
    current_old = {name for name, row in rows.items() if any(m["cohort"] in {"OPICA_ORIGINAL76", "OPICA_FOLLOWUP100", "OPICA_ROUND2_40"} for m in row["memberships"])}
    need(historical_names == current_old, "Historical216/current76+100+40 crosswalk is incomplete")
    csv_row = next(row for row in overlay["reference_inputs"] if row["kind"] == "ROOTS216_CSV")
    csv_rows = list(csv.DictReader(io.StringIO(csv_row["raw_utf8"])))
    need(len(csv_rows) == 216 and {r.get("name", r.get("declaration")) for r in csv_rows} == historical_names, "Historical JSON/CSV root crosswalk differs")
    for row in historical:
        add(row["name"], row["module"], row["source_path"], "UCDP_HISTORICAL216", row["id"], "HASHED_HISTORICAL_JSON_AND_CSV")
    contacts = reference(overlay, "CONTACTS185_JSON")["contacts"]
    need(len(contacts) == len({r["declaration"] for r in contacts}) == 185, "Exact185 contact backlog required")
    triples = 0
    for row in contacts:
        name, module = row["declaration"], row["module"]
        add(name, module, module.replace(".", "/") + ".lean", "UCDP_CONTACT185", name, "HASHED_HISTORICAL_CONTACT_CENSUS_NOT_IMPLICATION")
        if len(row["active_interfaces"]) == 3:
            triples += 1
            add(name, module, module.replace(".", "/") + ".lean", "UCDP_PRIORITY_TRIPLE18", name, "THREE_INTERFACE_MEMBERSHIP_NOT_MATHEMATICAL_ADAPTER")
    need(triples == 18, "Exact18 triple-interface priority cohort required")
    for row in overlay["support_declarations"]:
        need(set(row) == {"declaration", "module", "source", "reason"}, "Closed support identity binding required")
        add(row["declaration"], row["module"], row["source"], "REVIEWED_SUPPORT_IDENTITY", row["declaration"], row["reason"])
    need(len(rows) <= MAX_ROWS, "Atlas declaration budget exceeded")
    for row in rows.values():
        row["memberships"].sort(key=lambda x: (x["cohort"], x["identity"]))
        file_at(repo, row["source_path"], MAX_ROW)
    for review in overlay["reviews"].values():
        need(set(review["evidence_declarations"]) <= set(rows), "Reviewed identity lacks a compiler query")
    for connection in overlay["connections"]:
        need(set(connection["evidence_declarations"]) <= set(rows), "Connection evidence is not an exported declaration")
    return [rows[name] for name in sorted(rows)]


def render_driver(queries: list[dict]) -> bytes:
    modules = sorted({row["module"] for row in queries} | {"Zeta23.RHRC.OpicaRound3AtlasExport"})
    text = "\n".join("import " + module for module in modules)
    text += "\nset_option pp.fullNames true\nset_option pp.universes true\nrun_cmd do\n"
    text += "  Zeta23.RHRC.OpicaRound3AtlasExport.exportAtlas #[\n"
    text += ",\n".join("    { declaration := " + json.dumps(row["declaration"]) + ", moduleName := " + json.dumps(row["module"]) + " }" for row in queries)
    return (text + "\n  ]\n").encode()


def outer_dag_binders(expression: dict) -> list[tuple[str, str]]:
    nodes, current, result, seen = expression["nodes"], int(expression["root"]), [], set()
    while True:
        need(current not in seen and 0 <= current < len(nodes), "Cyclic or invalid outer telescope")
        seen.add(current)
        node = nodes[current]
        if node[0] == "mdata":
            current = int(node[2]); continue
        if node[0] != "forall":
            return result
        result.append((node[2], node[3]))
        current = int(node[4])


def parse_output(text: str, queries: list[dict]) -> list[dict]:
    compiler, cio = runtime()
    expected = {row["declaration"]: row for row in queries}
    rows = {}
    fields = {"schema", "declaration", "module", "kind", "universe_parameters", "type_text", "type_expression",
              "outer_telescope", "conclusion_text", "type_constants", "value_constants", "structure_constants", "axioms"}
    need(len(text.encode()) <= MAX_FILE and "error:" not in text.lower(), "Oversized or failed atlas native output")
    for line in text.splitlines():
        if not line.startswith("OPICA3_ATLAS\t"):
            need(not line.startswith("OPICA3_ATLAS"), "Malformed atlas protocol prefix")
            continue
        row = cio.loads_strict_json(line.split("\t", 1)[1], MAX_ROW, max_nodes=8_000_000)
        need(type(row) is dict and set(row) == fields and row["schema"] == "OPICA3_ATLAS_COMPILER_ROW_V1", "Closed actual compiler row required")
        name = row["declaration"]
        need(name in expected and name not in rows and row["module"] == expected[name]["module"], "Unknown/duplicate/wrong-origin compiler declaration")
        need(row["kind"] in {"THEOREM", "DEFINITION", "OPAQUE", "INDUCTIVE", "CONSTRUCTOR", "RECURSOR"}, "No axiom source provider admitted")
        if any(m["cohort"] in {"OPICA_ORIGINAL76", "OPICA_FOLLOWUP100", "OPICA_ROUND2_40", "OPICA_ROUND3_5", "ROUND3_INDEPENDENT_CONSUMERS5"} for m in expected[name]["memberships"]):
            need(row["kind"] == "THEOREM", "Mandatory root or consumer changed declaration kind")
        for key in ("type_text", "conclusion_text"):
            need(type(row[key]) is str and row[key] and len(row[key]) <= 1_000_000, "Missing exact pretty type/conclusion")
        for key in ("universe_parameters", "type_constants", "value_constants", "structure_constants", "axioms"):
            need(type(row[key]) is list and all(type(n) is str for n in row[key]) and len(row[key]) == len(set(row[key])), "Duplicate/malformed compiler constant list")
            if key != "universe_parameters": need(row[key] == sorted(row[key]), "Noncanonical compiler constant order")
        need(set(row["axioms"]) <= compiler.ALLOWED_AXIOMS, "Unadmitted transitive axiom")
        compiler.validate_expression(json.dumps(row["type_expression"], ensure_ascii=False, separators=(",", ":")))
        binders = outer_dag_binders(row["type_expression"])
        need(type(row["outer_telescope"]) is list and len(row["outer_telescope"]) == len(binders), "Actual telescope does not match full type DAG")
        for index, (binder, (info, _)) in enumerate(zip(row["outer_telescope"], binders)):
            need(type(binder) is dict and set(binder) == {"position", "name", "binder_info", "domain_text", "domain_is_prop", "typeclass_binder", "class_name"}
                 and type(binder["position"]) is int and binder["position"] == index and binder["binder_info"] == info
                 and type(binder["name"]) is str and type(binder["domain_text"]) is str and binder["domain_text"]
                 and type(binder["domain_is_prop"]) is bool and type(binder["typeclass_binder"]) is bool
                 and binder["typeclass_binder"] is (info == "instImplicit")
                 and (binder["class_name"] is None or type(binder["class_name"]) is str), "Malformed Prop/data/class binder classification")
        rows[name] = row
    need(set(rows) == set(expected), "Missing exact atlas compiler declarations")
    return [rows[name] for name in sorted(rows)]


def atlas_records(repo: Path, queries: list[dict], compiled: list[dict], overlay: dict) -> list[dict]:
    compiler, cio = runtime()
    schema = read_json(repo / SCHEMA)
    facts = {row["declaration"]: row for row in compiled}
    need(set(facts) == {row["declaration"] for row in queries}, "Compiler/query populations differ")
    known = {row["name"]: row for row in reference(overlay, "ROOTS216_JSON")["roots"]}
    contacts = {row["declaration"]: row for row in reference(overlay, "CONTACTS185_JSON")["contacts"]}
    rows = []
    for query in queries:
        name = query["declaration"]
        fact = facts[name]
        path = file_at(repo, query["source_path"], MAX_ROW)
        review = overlay["reviews"].get(name, {"status": "UNREVIEWED", "axes": {axis: {"status": "UNREVIEWED",
            "description": "Exact compiler statement is recorded; no semantic conclusion or object adapter has been inferred.", "constants": []} for axis in AXES},
            "evidence_declarations": [], "source_anchors": []})
        direct_type, direct_value = set(fact["type_constants"]), set(fact["value_constants"])
        links = [row for row in overlay["connections"] if name in row["from"] + row["to"] + row["evidence_declarations"]]
        historical = known.get(name)
        contact = contacts.get(name)
        row = {"schema": "OPICA3_CONSTRAINT_ATLAS_ROW_V1", "declaration": name, "module": query["module"],
               "kind": fact["kind"], "source": {"path": query["source_path"], "bytes": path.stat().st_size, "sha256": sha(path)},
               "memberships": query["memberships"], "statement": fact,
               "type_sha256": compiler.compiler_canonical_sha256(fact["type_expression"]),
               "type_sha256_format": "STRICT_CANONICAL_JSON_SORTED_KEYS_UTF8_V1",
               "exporter_source_sha256": sha(repo / EXPORTER), "semantic_overlay_sha256": sha(repo / OVERLAY),
               "theorem_inputs": fact["outer_telescope"] if fact["kind"] == "THEOREM" else [],
               "proposition_hypotheses": [binder for binder in fact["outer_telescope"] if binder["domain_is_prop"]] if fact["kind"] == "THEOREM" else [],
               "non_theorem_prop_arguments": [binder for binder in fact["outer_telescope"] if binder["domain_is_prop"]] if fact["kind"] != "THEOREM" else [],
               "data_and_typeclass_parameters": [binder for binder in fact["outer_telescope"] if not binder["domain_is_prop"]],
               "proof_only_dependencies": sorted(direct_value - direct_type) if fact["kind"] == "THEOREM" else [],
               "implementation_only_dependencies": sorted(direct_value - direct_type) if fact["kind"] != "THEOREM" else [],
               "input_classification": "THEOREM_INPUTS_ARE_ALL_OUTER_BINDERS_PROP_AND_DATA_ROLES_EXPLICIT_PROOF_DEPENDENCIES_ARE_NOT_PREMISES",
               "dependency_semantics": "DIRECT_TYPE_VALUE_STRUCTURE_CONSTANT_USE_IS_NOT_A_HYPOTHESIS_OR_MATHEMATICAL_IMPLICATION",
               "semantic_review": review, "connections": links,
               "relevant_known_falsifiers": [test for link in links for test in link["evidence_tests"]],
               "possible_downstream_consumers": [{"connection_id": link["id"], "target": target, "disposition": link["status"]}
                                                 for link in links if name in link["from"] for target in link["to"]],
               "not_applicable_links": [link["id"] for link in links if link["status"] == "NOT_APPLICABLE"],
               "contact_backlog": {"interfaces": contact["active_interfaces"] if contact else [],
                 "priority_triple": bool(contact and len(contact["active_interfaces"]) == 3),
                 "review_status": review["status"] if contact else "NOT_A_HISTORICAL_CONTACT",
                 "authority": "INTERFACE_MEMBERSHIP_DOES_NOT_PROVE_A_MATHEMATICAL_ADAPTER"},
               "historical_source": {"sha256": historical.get("source_sha256") if historical else None,
                 "matches_current": historical.get("source_sha256") == sha(path) if historical else None,
                 "status": "HISTORICAL_REFERENCE_PRESERVED_NOT_CURRENT_COMPILER_AUTHORITY" if historical else "NO_HISTORICAL_ROOT216_RECORD"},
               "scientific_status": "PROVED_EXACT_ELABORATED_STATEMENT" if fact["kind"] == "THEOREM" else "COMPILED_DECLARATION_NOT_THEOREM",
               "semantic_exhaustion": False, "full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
        cio.validate_schema(row, schema)
        rows.append(row)
    return rows


def capture(repo: Path, output: Path, timeout: int) -> dict:
    need(repo.resolve() == REPO.resolve(), "Run the atlas from the exact checkout being checked")
    need(not os.environ.get("LEAN_PATH"), "Atlas capture refuses external Lean object-path overrides")
    compiler, _ = runtime(repo)
    repo, output = repo.resolve(), output.absolute()
    need(not output.exists() and output == output.resolve() and not output.resolve().is_relative_to(repo),
         "Fresh external plain atlas capture directory required")
    need(type(timeout) is int and 1 <= timeout <= 22000, "Bounded positive capture timeout required")
    before = compiler.source_manifest(repo)
    head, tree = git(repo, "rev-parse", "HEAD"), git(repo, "rev-parse", "HEAD^{tree}")
    need(head == os.environ.get("REQUESTED_HEAD", head), "Atlas checked another requested head")
    overlay = load_overlay(repo)
    queries = query_inventory(repo, overlay)
    environment, packages = compiler.validate_environment(repo), compiler.validate_packages(repo)
    output.mkdir(parents=True)
    (output / "AtlasQuery.lean").write_bytes(render_driver(queries))
    (output / "source-manifest.json").write_bytes(canonical(before) + b"\n")
    commands = []
    report = {"schema": "OPICA3_ATLAS_CAPTURE_V1", "status": "FAILED_OR_INCOMPLETE", "checked_commit": head,
              "checked_tree": tree, "source_manifest_sha256": compiler.compiler_canonical_sha256(before),
              "environment": environment, "pinned_packages": packages, "build_mode": "WARM_NATIVE_CURRENT_ENVIRONMENT_EXPORT_NOT_COLD_PROOF_RECEIPT",
              "producer_root": str(output), "commands": commands, "query_sha256": sha(output / "AtlasQuery.lean"),
              "exporter_sha256": sha(repo / EXPORTER), "overlay_sha256": sha(repo / OVERLAY),
              "schema_sha256": sha(repo / SCHEMA), "records": len(queries), "full_core_accepted": False,
              "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
    try:
        commands.append(compiler.run_command(repo, ["lake", "env", "lean", "--version"], output, "version", tree, timeout=timeout))
        version = (output / "version.stdout.log").read_text(encoding="utf-8")
        need(version.startswith("Lean (version 4.33.0-rc2,") and "d8b18978322de05a8f3dba51ef03cf5461676c17" in version,
             "Actual Lean version/commit differs")
        modules = sorted({row["module"] for row in queries} | {"Zeta23.RHRC.OpicaRound3AtlasExport"})
        commands.append(compiler.run_command(repo, ["lake", "build", *modules], output, "build", tree, timeout=timeout))
        need(all(type(row["returncode"]) is int and row["returncode"] == 0 for row in commands), "Atlas prerequisite/version command failed")
        commands.append(compiler.run_command(repo, ["lake", "env", "lean", "-R", str(output), "-o", str(output / "AtlasQuery.olean"),
                                                   str(output / "AtlasQuery.lean")], output, "export", tree, timeout=timeout))
        need(type(commands[-1]["returncode"]) is int and commands[-1]["returncode"] == 0, "Actual atlas query failed")
        compiled = parse_output((output / "export.stdout.log").read_text(encoding="utf-8"), queries)
        need((output / "AtlasQuery.olean").is_file(), "Actual atlas object missing")
        report["object_sha256"] = sha(output / "AtlasQuery.olean")
        need(compiler.source_manifest(repo) == before and git(repo, "rev-parse", "HEAD") == head
             and git(repo, "rev-parse", "HEAD^{tree}") == tree and compiler.validate_environment(repo) == environment
             and compiler.validate_packages(repo) == packages, "Source/package identity changed during atlas query")
        report.update(status="PASS_SOURCE_BOUND_ATLAS_EXPORT", parsed_protocol_sha256=compiler.compiler_canonical_sha256(compiled))
        return report
    finally:
        (output / "receipt.json").write_bytes(canonical(report) + b"\n")


def verify_atlas_capture(repo: Path, capture_dir: Path) -> tuple[list[dict], dict]:
    need(repo.resolve() == REPO.resolve(), "Reparse atlas evidence in the exact checked runtime checkout")
    compiler, _ = runtime(repo)
    need(capture_dir.absolute() == capture_dir.resolve() and not capture_dir.resolve().is_relative_to(repo.resolve()), "Plain external capture required")
    expected = {"AtlasQuery.lean", "AtlasQuery.olean", "source-manifest.json", "receipt.json"}
    expected |= {name + "." + channel + ".log" for name in ("version", "build", "export") for channel in ("stdout", "stderr")}
    need({p.name for p in capture_dir.iterdir()} == expected, "Exact closed atlas capture inventory required")
    for name in expected: file_at(capture_dir, name)
    artifact_hashes = {name: sha(capture_dir / name) for name in expected}
    before = compiler.source_manifest(repo)
    receipt = read_json(capture_dir / "receipt.json")
    fields = {"schema", "status", "checked_commit", "checked_tree", "source_manifest_sha256", "environment", "pinned_packages",
              "build_mode", "producer_root", "commands", "query_sha256", "exporter_sha256", "overlay_sha256", "schema_sha256",
              "records", "object_sha256", "parsed_protocol_sha256", *CAPS}
    need(type(receipt) is dict and set(receipt) == fields and receipt["schema"] == "OPICA3_ATLAS_CAPTURE_V1"
         and receipt["status"] == "PASS_SOURCE_BOUND_ATLAS_EXPORT", "Incomplete or unknown atlas receipt")
    for key, value in CAPS.items(): need(type(receipt[key]) is type(value) and receipt[key] == value, "Atlas receipt promoted authority")
    need(receipt["checked_commit"] == git(repo, "rev-parse", "HEAD") == os.environ.get("REQUESTED_HEAD", receipt["checked_commit"])
         and receipt["checked_tree"] == git(repo, "rev-parse", "HEAD^{tree}")
         and receipt["source_manifest_sha256"] == compiler.compiler_canonical_sha256(before)
         and canonical(read_json(capture_dir / "source-manifest.json", MAX_FILE)) == canonical(before)
         and receipt["environment"] == compiler.validate_environment(repo) and receipt["pinned_packages"] == compiler.validate_packages(repo),
         "Atlas capture belongs to another source or pinned environment")
    need(receipt["build_mode"] == "WARM_NATIVE_CURRENT_ENVIRONMENT_EXPORT_NOT_COLD_PROOF_RECEIPT", "Atlas cannot fabricate cold scope")
    for key, path in (("exporter_sha256", EXPORTER), ("overlay_sha256", OVERLAY), ("schema_sha256", SCHEMA)):
        need(receipt[key] == sha(file_at(repo, path)), "Atlas source/schema/overlay changed")
    queries = query_inventory(repo)
    need(type(receipt["records"]) is int and receipt["records"] == len(queries)
         and (capture_dir / "AtlasQuery.lean").read_bytes() == render_driver(queries)
         and receipt["query_sha256"] == sha(capture_dir / "AtlasQuery.lean")
         and receipt["object_sha256"] == sha(capture_dir / "AtlasQuery.olean"), "Atlas exact driver/object differs")
    value = receipt["producer_root"]
    need(type(value) is str, "Recorded producer root required")
    root = PureWindowsPath(value) if re.match(r"^[A-Za-z]:[\\/]", value) else PurePosixPath(value)
    need(root.is_absolute() and ".." not in root.parts, "Unsafe recorded atlas root")
    modules = sorted({row["module"] for row in queries} | {"Zeta23.RHRC.OpicaRound3AtlasExport"})
    recipes = [["lake", "env", "lean", "--version"], ["lake", "build", *modules],
               ["lake", "env", "lean", "-R", str(root), "-o", str(root / "AtlasQuery.olean"), str(root / "AtlasQuery.lean")]]
    need(type(receipt["commands"]) is list and len(receipt["commands"]) == 3, "All three actual atlas commands required")
    for row, recipe, name in zip(receipt["commands"], recipes, ("version", "build", "export")):
        need(type(row) is dict and set(row) == {"argv", "returncode", "stdout_sha256", "stderr_sha256", "working_tree_sha"}
             and row["argv"] == recipe and type(row["returncode"]) is int and row["returncode"] == 0
             and row["working_tree_sha"] == receipt["checked_tree"], "Actual atlas recipe/exit/source identity changed")
        for channel in ("stdout", "stderr"):
            need(row[channel + "_sha256"] == sha(capture_dir / (name + "." + channel + ".log")), "Atlas raw log changed")
    version = (capture_dir / "version.stdout.log").read_text(encoding="utf-8")
    need(version.startswith("Lean (version 4.33.0-rc2,") and "d8b18978322de05a8f3dba51ef03cf5461676c17" in version, "Atlas used another actual compiler")
    compiled = parse_output((capture_dir / "export.stdout.log").read_text(encoding="utf-8"), queries)
    need(receipt["parsed_protocol_sha256"] == compiler.compiler_canonical_sha256(compiled), "Reparsed actual atlas protocol differs")
    rows = atlas_records(repo, queries, compiled, load_overlay(repo))
    need(compiler.source_manifest(repo) == before and git(repo, "rev-parse", "HEAD") == receipt["checked_commit"]
         and compiler.validate_environment(repo) == receipt["environment"] and compiler.validate_packages(repo) == receipt["pinned_packages"],
         "Source/package identity changed during atlas reparse")
    need({p.name for p in capture_dir.iterdir()} == expected
         and all(sha(file_at(capture_dir, name)) == expected_sha for name, expected_sha in artifact_hashes.items()),
         "Atlas capture artifacts changed during independent reparse")
    return rows, {"status": "PASS_REPARSED_CURRENT_ATLAS_CAPTURE", "checked_commit": receipt["checked_commit"],
                  "checked_tree": receipt["checked_tree"], "source_manifest_sha256": receipt["source_manifest_sha256"],
                  "records": len(rows), "receipt_sha256": sha(capture_dir / "receipt.json"), "fresh_compiler_replay": False,
                  "provider_authenticity_established_here": False, **CAPS}


def serialize_atlas(rows: list[dict]) -> bytes:
    need(rows and len(rows) <= MAX_ROWS and [r["declaration"] for r in rows] == sorted({r["declaration"] for r in rows}), "Sorted deduplicated atlas required")
    result = b"".join(canonical(row) + b"\n" for row in rows)
    need(len(result) <= MAX_FILE, "Atlas JSONL exceeds byte budget")
    return result


def check_atlas(repo: Path, capture_dir: Path) -> dict:
    rows, report = verify_atlas_capture(repo, capture_dir)
    expected = serialize_atlas(rows)
    need(file_at(repo, ATLAS).read_bytes() == expected, "Committed atlas differs from fresh current exact compiler types/source crosswalk")
    compiler, _ = runtime(repo)
    need(compiler.compiler_canonical_sha256(compiler.source_manifest(repo)) == report["source_manifest_sha256"],
         "Source changed while checking the committed atlas product")
    cohorts = {}
    for row in rows:
        for membership in row["memberships"]: cohorts[membership["cohort"]] = cohorts.get(membership["cohort"], 0) + 1
    return {**report, "status": "PASS_CURRENT_CONSTRAINT_ATLAS_WITHOUT_REWRITE", "atlas_sha256": digest(expected),
            "cohorts": cohorts, "reviewed_records": sum(r["semantic_review"]["status"] == "REVIEWED_SOURCE_CROSSWALK" for r in rows),
            "semantic_exhaustion": False, "source_only_search": load_overlay(repo)["source_only_review"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("capture", "check", "write"))
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--evidence-dir", type=Path)
    parser.add_argument("--capture", type=Path)
    parser.add_argument("--timeout", type=int, default=20000)
    args = parser.parse_args()
    try:
        if args.command in {"capture", "check"}:
            need(args.evidence_dir is not None and args.capture is None, "Fresh external evidence directory required")
            report = capture(args.repo, args.evidence_dir, args.timeout)
            if args.command == "check": report = check_atlas(args.repo, args.evidence_dir)
        else:
            need(args.capture is not None and args.evidence_dir is None, "Write needs a genuine previously captured current export")
            rows, input_report = verify_atlas_capture(args.repo, args.capture)
            target = file_at(args.repo, ATLAS)
            target.write_bytes(serialize_atlas(rows))
            report = {**input_report, "status": "WROTE_DERIVED_ATLAS_MIGRATION_INPUT_NOW_STALE_FOR_FINAL_HEAD", "atlas_sha256": sha(target),
                      "final_head_accepted": False}
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return 0
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as exc:
        print(json.dumps({"status": "FAIL_CONSTRAINT_ATLAS", "error": str(exc), "authority": "NO_ACCEPTANCE", **CAPS}, ensure_ascii=False))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
