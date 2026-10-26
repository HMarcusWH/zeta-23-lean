"""Scoped control dispatch; historical controls never become fresh executions."""
from __future__ import annotations

import argparse
from collections.abc import Callable
from copy import deepcopy
from pathlib import Path
from typing import Any

try:
    from .certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json, loads_strict_json, require
    from .finite_baseline import HERE, check_filtered_baseline, verify_filtered_baseline, verify_native_jump_minor
except ImportError:
    from certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json, loads_strict_json, require
    from finite_baseline import HERE, check_filtered_baseline, verify_filtered_baseline, verify_native_jump_minor


# Audited A21/A22 component split. Evidence and disposition may evolve; the
# normative clause scopes and linked control requirements need a reviewed amendment.
CONTROL_PLAN_SHA256 = "530606e59ec5d601701366d9a3840b5dbbd46d9b766e26f28eb31e8edc2a5bfd"


def control_plan_fingerprint(families: list[dict[str, Any]]) -> str:
    rows = deepcopy(families)
    for family in rows:
        for key in ("activation", "all_clause_acceptance_false", "source_pinned_receipt",
                    "unchanged_normative_record_ref", "source_package_normative_ref"):
            family.pop(key, None)
        for clause in family["components"]:
            clause.pop("acceptance", None)
            for link in clause["controls"]:
                link.pop("actual_evidence", None)
                link.pop("resolved_theorem_or_replay_reference", None)
    return canonical_sha256(rows)


def finite_mutation_controls(fixture: dict[str, Any]) -> list[dict[str, Any]]:
    """Current exact input/refusal controls, not 21 additional mathematical theorems."""
    variants = [
        ("wrong source", "source", "Q squared"),
        ("wrong filter", "filter", "2^-N I"),
        ("wrong tree", "source_tree", "0" * 40),
        ("wrong commit", "source_commit", "0" * 40),
        ("zero lower", "lower_square", "0"),
        ("forged upper", "upper_square", "0"),
        ("wrong coefficient", "coefficients", ["1", "-1", "-1", "-1"]),
        ("boolean rational", "coefficients", [True, "-1", "-1", "-2/3"]),
        ("zero denominator", "coefficients", ["1/0", "-1", "-1", "-2/3"]),
        ("noncanonical rational", "coefficients", ["2/2", "-1", "-1", "-2/3"]),
        ("wrong region", "region", {"delta": ["0", "3/8"], "abs_tau": ["1", "2"]}),
        ("boolean horizon", "tail_start", True),
        ("wrong horizon", "tail_start", 47),
        ("authority escalation", "authority", "KERNEL_CHECKED_THEOREM"),
        ("RH escalation", "RH", "PROVED"),
        ("unknown schema", "schema", "unknown"),
    ]
    cases: list[tuple[str, dict[str, Any]]] = []
    for name, key, value in variants:
        mutated = deepcopy(fixture)
        mutated[key] = value
        cases.append((name, mutated))
    extra = deepcopy(fixture)
    extra["ignored"] = 1
    cases.append(("extra field", extra))
    missing = deepcopy(fixture)
    del missing["source"]
    cases.append(("missing source", missing))
    results = []
    for name, mutated in cases:
        try:
            check_filtered_baseline(mutated)
        except (InvalidCertificate, ValueError, TypeError) as exc:
            results.append({"case": name, "expected": "REJECT", "actual": "REJECT",
                            "passed": True, "error_code": getattr(exc, "code", type(exc).__name__),
                            "evidence_class": "RUNTIME_NEGATIVE_FIXTURE",
                            "scope": "Frozen finite input and evidence rejection; not an analytic counterexample"})
        else:
            raise InvalidCertificate("mutation_accepted", "Independent finite checker accepted " + name)
    for text in ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}'):
        try:
            loads_strict_json(text)
        except InvalidCertificate as exc:
            results.append({"case": "JSON rejection " + text, "expected": "REJECT", "actual": "REJECT",
                            "passed": True, "error_code": exc.code,
                            "evidence_class": "RUNTIME_NEGATIVE_FIXTURE",
                            "scope": "Strict JSON parsing only"})
        else:
            raise InvalidCertificate("mutation_accepted", "Malformed JSON was accepted")
    return results


def check_control_bindings(mapping: Any, *, required_ids: set[str] | None = None,
                           acceptance: bool = False,
                           evidence_validator: Callable[[dict, dict | None, dict | None], bool] | None = None) -> dict[str, Any]:
    """Check clause coverage without inventing theorem/replay references."""
    require(type(mapping) is dict and type(mapping.get("family_bindings")) is list
            and type(mapping.get("controls")) is list, "control_mapping", "Complete clause/control mapping required")
    families = mapping["family_bindings"]
    expected_required = required_ids or (
        {f"OPICA2_P{k:02d}" for k in range(1, 24)} | {f"OPICA2_S{k:02d}" for k in range(1, 18)})
    expected_all = expected_required | {"OPICA2_P24", "OPICA2_P25", "OPICA2_O_C2",
                                        "OPICA2_O_C3", "OPICA2_O_C4", "OPICA2_X01"}
    require(len(families) == 46 and {f.get("family_id") for f in families} == expected_all,
            "family_coverage", "Exactly 46 original family bindings are required")
    require({f["family_id"] for f in families if f.get("required_for_full_core") is True} == expected_required,
            "mandatory_families", "Required/optional family classification changed")
    controls = mapping["controls"]
    ids = [c.get("id") for c in controls]
    require(all(type(x) is str and x for x in ids) and len(set(ids)) == len(ids),
            "control_identities", "Control IDs must be nonempty and unique")
    clauses = []
    pending = []
    for family in families:
        require(family.get("all_normative_fields_required") is True, "normative_scope", "Normative fields were narrowed")
        require(type(family.get("components")) is list and family["components"],
                "component_coverage", "Family has no component clauses")
        for clause in family["components"]:
            cid = clause.get("clause_id")
            require(type(cid) is str and bool(cid), "clause_id", "Missing clause ID")
            clauses.append(cid)
            require(type(clause.get("acceptance")) is bool and clause.get("evidence_required") is True,
                    "clause_acceptance", "A Boolean clause disposition and evidence requirement are mandatory")
            links = clause.get("controls")
            require(type(links) is list and links, "clause_controls", "Every clause needs scoped controls")
            require(len({x.get("control_id") for x in links}) == len(links),
                    "duplicate_clause_control", "A clause cannot duplicate a control to inflate evidence")
            all_links_verified = True
            for link in links:
                require(link.get("control_id") in ids, "unknown_control", "Unknown linked control")
                require(type(link.get("expected_scientific_disposition")) is str
                        and bool(link["expected_scientific_disposition"])
                        and type(link.get("accepted_evidence_classes")) is list
                        and bool(link["accepted_evidence_classes"])
                        and all(type(x) is str and x for x in link["accepted_evidence_classes"])
                        and len(set(link["accepted_evidence_classes"])) == len(link["accepted_evidence_classes"]),
                        "control_scope", "Expected disposition and evidence classes are required")
                require(link.get("not_applicable_requires_review") is True
                        and link.get("evidence_required") is True,
                        "control_review", "Control evidence or applicability review was silently removed")
                evidence = link.get("actual_evidence")
                reference = link.get("resolved_theorem_or_replay_reference")
                require(type(evidence) is list, "control_evidence", "Control evidence must be an explicit list")
                if evidence or reference is not None:
                    require(evidence_validator is not None and evidence and reference is not None
                            and evidence_validator(family, clause, link) is True,
                            "unverified_control_evidence", "Actual control evidence needs independent verification")
                else:
                    all_links_verified = False
            if clause["acceptance"]:
                require(all_links_verified and evidence_validator is not None,
                        "unverified_clause", "A Boolean cannot accept a clause without all verified controls")
            elif family["required_for_full_core"]:
                pending.append(cid)
        if family.get("source_pinned_receipt") is not None:
            require(evidence_validator is not None and evidence_validator(family, None, None) is True,
                    "unverified_family", "A family receipt needs compiler revalidation")
        elif family["required_for_full_core"] and acceptance:
            pending.append(family["family_id"] + ":receipt")
    require(len(clauses) == 143 and len(set(clauses)) == 143,
            "clause_coverage", "Exactly 143 unique proposed component clauses are required")
    require(control_plan_fingerprint(families) == CONTROL_PLAN_SHA256,
            "control_plan_changed", "Clause scope/control requirements differ from the audited component split")
    if acceptance:
        require(not pending and evidence_validator is not None, "pending_clause_evidence",
                "Clause acceptance requires independent actual evidence; a mapping PASS is insufficient")
    return {"status": "PASS_VERIFIED_CONTROL_EVIDENCE" if acceptance else "PASS_CONTROL_MAPPING_ONLY", "families": 46, "required_families": 40,
            "clauses": 143, "pending_required_clauses": pending,
            "all_acceptance_false": all(c["acceptance"] is False for f in families for c in f["components"]),
            "RH": "OPEN", "Step4": "OPEN"}


def run_controls(*, registry_path: Path | None = None, mapping_path: Path | None = None,
                 evidence_dir: Path | None = None, repo: Path | None = None,
                 lake: str = "lake", timeout: int = 3600) -> dict[str, Any]:
    fixture = load_strict_json(HERE / "fixtures" / "filtered_four_column.json", 65_536)
    finite = verify_filtered_baseline(fixture)
    minor = verify_native_jump_minor(load_strict_json(HERE / "fixtures" / "native_jump_minor.json", 65_536))
    current = finite_mutation_controls(fixture)
    inherited = []
    registry = None
    if registry_path is not None:
        registry = load_strict_json(registry_path)
        require(type(registry) is dict,"control_registry","Control registry must be an object")
        rows = registry.get("inherited_controls")
        require(type(rows) is list and len(rows) == 25
                and {r.get("id") for r in rows} == {f"OPICA2_F{k:02d}" for k in range(1, 26)},
                "inherited_controls", "All 25 original inherited controls must be retained")
        for row in rows:
            inherited.append({"id": row["id"], "scope": row["scope"], "inherited_authority": row["authority"],
                              "execution": "PRESERVED_NOT_REPLAYED",
                              "scientific_disposition": "Retain the exact inherited scoped result; no new theorem authority"})
    mapping_result = None
    if mapping_path is not None:
        mapping = load_strict_json(mapping_path)
        require(type(mapping) is dict,"control_mapping","Clause mapping must be an object")
        if "controls" not in mapping:
            require(registry is not None, "control_registry", "Clause mapping needs its actual control registry")
            combined = []
            for key in ("inherited_controls", "runtime_mutations", "typed_semantic_guards"):
                require(type(registry.get(key)) is list, "control_registry", "Missing control population: " + key)
                combined.extend(registry[key])
            mapping = {**mapping, "controls": combined}
        mapping_result = check_control_bindings(mapping)
    mutations = load_strict_json(HERE / "fixtures" / "mutations.json", 65_536)
    require({r["id"] for r in mutations["mutations"]} == {f"R2M{k:02d}" for k in range(1, 33)},
            "runtime_designs", "All 32 mutation designs must remain visible")
    result = {"schema": "OPICA2_CONTROL_RUN_V1", "status": "PASS_EXECUTED_FINITE_CONTROLS_ONLY",
            "finite": finite, "minor_budget": minor, "executed_controls": current,
            "inherited_controls": inherited, "clause_mapping": mapping_result,
            "additional_mutation_designs": [
                {"id": r["id"], "scope": r["mutation"], "expected": r["expected"],
                 "execution": "NOT_CLAIMED_BY_THIS_SCOPED_RUN"}
                for r in mutations["mutations"]],
            "full_control_acceptance": False, "full_core_accepted": False,
            "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
    if evidence_dir is not None:
        require(registry_path is not None and mapping_path is not None,
                "runtime_control_inputs", "Actual registry and complete clause mapping are required for runtime execution")
        rows=mapping.get("scoped_control_bindings")
        require(type(rows) is list and len(rows)==75,"runtime_control_bindings","Complete scoped execution bindings are required")
        bindings={row["control_id"]:row for row in rows}
        require(len(bindings)==75,"runtime_control_bindings","Duplicate scoped control identity")
        result["runtime_execution"]=execute_runtime_controls(repo or HERE.parents[3],evidence_dir,registry,bindings,lake=lake,timeout=timeout)
        result["status"]="PASS_EXECUTED_RUNTIME_CONTROL_INPUT_REFUSALS"
        for row in result["additional_mutation_designs"]:
            row["execution"]="ACTUAL_ID_KEYED_TESTS_"+result["runtime_execution"]["python_mode"]
    return result



def require_runtime_checkout(repo: Path) -> Path:
    require(repo.resolve()==HERE.parents[3].resolve(),"runtime_checkout",
            "Execute the runtime from the exact checkout being checked; cross-checkout dispatch is refused")
    return HERE


# Source and execution guards for the 32 ID-keyed runtime controls. Formal and
# historical controls are composed separately from authenticated compiler exports.
def runtime_test_inventory(bindings: dict[str, dict], tests_dir: Path) -> dict[str, dict]:
    import ast
    import hashlib
    import re
    required = {f"R2M{k:02d}" for k in range(1, 33)}
    require(type(bindings) is dict and all(type(row) is dict for row in bindings.values()),"runtime_bindings","Exact control binding objects required")
    require(required <= set(bindings), "runtime_controls", "All 32 runtime controls need exact bindings")
    inventory = {}
    for control_id in sorted(required):
        queries = bindings[control_id].get("runtime_test_queries")
        require(type(queries) is list and queries and len(set(queries)) == len(queries),
                "runtime_queries", "Every runtime control needs exact distinct test methods")
        for query in queries:
            require(type(query) is str and re.fullmatch(r"test_[A-Za-z0-9_]+\.[A-Za-z0-9_]+\.test_[A-Za-z0-9_]+",query),
                    "runtime_query", "Only exact local unittest methods may execute")
            module, class_name, method = query.split(".")
            path = tests_dir/(module+".py")
            require(path.is_file() and path.resolve().parent == tests_dir.resolve(),
                    "runtime_source", "Runtime control test is absent or outside the declared test directory")
            text = path.read_text(encoding="utf-8")
            tree = ast.parse(text)
            classes = [node for node in tree.body if isinstance(node,ast.ClassDef) and node.name==class_name]
            require(len(classes)==1, "runtime_class", "Exact runtime class is absent or ambiguous")
            methods = [node for node in classes[0].body if isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef)) and node.name==method]
            require(len(methods)==1 and not isinstance(methods[0],ast.AsyncFunctionDef),
                    "runtime_method", "Exact synchronous runtime test method is absent or ambiguous")
            segment=ast.get_source_segment(text,methods[0])
            row={"query":query,"path":path.name,"source_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                 "method_sha256":hashlib.sha256(segment.encode("utf-8")).hexdigest()}
            require(query not in inventory or inventory[query]==row,"runtime_source","Ambiguous test source")
            inventory[query]=row
    return inventory


def execute_runtime_controls(repo: Path, output: Path, registry: dict, bindings: dict[str,dict], *,
                             lake: str="lake", timeout: int=3600) -> dict:
    """Execute exact tests and literal Lean pairs; no historical control is replayed here."""
    import hashlib
    import re
    import sys
    try:
        from . import build_receipt as compiler
    except ImportError:
        import build_receipt as compiler
    repo,output=repo.resolve(),output.resolve()
    require_runtime_checkout(repo)
    require(not output.is_relative_to(repo) and not output.exists(),"control_output","Fresh external evidence directory required")
    sources=compiler.source_manifest(repo)
    identity={"checked_commit":compiler.contract.git(repo,"rev-parse","HEAD"),
              "checked_tree":compiler.contract.git(repo,"rev-parse","HEAD^{tree}")}
    inventory=runtime_test_inventory(bindings,HERE/"tests")
    import importlib.util
    fixture_path=HERE/"tests/test_claim_firewall.py"
    spec=importlib.util.spec_from_file_location("_opica2_native_control_runner",fixture_path)
    require(spec is not None and spec.loader is not None,"runtime_fixture_runner","Actual native control runner is unavailable")
    fixture_runner=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fixture_runner)
    canonical_registry=load_strict_json(repo/"research/RHRC/integration/opica_round2/CONTROL_REGISTRY.json",16*1024*1024)
    require(registry==canonical_registry,"runtime_registry","Runtime control payloads must match the committed source registry")
    pairs=registry["runtime_typed_negative_fixtures"]
    environment=compiler.validate_environment(repo)
    output.mkdir(parents=True)
    tests=[]
    for index,(query,source) in enumerate(sorted(inventory.items())):
        argv=[sys.executable,"-B"]+(["-O"] if sys.flags.optimize else [])+["-m","unittest","-v",query]
        name=f"test-{index:03d}"
        command=compiler.run_command(HERE/"tests",argv,output,name,identity["checked_tree"],timeout=timeout)
        text=(output/(name+".stderr.log")).read_text(encoding="utf-8")
        require(command["returncode"]==0 and re.search(r"Ran 1 test in [0-9.]+s",text)
                and re.search(r"\nOK\s*\Z",text) and "skipped" not in text.lower(),
                "runtime_control_failed","Exact runtime negative test failed, skipped, or changed its population: "+query)
        tests.append({**source,"name":name,"command":command,"outcome":"PASS_ACTUAL_ONE_TEST_EXECUTION"})
    modules=sorted({m for row in pairs for m in re.findall(r"^import (\S+)\s*$",row["positive_source"],re.M)})
    build=compiler.run_command(repo,[lake,"build",*modules],output,"typed-build",identity["checked_tree"],timeout=timeout)
    require(build["returncode"]==0,"typed_control_build","Actual Validation module build failed")
    typed=fixture_runner.execute_typed_semantic_guards(repo,registry,output=output/"typed",timeout=timeout,lake=lake)
    require(compiler.source_manifest(repo)==sources and compiler.validate_environment(repo)==environment,
            "runtime_source_drift","Current source or pinned package changed during runtime controls")
    return {"schema":"OPICA2_RUNTIME_CONTROL_EXECUTION_V1",**identity,**environment,
            "python_mode":"OPTIMIZED" if sys.flags.optimize else "NORMAL",
            "source_manifest_sha256":canonical_sha256(sources),"scoped_control_bindings_sha256":canonical_sha256(bindings),
            "runtime_test_inventory_sha256":canonical_sha256(inventory),"tests":tests,"typed_build":build,
            "typed_fixture_imports":modules,"typed_fixture_runner_sha256":compiler.contract.digest(fixture_path),
            "typed_result":typed,"typed_artifact_directory":"typed",
            "runtime_ids":sorted(k for k in bindings if k.startswith("R2M")),
            "fresh_processes_executed_here":True,"provider_authenticity_established_here":False,
            "historical_research_replayed":False,"full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}



def verify_typed_control_artifacts(repo: Path, artifacts: Path, registry: dict, *, optimized: bool) -> dict:
    """Reparse exact paired sources/logs/objects; this does not rerun the compiler."""
    import hashlib
    import re
    from pathlib import PurePosixPath,PureWindowsPath
    try:
        from . import build_receipt as compiler
    except ImportError:
        import build_receipt as compiler
    require_runtime_checkout(repo)
    data=load_strict_json(artifacts/"receipt.json",16*1024*1024)
    expected_fields={"schema","optimized_python","checked_commit","checked_tree","producer_artifact_root",
        "registry_sha256","registry_canonical_sha256","pinned_packages","version_command","source_manifest_sha256",
        "controls","authority","full_core_accepted","full_release_accepted","RH","Step4"}
    require(type(data) is dict and set(data)==expected_fields
            and data.get("authority")=="SOURCE_BOUND_NATIVE_TYPED_REJECTION_NOT_NEW_MATHEMATICAL_AUTHORITY"
            and data.get("full_core_accepted") is False and data.get("full_release_accepted") is False
            and data.get("RH")==data.get("Step4")=="OPEN","typed_control_envelope","Typed control fields or authority caps changed")
    require(data.get("schema")=="OPICA2_TYPED_NEGATIVE_CONTROL_RUN_V1" and data.get("optimized_python") is optimized,
            "typed_control_mode","Typed controls must be separately executed under normal and optimized Python")
    require(data.get("checked_commit")==compiler.contract.git(repo,"rev-parse","HEAD")
            and data.get("checked_tree")==compiler.contract.git(repo,"rev-parse","HEAD^{tree}"),
            "typed_control_source","Typed controls belong to another source head/tree")
    require(data.get("registry_canonical_sha256")==canonical_sha256(registry)
            and canonical_sha256(load_strict_json(artifacts/"registry-snapshot.json",16*1024*1024))==canonical_sha256(registry)
            and data.get("registry_sha256")==compiler.contract.digest(artifacts/"registry-snapshot.json"),
            "typed_control_registry","Paired fixture registry was replaced")
    current_sources=compiler.source_manifest(repo)
    require(data.get("source_manifest_sha256")==canonical_sha256(current_sources)
            and load_strict_json(artifacts/"source-manifest.json",16*1024*1024)==current_sources
            and data.get("pinned_packages")==compiler.validate_packages(repo),
            "typed_control_source","Typed control source/package census differs")
    value=data.get("producer_artifact_root")
    require(type(value) is str,"typed_control_root","Recorded producer root is required")
    root=PureWindowsPath(value) if re.match(r"^[A-Za-z]:[\\/]",value) else PurePosixPath(value)
    require(root.is_absolute() and ".." not in root.parts,"typed_control_root","Producer root must be absolute")
    version=data.get("version_command",{})
    require(type(version) is dict and set(version)=={"argv","returncode","log_sha256"},"typed_control_version","Exact version record required")
    require(type(version.get("argv")) is list and len(version["argv"])==4
            and version["argv"][1:]==["env","lean","--version"] and type(version.get("returncode")) is int and version["returncode"]==0
            and version.get("log_sha256")==compiler.contract.digest(artifacts/"lean-version.log"),
            "typed_control_version","Version command/log differs")
    text=(artifacts/"lean-version.log").read_text(encoding="utf-8")
    require("version 4.33.0-rc2," in text and "d8b18978322de05a8f3dba51ef03cf5461676c17" in text,
            "typed_control_version","Typed controls used another compiler")
    fixtures={row["id"]:row for row in registry["runtime_typed_negative_fixtures"]}
    rows=data.get("controls")
    require(type(rows) is list and len(rows)==7 and all(type(row) is dict for row in rows) and {row.get("id") for row in rows}==set(fixtures),
            "typed_control_inventory","Typed fixture population changed")
    for row in rows:
        require(type(row) is dict and set(row)=={"id","result","scope","commands"}
                and row["result"]=="POSITIVE_NATIVE_CONSUMER_AND_REJECTED_MUTANT_TYPE",
                "typed_control_envelope","Typed pair fields or disposition changed")
        fixture=fixtures[row["id"]]
        require(row.get("scope")==fixture["scope"] and len(row.get("commands",[]))==2,
                "typed_control_scope","Typed fixture lost its exact scoped pair")
        positive,negative=fixture["positive_source"],fixture["negative_source"]
        require(positive!=negative and positive.count(":=")==negative.count(":=")==1
                and positive.split(":=",1)[1]==negative.split(":=",1)[1],
                "typed_control_pair","Expected-type mutation must retain the actual proof body")
        for mode,command in zip(("positive","negative"),row["commands"]):
            require(type(command) is dict and set(command)=={"mode","argv","returncode","source_file","log_file",
                    "source_sha256","log_sha256","object_file","object_sha256"}
                    and type(command.get("returncode")) is int,"typed_control_envelope","Typed command fields/exit code changed")
            name=row["id"]+"_"+mode
            source_name=name+".lean";log_name=name+".log"
            require(command.get("mode")==mode and command.get("source_file")==source_name
                    and command.get("log_file")==log_name,"typed_control_files","Paired filenames changed")
            require((artifacts/source_name).read_bytes()==fixture[mode+"_source"].encode("utf-8")
                    and command.get("source_sha256")==compiler.contract.digest(artifacts/source_name)
                    and command.get("log_sha256")==compiler.contract.digest(artifacts/log_name),
                    "typed_control_artifact","Paired source or raw log changed")
            expected=[version["argv"][0],"env","lean","-R",str(root),str(root/source_name),"-o",str(root/(name+".olean"))]
            require(command.get("argv")==expected,"typed_control_command","Changed paired compiler recipe")
            text=(artifacts/log_name).read_text(encoding="utf-8");lower=text.lower()
            if mode=="positive":
                theorem="Zeta23.OPICARound2.PairedSemanticFixtures.fixture_"+row["id"]
                audit=re.findall(r"'"+re.escape(theorem)+r"' depends on axioms:\s*\[([^]]*)\]",text,re.S)
                no_axioms="'"+theorem+"' does not depend on any axioms" in text
                require(command.get("returncode")==0 and command.get("object_file")==name+".olean"
                        and command.get("object_sha256")==compiler.contract.digest(artifacts/(name+".olean"))
                        and "sorryAx" not in text and ((len(audit)==1 and {a.strip() for a in audit[0].split(',') if a.strip()}<=compiler.ALLOWED_AXIOMS)
                        or (not audit and no_axioms)),"typed_control_positive","Actual positive consumer/object/axiom audit differs")
            else:
                infrastructure=("unknown identifier","unknown constant","unknown tactic","unexpected identifier","unexpected token",
                    "invalid field","invalid dotted identifier","object file","failed to open","invalid import","unknown module","invalid projection")
                meaningful=("type mismatch","application type mismatch","unsolved goals","tactic `exact` failed","failed to synthesize","tactic `rfl` failed")
                require(command.get("returncode")==1 and "error:" in lower and not any(x in lower for x in infrastructure)
                        and any(x in lower for x in meaningful) and command.get("object_sha256") is None,
                        "typed_control_negative","A semantic rejection cannot be replaced by a missing-tool/import/name failure")
    return {"status":"PASS_SOURCE_BOUND_TYPED_PAIR_REPARSE","ids":sorted(fixtures),
            "receipt_sha256":compiler.contract.digest(artifacts/"receipt.json"),"fresh_compiler_replay":False,
            "provider_authenticity_established_here":False}


def verify_runtime_control_evidence(repo: Path, result_path: Path, bindings: dict[str,dict], *, optimized: bool) -> dict:
    import re
    try:
        from . import build_receipt as compiler
    except ImportError:
        import build_receipt as compiler
    require_runtime_checkout(repo)
    report=load_strict_json(result_path,32*1024*1024)
    require(type(report) is dict and report.get("schema")=="OPICA2_CONTROL_RUN_V1"
            and report.get("full_core_accepted") is False and report.get("full_release_accepted") is False
            and report.get("RH")==report.get("Step4")=="OPEN","runtime_control_envelope","Runtime report authority caps changed")
    data=report.get("runtime_execution")
    expected_fields={"schema","checked_commit","checked_tree","lean_toolchain","mathlib_commit","python_mode",
        "source_manifest_sha256","scoped_control_bindings_sha256","runtime_test_inventory_sha256","tests","typed_build",
        "typed_fixture_imports","typed_fixture_runner_sha256","typed_result","typed_artifact_directory","runtime_ids",
        "fresh_processes_executed_here","provider_authenticity_established_here","historical_research_replayed",
        "full_core_accepted","full_release_accepted","RH","Step4"}
    require(type(data) is dict and set(data)==expected_fields and data.get("schema")=="OPICA2_RUNTIME_CONTROL_EXECUTION_V1"
            and data.get("fresh_processes_executed_here") is True and data.get("provider_authenticity_established_here") is False
            and data.get("historical_research_replayed") is False and data.get("full_core_accepted") is False
            and data.get("full_release_accepted") is False and data.get("RH")==data.get("Step4")=="OPEN",
            "runtime_control_evidence","An executed ID-keyed runtime report is required")
    require(data.get("python_mode")==('OPTIMIZED' if optimized else 'NORMAL')
            and data.get("checked_commit")==compiler.contract.git(repo,"rev-parse","HEAD")
            and data.get("checked_tree")==compiler.contract.git(repo,"rev-parse","HEAD^{tree}"),
            "runtime_control_mode","Runtime control mode or exact source head differs")
    require(data.get("source_manifest_sha256")==canonical_sha256(compiler.source_manifest(repo))
            and data.get("scoped_control_bindings_sha256")==canonical_sha256(bindings),
            "runtime_control_source","Runtime control source/semantic bindings changed")
    inventory=runtime_test_inventory(bindings,HERE/"tests")
    require(data.get("runtime_test_inventory_sha256")==canonical_sha256(inventory),
            "runtime_control_inventory","Control test source or exact test selection changed")
    rows=data.get("tests")
    require(type(rows) is list and len(rows)==len(inventory) and all(type(row) is dict for row in rows) and {r.get("query") for r in rows}==set(inventory),
            "runtime_control_inventory","Missing or duplicated exact runtime test execution")
    artifacts=result_path.parent/"runtime"
    for index,row in enumerate(sorted(rows,key=lambda r:r["query"])):
        query=row["query"];name=f"test-{index:03d}"
        require(type(row) is dict and set(row)=={"query","path","source_sha256","method_sha256","name","command","outcome"}
                and row.get("outcome")=="PASS_ACTUAL_ONE_TEST_EXECUTION"
                and all(row.get(k)==v for k,v in inventory[query].items()) and row.get("name")==name,
                "runtime_control_source","Runtime test source fingerprint changed")
        command=row.get("command",{})
        expected=["-B"]+(["-O"] if optimized else [])+["-m","unittest","-v",query]
        require(type(command.get("argv")) is list and command["argv"][1:]==expected
                and type(command.get("returncode")) is int and command["returncode"]==0 and command.get("working_tree_sha")==data["checked_tree"],
                "runtime_control_command","Exact test command changed or failed")
        for channel in ("stdout","stderr"):
            require(command.get(channel+"_sha256")==compiler.contract.digest(artifacts/(name+"."+channel+".log")),
                    "runtime_control_log","Runtime test raw log changed")
        text=(artifacts/(name+".stderr.log")).read_text(encoding="utf-8")
        require(re.search(r"Ran 1 test in [0-9.]+s",text) and re.search(r"\nOK\s*\Z",text) and "skipped" not in text.lower(),
                "runtime_control_result","Runtime method skipped, failed, or changed population")
    registry=load_strict_json(HERE/"CONTROL_REGISTRY.json",16*1024*1024)
    require(data.get("typed_artifact_directory")=="typed" and data.get("typed_fixture_runner_sha256")==compiler.contract.digest(HERE/"tests/test_claim_firewall.py"),
            "typed_control_runner","Actual typed runner source or artifact location changed")
    imports=sorted({m for fixture in registry["runtime_typed_negative_fixtures"]
                    for m in re.findall(r"^import (\S+)\s*$",fixture["positive_source"],re.M)})
    require(imports and data.get("typed_fixture_imports")==imports,"typed_control_build","Typed fixture import inventory changed")
    command=data.get("typed_build",{})
    require(type(command) is dict and set(command)=={"argv","returncode","stdout_sha256","stderr_sha256","working_tree_sha"}
            and type(command.get("argv")) is list and command["argv"][1:]==["build",*imports]
            and type(command.get("returncode")) is int and command["returncode"]==0
            and command.get("working_tree_sha")==data["checked_tree"],"typed_control_build","Typed Validation build changed or failed")
    for channel in ("stdout","stderr"):
        require(command.get(channel+"_sha256")==compiler.contract.digest(artifacts/("typed-build."+channel+".log")),
                "typed_control_build","Typed Validation build raw log changed")
    typed=verify_typed_control_artifacts(repo,artifacts/"typed",registry,optimized=optimized)
    require(canonical_sha256(data.get("typed_result"))==canonical_sha256(load_strict_json(artifacts/"typed/receipt.json",16*1024*1024)),
            "typed_control_result","Embedded typed observations differ from actual artifacts")
    ids=sorted(k for k in bindings if k.startswith("R2M"))
    require(data.get("runtime_ids")==ids and len(ids)==32,"runtime_control_inventory","Missing ID-specific runtime dispositions")
    return {"status":"PASS_SOURCE_BOUND_RUNTIME_CONTROL_REPARSE","ids":ids,"typed":typed,
            "result_sha256":compiler.contract.digest(result_path),"fresh_runtime_replay":False,
            "provider_authenticity_established_here":False}



def compose_control_dispositions(repo: Path, crosswalk: dict, parsed: dict, *,
                                 normal: dict, optimized: dict, upstream_parsed: dict) -> dict[str,dict]:
    """Keep formal controls, runtime refusals, and inherited paper authority distinct."""
    require_runtime_checkout(repo)
    registry=load_strict_json(HERE/"CONTROL_REGISTRY.json",16*1024*1024)
    rows=crosswalk.get("scoped_control_bindings")
    require(type(rows) is list and len(rows)==75 and all(type(row) is dict for row in rows),"control_disposition_inventory","Exactly75 scoped control bindings required")
    bindings={row["control_id"]:row for row in rows}
    require(len(bindings)==75 and registry.get("scoped_execution_bindings")==rows,
            "control_disposition_inventory","Scoped controls differ from the committed control registry")
    runtime_ids={f"R2M{k:02d}" for k in range(1,33)}
    require(set(normal.get("ids",[]))==set(optimized.get("ids",[]))==runtime_ids
            and normal.get("status")==optimized.get("status")=="PASS_SOURCE_BOUND_RUNTIME_CONTROL_REPARSE",
            "control_runtime_modes","Every ID must pass independent normal and optimized runtime artifact verification")
    current={row["name"]:row for row in parsed["declarations"]}
    upstream={row["name"]:row for row in upstream_parsed["declarations"]}
    inherited={row["id"]:row for row in registry["inherited_controls"]}
    result={}
    for control_id,row in bindings.items():
        classes=[]; records=[]
        for name in row.get("actual_declarations",[]):
            source=current if name.startswith("Zeta23.OPICARound2.") else upstream
            require(name in source,"control_declaration","A scoped control declaration is absent from its authenticated compiler export: "+name)
            declaration=source[name]
            require(declaration["kind"]=="THEOREM" and set(declaration["axioms"])<={"propext","Classical.choice","Quot.sound"},
                    "control_declaration","A formal control must be an audited theorem with admitted axioms")
            records.append({"name":name,"module":declaration["module"],"type_sha256":declaration["type_sha256"],"axioms":declaration["axioms"],
                            "authority":"CURRENT_ROUND2_COMPILER_EXPORT" if source is current else "CURRENT_ORIGINAL100_COMPILER_EXPORT"})
        if control_id in runtime_ids:
            require(row.get("runtime_test_queries"),"control_runtime_queries","Runtime control lacks exact executable test binding")
            classes.append("RUNTIME_NEGATIVE_FIXTURE_NORMAL_AND_OPTIMIZED")
            disposition="SOURCE_BOUND_RUNTIME_INPUT_AND_EVIDENCE_REFUSALS_VERIFIED"
            details={"normal_result_sha256":normal["result_sha256"],"optimized_result_sha256":optimized["result_sha256"],
                     "queries":row["runtime_test_queries"],"native_typed_pair":control_id in normal["typed"]["ids"] and control_id in optimized["typed"]["ids"]}
        elif records:
            classes.extend(["LEAN_EXPECTED_TYPE_AND_NATIVE_DOMAIN_CONSUMER","LEAN_NEGATIVE_FIXTURE_OR_EXPLICIT_COUNTEREXAMPLE_AS_APPROPRIATE"])
            if control_id.startswith("OPICA2_F"):
                classes.append("EXISTING_FORMAL_OR_HISTORICAL_RESEARCH_CLASS_MATCHED_TO_AUTHORITY")
            disposition="EXACT_SOURCE_BOUND_FORMAL_CONTROL_TYPES_AND_AXIOMS_VERIFIED"
            details={"compiler_records":records}
        elif row.get("status")=="HISTORICAL_SCOPE_RETAINED_NO_FRESH_REPLAY_OR_FORMAL_PROMOTION":
            require(control_id in inherited,"historical_control","Historical disposition lacks its original unchanged catalog row")
            original=inherited[control_id]
            require(row.get("historical_source_refs")==original.get("source_refs")
                    and row.get("historical_source_catalog_records")
                    and row["expected_scientific_disposition"]=="RETAIN_EXACT_SCOPED_RESULT: "+original["scope"],
                    "historical_control","Historical scientific scope or source authority changed")
            classes.append("EXISTING_FORMAL_OR_HISTORICAL_RESEARCH_CLASS_MATCHED_TO_AUTHORITY")
            disposition="UNCHANGED_HISTORICAL_RESEARCH_AUTHORITY_RETAINED"
            details={"original_record":original,"original_record_sha256":canonical_sha256(original),
                     "historical_source_catalog_records":row["historical_source_catalog_records"],
                     "fresh_replay":False,"new_formal_theorem_authority":False}
        elif row.get("status")=="OPTIONAL_DISABLED_NOT_ACTIVATED":
            require(not row.get("actual_declarations") and not row.get("runtime_test_queries"),
                    "optional_control","Disabled optional control acquired an unreviewed implementation claim")
            disposition="OPTIONAL_DISABLED_NOT_ACTIVATED";classes.append("OPTIONAL_DISABLED_NOT_ACTIVATED")
            details={"optional_activation_accepted":False}
        else:
            raise InvalidCertificate("control_evidence_missing","Control has no authenticated current proof, runtime test, or retained historical authority: "+control_id)
        result[control_id]={"control_id":control_id,"verified":True,"disposition":disposition,
                            "evidence_classes":classes,"scoped_binding_sha256":canonical_sha256(row),
                            "expected_scientific_disposition":row["expected_scientific_disposition"],"details":details,
                            "freshness_from_reparse":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}
    return result


def main() -> int:
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registry", type=Path, default=HERE / "CONTROL_REGISTRY.json")
    parser.add_argument("--mapping", type=Path, default=HERE / "PAPER_CROSSWALK.json")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--evidence-dir", type=Path)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args()
    try:
        result = run_controls(registry_path=args.registry, mapping_path=args.mapping,
                              evidence_dir=args.evidence_dir,lake=args.lake,timeout=args.timeout)
    except (OSError, ValueError, TypeError, KeyError) as exc:
        result = failure_envelope("controls", exc)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if result.get("status", "").startswith("PASS_") else 1


if __name__ == "__main__":
    raise SystemExit(main())

