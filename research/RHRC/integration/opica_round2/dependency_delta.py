"""Exact frozen/current compiler comparison; graph equality is not new mathematics.

Legacy receipts are reparsed with their unchanged sealed parsers. This tool
does not call a source-only capture a compiler replay or invent CI provenance.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from pathlib import PureWindowsPath,PurePosixPath
import subprocess
from typing import Any, Mapping

try:
    from .certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json
    from . import build_receipt as compiler
    from . import validate_contract as contract
except ImportError:
    from certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json
    import build_receipt as compiler
    import validate_contract as contract

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
CHANNELS = ("TYPE", "VALUE", "STRUCTURE")


def recorded_current_export_root(value):
    require(type(value) is str and value and not any(ord(c)<32 for c in value),
            "Recorded producer artifact root required")
    root=PureWindowsPath(value) if PureWindowsPath(value).is_absolute() else PurePosixPath(value)
    require(root.is_absolute() and '..' not in root.parts,"Producer artifact root must be absolute and traversal-free")
    return root


def validate_current_export_envelope(data):
    fixed={"schema":"OPICA2_CURRENT_ANCESTOR_EXPORT_V1","status":"PASS_CURRENT_NATIVE_COMPILER_EXPORT",
        "source_manifest_path":"source-manifest.json",
        "build_mode":"WARM_PROJECT_OBJECTS_ALLOWED_FRESH_COMPILER_PROCESSES",
        "fresh_compiler_process_executed":True,"frozen_legacy_release_gate_rebound":False,
        "ancestor_baseline_replay":False,"ancestor_current_compatibility":False,
        "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}
    keys=set(fixed)|{"checked_commit","checked_tree","lean_toolchain","mathlib_commit","population",
        "root_names","query_inventory_sha256","source_manifest_sha256","exporter_source_sha256",
        "compiled_export_sha256","commands","pinned_packages","parsed","producer_artifact_root",
        "descendant_source_scope"}
    require(type(data) is dict and set(data)==keys,"Current compiler receipt has unknown or missing fields")
    require(all(type(data.get(k)) is type(v) and data[k]==v for k,v in fixed.items()),
            "Current compiler status, scope or authority cap changed")
    commands=data.get("commands")
    command_keys={"argv","returncode","stdout_sha256","stderr_sha256","working_tree_sha"}
    require(type(commands) is list and len(commands)==3 and all(type(row) is dict and set(row)==command_keys
        and type(row.get("argv")) is list and row["argv"]
        and all(type(arg) is str and arg for arg in row["argv"]) for row in commands),
        "Current compiler requires three complete native command records")
    recorded_current_export_root(data.get("producer_artifact_root"))


def current_export_plan(repo: Path, population: int) -> dict[str, Any]:
    """Select immutable ancestor roots/parsers, never the ancestor release CLI."""
    require(type(population) is int and population in {76,100}, "Exact ancestor population required")
    prefix="research/RHRC/integration/"+("opica" if population==76 else "opica_followup")
    builder=compiler.frozen_tool(repo,prefix+"/build_receipt.py","_opica2_current_builder_"+str(population))
    if population==76:
        for name in ("BUILD_MANIFEST.json","PUBLIC_ROOTS.json","WORKFLOW_CONTRACT.json"):
            relative=prefix+"/"+name
            frozen_bytes=subprocess.run(["git","-C",str(repo),"show",contract.FROZEN_COMMIT+":"+relative],
                                        capture_output=True,check=True).stdout
            require(contract.file_at(repo,relative).read_bytes()==frozen_bytes,
                    "Original76 query or reviewed type document changed: "+name)
        manifest=load_strict_json(repo/prefix/"BUILD_MANIFEST.json")
        roots=load_strict_json(repo/prefix/"PUBLIC_ROOTS.json")["primary_roots"]
        workflow=load_strict_json(repo/prefix/"WORKFLOW_CONTRACT.json")
        queries=builder.with_reviewed_root_types(roots,workflow["reviewed_root_type_sha256"])
        relative="Zeta23/RHRC/OpicaBindings.lean"
        driver=contract.file_at(repo,relative).read_bytes()
        frozen=subprocess.run(["git","-C",str(repo),"show",contract.FROZEN_COMMIT+":"+relative],
                              capture_output=True,check=True).stdout
        require(driver==frozen,"Original76 compiler exporter source changed")
        targets=list(manifest["no_root_api_pollution"]["required_build_targets"])
        modules=None
    else:
        frozen=builder.full_contract(repo)
        reviewed=builder.reviewed_full_contract(repo,frozen)
        roots=frozen["roots"]
        queries=reviewed["queries"]
        driver=builder.render_full_exporter(repo,frozen,reviewed)
        targets=[*frozen["manifest"]["required_final_build_targets"],"Zeta23.RHRC.OpicaTypeExprExport"]
        modules=frozen["export_modules"]
        relative=None
    require(len(roots)==population and len({r["full_name"] for r in roots})==population,
            "Original exact root population changed")
    return {"builder":builder,"population":population,"roots":roots,"queries":queries,
            "targets":targets,"driver":driver,"relative_exporter":relative,"mathematical_modules":modules}


def current_export_commands(plan: Mapping[str, Any], output: Path, lake: str) -> list[tuple[list[str],str]]:
    require(type(lake) is str and bool(lake),"Pinned Lake executable required")
    if plan["population"]==76:
        exporter=[lake,"env","lean","-o",str(output/"CurrentAncestorExport.olean"),plan["relative_exporter"]]
    else:
        exporter=[lake,"env","lean","-R",str(output),str(output/"CurrentAncestorExport.lean"),
                  "-o",str(output/"CurrentAncestorExport.olean")]
    return [([lake,"env","lean","--version"],"lean-version"),
            ([lake,"build",*plan["targets"]],"build"),(exporter,"bindings")]


def _parse_current(plan: Mapping[str, Any], log: str) -> dict[str, Any]:
    builder=plan["builder"]
    if plan["population"]==76:
        return builder.parse_compiler_output(log,plan["queries"])
    parsed=builder.parse_compiler_output(log,plan["queries"],mathematical_modules=plan["mathematical_modules"])
    # The genuine frozen consumer and definition checks are retained. Registry
    # counts/release seals for the old298 objects are deliberately not rebound.
    frozen=builder.full_contract(plan["repo"])
    reviewed=builder.reviewed_full_contract(plan["repo"],frozen)
    builder.validate_consumer_provenance(parsed,reviewed)
    builder.validate_required_definitions(parsed,reviewed)
    return parsed


def produce_current_export(repo: Path, output: Path, *, population: int,
                           lake: str="lake",timeout: int=7200) -> dict[str, Any]:
    """Actually compile original76/100 on the clean current head in a fresh process.

    This separate descendant producer retains frozen mathematical queries and
    parsers. It never changes the legacy producer's identity or registry rules.
    Warm project objects are permitted and explicitly reported.
    """
    repo,output=repo.resolve(),output.resolve()
    require(not output.is_relative_to(repo) and not output.exists(),"Fresh external artifact directory required")
    require(type(timeout) is int and 1<=timeout<=86400,"Bounded execution timeout required")
    identity={"checked_commit":contract.git(repo,"rev-parse","HEAD"),
              "checked_tree":contract.git(repo,"rev-parse","HEAD^{tree}")}
    try:
        from .ancestor_projection import inspect_descendant
    except ImportError:
        from ancestor_projection import inspect_descendant
    source_scope=inspect_descendant(repo,repo/"research/RHRC/integration/opica_round2")
    sources=compiler.source_manifest(repo)
    environment=compiler.validate_environment(repo)
    packages=compiler.validate_packages(repo)
    plan=current_export_plan(repo,population)
    plan["repo"]=repo
    output.mkdir(parents=True)
    (output/"CurrentAncestorExport.lean").write_bytes(plan["driver"])
    (output/"source-manifest.json").write_bytes((json.dumps(sources,indent=2)+"\n").encode("utf-8"))
    commands=[]
    for argv,name in current_export_commands(plan,output,lake):
        record=compiler.run_command(repo,argv,output,name,identity["checked_tree"],timeout=timeout)
        commands.append(record)
        require(record["returncode"]==0,"Current ancestor compiler failed; raw logs preserved: "+name)
    version=(output/"lean-version.stdout.log").read_text(encoding="utf-8")
    require("version 4.33.0-rc2," in version and "d8b18978322de05a8f3dba51ef03cf5461676c17" in version,
            "Executed compiler is not the pinned Lean binary")
    parsed=_parse_current(plan,(output/"bindings.stdout.log").read_text(encoding="utf-8"))
    require(compiler.source_manifest(repo)==sources and compiler.validate_environment(repo)==environment
            and compiler.validate_packages(repo)==packages,"Current source or pinned package changed during replay")
    require(identity["checked_commit"]==contract.git(repo,"rev-parse","HEAD"),"Current head changed during replay")
    result={"schema":"OPICA2_CURRENT_ANCESTOR_EXPORT_V1","status":"PASS_CURRENT_NATIVE_COMPILER_EXPORT",
        **identity,**environment,"population":population,"root_names":[r["full_name"] for r in plan["roots"]],
        "query_inventory_sha256":canonical_sha256(plan["queries"]),
        "source_manifest_sha256":canonical_sha256(sources),"source_manifest_path":"source-manifest.json",
        "exporter_source_sha256":hashlib.sha256(plan["driver"]).hexdigest(),
        "compiled_export_sha256":contract.digest(output/"CurrentAncestorExport.olean"),
        "commands":commands,"pinned_packages":packages,"parsed":parsed,
        "producer_artifact_root":str(output),
        "descendant_source_scope":source_scope,
        "build_mode":"WARM_PROJECT_OBJECTS_ALLOWED_FRESH_COMPILER_PROCESSES",
        "fresh_compiler_process_executed":True,"frozen_legacy_release_gate_rebound":False,
        "ancestor_baseline_replay":False,"ancestor_current_compatibility":False,
        "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}
    (output/"current-compiler-receipt.json").write_bytes((json.dumps(result,indent=2)+"\n").encode("utf-8"))
    return result


def verify_current_export(repo: Path, receipt_path: Path, artifacts: Path, *,population: int,
                          expected_commit: str,expected_tree: str) -> dict[str, Any]:
    """Independently reconstruct the frozen plan and reparse exact current raw logs."""
    require(not receipt_path.is_symlink() and not artifacts.is_symlink(),"Linked current evidence is not accepted")
    repo,receipt_path,artifacts=repo.resolve(),receipt_path.resolve(),artifacts.resolve()
    require(not artifacts.is_relative_to(repo),"Current replay artifacts must remain outside the source checkout")
    def artifact(name): return contract.file_at(artifacts,name)
    try:
        from .ancestor_projection import inspect_descendant
    except ImportError:
        from ancestor_projection import inspect_descendant
    data=legacy_json(receipt_path)
    validate_current_export_envelope(data)
    require(data.get("schema")=="OPICA2_CURRENT_ANCESTOR_EXPORT_V1"
            and data.get("population")==population,"Current ancestor export schema/population differs")
    require(data.get("checked_commit")==expected_commit and data.get("checked_tree")==expected_tree
            and contract.git(repo,"rev-parse","HEAD")==expected_commit
            and contract.git(repo,"rev-parse","HEAD^{tree}")==expected_tree,"Current replay mixes source heads")
    sources=compiler.source_manifest(repo)
    require(all(data.get(key)==value for key,value in compiler.validate_environment(repo).items()),
            "Current compiler recorded environment differs from the actual pinned source")
    source_records=load_strict_json(artifact("source-manifest.json"),16*1024*1024)
    require(sources==source_records and canonical_sha256(sources)==data.get("source_manifest_sha256"),
            "Current replay source inventory differs from the exact checkout")
    require(data.get("pinned_packages")==compiler.validate_packages(repo),"Current replay package source differs")
    require(data.get("descendant_source_scope")==inspect_descendant(repo,repo/"research/RHRC/integration/opica_round2"),
            "Current replay does not preserve the authenticated ancestor source scope")
    plan=current_export_plan(repo,population);plan["repo"]=repo
    require(artifact("CurrentAncestorExport.lean").read_bytes()==plan["driver"]
            and data.get("exporter_source_sha256")==hashlib.sha256(plan["driver"]).hexdigest(),
            "Current ancestor exporter is not the exact frozen mathematical driver")
    require(data.get("compiled_export_sha256")==contract.digest(artifact("CurrentAncestorExport.olean")),
            "Current compiler object differs")
    require(data.get("query_inventory_sha256")==canonical_sha256(plan["queries"])
            and data.get("root_names")==[r["full_name"] for r in plan["roots"]],"Current original roots or types changed")
    original_root=recorded_current_export_root(data.get("producer_artifact_root"))
    expected=current_export_commands(plan,original_root,data["commands"][0]["argv"][0])
    require(len(data["commands"])==len(expected),"Current compiler command inventory is incomplete")
    for row,(argv,name) in zip(data["commands"],expected):
        require(row.get("argv")==argv and row.get("returncode")==0
                and row.get("working_tree_sha")==expected_tree,"Current compiler command changed, failed or mixed trees")
        require(row.get("stdout_sha256")==contract.digest(artifact(name+".stdout.log"))
                and row.get("stderr_sha256")==contract.digest(artifact(name+".stderr.log")),
                "Current compiler raw logs are missing or changed")
    version=artifact("lean-version.stdout.log").read_text(encoding="utf-8")
    require("version 4.33.0-rc2," in version and "d8b18978322de05a8f3dba51ef03cf5461676c17" in version,
            "Current replay compiler pin differs")
    parsed=_parse_current(plan,artifact("bindings.stdout.log").read_text(encoding="utf-8"))
    require(parsed==data.get("parsed"),"Current raw-log reparse differs from claimed records")
    return {"schema":"OPICA2_CURRENT_ANCESTOR_REPARSE_V1","population":population,
            "checked_commit":expected_commit,"checked_tree":expected_tree,"parsed":parsed,
            "root_names":sorted(r["full_name"] for r in plan["roots"]),
            "receipt_sha256":contract.digest(receipt_path),"fresh_compiler_replay":False,
            "provider_authenticity_established_here":False,"authority":"SOURCE_BOUND_CURRENT_RAW_LOG_REPARSE_ONLY"}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise InvalidCertificate("ancestry_evidence", message)


def legacy_json(path: Path) -> dict[str, Any]:
    """Legacy receipts contain finite duration floats; keep their sealed format."""
    require(path.is_file() and not path.is_symlink() and path.stat().st_size <= 256*1024*1024,
            "Missing, linked or oversized legacy receipt")
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "Duplicate legacy JSON key")
            result[key] = value
        return result
    def constant(value):
        raise InvalidCertificate("legacy_json", "Nonfinite legacy JSON value: " + value)
    value = json.loads(path.read_bytes(), object_pairs_hook=pairs, parse_constant=constant)
    require(type(value) is dict, "Legacy receipt must be an object")
    return value


def channels(export: Mapping[str, Any]) -> dict[tuple[str, str], tuple[str, ...]]:
    result = {}
    for row in export["dependencies"]:
        key = row["source"], row["channel"]
        require(row["channel"] in CHANNELS and key not in result, "Duplicate or unknown dependency channel")
        targets = row["targets"]
        require(type(targets) is list and len(set(targets)) == len(targets)
                and all(type(t) is str and t for t in targets), "Malformed dependency targets")
        result[key] = tuple(sorted(targets))
    for source, _ in result:
        require(all((source, channel) in result for channel in CHANNELS), "Truncated dependency closure")
    return result


def compare_exports(baseline: Mapping[str, Any], current: Mapping[str, Any],
                    root_names: set[str]) -> dict[str, Any]:
    """Require the whole original public/constructor/private-use export unchanged."""
    old = {r["name"]: r for r in baseline["declarations"]}
    new = {r["name"]: r for r in current["declarations"]}
    require(len(old) == len(baseline["declarations"]) and len(new) == len(current["declarations"]),
            "Duplicate compiler declaration")
    require(root_names and root_names <= set(old) and root_names <= set(new), "Missing original root")
    differences = []
    for name, row in old.items():
        if new.get(name) != row:
            differences.append(name)
    require(not differences, "Original compiler declaration/type/axiom changed: " + ", ".join(differences[:10]))
    require(current.get("constructors") == baseline.get("constructors")
            and current.get("generated_equations", {}) == baseline.get("generated_equations", {}),
            "Original constructor/generated-equation metadata changed")
    old_channels, new_channels = channels(baseline), channels(current)
    require(old_channels == new_channels, "Original transitive TYPE/VALUE/STRUCTURE use graph changed")
    def nodes(data):
        rows = data["dependency_declarations"]
        result = {r["name"]: r for r in rows}
        require(len(result) == len(rows), "Duplicate dependency metadata")
        return result
    require(nodes(baseline) == nodes(current), "Original private/helper/kind/module dependency metadata changed")
    return {"status": "PASS_EXACT_ORIGINAL_COMPILER_EXPORT_EQUALITY", "original_roots": len(root_names),
            "original_public_declarations": len(old), "dependency_channels": len(old_channels),
            "current_additional_public_declarations": sorted(set(new)-set(old)),
            "authority": "Compiler metadata equality only; no theorem strength or human-review inference",
            "RH": "OPEN", "Step4": "OPEN"}


def verify_legacy(repo: Path, receipt_path: Path, artifacts: Path, *, population: int,
                  expected_commit: str, expected_tree: str) -> dict[str, Any]:
    """Bind legacy sources/logs and invoke that version's exact compiler parser.

    This is a reparse of supplied artifacts. A caller must independently establish
    provider provenance or run a fresh compiler replay before treating it as fresh.
    """
    require(population in {76, 100}, "Only the exact original76/100 populations are supported")
    data = legacy_json(receipt_path)
    require(data.get("checked_commit") == expected_commit and data.get("checked_tree") == expected_tree,
            "Legacy receipt belongs to another source head/tree")
    require(contract.git(repo, "rev-parse", expected_commit + "^{tree}") == expected_tree,
            "Expected legacy source is not the actual Git tree")
    prefix = "research/RHRC/integration/" + ("opica" if population == 76 else "opica_followup")
    builder = compiler.frozen_tool(repo, prefix+"/build_receipt.py", "_opica2_legacy_"+str(population))
    roots_document = json.loads(subprocess.run(["git", "-C", str(repo), "show",
        contract.FROZEN_COMMIT + ":" + prefix + "/PUBLIC_ROOTS.json"], capture_output=True, check=True).stdout)
    roots = roots_document["primary_roots" if population == 76 else "roots"]
    require(len(roots) == population and len({r["full_name"] for r in roots}) == population,
            "Frozen original root population differs")
    if population == 76:
        manifest = load_strict_json(repo/prefix/"BUILD_MANIFEST.json")
        workflow = load_strict_json(repo/prefix/"WORKFLOW_CONTRACT.json")
        queries = builder.with_reviewed_root_types(roots, workflow["reviewed_root_type_sha256"])
        builder.validate_compiler_receipt(data, manifest, queries)
        parsed = builder.parse_compiler_output((artifacts/"bindings.log").read_text(encoding="utf-8"), queries)
        require(set(data.get("sources", {})) == {r["path"] for k in ("create", "modify") for r in manifest[k]},
                "Original76 source inventory is incomplete")
        sources = [{"path": p, "sha256": h} for p, h in data["sources"].items()]
    else:
        frozen = builder.full_contract(repo)
        reviewed = builder.reviewed_full_contract(repo, frozen)
        require(data.get("schema") == builder.FULL_RECEIPT_SCHEMA
                and data.get("original_primary_count") == 100
                and data.get("original_primary_roots") == [r["full_name"] for r in roots],
                "Original100 schema/root inventory differs")
        parsed = builder.parse_compiler_output((artifacts/"bindings.log").read_text(encoding="utf-8"),
                    reviewed["queries"], mathematical_modules=frozen["export_modules"])
        builder.validate_consumer_provenance(parsed, reviewed)
        require(data.get("required_definition_inventory") == builder.validate_required_definitions(parsed, reviewed),
                "Original100 definition inventory changed")
        expected_commands = builder.full_commands(frozen)
        require(len(data.get("commands", [])) == len(expected_commands), "Missing original100 compiler command")
        for row, (argv, log) in zip(data["commands"], expected_commands):
            require(row.get("argv") == argv and row.get("log") == log and row.get("exit_code") == 0,
                    "Original100 compiler command changed or failed")
        require((artifacts/"FullOpicaFollowupExport.lean").read_bytes() == builder.render_full_exporter(repo, frozen, reviewed),
                "Original100 exporter source differs")
        require(data.get("compiled_export_sha256") == contract.digest(artifacts/"FullOpicaFollowupExport.olean"),
                "Original100 exporter object differs")
        sources = data.get("source_manifest")
        require(type(sources) is list and sources and data.get("source_manifest_sha256") == builder.object_sha256(sources),
                "Original100 source inventory hash differs")
    require(all(data.get(key) == value for key, value in parsed.items()), "Reparsed legacy records differ from receipt")
    names = [r["path"] for r in sources]
    require(len(set(names)) == len(names), "Duplicate legacy source record")
    index = {}
    for line in contract.git(repo, "ls-tree", "-r", expected_commit).splitlines():
        metadata, path = line.split("\t", 1)
        mode, kind, blob = metadata.split()
        require(kind == "blob", "Non-file legacy source object")
        index[path] = (mode, blob)
    if population == 100:
        require(set(names) == set(index), "Original100 complete source census differs from the actual Git tree")
    for row in sources:
        path = contract.safe_relative(row["path"])
        require(path in index, "Unknown legacy source path")
        if "mode" in row:
            require((row["mode"], row["git_blob"]) == index[path], "Legacy source mode/blob differs from Git tree")
        current = contract.file_at(repo, path)
        if current.is_file():
            _, blob, sha256 = contract.actual_blob_identity(current)
        else:
            blob, sha256 = None, None
        if blob != index[path][1]:
            original = subprocess.run(["git", "-C", str(repo), "show", expected_commit+":"+path],
                                      capture_output=True, check=True).stdout
            sha256 = hashlib.sha256(original).hexdigest()
        require(sha256 == row["sha256"], "Legacy receipt source hash differs: " + path)
    for command in data["commands"]:
        name = contract.safe_relative(command["log"])
        require("/" not in name and command["exit_code"] == 0
                and contract.digest(contract.file_at(artifacts, name)) == command["log_sha256"],
                "Legacy command log missing, altered or failed")
    return {"schema": "OPICA2_LEGACY_REPARSE_V1", "population": population,
            "checked_commit": expected_commit, "checked_tree": expected_tree,
            "receipt_sha256": contract.digest(receipt_path), "parsed": parsed,
            "root_names": sorted(r["full_name"] for r in roots),
            "fresh_compiler_replay": False, "provider_authenticity_established_here": False,
            "authority": "SOURCE_BOUND_RAW_LOG_REPARSE_ONLY"}


def ancestry_report(baseline76: Mapping[str, Any], current76: Mapping[str, Any],
                    baseline100: Mapping[str, Any], current100: Mapping[str, Any], *,
                    current_commit: str, current_tree: str) -> dict[str, Any]:
    pairs = ((76, baseline76, current76), (100, baseline100, current100))
    comparisons = []
    for population, old, new in pairs:
        require(old["population"] == new["population"] == population, "Mixed ancestor populations")
        require(old["checked_commit"] == contract.FROZEN_COMMIT and old["checked_tree"] == contract.FROZEN_TREE,
                "Baseline is not the exact frozen PR294 source")
        require(new["checked_commit"] == current_commit and new["checked_tree"] == current_tree,
                "Current compiler evidence mixes heads/trees")
        require(old["root_names"] == new["root_names"], "Original root identity set changed")
        comparisons.append(compare_exports(old["parsed"], new["parsed"], set(old["root_names"])))
    return {"schema": "OPICA2_ANCESTRY_COMPARISON_V1", "status": "PASS_REPARSED_COMPILER_EQUALITY_ONLY",
            "checked_commit": current_commit, "checked_tree": current_tree, "comparisons": comparisons,
            "baseline_compiler_freshness": "NOT_ESTABLISHED_BY_THIS_REPARSE",
            "current_compiler_freshness": "NOT_ESTABLISHED_BY_THIS_REPARSE",
            "ancestor_baseline_replay": False, "ancestor_current_compatibility": False,
            "full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=REPO)
    for name in ("baseline76", "current76", "baseline100", "current100"):
        parser.add_argument("--"+name, type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--produce-current",type=int,choices=(76,100))
    parser.add_argument("--output-dir",type=Path)
    parser.add_argument("--lake",default="lake")
    parser.add_argument("--timeout",type=int,default=7200)
    args = parser.parse_args()
    try:
        if args.produce_current is not None:
            require(args.output_dir is not None and args.output is None
                    and all(getattr(args,n) is None for n in ("baseline76","current76","baseline100","current100")),
                    "Current producer needs only --produce-current and a fresh --output-dir")
            result=produce_current_export(args.repo,args.output_dir,population=args.produce_current,
                                          lake=args.lake,timeout=args.timeout)
            print(json.dumps({k:v for k,v in result.items() if k!="parsed"},indent=2))
            return 0
        require(args.output is not None and args.output_dir is None
                and all(getattr(args,n) is not None for n in ("baseline76","current76","baseline100","current100")),
                "Comparison requires all four exact original-population receipts and --output")
        head, tree = contract.git(args.repo, "rev-parse", "HEAD"), contract.git(args.repo, "rev-parse", "HEAD^{tree}")
        inputs = []
        for name, population, commit, source_tree in (("baseline76",76,contract.FROZEN_COMMIT,contract.FROZEN_TREE),
            ("current76",76,head,tree),("baseline100",100,contract.FROZEN_COMMIT,contract.FROZEN_TREE),("current100",100,head,tree)):
            path = getattr(args, name)
            verify=verify_current_export if name.startswith("current") else verify_legacy
            inputs.append(verify(args.repo,path,path.parent,population=population,
                                 expected_commit=commit,expected_tree=source_tree))
        result = ancestry_report(*inputs, current_commit=head, current_tree=tree)
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as exc:
        result = failure_envelope("ancestry_comparison", exc)
    if args.output is not None:
        args.output.write_bytes((json.dumps(result,indent=2)+"\n").encode("utf-8"))
    print(json.dumps({k:v for k,v in result.items() if k != "parsed"}, indent=2))
    return 0 if result.get("status") == "PASS_REPARSED_COMPILER_EQUALITY_ONLY" else 1


if __name__ == "__main__":
    raise SystemExit(main())
