"""Exact frozen/current compiler comparison; graph equality is not new mathematics.

Legacy receipts are reparsed with their unchanged sealed parsers. This tool
does not call a source-only capture a compiler replay or invent CI provenance.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
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
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        head, tree = contract.git(args.repo, "rev-parse", "HEAD"), contract.git(args.repo, "rev-parse", "HEAD^{tree}")
        inputs = []
        for name, population, commit, source_tree in (("baseline76",76,contract.FROZEN_COMMIT,contract.FROZEN_TREE),
            ("current76",76,head,tree),("baseline100",100,contract.FROZEN_COMMIT,contract.FROZEN_TREE),("current100",100,head,tree)):
            path = getattr(args, name)
            inputs.append(verify_legacy(args.repo, path, path.parent, population=population,
                                       expected_commit=commit, expected_tree=source_tree))
        result = ancestry_report(*inputs, current_commit=head, current_tree=tree)
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as exc:
        result = failure_envelope("ancestry_comparison", exc)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items() if k != "parsed"}, indent=2))
    return 0 if result.get("status") == "PASS_REPARSED_COMPILER_EQUALITY_ONLY" else 1


if __name__ == "__main__":
    raise SystemExit(main())
