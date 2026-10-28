"""Independent exact-inventory acceptance; summaries do not verify themselves."""
from __future__ import annotations
from pathlib import Path
from .canonical import (require, closed_keys, digest, digest_text, load_bytes,
                        validate_path_inventory)
from .snapshot import unlinked, file_hash

BASELINE_LANES = ("CONTRACT", "PARENT_REGRESSION", "CURRENT_COMPATIBILITY", "COMPOSITION_FORMAL",
    "SEMANTIC_NEGATIVES", "FRAMEWORK_ADAPTERS", "PROVIDER_SELECTED", "REPLAY_CAMPAIGN", "GENERATED_STATE")
ROUND4_LANES = BASELINE_LANES + ("MATHEMATICAL_SUPPORT", "SOURCE_NUMERICS")

def verify_gate_inventory(ids, *, round4=True) -> tuple[str, ...]:
    expected = ROUND4_LANES if round4 else BASELINE_LANES
    require(type(ids) in (list, tuple) and len(ids) == len(set(ids)), "duplicate lane inventory")
    require(tuple(ids) == expected, "required lane inventory/order differs; aggregate cannot require itself")
    return expected

def validate_artifacts(root: Path, rows: list[dict], *, exempt=frozenset({"lane.json"})) -> dict:
    root = unlinked(root).resolve()
    require(type(rows) is list and bool(rows), "nonempty raw artifact inventory required")
    for row in rows:
        closed_keys(row, {"path", "bytes", "sha256"})
        require(type(row["bytes"]) is int and row["bytes"] >= 0, "invalid artifact byte count")
        digest_text(row["sha256"])
    paths = validate_path_inventory([r["path"] for r in rows])
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
    require(actual == set(paths) | set(exempt), "missing or unlisted evidence artifact")
    result = {}
    for row in rows:
        path = unlinked(root/row["path"])
        require(path.resolve().is_relative_to(root) and path.is_file(), "artifact escapes evidence root")
        require(path.stat().st_size == row["bytes"] and file_hash(path) == row["sha256"], "artifact content differs")
        result[row["path"]] = path
    return result

def verify_lane_bundle(expected: dict, root: Path, *, experiment: dict, replay) -> dict:
    record = load_bytes((Path(root)/'lane.json').read_bytes())
    closed_keys(record, {"schema", "lane_id", "scope", "experiment", "checked", "conclusion", "artifacts", "records"})
    require(record["schema"] == "OPICA4_LANE_BUNDLE_V1", "lane schema differs")
    require(record["lane_id"] == expected["id"] and record["scope"] == expected["scope"], "lane/scope differs")
    require(record["experiment"] == experiment, "cross-run/attempt/profile evidence")
    require(record["checked"] == expected["checked"], "checked source/environment differs")
    require(record["conclusion"] == "success", "required lane incomplete, skipped or failed")
    files = validate_artifacts(root, record["artifacts"])
    require(type(record["records"]) is list and bool(record["records"]) and
            set(record["records"]) <= set(files), "raw scientific/command records absent")
    require(callable(replay) and replay(expected, record, files) is True,
            "independent raw evidence reconstruction failed")
    return {"id": expected["id"], "scope": expected["scope"],
            "evidence_digest": digest(record, domain="OPICA_LANE_EVIDENCE_V1")}

def accept_application_scope(requirements: list[dict], roots: dict[str, Path], *,
                             experiment: dict, checkers: dict, required_needs: dict) -> dict:
    """Called by the frozen host CLI with fixed checker functions, never proposal code."""
    ids = verify_gate_inventory([r["id"] for r in requirements])
    require(set(roots) == set(ids) == set(checkers) == set(required_needs), "required gate set differs")
    require(all(required_needs[k] == "success" for k in ids), "required CI lane missing or unsuccessful")
    evidence = []
    for row in requirements:
        evidence.append(verify_lane_bundle(row, roots[row["id"]], experiment=experiment, replay=checkers[row["id"]]))
    return {"schema": "OPICA4_INTEGRATED_ACCEPTANCE_V1", "status": "PASS_DECLARED_INTEGRATED_SCOPE",
            "experiment": experiment, "independently_reconstructed_lanes": evidence,
            "full_release_human_review": "NOT_ESTABLISHED", "RH": "OPEN", "Step4": "OPEN"}

def require_test_receipt(record: dict, expected_ids: list[str], *, optimized: bool):
    require(type(expected_ids) is list and bool(expected_ids) and len(expected_ids) == len(set(expected_ids)),
            "nonempty exact test-method inventory required")
    require(record.get("optimized") is optimized and record.get("status") == "PASS", "wrong test mode/result")
    require(record.get("test_ids") == sorted(expected_ids), "test method inventory differs")
    require(record.get("executed") == len(expected_ids) and record.get("expected") == len(expected_ids),
            "test count differs")
    for key in ("skips", "failures", "errors", "expected_failures", "unexpected_successes"):
        require(type(record.get(key)) is int and record[key] == 0, "incomplete test execution: " + key)

def require_native_receipt(record: dict) -> None:
    require(record.get("exit_code") == 0 and record.get("native_executed") is True,
            "native compiler did not execute successfully")
    require(record.get("compiled_object") and record.get("independent_consumer") and
            record.get("axioms_checked") is True, "incomplete native evidence")

def preserve_scientific_disposition(old: dict, new: dict) -> str:
    require(new.get("source") == old.get("source") and new.get("case") == old.get("case"),
            "scientific case/source changed")
    status = new.get("scientific_status")
    require(status in {"PROVED", "DERIVED", "FALSIFIED", "SURVIVED_TEST", "OPEN", "UNRESOLVED"},
            "unknown scientific disposition")
    if status != old.get("scientific_status"): return "CHANGED_REQUIRES_INVESTIGATION"
    return "PRESERVED_" + status
