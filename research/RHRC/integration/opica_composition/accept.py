"""Independent exact-inventory acceptance; summaries do not verify themselves."""
from __future__ import annotations
from pathlib import Path
import re
from types import MappingProxyType
from .canonical import (require, closed_keys, digest, digest_text, load_bytes,
                        validate_path_inventory)
from .snapshot import unlinked, file_hash

BASELINE_LANES = ("CONTRACT", "PARENT_REGRESSION", "CURRENT_COMPATIBILITY", "COMPOSITION_FORMAL",
    "SEMANTIC_NEGATIVES", "FRAMEWORK_ADAPTERS", "PROVIDER_SELECTED", "REPLAY_CAMPAIGN", "GENERATED_STATE")
ROUND4_LANES = BASELINE_LANES + ("MATHEMATICAL_SUPPORT", "SOURCE_NUMERICS")

# Scheduling partitions only: no group is independently full acceptance.
# Each tuple preserves the corresponding order in the original eleven lanes.
REPLAY_GROUPS = MappingProxyType({
    "CORE": ("CONTRACT", "PARENT_REGRESSION", "CURRENT_COMPATIBILITY", "COMPOSITION_FORMAL"),
    "AUXILIARY": ("SEMANTIC_NEGATIVES", "FRAMEWORK_ADAPTERS", "PROVIDER_SELECTED",
                  "REPLAY_CAMPAIGN", "MATHEMATICAL_SUPPORT", "SOURCE_NUMERICS"),
    "CANONICAL": ("GENERATED_STATE",),
})
REPLAY_GROUP_IDS = ("CORE", "AUXILIARY", "CANONICAL")


def group_lanes(group_id: str) -> tuple[str, ...]:
    """Return one source-owned partition; callers cannot supply a lane subset."""
    require(type(group_id) is str and group_id in REPLAY_GROUP_IDS, "unknown independent replay group")
    require(tuple(REPLAY_GROUPS) == REPLAY_GROUP_IDS, "independent group inventory/order differs")
    flattened = tuple(lane for group in REPLAY_GROUP_IDS for lane in REPLAY_GROUPS[group])
    require(len(flattened) == len(set(flattened)) == len(ROUND4_LANES) and
            set(flattened) == set(ROUND4_LANES), "independent groups must partition all eleven lanes")
    for members in REPLAY_GROUPS.values():
        require(members == tuple(lane for lane in ROUND4_LANES if lane in members),
                "independent group lane order differs")
    return REPLAY_GROUPS[group_id]

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


def _group_checked(experiment: dict) -> dict:
    closed_keys(experiment, {"run_id", "attempt", "requested_commit", "requested_tree", "profile_digest"})
    require(type(experiment["run_id"]) is str and bool(experiment["run_id"].strip()) and
            type(experiment["attempt"]) is int and experiment["attempt"] > 0,
            "exact independent run/attempt identity required")
    for key in ("requested_commit", "requested_tree"):
        require(type(experiment[key]) is str and re.fullmatch(r"[0-9a-f]{40}", experiment[key]) is not None,
                "exact independent source commit/tree required")
    digest_text(experiment["profile_digest"])
    return {"commit": experiment["requested_commit"], "tree": experiment["requested_tree"]}


def _group_requirements(requirements: list[dict]) -> dict[str, dict]:
    require(type(requirements) is list, "full ordered lane requirements required")
    for row in requirements:
        closed_keys(row, {"id", "scope", "checked"})
        require(type(row["id"]) is str and type(row["scope"]) is str and
                type(row["checked"]) is dict, "invalid lane source requirement")
    verify_gate_inventory([row["id"] for row in requirements])
    return {row["id"]: row for row in requirements}


def verify_independent_group(group_id: str, requirements: list[dict], roots: dict[str, Path], *,
                             experiment: dict, checkers: dict, required_needs: dict) -> dict:
    """Execute the unchanged native/scientific lane checkers for one fixed group.

    Only the frozen host CLI supplies these checker functions. This result must
    travel with the complete independent raw evidence; it is not acceptance.
    """
    members = group_lanes(group_id)
    checked = _group_checked(experiment)
    expected = _group_requirements(requirements)
    require(type(roots) is dict and type(checkers) is dict and
            set(roots) == set(checkers) == set(members), "exact independent group inputs required")
    closed_keys(required_needs, {"lanes"})
    require(required_needs["lanes"] == "success", "producer workflow lanes were not all successful")
    evidence = [verify_lane_bundle(expected[lane], roots[lane], experiment=experiment,
                                   replay=checkers[lane]) for lane in members]
    return {"schema": "OPICA4_INDEPENDENT_REPLAY_GROUP_V1", "group_id": group_id,
            "experiment": experiment, "checked": checked, "conclusion": "success",
            "independently_reconstructed_lanes": evidence}


def join_independent_groups(requirements: list[dict], original_records: dict[str, dict],
                            groups: list[dict], *, experiment: dict, required_needs: dict) -> dict:
    """Join complete, independently verified group artifacts without rerunning Lean.

    The frozen CLI must first verify every group's full sealed raw-file tree,
    native archives and command/test receipts. Summary flags alone must never
    reach this join. Lane identities below are recomputed from the ORIGINAL
    producer records, never copied from an independent group's claims.
    """
    checked = _group_checked(experiment)
    expected = _group_requirements(requirements)
    require(type(original_records) is dict and set(original_records) == set(ROUND4_LANES),
            "all eleven original producer records required")
    closed_keys(required_needs, {"lanes", "independent"})
    require(all(required_needs[key] == "success" for key in ("lanes", "independent")),
            "producer and independent workflow jobs must all succeed")
    originals = {}
    for lane in ROUND4_LANES:
        record = original_records[lane]
        closed_keys(record, {"schema", "lane_id", "scope", "experiment", "checked", "conclusion", "artifacts", "records"})
        require(record["schema"] == "OPICA4_LANE_BUNDLE_V1" and record["lane_id"] == lane and
                record["scope"] == expected[lane]["scope"] and record["checked"] == expected[lane]["checked"],
                "original producer lane/source/scope differs")
        require(record["experiment"] == experiment and record["conclusion"] == "success",
                "original producer evidence is stale or unsuccessful")
        require(type(record["artifacts"]) is list and bool(record["artifacts"]) and
                type(record["records"]) is list and bool(record["records"]),
                "original producer raw evidence inventory absent")
        originals[lane] = {"id": lane, "scope": expected[lane]["scope"],
                           "evidence_digest": digest(record, domain="OPICA_LANE_EVIDENCE_V1")}
    require(type(groups) is list and len(groups) == len(REPLAY_GROUP_IDS),
            "all three independent replay groups required")
    dispositions = []
    reconstructed = []
    for group_id, record in zip(REPLAY_GROUP_IDS, groups):
        members = group_lanes(group_id)
        closed_keys(record, {"schema", "group_id", "experiment", "checked", "conclusion", "independently_reconstructed_lanes"})
        require(record["schema"] == "OPICA4_INDEPENDENT_REPLAY_GROUP_V1" and
                record["group_id"] == group_id, "independent group identity/order differs")
        require(record["experiment"] == experiment and record["checked"] == checked,
                "independent group source/run/attempt/profile differs")
        require(record["conclusion"] == "success", "independent group incomplete, skipped or failed")
        rows = record["independently_reconstructed_lanes"]
        require(type(rows) is list and rows == [originals[lane] for lane in members],
                "independent group lane inventory or original producer digest differs")
        reconstructed.extend(row["id"] for row in rows)
        dispositions.append({"group_id": group_id, "conclusion": "success", "lanes": list(members),
                             "evidence_digest": digest(record, domain="OPICA_INDEPENDENT_REPLAY_GROUP_V1")})
    require(len(reconstructed) == len(set(reconstructed)) == len(ROUND4_LANES) and
            set(reconstructed) == set(ROUND4_LANES), "independent groups omit or duplicate a required lane")
    return {"schema": "OPICA4_INTEGRATED_ACCEPTANCE_V1", "status": "PASS_DECLARED_INTEGRATED_SCOPE",
            "experiment": experiment, "independently_reconstructed_lanes": [originals[lane] for lane in ROUND4_LANES],
            "independent_groups": dispositions,
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
