from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path

from ffbbp.v16_commutation import assess_categorical_snapshot_sufficiency
from ffbbp.v16_contracts import XiMode, XiReductionContract
from ffbbp.v16_gates import reduction_assurance_gate

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
CONFIG = RHRC / "ffbbp" / "configs" / "rhkg_candidate_reduction_v1.json"
CANDIDATES = RHRC / "integration" / "generated" / "SOURCE_CANDIDATE_RESOLUTION.jsonl"
CANDIDATE_SUMMARY = RHRC / "integration" / "generated" / "SOURCE_CANDIDATE_SUMMARY.json"
COVERAGE = RHRC / "graph" / "generated" / "REPOSITORY_COVERAGE.json"
OUTPUT = RHRC / "ffbbp" / "generated" / "RHKG_CANDIDATE_REDUCTION_ASSURANCE.json"


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sha256_bytes(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_hash(obj: object) -> str:
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def reduction_key(row: dict, fields: list[str]) -> tuple[str, ...]:
    vals: list[str] = []
    for field in fields:
        value = row.get(field)
        if value is None:
            vals.append("<NONE>")
        else:
            vals.append(str(value))
    return tuple(vals)


def source_only_decision(row: dict) -> str:
    return "SOURCE_ONLY_PUBLIC_THEOREM" if row.get("visibility_class") == "SOURCE_ONLY_PUBLIC_THEOREM" else "NOT_SOURCE_ONLY_PUBLIC_THEOREM"


def visibility_diagnostic(row: dict) -> str:
    return str(row.get("visibility_class"))


def build_report() -> dict:
    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    summary = json.loads(CANDIDATE_SUMMARY.read_text(encoding="utf-8"))
    coverage = json.loads(COVERAGE.read_text(encoding="utf-8"))
    rows = load_jsonl(CANDIDATES)

    if config.get("schema_version") != "RHRC-FFBBP-RHKG-assurance-config-1.0":
        raise RuntimeError("FFBBP RHKG config schema drift")
    if config.get("theory_version") != "1.6.0":
        raise RuntimeError("FFBBP RHKG adapter must bind v1.6.0")
    if config.get("xi_mode") != "SNAPSHOT":
        raise RuntimeError("RHKG candidate assurance is snapshot-only")
    if config.get("terminal_claim") != "RH_OPEN":
        raise RuntimeError("FFBBP RHKG config does not preserve RH_OPEN")
    if config.get("theorem_promotion") is not False:
        raise RuntimeError("FFBBP RHKG config attempts theorem promotion")
    if summary.get("candidate_count") != len(rows):
        raise RuntimeError("candidate summary/count drift")
    if summary.get("source_only_public_theorem_count") != sum(
        1 for row in rows if row.get("visibility_class") == "SOURCE_ONLY_PUBLIC_THEOREM"
    ):
        raise RuntimeError("source-only candidate count drift")

    config_hash = canonical_hash(config)
    contract = XiReductionContract(
        reduction_id=config["contract"]["reduction_id"],
        xi_mode=XiMode.SNAPSHOT,
        source_state_schema=config["contract"]["source_state_schema"],
        xi_schema=config["contract"]["xi_schema"],
        reduction_map_version=config["contract"]["reduction_map_version"],
        reference_path_id=config["contract"]["reference_path_id"],
        diagnostic_map_id=config["contract"]["diagnostic_map_id"],
        decision_map_id=config["contract"]["decision_map_id"],
        metric_refs=tuple(config["contract"]["metric_refs"]),
        clock_contract_refs=tuple(config["contract"]["clock_contract_refs"]),
        trust_region=config["contract"]["trust_region"],
        claim_cap_ref=config["contract"]["claim_cap_ref"],
        provenance_hash=config_hash,
    )
    contract.validate()

    reduction_results: dict[str, dict] = {}
    for spec in config["reductions"]:
        key_fields = list(spec["key_fields"])
        diagnostic = assess_categorical_snapshot_sufficiency(
            rows,
            reduction_key=lambda row, f=key_fields: reduction_key(row, f),
            value_map=visibility_diagnostic,
            item_id=lambda row: row["source_declaration_id"],
            max_counterexamples=20,
        )
        decision = assess_categorical_snapshot_sufficiency(
            rows,
            reduction_key=lambda row, f=key_fields: reduction_key(row, f),
            value_map=source_only_decision,
            item_id=lambda row: row["source_declaration_id"],
            max_counterexamples=20,
        )
        gate = reduction_assurance_gate(
            diagnostic_commutation_pass=diagnostic.passed,
            decision_bearing=True,
            decision_sufficiency_pass=decision.passed,
            decision_commutation_pass=decision.passed,
            stateful_reduction=False,
            transition_closure_pass=None,
            horizon_bearing=False,
            horizon_certificate=None,
            witness_bearing=False,
            witness_pass=None,
        )
        reduction_results[spec["id"]] = {
            "id": spec["id"],
            "description": spec["description"],
            "key_fields": key_fields,
            "declared_use": spec["declared_use"],
            "diagnostic_factorization": diagnostic.to_dict(),
            "decision_factorization": decision.to_dict(),
            "assurance_gate": {
                "passed": gate.passed,
                "blockers": list(gate.blockers),
            },
        }

    selected = config["selected_reduction"]
    selected_result = reduction_results[selected]
    if not selected_result["assurance_gate"]["passed"]:
        raise RuntimeError("selected FFBBP RHKG reduction failed assurance gate")

    source_only_rows = [row for row in rows if row.get("visibility_class") == "SOURCE_ONLY_PUBLIC_THEOREM"]
    cohorts: dict[str, list[str]] = defaultdict(list)
    for row in source_only_rows:
        cohorts[row["module"]].append(row["resolved_full_name"])
    cohort_rows = [
        {
            "module": module,
            "count": len(names),
            "declarations": sorted(names),
        }
        for module, names in sorted(cohorts.items())
    ]
    cohort_rows.sort(key=lambda row: (-row["count"], row["module"]))

    visibility_counts = Counter(row["visibility_class"] for row in rows)

    report = {
        "schema_version": "RHRC-FFBBP-RHKG-assurance-report-1.0",
        "theory_version": "1.6.0",
        "status": "RESEARCH_CONTROL_ONLY",
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
        "inherits_run42c_qualification": False,
        "input_snapshot": {
            "base_pr": 264,
            "base_merge_commit": "dd4636d021ccc95d915bcdd9635fe100b8e4c5bb",
            "base_tree": "4e507b8f86de8e7e1bee28d135722d7396a1a8f6",
            "candidate_resolution_sha256": sha256_bytes(CANDIDATES),
            "candidate_summary_sha256": sha256_bytes(CANDIDATE_SUMMARY),
            "candidate_count": len(rows),
            "source_only_public_theorem_count": len(source_only_rows),
            "rhkg_subject_digest_sha256": coverage["subject_digest_sha256"],
            "candidate_source_surface_sha256": summary["source_surface_sha256"],
            "registered_compiler_receipt_sha256": summary["registered_compiler_receipt_sha256"],
            "lean_toolchain": summary["lean_toolchain"],
        },
        "contract": {
            "reduction_id": contract.reduction_id,
            "xi_mode": contract.xi_mode.value,
            "source_state_schema": contract.source_state_schema,
            "xi_schema": contract.xi_schema,
            "reduction_map_version": contract.reduction_map_version,
            "reference_path_id": contract.reference_path_id,
            "diagnostic_map_id": contract.diagnostic_map_id,
            "decision_map_id": contract.decision_map_id,
            "metric_refs": list(contract.metric_refs),
            "clock_contract_refs": list(contract.clock_contract_refs),
            "trust_region": contract.trust_region,
            "claim_cap_ref": contract.claim_cap_ref,
            "provenance_hash": contract.provenance_hash,
        },
        "decision_semantics": {
            "diagnostic": "exact visibility_class categorical value",
            "decision": "visibility_class == SOURCE_ONLY_PUBLIC_THEOREM",
            "decision_tolerance": "exact categorical equality",
            "stateful_transition_claim": False,
            "transition_closure_status": "NOT_APPLICABLE_SNAPSHOT_XI",
            "horizon_claim": False,
            "witness_claim": False,
        },
        "visibility_counts": dict(sorted(visibility_counts.items())),
        "reductions": reduction_results,
        "selected_reduction": selected,
        "selected_reduction_disposition": "PASS_FOR_POST_REFERENCE_COHORT_NAVIGATION_ONLY",
        "source_only_module_cohort_count": len(cohort_rows),
        "source_only_module_cohorts": cohort_rows,
        "falsification_result": {
            "module_only_reduction_passed": reduction_results["MODULE_ONLY_SNAPSHOT"]["assurance_gate"]["passed"],
            "interpretation": (
                "Module identity alone is not decision-sufficient for source-only visibility on the current snapshot; "
                "the mixed fibers are an exact repository-backed counterexample to module-only collapse."
            ),
        },
        "claim_firewall": [
            "FFBBP v1.6 assurance does not inherit RUN42C qualification",
            "snapshot decision sufficiency does not establish stateful transition closure",
            "post-reference cohorting does not rank mathematical relevance",
            "type-digest current-snapshot sufficiency does not generalize to future repository states",
            "FFBBP assurance output is not a mathematical theorem",
            "RH remains OPEN",
        ],
    }
    return report


def render(report: dict) -> bytes:
    return (json.dumps(report, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Build/check FFBBP v1.6 RHKG candidate reduction assurance")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    payload = render(build_report())
    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_bytes(payload)
        data = json.loads(payload)
        module_only = data["reductions"]["MODULE_ONLY_SNAPSHOT"]
        selected = data["reductions"][data["selected_reduction"]]
        print(
            "FFBBP RHKG ASSURANCE: WROTE "
            f"{data['input_snapshot']['candidate_count']} candidates; "
            f"{data['input_snapshot']['source_only_public_theorem_count']} source-only; "
            f"module-only mixed decision fibers="
            f"{module_only['decision_factorization']['mixed_value_fiber_count']}; "
            f"selected fibers={selected['decision_factorization']['fiber_count']}"
        )
        return 0

    if not OUTPUT.exists() or OUTPUT.read_bytes() != payload:
        raise SystemExit("FFBBP RHKG ASSURANCE: FAIL (checked-in report is stale)")
    print("FFBBP RHKG ASSURANCE: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
