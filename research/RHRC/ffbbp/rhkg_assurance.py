from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(RHRC))

from ffbbp.v16_commutation import assess_categorical_snapshot_sufficiency
from ffbbp.v16_contracts import XiMode, XiReductionContract
from ffbbp.v17_contracts import GateStatus, QualificationIdentity, TypedGateResult
from ffbbp.v17_gates import reduction_assurance_gate

REPO = RHRC.parents[1]
CONFIG = RHRC / "ffbbp" / "configs" / "rhkg_candidate_reduction_v2.json"
REFERENCE = RHRC / "ffbbp" / "FFBBP_V17_ASSURANCE_REFERENCE.json"
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
    return tuple("<NONE>" if row.get(field) is None else str(row.get(field)) for field in fields)


def source_only_decision(row: dict) -> str:
    return "SOURCE_ONLY_PUBLIC_THEOREM" if row.get("visibility_class") == "SOURCE_ONLY_PUBLIC_THEOREM" else "NOT_SOURCE_ONLY_PUBLIC_THEOREM"


def visibility_diagnostic(row: dict) -> str:
    return str(row.get("visibility_class"))


def typed_result(key: str, passed: bool, execution_identity: str) -> TypedGateResult:
    return TypedGateResult(
        key=key,
        status=GateStatus.PASS if passed else GateStatus.FAIL,
        owner="REFERENCE",
        identity=execution_identity,
        scope="STATIC_REPOSITORY_SNAPSHOT",
        evidence_kind="EXACT_REPOSITORY_RECEIPT",
        evidence_ref="SOURCE_CANDIDATE_RESOLUTION",
    )


def build_report() -> dict:
    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    reference = json.loads(REFERENCE.read_text(encoding="utf-8"))
    summary = json.loads(CANDIDATE_SUMMARY.read_text(encoding="utf-8"))
    coverage = json.loads(COVERAGE.read_text(encoding="utf-8"))
    rows = load_jsonl(CANDIDATES)

    if config.get("schema_version") != "RHRC-FFBBP-RHKG-assurance-config-2.0":
        raise RuntimeError("FFBBP RHKG config schema drift")
    if config.get("theory_version") != "1.7":
        raise RuntimeError("FFBBP RHKG adapter must bind FFBBP 1.7 assurance architecture")
    if reference.get("theory_version") != "1.7":
        raise RuntimeError("FFBBP 1.7 reference drift")
    if config.get("xi_mode") != "SNAPSHOT":
        raise RuntimeError("RHKG candidate assurance is snapshot-only")
    if config.get("terminal_claim") != "RH_OPEN" or config.get("theorem_promotion") is not False:
        raise RuntimeError("FFBBP RHKG authority firewall drift")
    if config.get("inherits_runtime_qualification") is not False:
        raise RuntimeError("FFBBP 1.7 assurance may not inherit RUN42C runtime qualification")
    if summary.get("candidate_count") != len(rows):
        raise RuntimeError("candidate summary/count drift")
    if summary.get("source_only_public_theorem_count") != sum(
        1 for row in rows if row.get("visibility_class") == "SOURCE_ONLY_PUBLIC_THEOREM"
    ):
        raise RuntimeError("source-only candidate count drift")

    config_hash = canonical_hash(config)
    execution_digest = canonical_hash({
        "candidate_resolution_sha256": sha256_bytes(CANDIDATES),
        "candidate_summary_sha256": sha256_bytes(CANDIDATE_SUMMARY),
        "rhkg_subject_digest_sha256": coverage["subject_digest_sha256"],
    })
    identity = QualificationIdentity(
        profile_id=config["qualification_identity"]["profile_id"],
        profile_digest=sha256_bytes(REFERENCE),
        protocol_id=config["qualification_identity"]["protocol_id"],
        protocol_digest=config_hash,
        execution_id="RHKG_CANDIDATE_SNAPSHOT:" + coverage["subject_digest_sha256"][:16],
        execution_digest=execution_digest,
    )
    identity.validate()

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
            required_results=(
                typed_result("diagnostic_factorization", diagnostic.passed, identity.execution_id),
                typed_result("decision_factorization", decision.passed, identity.execution_id),
            ),
            structurally_inapplicable=("stateful_transition_closure", "horizon", "witness"),
        )
        reduction_results[spec["id"]] = {
            "id": spec["id"],
            "description": spec["description"],
            "key_fields": key_fields,
            "declared_use": spec["declared_use"],
            "diagnostic_factorization": diagnostic.to_dict(),
            "decision_factorization": decision.to_dict(),
            "assurance_gate": {
                "status": gate.status.value,
                "passed": gate.passed,
                "blockers": list(gate.blockers),
            },
        }

    selected = config["selected_reduction"]
    if not reduction_results[selected]["assurance_gate"]["passed"]:
        raise RuntimeError("selected FFBBP RHKG reduction failed assurance gate")

    source_only_rows = [row for row in rows if row.get("visibility_class") == "SOURCE_ONLY_PUBLIC_THEOREM"]
    cohorts: dict[str, list[str]] = defaultdict(list)
    for row in source_only_rows:
        cohorts[row["module"]].append(row["resolved_full_name"])
    cohort_rows = [
        {"module": module, "count": len(names), "declarations": sorted(names)}
        for module, names in sorted(cohorts.items())
    ]
    cohort_rows.sort(key=lambda row: (-row["count"], row["module"]))

    visibility_counts = Counter(row["visibility_class"] for row in rows)
    report = {
        "schema_version": "RHRC-FFBBP-RHKG-assurance-report-2.0",
        "theory_version": "1.7",
        "status": "RESEARCH_CONTROL_ONLY",
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
        "inherits_runtime_qualification": False,
        "runtime_authority": reference["runtime_authority"],
        "qualification_identity": {
            "profile_id": identity.profile_id,
            "profile_digest": identity.profile_digest,
            "protocol_id": identity.protocol_id,
            "protocol_digest": identity.protocol_digest,
            "execution_id": identity.execution_id,
            "execution_digest": identity.execution_digest,
        },
        "input_snapshot": {
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
            "required_gate_satisfaction": "PASS_ONLY",
            "not_evaluated_is_success": False,
            "not_applicable_is_waiver": False,
            "stateful_transition_claim": False,
            "transition_closure_status": "STRUCTURALLY_NOT_APPLICABLE_SNAPSHOT_XI",
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
            "interpretation": "Module identity alone is not decision-sufficient for source-only visibility on this snapshot.",
        },
        "claim_firewall": [
            "FFBBP 1.7 assurance does not promote the RUN42C runtime or claim RUN46F execution authority",
            "snapshot decision sufficiency does not establish stateful transition closure",
            "NOT_EVALUATED is never success",
            "NOT_APPLICABLE is legal only through frozen protocol scope, not post-hoc waiver",
            "post-reference cohorting does not rank mathematical relevance",
            "FFBBP assurance output is not a mathematical theorem or RH evidence",
            "RH remains OPEN",
        ],
    }
    return report


def render(report: dict) -> bytes:
    return (json.dumps(report, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Build/check FFBBP 1.7 RHKG candidate reduction assurance")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = render(build_report())
    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_bytes(payload)
        data = json.loads(payload)
        print(
            "FFBBP 1.7 RHKG ASSURANCE: WROTE "
            f"{data['input_snapshot']['candidate_count']} candidates; "
            f"{data['input_snapshot']['source_only_public_theorem_count']} source-only"
        )
        return 0
    if not OUTPUT.exists() or OUTPUT.read_bytes() != payload:
        raise SystemExit("FFBBP 1.7 RHKG ASSURANCE: FAIL (checked-in report is stale)")
    print("FFBBP 1.7 RHKG ASSURANCE: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
