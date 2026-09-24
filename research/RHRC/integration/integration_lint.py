from __future__ import annotations

import json
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
INTEGRATION = RHRC / "integration"


def bootstrap_materializer_present() -> bool:
    workflow_dir = REPO / ".github" / "workflows"
    return any(workflow_dir.glob("rhrc_*_materializer.yml"))


def load(name: str) -> dict:
    return json.loads((INTEGRATION / name).read_text(encoding="utf-8"))


def main() -> int:
    state = load("INTEGRATION_STATE.json")
    boundary = load("INTEGRATION_BOUNDARY.json")
    frameworks = load("FRAMEWORK_REGISTRY.json")

    for name, data in (
        ("state", state),
        ("boundary", boundary),
        ("framework registry", frameworks),
    ):
        if data.get("terminal_claim") != "RH_OPEN":
            raise SystemExit(f"integration_lint: {name} does not preserve RH_OPEN")

    if state["theorem_authority"]["pr"] != 262:
        raise SystemExit("integration_lint: theorem authority must remain PR #262")
    if state["frozen_control_authority"]["pr"] != 117:
        raise SystemExit("integration_lint: frozen control authority must remain PR #117")
    if state["repository_graph_authority"]["pr"] != 263:
        raise SystemExit("integration_lint: graph authority must remain PR #263")
    if state.get("integration_foundation_authority", {}).get("pr") != 264:
        raise SystemExit("integration_lint: integration foundation authority must remain PR #264")
    if state.get("current_operation") != "FFBBP_RHKG_SNAPSHOT_REDUCTION_ASSURANCE":
        raise SystemExit("integration_lint: current integration operation drift")
    if state.get("theorem_promotion") is not False:
        raise SystemExit("integration_lint: integration state attempts theorem promotion")
    if boundary["claim_firewall"].get("theorem_promotion") is not False:
        raise SystemExit("integration_lint: integration boundary attempts theorem promotion")

    by_id = {row["id"]: row for row in frameworks["frameworks"]}
    required = {
        "FFBBP_RUNTIME",
        "FFBBP_ASSURANCE",
        "OOL_MVS",
        "PERMANSSON_EMBEDDED",
        "PERMANSSON_EXTERNAL",
        "MCM_HMWH",
    }
    if set(by_id) != required:
        raise SystemExit(
            "integration_lint: framework registry drift "
            f"missing={sorted(required - set(by_id))} extra={sorted(set(by_id) - required)}"
        )
    if by_id["FFBBP_ASSURANCE"].get("inherits_run42c_qualification") is not False:
        raise SystemExit("integration_lint: FFBBP v1.6 may not inherit RUN42C qualification")
    if by_id["FFBBP_ASSURANCE"].get("status") != "RHKG_SNAPSHOT_ASSURANCE_INTEGRATED_NOT_RUN42C_QUALIFIED":
        raise SystemExit("integration_lint: FFBBP RHKG assurance status drift")
    if by_id["MCM_HMWH"]["status"] != "NOT_YET_INTEGRATED":
        raise SystemExit("integration_lint: MCM-HMWH must remain not-yet-integrated in foundation PR")

    boundary_source = json.loads((RHRC / "BOUNDARY.json").read_text(encoding="utf-8"))
    diagnostic = boundary_source["diagnostic_engine"]
    route_engine = boundary_source["route_closure_engine"]
    if by_id["FFBBP_RUNTIME"]["version"] != diagnostic["reference_architecture_version"]:
        raise SystemExit("integration_lint: FFBBP runtime version drift from BOUNDARY.json")
    if by_id["FFBBP_RUNTIME"]["scope"] != diagnostic["qualification_scope"]:
        raise SystemExit("integration_lint: FFBBP runtime qualification scope drift")
    if by_id["OOL_MVS"]["version"] != route_engine["kernel_version"]:
        raise SystemExit("integration_lint: OoL-MVS version drift from BOUNDARY.json")
    if by_id["OOL_MVS"]["scope"] != route_engine["import_scope"]:
        raise SystemExit("integration_lint: OoL-MVS import scope drift")

    ffbbp_v16 = json.loads(
        (RHRC / "ffbbp" / "FFBBP_V16_ASSURANCE_REFERENCE.json").read_text(encoding="utf-8")
    )
    if by_id["FFBBP_ASSURANCE"]["version"] != ffbbp_v16["theory_version"]:
        raise SystemExit("integration_lint: FFBBP v1.6 theory version drift")
    if ffbbp_v16.get("inherits_run42c_qualification") is not False:
        raise SystemExit("integration_lint: source FFBBP v1.6 overlay qualification drift")

    ool_reference = json.loads(
        (RHRC / "ool" / "OOL_REFERENCE.json").read_text(encoding="utf-8")
    )
    if by_id["OOL_MVS"]["version"] != ool_reference["version"]:
        raise SystemExit("integration_lint: OoL reference version drift")

    host_toolchain = (REPO / "lean-toolchain").read_text(encoding="utf-8").strip()
    if not host_toolchain.endswith(by_id["PERMANSSON_EXTERNAL"]["host_lean_toolchain"]):
        raise SystemExit("integration_lint: recorded host Lean toolchain drift")

    summary_path = INTEGRATION / "generated" / "SOURCE_CANDIDATE_SUMMARY.json"
    resolution_path = INTEGRATION / "generated" / "SOURCE_CANDIDATE_RESOLUTION.jsonl"
    source_only_path = INTEGRATION / "generated" / "RH_CORE_SOURCE_ONLY_THEOREMS.jsonl"
    if summary_path.exists():
        data = json.loads(summary_path.read_text(encoding="utf-8"))
        if data.get("terminal_claim") != "RH_OPEN":
            raise SystemExit("integration_lint: candidate summary does not preserve RH_OPEN")
        if data.get("theorem_promotion") is not False:
            raise SystemExit("integration_lint: candidate summary attempts theorem promotion")

        resolution_rows = [
            json.loads(line)
            for line in resolution_path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        source_only_rows = [
            json.loads(line)
            for line in source_only_path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        if data.get("candidate_count") != len(resolution_rows):
            raise SystemExit("integration_lint: candidate summary/resolution count drift")
        if data.get("source_only_public_theorem_count") != len(source_only_rows):
            raise SystemExit("integration_lint: source-only summary/product count drift")

        if resolution_rows:
            subject_hashes = {
                row.get("rhkg_subject_digest_sha256") for row in resolution_rows
            }
            source_hashes = {row.get("source_surface_sha256") for row in resolution_rows}
            compiler_hashes = {
                row.get("registered_compiler_receipt_sha256") for row in resolution_rows
            }
            toolchains = {row.get("lean_toolchain") for row in resolution_rows}
            if subject_hashes != {data.get("rhkg_subject_digest_sha256")}:
                raise SystemExit("integration_lint: RHKG subject digest drift")
            if source_hashes != {data.get("source_surface_sha256")}:
                raise SystemExit("integration_lint: source-surface digest drift")
            if compiler_hashes != {data.get("registered_compiler_receipt_sha256")}:
                raise SystemExit("integration_lint: compiler-receipt digest drift")
            if toolchains != {data.get("lean_toolchain")}:
                raise SystemExit("integration_lint: Lean toolchain receipt drift")

        for row in resolution_rows:
            if row.get("claim_cap") != "DISCOVERY_ONLY":
                raise SystemExit("integration_lint: candidate claim-cap widening")
            if row.get("terminal_claim") != "RH_OPEN" or row.get("theorem_promotion") is not False:
                raise SystemExit("integration_lint: candidate authority firewall drift")
            if row.get("trust_zone") != "RH_FORMAL_CORE":
                raise SystemExit("integration_lint: candidate escaped RH_FORMAL_CORE")
            if row.get("source_command_kind") not in {"THEOREM", "LEMMA"}:
                raise SystemExit("integration_lint: non theorem/lemma candidate entered farming set")

        source_only_ids = {row["source_declaration_id"] for row in source_only_rows}
        expected_source_only_ids = {
            row["source_declaration_id"]
            for row in resolution_rows
            if row.get("visibility_class") == "SOURCE_ONLY_PUBLIC_THEOREM"
        }
        if source_only_ids != expected_source_only_ids:
            raise SystemExit("integration_lint: source-only projection drift")
        for row in source_only_rows:
            if row.get("registered_claim_id") is not None:
                raise SystemExit("integration_lint: source-only candidate carries registered claim")

        if resolution_rows:
            by_full_name = {
                row["resolved_full_name"]: row
                for row in resolution_rows
                if row.get("resolved_full_name") is not None
            }
            known_root = (
                "Zeta23.CCM.GlobalBottomResidualState."
                "primeTestWeight_endpoint_order_eight_of_evenStrict"
            )
            root_row = by_full_name.get(known_root)
            if root_row is None:
                raise SystemExit("integration_lint: known PR #262 theorem did not exactify")
            if root_row.get("visibility_class") != "ALREADY_REGISTERED_ROOT":
                raise SystemExit(
                    "integration_lint: known PR #262 theorem lost registered-root visibility"
                )
            if root_row.get("registered_claim_id") != "R003_GLOBAL_BOTTOM_PRIME_WEIGHT_ENDPOINT_JETS":
                raise SystemExit(
                    "integration_lint: known PR #262 theorem/claim binding drift"
                )

            known_hidden = "Zeta23.CCM.hasDerivAt_sourceAtomPairing"
            hidden_row = by_full_name.get(known_hidden)
            if hidden_row is None:
                raise SystemExit(
                    "integration_lint: known MixedSourceDerivativeTransport theorem did not exactify"
                )
            if hidden_row.get("visibility_class") != "SOURCE_ONLY_PUBLIC_THEOREM":
                raise SystemExit(
                    "integration_lint: hidden-body sentinel unexpectedly entered registered closure"
                )

    ffbbp_config_path = RHRC / "ffbbp" / "configs" / "rhkg_candidate_reduction_v1.json"
    ffbbp_report_path = RHRC / "ffbbp" / "generated" / "RHKG_CANDIDATE_REDUCTION_ASSURANCE.json"
    ffbbp_config = json.loads(ffbbp_config_path.read_text(encoding="utf-8"))
    if ffbbp_config.get("theory_version") != "1.6.0":
        raise SystemExit("integration_lint: FFBBP RHKG config theory-version drift")
    if ffbbp_config.get("xi_mode") != "SNAPSHOT":
        raise SystemExit("integration_lint: FFBBP RHKG adapter must remain snapshot Xi")
    if ffbbp_config.get("inherits_run42c_qualification") is not False:
        raise SystemExit("integration_lint: FFBBP RHKG adapter may not inherit RUN42C qualification")
    if ffbbp_config.get("theorem_promotion") is not False:
        raise SystemExit("integration_lint: FFBBP RHKG config attempts theorem promotion")

    if bootstrap_materializer_present():
        print("integration_lint: FFBBP RHKG generated-report validation deferred during one-shot bootstrap")
    else:
        report = json.loads(ffbbp_report_path.read_text(encoding="utf-8"))
        if report.get("schema_version") != "RHRC-FFBBP-RHKG-assurance-report-1.0":
            raise SystemExit("integration_lint: FFBBP RHKG report schema drift")
        if report.get("terminal_claim") != "RH_OPEN" or report.get("theorem_promotion") is not False:
            raise SystemExit("integration_lint: FFBBP RHKG report authority drift")
        if report.get("inherits_run42c_qualification") is not False:
            raise SystemExit("integration_lint: FFBBP RHKG report qualification drift")
        if report["input_snapshot"]["candidate_count"] != 2356:
            raise SystemExit("integration_lint: FFBBP RHKG candidate-count drift")
        if report["input_snapshot"]["source_only_public_theorem_count"] != 680:
            raise SystemExit("integration_lint: FFBBP RHKG source-only-count drift")
        module_only = report["reductions"]["MODULE_ONLY_SNAPSHOT"]
        if module_only["assurance_gate"]["passed"] is not False:
            raise SystemExit("integration_lint: module-only negative control unexpectedly passed")
        if module_only["decision_factorization"]["mixed_value_fiber_count"] != 128:
            raise SystemExit("integration_lint: module-only decision counterexample count drift")
        selected = report["reductions"][report["selected_reduction"]]
        if report["selected_reduction"] != "MODULE_VISIBILITY_SNAPSHOT":
            raise SystemExit("integration_lint: selected FFBBP reduction drift")
        if selected["assurance_gate"]["passed"] is not True:
            raise SystemExit("integration_lint: selected FFBBP reduction no longer assured")
        if report["source_only_module_cohort_count"] != 195:
            raise SystemExit("integration_lint: source-only module cohort count drift")

    print("RHRC INTEGRATION LINT: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
