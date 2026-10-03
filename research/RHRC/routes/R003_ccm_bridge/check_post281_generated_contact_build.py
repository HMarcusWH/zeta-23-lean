#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
RHRC=ROOT/"research"/"RHRC"

LEAN_MODULES=[
"Zeta23/CCM/GlobalParityFirstNegativeBoundary.lean",
"Zeta23/CCM/FirstCrossingGlobalAlignment.lean",
"Zeta23/ExceptionalZero/GlobalParityFirstNegativeBoundary.lean",
"Zeta23/CCM/FirstCrossingProductionTests.lean",
"Zeta23/CCM/FirstCrossingProductionRemainder.lean",
"Zeta23/CCM/FirstCrossingProductionFirstVariation.lean",
"Zeta23/CCM/FirstCrossingProductionResponse.lean",
"Zeta23/CCM/FirstCrossingProductionCurvatureBridge.lean",
"Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean",
]
INTEGRATION_FILES=[
".github/workflows/rhrc.yml",
".github/workflows/rhrc_closure_campaign.yml",
".github/workflows/rhrc_post281_generated_contact_frontier.yml",
"research/RHRC/closure_batch/check_lean_proof_escapes.py",
"research/RHRC/closure_batch/test_lean_proof_escapes.py",
"research/RHRC/tools/run_suite.py",
"research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json",
"research/RHRC/control_v2/CONTROL_STATE.json",
"research/RHRC/control_v2/tests/test_control.py",
"research/RHRC/control_v2/tests/test_current_state_surfaces.py",
"research/RHRC/control_v2/tests/test_post272_sync.py",
"research/RHRC/control_v2/tests/test_post278_sync.py",
"research/RHRC/CURRENT_RESEARCH_PLAN.md",
"research/RHRC/OBSTRUCTION_LEDGER.md",
"research/RHRC/RESEARCH_LEADS.md",
"research/RHRC/DEAD_ROUTES.md",
"research/RHRC/VALIDATION_PROTOCOL.md",
"research/RHRC/routes/R003_ccm_bridge/README.md",
]

RESEARCH_FILES=[
"research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_lean_targets.py",
"research/RHRC/routes/R003_ccm_bridge/POST281_PR282_REPAIR_AUDIT.md",
"research/RHRC/routes/R003_ccm_bridge/POST281_PR282_REPAIR_AUDIT.json",
"research/RHRC/routes/R003_ccm_bridge/canonical_contact_frontier_arb.py",
"research/RHRC/routes/R003_ccm_bridge/post281_generated_contact_frontier.py",
"research/RHRC/routes/R003_ccm_bridge/certify_post281_generated_contact_frontier.py",
"research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_scope.py",
"research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_results.py",
"research/RHRC/routes/R003_ccm_bridge/write_post281_generated_contact_receipt.py",
"research/RHRC/routes/R003_ccm_bridge/POST281_GENERATED_CONTACT_FRONTIER_PROTOCOL.md",
"research/RHRC/routes/R003_ccm_bridge/POST281_PRODUCTION_CONTACT_OBLIGATIONS.json",
"research/RHRC/routes/R003_ccm_bridge/POST281_PRODUCTION_CONTACT_OBSERVABLES.json",
"research/RHRC/routes/R003_ccm_bridge/fixtures/post281_generated_contact_frontier_protocol_v1.json",
"research/RHRC/routes/R003_ccm_bridge/tests/test_post281_generated_contact_frontier.py",
]

def require_contains(path:Path,tokens:list[str]):
    text=path.read_text(encoding="utf-8")
    missing=[x for x in tokens if x not in text]
    if missing:
        raise SystemExit(f"generated-contact build contract: {path} missing {missing}")

def obligation_statuses():
    import json
    p=RHRC/"routes/R003_ccm_bridge/POST281_PRODUCTION_CONTACT_OBLIGATIONS.json"
    data=json.loads(p.read_text(encoding="utf-8"))
    return {row["id"]:row["status"] for row in data["obligations"]}

def main()->int:
    missing=[x for x in LEAN_MODULES+RESEARCH_FILES+INTEGRATION_FILES if not (ROOT/x).is_file()]
    if missing:
        raise SystemExit("generated-contact build contract: missing files: "+", ".join(missing))
    module_names=[x[:-5].replace("/",".") for x in LEAN_MODULES]
    require_contains(ROOT/".github/workflows/rhrc.yml",module_names)
    require_contains(ROOT/".github/workflows/rhrc_closure_campaign.yml",module_names)
    require_contains(RHRC/"closure_batch/check_lean_proof_escapes.py",LEAN_MODULES)
    require_contains(RHRC/"graph/SEMANTIC_CLOSURE_CONFIG.json",module_names)
    workflow=(ROOT/".github/workflows/rhrc_post281_generated_contact_frontier.yml")
    require_contains(workflow,[
        "lean-generated-contact","lean-production-contact",
        "research-generated-contact","arb-generated-contact","generated-contact-complete",
        "post280_saturation_frontier.py",
        "post194_fb05_q14_fixed_unit_second_derivative.py",
        "post198_fb05_q14_four_way_channel_second_derivative.py",
        "post247_remainder_budget_ratio_scout.py",
        "canonical_source_arb.py",
        "canonical_source_numeric.py",
        "run_commutator_gauntlet_v2.py",
    ])
    state=RHRC/"control_v2/CONTROL_STATE.json"
    require_contains(state,[
        '"pr": 281',
        '"merge_commit": "0c22ae4101d7ad3e0b1a81029fff1472c52a5750"',
        '"tree": "f729b05e6fee9f6fbeb9d18a65e26742086244f8"',
        '"pr": 282',
        '"branch": "research/post281-generated-production-contact"',
        '"terminal_claim": "RH_OPEN"',
    ])
    for doc in [
        RHRC/"CURRENT_RESEARCH_PLAN.md",
        RHRC/"OBSTRUCTION_LEDGER.md",
        RHRC/"RESEARCH_LEADS.md",
        RHRC/"VALIDATION_PROTOCOL.md",
        RHRC/"routes/R003_ccm_bridge/README.md",
    ]:
        require_contains(doc,["PR #281","PR #282","RH remains OPEN"])
    import json
    repair=json.loads((RHRC/"routes/R003_ccm_bridge/POST281_PR282_REPAIR_AUDIT.json").read_text(encoding="utf-8"))
    repair_ids=[row["id"] for row in repair["items"]]
    expected=["L01","L02","L03","L04","M01","M02","M03","M04","N01","N02","N03","V01","V02","V03","V04","X01","X02","X03","G01","G02","W01","W02"]
    if sorted(repair_ids) != sorted(expected) or len(repair_ids) != len(set(repair_ids)):
        raise SystemExit("generated-contact repair audit: incomplete or duplicate 22-item ledger")
    if repair.get("terminal_claim") != "RH_OPEN":
        raise SystemExit("generated-contact repair audit: claim firewall violated")
    statuses=obligation_statuses()
    forbidden={"PROVED","CLOSED","DISCHARGED"}
    for oid in ("L04_WEIGHTED_TEST_AUTHORITY","L06_FIRST_VARIATION","L08_CURVATURE_BRIDGE","OBS060O_SATURATION_EXCLUSION","RH"):
        if statuses.get(oid) in forbidden:
            raise SystemExit(f"generated-contact semantic contract: {oid} falsely promoted")
    print(
        f"generated-contact build contract: SURFACE_PASS "
        f"({len(LEAN_MODULES)} Lean + {len(RESEARCH_FILES)} research + "
        f"{len(INTEGRATION_FILES)} integration files); "
        "semantic obligations remain independently gated"
    )
    return 0

if __name__=="__main__":
    raise SystemExit(main())
