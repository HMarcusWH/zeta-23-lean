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
RESEARCH_FILES=[
"research/RHRC/routes/R003_ccm_bridge/canonical_contact_frontier_arb.py",
"research/RHRC/routes/R003_ccm_bridge/post281_generated_contact_frontier.py",
"research/RHRC/routes/R003_ccm_bridge/certify_post281_generated_contact_frontier.py",
"research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_scope.py",
"research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_results.py",
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

def main()->int:
    missing=[x for x in LEAN_MODULES+RESEARCH_FILES if not (ROOT/x).is_file()]
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
    ])
    print(f"generated-contact build contract: PASS ({len(LEAN_MODULES)} Lean + {len(RESEARCH_FILES)} research files)")
    return 0

if __name__=="__main__":
    raise SystemExit(main())
