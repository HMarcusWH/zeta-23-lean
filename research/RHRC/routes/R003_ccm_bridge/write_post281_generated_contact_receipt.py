#!/usr/bin/env python3
"""Write exact execution/provenance receipt for the post-#281 frontier campaign.

This is execution-integrity metadata only.  It creates no theorem authority.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import os
import importlib.metadata
from pathlib import Path

ROUTE = Path(__file__).resolve().parent
ROOT = ROUTE.parents[3]

TRACKED = [
    "research/RHRC/routes/R003_ccm_bridge/post281_generated_contact_frontier.py",
    "research/RHRC/routes/R003_ccm_bridge/canonical_contact_frontier_arb.py",
    "research/RHRC/routes/R003_ccm_bridge/certify_post281_generated_contact_frontier.py",
    "research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_scope.py",
    "research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_results.py",
    "research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_build.py",
    "research/RHRC/routes/R003_ccm_bridge/POST281_GENERATED_CONTACT_FRONTIER_PROTOCOL.md",
    "research/RHRC/routes/R003_ccm_bridge/POST281_PRODUCTION_CONTACT_OBLIGATIONS.json",
    "research/RHRC/routes/R003_ccm_bridge/POST281_PRODUCTION_CONTACT_OBSERVABLES.json",
    "research/RHRC/routes/R003_ccm_bridge/fixtures/post281_generated_contact_frontier_protocol_v1.json",
    "research/RHRC/routes/R003_ccm_bridge/post194_fb05_q14_fixed_unit_second_derivative.py",
    "research/RHRC/routes/R003_ccm_bridge/post198_fb05_q14_four_way_channel_second_derivative.py",
    "research/RHRC/routes/R003_ccm_bridge/post247_remainder_budget_ratio_scout.py",
    "research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py",
    "research/RHRC/routes/R003_ccm_bridge/canonical_source_numeric.py",
    "research/RHRC/routes/R003_ccm_bridge/run_commutator_gauntlet_v2.py",
    "research/RHRC/routes/R003_ccm_bridge/requirements.txt",
    "research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_lean_targets.py",
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

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()

def main() -> int:
    ap=argparse.ArgumentParser()
    ap.add_argument("--protocol",required=True)
    ap.add_argument("--discovery",required=True)
    ap.add_argument("--arb",required=True)
    ap.add_argument("--output",required=True)
    a=ap.parse_args()
    protocol_path=Path(a.protocol)
    discovery_path=Path(a.discovery)
    arb_path=Path(a.arb)
    protocol=json.loads(protocol_path.read_text(encoding="utf-8"))
    discovery=json.loads(discovery_path.read_text(encoding="utf-8"))
    arb=json.loads(arb_path.read_text(encoding="utf-8"))
    checkout_head=git("rev-parse","HEAD")
    tree=git("rev-parse","HEAD^{tree}")
    event_path=os.environ.get("GITHUB_EVENT_PATH")
    event={}
    if event_path and Path(event_path).is_file():
        event=json.loads(Path(event_path).read_text(encoding="utf-8"))
    pr=event.get("pull_request") if isinstance(event,dict) else None
    base_sha=pr["base"]["sha"] if pr else None
    pr_head=pr["head"]["sha"] if pr else checkout_head
    pr_head_tree=None
    if pr:
        try:
            pr_head_tree=git("rev-parse",f"{pr_head}^{{tree}}")
        except subprocess.CalledProcessError:
            raise SystemExit(
                "generated-contact receipt: PR head object unavailable; "
                "checkout must use fetch-depth >= 2"
            )
    status=git("status","--porcelain")
    if status:
        raise SystemExit("generated-contact receipt: working tree is not clean")
    files={}
    for rel in TRACKED:
        p=ROOT/rel
        if not p.is_file():
            raise SystemExit(f"generated-contact receipt: missing tracked input {rel}")
        files[rel]=sha256(p)
    out={
        "schema_version":"POST281_GENERATED_CONTACT_EXECUTION_RECEIPT_v1",
        "claim_cap":"EXECUTION_INTEGRITY_ONLY",
        "git":{"checkout_sha":checkout_head,"pr_head_sha":pr_head,
               "pr_head_tree":pr_head_tree,
               "base_sha":base_sha,"checkout_tree":tree,"base_pr":281,
               "base_merge":protocol.get("base_merge"),
               "synthetic_merge_checkout": checkout_head != pr_head},
        "protocol_sha256":sha256(protocol_path),
        "discovery_sha256":sha256(discovery_path),
        "arb_sha256":sha256(arb_path),
        "tracked_input_sha256":dict(sorted(files.items())),
        "runtime_versions":{
            name: importlib.metadata.version(name)
            for name in ("numpy","scipy","python-flint")
        },
        "discovery_summary":discovery.get("summary"),
        "arb_summary":arb.get("summary"),
        "formal_status_note":
          "Lean theorem authority is determined only by compiler/axiom/proof-escape gates on this exact source tree.",
        "terminal_claim":"RH_OPEN",
        "theorem_promotion":False,
    }
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"checkout_sha":checkout_head,"pr_head_sha":pr_head,"tree":tree,
      "protocol_sha256":out["protocol_sha256"],
      "discovery_sha256":out["discovery_sha256"],
      "arb_sha256":out["arb_sha256"],
      "terminal_claim":"RH_OPEN"},indent=2,sort_keys=True))
    return 0

if __name__=="__main__":
    raise SystemExit(main())
