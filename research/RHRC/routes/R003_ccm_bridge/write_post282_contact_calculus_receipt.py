#!/usr/bin/env python3
from __future__ import annotations
import argparse,hashlib,importlib.metadata,json,subprocess
from pathlib import Path
ROUTE=Path(__file__).resolve().parent
ROOT=ROUTE.parents[3]
TRACKED=[
"Zeta23/CCM/CanonicalCompressedApertureC2.lean","Zeta23/CCM/ProductionWeightedTestCalculus.lean",
"Zeta23/CCM/StationarySchurContact.lean","Zeta23/CCM/FirstCrossingInheritedStationarity.lean",
"Zeta23/RHRC/ContactCalculusContract.lean","Zeta23/CCM/FirstCrossingProductionFirstVariation.lean",
"Zeta23/CCM/FirstCrossingProductionResponse.lean","Zeta23/CCM/FirstCrossingProductionCurvatureBridge.lean",
"Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean","research/RHRC/closure_batch/interval_codec.py",
"research/RHRC/routes/R003_ccm_bridge/canonical_contact_balance_arb.py",
"research/RHRC/routes/R003_ccm_bridge/canonical_contact_frontier_arb.py",
"research/RHRC/routes/R003_ccm_bridge/certify_post281_generated_contact_frontier.py",
"research/RHRC/routes/R003_ccm_bridge/post194_fb05_q14_fixed_unit_second_derivative.py",
"research/RHRC/routes/R003_ccm_bridge/post247_remainder_budget_ratio_scout.py",
"research/RHRC/routes/R003_ccm_bridge/post280_saturation_frontier.py",
"research/RHRC/routes/R003_ccm_bridge/post282_contact_calculus.py",
"research/RHRC/routes/R003_ccm_bridge/fixtures/post282_contact_calculus_v1.json"]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(["git",*a],cwd=ROOT,text=True).strip()
def main()->int:
 ap=argparse.ArgumentParser();ap.add_argument("--protocol",required=True);ap.add_argument("--results",required=True);ap.add_argument("--output",required=True);a=ap.parse_args()
 if git("status","--porcelain"):raise SystemExit("post282 receipt: working tree dirty")
 files={}
 for rel in TRACKED:
  p=ROOT/rel
  if not p.is_file():raise SystemExit(f"post282 receipt: missing {rel}")
  files[rel]=sha(p)
 result=json.loads(Path(a.results).read_text());rows=result.get("balance_rows") or []
 coverage={"selected_case_ids":[r.get("candidate") for r in rows],"selected_count":len(rows),
 "seam_control_count":len(result.get("seam_controls") or []),
 "quantity_resolution":{"response_certified":sum(1 for r in rows if r.get("response",{}).get("status") in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}),
 "Q_overlap":sum(1 for r in rows if r.get("Q",{}).get("overlap") is True),
 "physical_remainder_certified":sum(1 for r in rows if r.get("physical_remainder",{}).get("status")=="CERTIFIED"),
 "curvature_certified":sum(1 for r in rows if r.get("curvature",{}).get("status")=="CERTIFIED_FROM_JETS_AND_RESPONSE")},
 "hypothesis_dispositions":result.get("hypothesis_dispositions")}
 out={"schema_version":"POST282_CONTACT_CALCULUS_RECEIPT_v2","claim_cap":"EXECUTION_INTEGRITY_ONLY",
 "git":{"checkout_sha":git("rev-parse","HEAD"),"checkout_tree":git("rev-parse","HEAD^{tree}"),"base_merge":"01871f7d2256b1eac2dbd7967346954367c8eef9"},
 "protocol_sha256":sha(Path(a.protocol)),"results_sha256":sha(Path(a.results)),
 "tracked_input_sha256":dict(sorted(files.items())),
 "runtime_versions":{n:importlib.metadata.version(n) for n in ("numpy","scipy","python-flint")},
 "coverage":coverage,"theorem_promotion":False,"terminal_claim":"RH_OPEN"}
 Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n");print(json.dumps({"git":out["git"],"coverage":coverage},indent=2,sort_keys=True));return 0
if __name__=="__main__":raise SystemExit(main())
