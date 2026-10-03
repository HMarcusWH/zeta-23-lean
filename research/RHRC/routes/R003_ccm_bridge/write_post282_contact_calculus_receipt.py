#!/usr/bin/env python3
from __future__ import annotations
import argparse,hashlib,importlib.metadata,json,subprocess
from pathlib import Path

ROUTE=Path(__file__).resolve().parent
ROOT=ROUTE.parents[3]
TRACKED=[
 "Zeta23/CCM/CanonicalCompressedApertureC2.lean",
 "Zeta23/CCM/ProductionWeightedTestCalculus.lean",
 "Zeta23/CCM/StationarySchurContact.lean",
 "Zeta23/CCM/FirstCrossingInheritedStationarity.lean",
 "Zeta23/RHRC/ContactCalculusContract.lean",
 "Zeta23/CCM/FirstCrossingProductionFirstVariation.lean",
 "Zeta23/CCM/FirstCrossingProductionResponse.lean",
 "Zeta23/CCM/FirstCrossingProductionCurvatureBridge.lean",
 "Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean",
 "research/RHRC/closure_batch/interval_codec.py",
 "research/RHRC/routes/R003_ccm_bridge/canonical_contact_balance_arb.py",
 "research/RHRC/routes/R003_ccm_bridge/post282_contact_calculus.py",
 "research/RHRC/routes/R003_ccm_bridge/fixtures/post282_contact_calculus_v1.json",
]

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(["git",*args],cwd=ROOT,text=True).strip()

def main()->int:
 ap=argparse.ArgumentParser()
 ap.add_argument("--protocol",required=True); ap.add_argument("--results",required=True); ap.add_argument("--output",required=True)
 a=ap.parse_args()
 status=git("status","--porcelain")
 if status: raise SystemExit("post282 receipt: working tree dirty")
 files={}
 for rel in TRACKED:
   p=ROOT/rel
   if not p.is_file(): raise SystemExit(f"post282 receipt: missing {rel}")
   files[rel]=sha(p)
 out={
  "schema_version":"POST282_CONTACT_CALCULUS_RECEIPT_v1",
  "claim_cap":"EXECUTION_INTEGRITY_ONLY",
  "git":{"checkout_sha":git("rev-parse","HEAD"),"checkout_tree":git("rev-parse","HEAD^{tree}"),
         "base_merge":"01871f7d2256b1eac2dbd7967346954367c8eef9"},
  "protocol_sha256":sha(Path(a.protocol)),
  "results_sha256":sha(Path(a.results)),
  "tracked_input_sha256":dict(sorted(files.items())),
  "runtime_versions":{n:importlib.metadata.version(n) for n in ("numpy","scipy","python-flint")},
  "theorem_promotion":False,"terminal_claim":"RH_OPEN"}
 Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
 print(json.dumps(out["git"],indent=2,sort_keys=True))
 return 0
if __name__=="__main__": raise SystemExit(main())
