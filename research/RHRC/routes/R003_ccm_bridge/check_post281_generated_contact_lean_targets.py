#!/usr/bin/env python3
"""Build every #282 Lean target independently and emit a concise failure receipt."""
from __future__ import annotations
import argparse,json,re,subprocess
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
GROUPS={
 "generated":[
  "Zeta23.CCM.GlobalParityFirstNegativeBoundary",
  "Zeta23.CCM.FirstCrossingGlobalAlignment",
  "Zeta23.ExceptionalZero.GlobalParityFirstNegativeBoundary",
 ],
 "production":[
  "Zeta23.CCM.FirstCrossingProductionTests",
  "Zeta23.CCM.FirstCrossingProductionRemainder",
  "Zeta23.CCM.FirstCrossingProductionFirstVariation",
  "Zeta23.CCM.FirstCrossingProductionResponse",
  "Zeta23.CCM.FirstCrossingProductionCurvatureBridge",
  "Zeta23.CCM.FirstCrossingGeneratedStrictEvenFrontier",
 ],
}
ERR=re.compile(r"(^|\n)(error: .*|.*\.lean:\d+:\d+: error:.*)",re.M)

def main():
 ap=argparse.ArgumentParser(); ap.add_argument("--group",choices=GROUPS,required=True); ap.add_argument("--output",required=True); a=ap.parse_args()
 rows=[]; failed=False
 for module in GROUPS[a.group]:
  p=subprocess.run(["lake","build",module],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  matches=ERR.findall(p.stdout)
  first=matches[0][1].strip() if matches else None
  rows.append({"module":module,"returncode":p.returncode,"first_error":first})
  print(f"{module}: {'PASS' if p.returncode==0 else 'FAIL'}")
  if first: print("  "+first)
  failed |= p.returncode!=0
 out={"schema_version":"POST281_LEAN_TARGET_RECEIPT_v1","group":a.group,"rows":rows,"all_passed":not failed,"terminal_claim":"RH_OPEN"}
 Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
 return 1 if failed else 0
if __name__=="__main__": raise SystemExit(main())
