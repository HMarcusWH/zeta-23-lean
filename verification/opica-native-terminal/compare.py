#!/usr/bin/env python3
import json, pathlib, sys
P=pathlib.Path
def require(b,m):
    if not b:raise RuntimeError(m)
a,b=map(P,sys.argv[1:3])
roots=[
"Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds",
"Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_zero_of_critical_line",
"Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_zero_of_critical_line",
"Zeta23Arithmetic.Principal.principal_weighted_upper","Zeta23Arithmetic.Principal.principal_fixed_strip",
"Zeta23.OPICANativeTerminal.both_parity_zero_floor_arithmetic",
"Zeta23.OPICANativeTerminal.step4C1_native_arithmetic",
"Zeta23.OPICANativeTerminal.riemannHypothesis_step4_native_arithmetic"]
require(json.loads((a/"source.json").read_text())==json.loads((b/"source.json").read_text()),"source staging receipts differ")
for path in (a,b):
    require((path/"kernel-pass.txt").is_file(),"missing successful build/replay marker")
    require({p.stem for p in (path/"audit").glob("*.json")}==set(roots),"wrong root receipt set")
for root in roots:
    x=json.loads((a/"audit"/(root+".json")).read_text())
    y=json.loads((b/"audit"/(root+".json")).read_text())
    for q in (x,y):
        q["dependencies"]=sorted(q["dependencies"],key=lambda r:r["name"])
        q["axioms"]=sorted(q["axioms"])
        q["required"]=sorted(q["required"])
        require(q["root"]==root,"root identity drift")
        require(set(q["axioms"])<={"propext","Classical.choice","Quot.sound"},"axiom drift")
        require(q["count"]==len(q["dependencies"]),"dependency count drift")
        require(len({d["name"] for d in q["dependencies"]})==q["count"],"duplicate dependency")
        require(set(q["required"])<={d["name"] for d in q["dependencies"]},"required root missing")
    require(x==y,"independent stock receipts differ for "+root)
print("NATIVE_INDEPENDENT_STOCK_REPLAY_MATCH",len(roots))
