#!/usr/bin/env python3
import json, pathlib, sys, hashlib
P=pathlib.Path
def require(b,m):
    if not b:raise RuntimeError(m)
a,b=map(P,sys.argv[1:3])
roots=[
"eventually_primeError_le_rpow","entireL_ne_zero_of_primeError_le",
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
edge_roots=["eventually_primeError_le_rpow","Zeta23.OPICANativeTerminal.riemannHypothesis_step4_native_arithmetic"]
def graph_digest(path,root):
    receipt=json.loads((path/"audit"/(root+".json")).read_text())
    members={d["name"]:d["module"] for d in receipt["dependencies"]}
    member_names=set(members)
    rows={}
    with (path/"audit"/(root+".edges.jsonl")).open() as f:
        for line in f:
            row=json.loads(line);n=row["name"]
            require(n not in rows and members.get(n)==row["module"],"edge origin/membership drift")
            for k in ("type_refs","value_refs","structural_refs"):
                row[k]=sorted(set(row[k]))
                require(set(row[k])<=member_names,"edge leaves closure "+n)
            rows[n]=hashlib.sha256(json.dumps(row,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    require(set(rows)==set(members),"edge coverage incomplete")
    digest=hashlib.sha256()
    for n in sorted(rows):digest.update((n+"\0"+rows[n]+"\n").encode())
    return digest.hexdigest()
for root in edge_roots:
    x=graph_digest(a,root);y=graph_digest(b,root)
    require(x==y,"independent proof graph drift "+root)
    print("NATIVE_PROOF_GRAPH_MATCH",root,x)
print("NATIVE_INDEPENDENT_STOCK_REPLAY_MATCH",len(roots))
