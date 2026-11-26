#!/usr/bin/env python3
"""Compare compiler-exported public types; require coverage of every mathematical overlay."""
import json, pathlib, sys, tempfile
from receipts import require, digest
P=pathlib.Path
HERE=P(__file__).resolve().parent
OVERLAY=HERE/"compatibility/lean-4.35.0/OVERLAY_MANIFEST.json"
def expected_modules():
    rows=json.loads(OVERLAY.read_text())["replacements"]
    modules={r["destination"].removesuffix(".lean").replace("/", ".") for r in rows}
    require(len(modules)==17 and "Zeta23.FromPNTPlus.Tactic.AdditiveCombination" in modules,
            "overlay module inventory drift")
    return modules-{"Zeta23.FromPNTPlus.Tactic.AdditiveCombination"}
def load(path):
    rows=json.loads(path.read_text())
    out={(r["module"],r["name"]):(r["kind"],r["type_expr"]) for r in rows}
    require(len(out)==len(rows)>0,"empty/duplicate public type surface")
    require({m for m,_ in out}==expected_modules(),"incomplete/unexpected public module coverage")
    require(all(n and k and t for (_,n),(k,t) in out.items()),"empty declaration identity")
    return out
def comparison(a,b):
    x,y=load(a),load(b)
    missing=sorted(set(x)-set(y));extra=sorted(set(y)-set(x))
    changed=sorted(k for k in set(x)&set(y) if x[k]!=y[k])
    return {"schema":"NATIVE_R5_PUBLIC_TYPE_COMPARISON","historical_sha256":digest(a),
       "common_sha256":digest(b),"historical_count":len(x),"common_count":len(y),
       "modules":sorted(expected_modules()),
       "missing":[list(k) for k in missing],"extra":[list(k) for k in extra],
       "changed":[list(k) for k in changed],
       "status":"PASS" if not (missing or extra or changed) else "REVIEW_REQUIRED","claim":"RH_OPEN"}
def self_test():
    def reject(f):
        try: f()
        except (RuntimeError,KeyError,ValueError): return
        raise RuntimeError("type surface negative control accepted")
    rows=[{"module":m,"name":m+".example","kind":"theorem","type_expr":"True"} for m in sorted(expected_modules())]
    with tempfile.TemporaryDirectory() as d:
        a,b=P(d)/"a.json",P(d)/"b.json"
        a.write_text(json.dumps(rows));b.write_text(json.dumps(rows))
        require(comparison(a,b)["status"]=="PASS","positive control failed")
        b.write_text(json.dumps(rows[:-1]));reject(lambda:comparison(a,b))
        b.write_text(json.dumps(rows+[rows[0]]));reject(lambda:comparison(a,b))
        wrong=[dict(r) for r in rows];wrong[0]["module"]="Unexpected"
        b.write_text(json.dumps(wrong));reject(lambda:comparison(a,b))
        wrong=[dict(r) for r in rows];wrong[0]["type_expr"]="False"
        b.write_text(json.dumps(wrong));require(comparison(a,b)["status"]=="REVIEW_REQUIRED","changed type accepted")
    print("NATIVE_R5_TYPE_CONTROLS_PASS 4")
if __name__=="__main__":
    if sys.argv[1:]==["--self-test"]: self_test()
    else:
        require(len(sys.argv)==4,"expected historical, common and output paths")
        a,b,out=map(P,sys.argv[1:])
        r=comparison(a,b)
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(json.dumps(r,indent=2)+"\n")
        print(json.dumps(r))
        require(r["status"]=="PASS","cross-epoch type surface differs; inspect exact declarations")
