#!/usr/bin/env python3
"""Strict compiler-exported public type comparison across the two epochs.
Generated/private helper names and the retired tactic engine are excluded by TypeSurface.lean.
A representation difference is a review blocker, never silently waived."""
import json, pathlib, sys
from receipts import require, digest
P=pathlib.Path
def load(path):
    rows=json.loads(path.read_text())
    out={(r["module"],r["name"]): (r["kind"],r["type_expr"]) for r in rows}
    require(len(out)==len(rows)>0,"empty/duplicate public type surface")
    return out
a,b,out=map(P,sys.argv[1:4]);x,y=load(a),load(b)
missing=sorted(set(x)-set(y));extra=sorted(set(y)-set(x))
changed=sorted(k for k in set(x)&set(y) if x[k]!=y[k])
r={"schema":"NATIVE_R2_PUBLIC_TYPE_COMPARISON","historical_sha256":digest(a),
   "common_sha256":digest(b),"historical_count":len(x),"common_count":len(y),
   "missing":missing,"extra":extra,"changed":changed,
   "status":"PASS" if not (missing or extra or changed) else "REVIEW_REQUIRED","claim":"RH_OPEN"}
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(r,indent=2)+"\n")
print(json.dumps(r))
require(r["status"]=="PASS","cross-epoch type surface differs; inspect exact declarations")
