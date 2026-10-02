#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,math
from pathlib import Path

def walk(x):
    if isinstance(x,dict):
        for v in x.values(): yield from walk(v)
    elif isinstance(x,list):
        for v in x: yield from walk(v)
    elif isinstance(x,float):
        yield x

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--discovery",required=True); ap.add_argument("--arb",required=True); a=ap.parse_args()
    d=json.loads(Path(a.discovery).read_text()); r=json.loads(Path(a.arb).read_text())
    assert d["claim_cap"]=="EXPERIMENTAL_SIGNAL_ONLY"
    assert d["summary"]["terminal_claim"]=="RH_OPEN" and not d["summary"]["contact_claimed"]
    assert len(d["selected_neighborhoods"])<=d["protocol"]["discovery"]["additional_neighborhood_cap"]
    assert all(math.isfinite(x) for x in walk(d))
    assert r["claim_cap"]=="EXPERIMENTAL_SIGNAL_ONLY" and r["summary"]["terminal_claim"]=="RH_OPEN"
    assert r["summary"].get("first_boundary_certified_count",0)==0
    allowed={"NEAR_CONTACT_PROXY","CERTIFIED_SIGN_BRACKET"}
    assert all(row["contact_status"] in allowed for row in r["rows"])
    assert all(not row.get("first_boundary_claimed",False) for row in r["rows"])
    assert all(math.isfinite(x) for x in walk(r))
    print("post281 generated-contact results: PASS")
    return 0
if __name__=="__main__": raise SystemExit(main())
