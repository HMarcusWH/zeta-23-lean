#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,math,sys
from pathlib import Path

ALLOWED_CONTACT={"NEAR_CONTACT_PROXY","CERTIFIED_SIGN_BRACKET"}

def fail(code,msg):
    raise SystemExit(f"post281 generated-contact results: {code}: {msg}")

def walk(x):
    if isinstance(x,dict):
        for v in x.values(): yield from walk(v)
    elif isinstance(x,list):
        for v in x: yield from walk(v)
    elif isinstance(x,float):
        yield x

def finite_payload(x,name):
    bad=[v for v in walk(x) if not math.isfinite(v)]
    if bad: fail("NONFINITE",f"{name} contains nonfinite floats")

def key(c):
    return json.dumps(c,sort_keys=True,separators=(",",":"))

def validate_discovery(d):
    if not isinstance(d,dict): fail("DISCOVERY_TYPE","discovery must be object")
    if d.get("claim_cap")!="EXPERIMENTAL_SIGNAL_ONLY": fail("CLAIM_CAP","bad discovery claim cap")
    s=d.get("summary")
    if not isinstance(s,dict): fail("SUMMARY","missing discovery summary")
    if s.get("terminal_claim")!="RH_OPEN" or s.get("contact_claimed") is not False:
        fail("CLAIM_FIREWALL","discovery claim firewall violated")
    rows=d.get("measurements")
    if not isinstance(rows,list) or not rows: fail("EMPTY_DISCOVERY","measurements must be nonempty")
    if s.get("measurement_count")!=len(rows): fail("COUNT_MISMATCH","measurement count")
    selected=d.get("selected_neighborhoods")
    if not isinstance(selected,list) or not selected: fail("EMPTY_SELECTION","selection must be nonempty")
    cap=d.get("protocol",{}).get("discovery",{}).get("additional_neighborhood_cap")
    if not isinstance(cap,int) or len(selected)>cap: fail("SELECTION_CAP","selection cap violated")
    if s.get("selected_count")!=len(selected): fail("COUNT_MISMATCH","selected count")
    keys=[key(x) for x in selected]
    if len(keys)!=len(set(keys)): fail("DUPLICATE_SELECTION","duplicate selected candidate")
    finite_payload(d,"discovery")
    return selected

def validate_point(p,label):
    if not isinstance(p,dict): fail("POINT",f"{label} missing")
    if p.get("global_sign") not in {"POSITIVE","NEGATIVE","UNRESOLVED"}:
        fail("POINT_SIGN",f"{label} invalid global sign")
    attempts=p.get("attempts")
    if not isinstance(attempts,list) or not attempts: fail("POINT_ATTEMPTS",f"{label} no attempts")
    spec=p.get("exact_cell_spec")
    if not isinstance(spec,dict): fail("EXACT_COORD",f"{label} lacks exact cell spec")
    frac=spec.get("fraction")
    if not (isinstance(frac,list) and len(frac)==2 and all(type(x) is int for x in frac)):
        fail("EXACT_COORD",f"{label} bad fraction")
    if frac[1]<=0 or not 0<frac[0]<frac[1]: fail("EXACT_COORD",f"{label} illegal fraction")

def validate_arb(r,selected):
    if not isinstance(r,dict): fail("ARB_TYPE","arb payload must be object")
    if r.get("claim_cap")!="EXPERIMENTAL_SIGNAL_ONLY": fail("CLAIM_CAP","bad arb claim cap")
    s=r.get("summary")
    rows=r.get("rows")
    if not isinstance(s,dict) or s.get("terminal_claim")!="RH_OPEN":
        fail("CLAIM_FIREWALL","arb terminal claim")
    if not isinstance(rows,list) or not rows: fail("EMPTY_ARB","arb rows must be nonempty")
    if s.get("row_count")!=len(rows) or len(rows)!=len(selected):
        fail("COUNT_MISMATCH","arb row count")
    selected_keys={key(x) for x in selected}
    seen=set()
    cert=0
    for i,row in enumerate(rows):
        if not isinstance(row,dict): fail("ROW_TYPE",f"row {i}")
        cand=row.get("candidate")
        ck=key(cand)
        if ck not in selected_keys: fail("CANDIDATE_MISMATCH",f"row {i}")
        if ck in seen: fail("DUPLICATE_ARB_ROW",f"row {i}")
        seen.add(ck)
        status=row.get("contact_status")
        if status not in ALLOWED_CONTACT: fail("CONTACT_STATUS",f"row {i}: {status}")
        if row.get("first_boundary_claimed") is not False:
            fail("FIRST_BOUNDARY","first-boundary claim forbidden")
        if status=="CERTIFIED_SIGN_BRACKET":
            cert+=1
            validate_point(row.get("left"),f"row {i} left")
            validate_point(row.get("right"),f"row {i} right")
            if {row["left"]["global_sign"],row["right"]["global_sign"]}!={"POSITIVE","NEGATIVE"}:
                fail("FALSE_BRACKET",f"row {i} endpoints not opposite")
            exact=row.get("final_bracket_exact")
            if not (isinstance(exact,list) and len(exact)==2):
                fail("BRACKET_COORD",f"row {i} missing exact bracket")
        else:
            point=row.get("point")
            if point is not None: validate_point(point,f"row {i} point")
    if s.get("certified_sign_bracket_count")!=cert:
        fail("COUNT_MISMATCH","certified bracket count")
    if s.get("first_boundary_certified_count")!=0:
        fail("FIRST_BOUNDARY","first-boundary count must be zero")
    controls=r.get("generic_control_certificates")
    if not isinstance(controls,list) or not controls:
        fail("CONTROL_QUALIFICATION","generic control certificates missing")
    if not all(c.get("qualification_pass") is True and c.get("canonical_arithmetic_authority") is False for c in controls):
        fail("CONTROL_QUALIFICATION","generic control qualification failed")
    finite_payload(r,"arb")

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--discovery",required=True)
    ap.add_argument("--arb",required=True)
    a=ap.parse_args()
    try:
        d=json.loads(Path(a.discovery).read_text())
        r=json.loads(Path(a.arb).read_text())
    except (OSError,json.JSONDecodeError) as exc:
        fail("READ",str(exc))
    selected=validate_discovery(d)
    validate_arb(r,selected)
    print("post281 generated-contact results: PASS")
    return 0

if __name__=="__main__":
    raise SystemExit(main())
