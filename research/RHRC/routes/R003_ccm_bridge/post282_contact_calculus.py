#!/usr/bin/env python3
"""Frozen post-#282 contact-calculus campaign driver."""
from __future__ import annotations
import argparse,json
from pathlib import Path
from canonical_contact_balance_arb import campaign


def _strict_fraction_pair(value,label):
    if not (isinstance(value,list) and len(value)==2):
        raise SystemExit(f"post282 protocol: {label} must be [num,den]")
    n,d=value
    if (not isinstance(n,int) or isinstance(n,bool)
            or not isinstance(d,int) or isinstance(d,bool) or d<=0):
        raise SystemExit(f"post282 protocol: {label} must be exact integer fraction")
    if n<0 or n>d:
        raise SystemExit(f"post282 protocol: {label} outside cell")
    return (n,d)


def validate_protocol(p:dict)->None:
    if p.get("schema_version")!="POST282_CONTACT_CALCULUS_PROTOCOL_v1":
        raise SystemExit("post282 protocol: bad schema")
    if p.get("claim_cap")!="EXPERIMENTAL_SIGNAL_ONLY":
        raise SystemExit("post282 protocol: claim cap")
    if p.get("base_merge")!="01871f7d2256b1eac2dbd7967346954367c8eef9":
        raise SystemExit("post282 protocol: wrong merged base")
    if p.get("base_tree")!="c7749d37c4b63270818c3fb0d7fb5dbc22638790":
        raise SystemExit("post282 protocol: wrong frozen source tree")
    if p.get("terminal_claim")!="RH_OPEN":
        raise SystemExit("post282 protocol: terminal claim")
    if p.get("precision_bits")!=[192,384,768]:
        raise SystemExit("post282 protocol: precision ladder drift")
    if p.get("refinement_cap_per_neighborhood")!=96:
        raise SystemExit("post282 protocol: refinement cap drift")
    art=p.get("inherited_artifact") or {}
    expected_art={
        "run_id":37149698793,
        "artifact_id":11282789337,
        "zip_sha256":"67a8dc2e766e2c7ea6ec02809ade4e4d530b055be382901637368e4cf9711e39",
        "discovery_sha256":"9cd30f99a1841e5ef70951f1339ff18b9b9492e5273659bb560fb5e457aedd0a",
        "arb_sha256":"e137b8db0c726085c1fc9875efa778ff115de705c26fd1205154133541baea29",
    }
    for k,v in expected_art.items():
        if art.get(k)!=v:
            raise SystemExit(f"post282 protocol: inherited artifact provenance drift: {k}")
    seams=p.get("seam_controls")
    if not isinstance(seams,list) or not seams:
        raise SystemExit("post282 protocol: empty seam controls")
    selected=p.get("selected_neighborhoods")
    if not isinstance(selected,list) or len(selected)!=11:
        raise SystemExit("post282 protocol: exact #282 selected panel must contain 11 cases")
    if sum(1 for x in selected if x.get("reason")=="sign_bracket")!=4:
        raise SystemExit("post282 protocol: selected bracket count drift")
    if any(x.get("model")!="CANONICAL" for x in selected):
        raise SystemExit("post282 protocol: noncanonical selected model")
    keys=[]
    for i,row in enumerate(selected):
        if not isinstance(row.get("Q"),int) or isinstance(row.get("Q"),bool) or row["Q"]<1:
            raise SystemExit("post282 protocol: bad selected Q")
        if not isinstance(row.get("K"),int) or isinstance(row.get("K"),bool) or row["K"]<2:
            raise SystemExit("post282 protocol: bad selected K")
        if row.get("reason")=="sign_bracket":
            left=_strict_fraction_pair(row.get("fraction_left"),f"selected[{i}].fraction_left")
            right=_strict_fraction_pair(row.get("fraction_right"),f"selected[{i}].fraction_right")
            if left[0]*right[1] >= right[0]*left[1]:
                raise SystemExit("post282 protocol: reversed/degenerate sign bracket")
            frac_key=(left,right)
        else:
            frac_key=_strict_fraction_pair(row.get("cell_fraction"),f"selected[{i}].cell_fraction")
        keys.append((row["Q"],row["K"],row.get("reason"),frac_key))
    if len(set(map(repr,keys)))!=len(keys):
        raise SystemExit("post282 protocol: duplicate selected case")
    prov=p.get("selected_panel_provenance") or {}
    if prov.get("artifact_id")!=11282789337 or prov.get("selected_count")!=11 or prov.get("selected_sign_bracket_count")!=4:
        raise SystemExit("post282 protocol: selected provenance drift")
    n03=p.get("n03_requirements") or {}
    for k in ("independent_physical_remainder","validated_bordered_response",
              "shifted_eigenvalue_subtraction","independent_balance_comparison"):
        if n03.get(k) is not True:
            raise SystemExit(f"post282 protocol: missing N03 requirement {k}")
    n04=p.get("n04_requirements") or {}
    for k in ("frozen_state_and_reoptimized_distinguished",
              "unmatched_models_must_be_not_applicable","empty_success_payload_forbidden"):
        if n04.get(k) is not True:
            raise SystemExit(f"post282 protocol: missing N04 requirement {k}")
    for row in seams:
        if not isinstance(row.get("q"),int) or isinstance(row.get("q"),bool) or row["q"]<2:
            raise SystemExit("post282 protocol: bad q")
        if row.get("K") not in (2,3):
            raise SystemExit("post282 protocol: bad K")


def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument("--protocol",required=True)
    ap.add_argument("--output",required=True)
    a=ap.parse_args()
    p=json.loads(Path(a.protocol).read_text())
    validate_protocol(p)
    out=campaign(p)
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    return 0


if __name__=="__main__":
    raise SystemExit(main())
