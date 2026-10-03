#!/usr/bin/env python3
"""Frozen post-#282 contact-calculus campaign driver."""
from __future__ import annotations
import argparse,json
from pathlib import Path
from canonical_contact_balance_arb import campaign


def validate_protocol(p:dict)->None:
    if p.get("schema_version")!="POST282_CONTACT_CALCULUS_PROTOCOL_v1":
        raise SystemExit("post282 protocol: bad schema")
    if p.get("claim_cap")!="EXPERIMENTAL_SIGNAL_ONLY":
        raise SystemExit("post282 protocol: claim cap")
    if p.get("base_merge")!="01871f7d2256b1eac2dbd7967346954367c8eef9":
        raise SystemExit("post282 protocol: wrong merged base")
    if p.get("terminal_claim")!="RH_OPEN":
        raise SystemExit("post282 protocol: terminal claim")
    if p.get("precision_bits")!=[192,384,768]:
        raise SystemExit("post282 protocol: precision ladder drift")
    seams=p.get("seam_controls")
    if not isinstance(seams,list) or not seams:
        raise SystemExit("post282 protocol: empty seam controls")
    selected=p.get("selected_neighborhoods")
    if not isinstance(selected,list) or len(selected)!=11:
        raise SystemExit("post282 protocol: exact #282 selected panel must contain 11 cases")
    if sum(1 for x in selected if x.get("reason")=="sign_bracket")!=4:
        raise SystemExit("post282 protocol: selected bracket count drift")
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
