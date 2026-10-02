#!/usr/bin/env python3
from __future__ import annotations
import argparse,json
from pathlib import Path
from post281_generated_contact_frontier import validate_protocol

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--protocol",required=True); a=ap.parse_args()
    p=json.loads(Path(a.protocol).read_text()); validate_protocol(p)
    d=p["discovery"]
    assert d["forbidden_selection_features"]==["rho_distance_to_one","preferred_delta_sign"]
    assert p["arb"]["precision_bits"]==[192,384,768]
    assert p["arb"]["root_or_subdivision_cap_per_neighborhood"]==96
    assert len(p["legacy_replay"]["cases"])==11
    print("post281 generated-contact scope: PASS")
    return 0
if __name__=="__main__": raise SystemExit(main())
