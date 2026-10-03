#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,math
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
ROUTE=Path(__file__).resolve().parent
NEW_LEAN=[
 "Zeta23/CCM/CanonicalCompressedApertureC2.lean",
 "Zeta23/CCM/ProductionWeightedTestCalculus.lean",
 "Zeta23/CCM/StationarySchurContact.lean",
 "Zeta23/CCM/FirstCrossingInheritedStationarity.lean",
 "Zeta23/RHRC/ContactCalculusContract.lean",
]
REQUIRED_SYMBOLS={
 "Zeta23/CCM/CanonicalCompressedApertureC2.lean":[
   "canonicalParityCompressedC2_proved","canonicalEvenCompressedC2_proved",
   "canonicalEvenApertureFirst"],
 "Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean":[
   "production_frontier","firstVariation_eq_zero_of_inherited",
   "production_stationary_saturation"],
 "Zeta23/CCM/FirstCrossingProductionCurvatureBridge.lean":[
   "canonicalSecondPairing_euler_eq_productionSaturationGap",
   "canonicalOptimizedContactCurvature"],
}


def fail(code,msg): raise SystemExit(f"POST282 CONTACT CALCULUS CONTRACT: FAIL {code}: {msg}")

def check_surface()->None:
    for rel in NEW_LEAN:
        if not (ROOT/rel).is_file(): fail("MISSING",rel)
    for rel,tokens in REQUIRED_SYMBOLS.items():
        text=(ROOT/rel).read_text()
        miss=[x for x in tokens if x not in text]
        if miss: fail("SYMBOL",f"{rel}: {miss}")
    frontier=(ROOT/"Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean").read_text()
    tail=frontier[frontier.find("theorem GeneratedStrictEvenContact.production_frontier"):]
    for forbidden in ("hbridge :","hkappa :","EvenProductionContactC2Realized"):
        if forbidden in tail: fail("PREMISE",forbidden)

def check_results(path:Path)->None:
    d=json.loads(path.read_text())
    if d.get("schema_version")!="POST282_CONTACT_BALANCE_ARB_v1": fail("SCHEMA","results")
    if d.get("claim_cap")!="EXPERIMENTAL_SIGNAL_ONLY": fail("CLAIM_CAP","results")
    s=d.get("summary") or {}
    if s.get("terminal_claim")!="RH_OPEN" or s.get("theorem_promotion") is not False:
        fail("FIREWALL","results")
    if s.get("calibration_qualified") is not True:
        fail("VACUOUS","K2/log2 calibration did not qualify")
    if s.get("selected_count")!=11 or s.get("selected_sign_bracket_count")!=4:
        fail("SELECTION","frozen #282 selected-panel identity drift")
    rows=d.get("selected_replay")
    if not isinstance(rows,list) or len(rows)!=11:
        fail("SELECTION","selected replay missing")
    if any(r.get("first_boundary_claimed") is not False for r in rows):
        fail("FIRST_BOUNDARY","finite replay may not claim first boundary")
    cal=d.get("calibration") or {}
    if not all(cal.get(k) is True for k in ("value_overlap","first_overlap","second_overlap")):
        fail("SEAM","compressed seam jets do not overlap")


def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument("--results")
    a=ap.parse_args()
    check_surface()
    if a.results: check_results(Path(a.results))
    print("POST282 CONTACT CALCULUS CONTRACT: PASS")
    return 0

if __name__=="__main__": raise SystemExit(main())
