#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,math
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
ROUTE=Path(__file__).resolve().parent
NEW_LEAN=[
 "Zeta23/CCM/CanonicalCompressedSeamJets.lean",
 "Zeta23/CCM/CanonicalFrozenApertureC2.lean",
 "Zeta23/CCM/CanonicalCompressedApertureC2.lean",
 "Zeta23/CCM/ProductionWeightedTestCalculus.lean",
 "Zeta23/CCM/StationarySchurContact.lean",
 "Zeta23/CCM/FirstCrossingInheritedStationarity.lean",
 "Zeta23/RHRC/ContactCalculusContract.lean",
]
REQUIRED_SYMBOLS={
 "Zeta23/CCM/CanonicalCompressedSeamJets.lean":[
   "hasDerivAt_sourceMatrix_primeSourceCoordinate",
   "primeSourceMatrixFirstApertureJet_log_mulVec_zero",
   "primeSourceMatrixSecondApertureJet_log_mulVec_zero"],
 "Zeta23/CCM/CanonicalFrozenApertureC2.lean":[
   "hasDerivAt_parityCompressedCanonicalCLM_pos",
   "hasDerivAt_productionParityFirstJetCLM_pos",
   "continuousAt_productionParitySecondJetCLM_pos"],
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
    if d.get("schema_version")!="POST282_CONTACT_BALANCE_ARB_v2": fail("SCHEMA","results")
    if d.get("claim_cap")!="EXPERIMENTAL_SIGNAL_ONLY": fail("CLAIM_CAP","results")
    s=d.get("summary") or {}
    if s.get("terminal_claim")!="RH_OPEN" or s.get("theorem_promotion") is not False:
        fail("FIREWALL","results")
    if s.get("calibration_qualified") is not True:
        fail("VACUOUS","K2/log2 calibration did not qualify")
    if s.get("selected_count")!=11 or s.get("selected_sign_bracket_count")!=4:
        fail("SELECTION","frozen #282 selected-panel identity drift")
    if s.get("balance_row_count")!=11:
        fail("BALANCE","all selected rows must receive a balance disposition")
    if s.get("certified_response_count",0)<1:
        fail("VACUOUS","no response certificate resolved")
    if s.get("independent_physical_remainder_certified_count",0)<1:
        fail("VACUOUS","no independent physical remainder certified")
    if s.get("independent_balance_overlap_count",0)<1:
        fail("BALANCE","no independently evaluated balance overlap")
    rows=d.get("selected_replay")
    if not isinstance(rows,list) or len(rows)!=11:
        fail("SELECTION","selected replay missing")
    balances=d.get("balance_rows")
    if not isinstance(balances,list) or len(balances)!=11:
        fail("BALANCE","balance rows missing")
    if not any(r.get("physical_remainder",{}).get("status")=="CERTIFIED" for r in balances):
        fail("N03","direct physical remainder lane is vacuous")
    if not all(isinstance(r.get("matched_ablations"),list) for r in balances if r.get("response")):
        fail("N04","matched ablation dispositions missing")
    for row in balances:
        abl=row.get("matched_ablations") or []
        if abl and abl[0].get("name")!="ALL":
            modes={(a.get("name"),a.get("mode")) for a in abl}
            for channel in ("DROP_POLE","DROP_ARCH","DROP_PRIME"):
                if (channel,"FROZEN_STATE") not in modes or (channel,"REOPTIMIZED") not in modes:
                    fail("N04",f"ablation modes incomplete for {channel}")
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
