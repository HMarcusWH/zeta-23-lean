#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,math,sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
ROUTE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/"research/RHRC/closure_batch"))
from interval_codec import DyadicInterval,IntervalCodecError
NEW_LEAN=[
 "Zeta23/CCM/CanonicalCompressedSeamJets.lean",
 "Zeta23/CCM/CanonicalFrozenApertureC2.lean",
 "Zeta23/CCM/CanonicalCompressedApertureC2.lean",
 "Zeta23/CCM/ProductionWeightedTestCalculus.lean",
 "Zeta23/CCM/ProductionWeightedGlobalTests.lean",
 "Zeta23/CCM/ProductionNormalSourceAuthority.lean",
 "Zeta23/CCM/FirstCrossingProductionRemainderAuthority.lean",
 "Zeta23/CCM/ProductionPhysicalFunctionalCongruence.lean",
 "Zeta23/CCM/FirstCrossingProductionRemainderValueAuthority.lean",
 "Zeta23/CCM/StationarySchurContact.lean",
 "Zeta23/CCM/FirstCrossingInheritedStationarity.lean",
 "Zeta23/CCM/FirstCrossingProductionCurvatureBridge.lean",
 "Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean",
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
   "canonicalEvenApertureFirst","canonicalEvenApertureSecond"],
 "Zeta23/CCM/ProductionWeightedGlobalTests.lean":[
   "productionFirstDerivativeTest_authority",
   "productionSecondDerivativeTest_authority",
   "productionMixedDerivativeTest_authority",
   "productionDerivativeWeightedTests_admissible"],
 "Zeta23/CCM/FirstCrossingProductionRemainderValueAuthority.lean":[
   "productionContactRemainderValue_eq_physicalTest",
   "productionContactRemainder_authority"],
 "Zeta23/CCM/StationarySchurContact.lean":[
   "stationarySchurComplement","stationarySchurBlock",
   "stationarySchurBlock_isInvertible_of_kernel_line",
   "stationarySchur_completedSquare",
   "eventually_stationarySchurBlock_nonnegative",
   "stationarySchur_contact_secondPairing_eq_zero",
   "StationarySchurContactCertificate",
   "curvature_eq_zero"],
 "Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean":[
   "production_frontier","completed_production_frontier",
   "firstVariation_eq_zero_of_inherited",
   "production_stationary_schur_curvature_eq_zero",
   "actual_stationary_curvature_eq_zero",
   "production_stationary_saturation",
   "inherited_production_saturation",
   "inherited_completed_production_frontier"],
 "Zeta23/CCM/FirstCrossingProductionCurvatureBridge.lean":[
   "canonicalFirstVariation_eq_physical",
   "canonicalFixedSecondEuler_eq_physical",
   "canonicalMixedFirstVariation_eq_physical",
   "canonicalSecondPairing_euler_eq_productionSaturationGap",
   "canonicalOptimizedContactCurvature"],
 "Zeta23/RHRC/ContactCalculusContract.lean":[
   "canonicalFirstVariation_eq_physical",
   "canonicalFixedSecondEuler_eq_physical",
   "canonicalMixedFirstVariation_eq_physical",
   "actual_stationary_curvature_eq_zero",
   "production_stationary_saturation",
   "completed_production_frontier",
   "inherited_production_saturation",
   "inherited_completed_production_frontier"],
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
    for forbidden in (
        "hbridge :", "hkappa :", "EvenProductionContactC2Realized",
        "ProductionContactCurvatureArithmeticIdentity", "remainderSource :",
        "sourceQ :", "RiemannHypothesis"
    ):
        if forbidden in tail: fail("PREMISE",forbidden)
    obligations=json.loads((ROUTE/"POST282_CONTACT_CALCULUS_OBLIGATIONS.json").read_text())
    ids=[x.get("id") for x in obligations.get("obligations",[])]
    for required in ("F01_COMPRESSED_C2","F02_WEIGHTED_TESTS",
                     "F03_REMAINDER_AUTHORITY","F04_PAIR_BALANCE",
                     "F05_STATIONARY_CURVATURE","F06_INHERITED_STATIONARITY",
                     "F07_FRONTIER","N01_EXACT_INTERVAL_CODEC",
                     "N02_INDEPENDENT_CALIBRATION",
                     "N03_RESPONSE_PHYSICAL_BALANCE",
                     "N04_MATCHED_ADVERSARIAL_CONTROLS",
                     "X01_INHERITED_RESPONSE_INVESTIGATION",
                     "X02_DILATION_RESIDUAL_INVESTIGATION"):
        if required not in ids: fail("OBLIGATION",f"missing {required}")
    by_id={x.get("id"):x for x in obligations.get("obligations",[])}
    for required in ("F01_COMPRESSED_C2","F02_WEIGHTED_TESTS",
                     "F03_REMAINDER_AUTHORITY","F04_PAIR_BALANCE",
                     "F05_STATIONARY_CURVATURE","F06_INHERITED_STATIONARITY",
                     "F07_FRONTIER","N01_EXACT_INTERVAL_CODEC",
                     "N02_INDEPENDENT_CALIBRATION",
                     "N03_RESPONSE_PHYSICAL_BALANCE",
                     "N04_MATCHED_ADVERSARIAL_CONTROLS"):
        if by_id[required].get("status")!="CANDIDATE_IMPLEMENTED_PENDING_CI":
            fail("OBLIGATION",f"{required} not recorded as implemented candidate")
    for required in ("X01_INHERITED_RESPONSE_INVESTIGATION",
                     "X02_DILATION_RESIDUAL_INVESTIGATION"):
        if by_id[required].get("status") not in {
            "CANDIDATE_IMPLEMENTED_PENDING_EXECUTION",
            "CANDIDATE_IMPLEMENTED_PENDING_CI"}:
            fail("OBLIGATION",f"{required} not recorded as implemented candidate")
    for required in ("OBS060O_SATURATION_EXCLUSION","ODD_TIE_BRANCHES","RH"):
        if by_id.get(required,{}).get("status")!="OPEN":
            fail("FIREWALL",f"{required} must remain OPEN")
    if obligations.get("claim_firewall")!="RH_OPEN":
        fail("FIREWALL","obligation ledger terminal claim drift")

    candidate_ids={
        "R003_COMPRESSED_PRODUCTION_C2":"Zeta23.CCM.canonicalEvenCompressedC2_proved",
        "R003_WEIGHTED_PRODUCTION_PAIR_BALANCE":"Zeta23.CCM.canonicalSecondPairing_euler_eq_productionSaturationGap",
        "R003_INHERITED_FIRST_VARIATION_RESTRICTION":"Zeta23.CCM.GeneratedStrictEvenContact.firstVariation_eq_zero_of_inherited",
        "R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER":"Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier",
    }
    registry=json.loads((ROOT/"research/RHRC/CLAIM_REGISTRY.json").read_text())
    claims={x.get("id"):x for x in registry.get("claims",[])}
    for cid,theorem in candidate_ids.items():
        row=claims.get(cid)
        if not isinstance(row,dict): fail("CLAIM_BINDING",f"missing {cid}")
        if row.get("status")!="OPEN" or row.get("promotion_cap")!="OPEN":
            fail("CLAIM_BINDING",f"{cid} must remain OPEN before exact-head promotion")
        if row.get("candidate_binding") is not True:
            fail("CLAIM_BINDING",f"{cid} missing candidate_binding marker")
        if row.get("theorem")!=theorem:
            fail("CLAIM_BINDING",f"{cid} theorem drift")

    promoted=json.loads((ROOT/"research/RHRC/R003_PROMOTED_BINDINGS.json").read_text())
    pc={x.get("id"):x for x in promoted.get("candidate_bindings",[])}
    registered=json.loads((ROOT/"research/RHRC/REGISTERED_THEOREM_BINDINGS.json").read_text())
    rc={x.get("id"):x for x in registered.get("candidate_bindings",[])}
    if set(pc)!=set(candidate_ids): fail("CLAIM_BINDING","R003 candidate binding inventory drift")
    if set(rc)!=set(candidate_ids): fail("CLAIM_BINDING","registered candidate binding inventory drift")
    for cid,theorem in candidate_ids.items():
        if pc[cid].get("theorem")!=theorem or pc[cid].get("status")!="OPEN_PENDING_CI":
            fail("CLAIM_BINDING",f"{cid} R003 candidate binding drift")
        if rc[cid].get("theorem")!=theorem or rc[cid].get("status")!="OPEN_PENDING_CI":
            fail("CLAIM_BINDING",f"{cid} registered candidate binding drift")

def _validate_dyadic_payload(obj,path="results")->None:
    if isinstance(obj,dict):
        if "dyadic_interval" in obj:
            try:
                d=DyadicInterval.from_json(obj["dyadic_interval"])
            except (IntervalCodecError,TypeError,KeyError) as exc:
                fail("INTERVAL",f"{path}: invalid dyadic interval: {exc}")
            if obj.get("sign") is not None and obj.get("sign")!=d.sign():
                fail("INTERVAL",f"{path}: stored sign disagrees with exact interval")
        for k,v in obj.items():
            _validate_dyadic_payload(v,f"{path}.{k}")
    elif isinstance(obj,list):
        for i,v in enumerate(obj):
            _validate_dyadic_payload(v,f"{path}[{i}]")


def _require_certified_payload(node:dict,path:str)->None:
    status=node.get("status")
    if isinstance(status,str) and status.startswith("CERTIFIED"):
        meaningful=[k for k in node if k not in {"status","display_only"}]
        if not meaningful:
            fail("EMPTY_SUCCESS",path)


def validate_results_dict(d:dict)->None:
    if d.get("schema_version")!="POST282_CONTACT_BALANCE_ARB_v2": fail("SCHEMA","results")
    if d.get("claim_cap")!="EXPERIMENTAL_SIGNAL_ONLY": fail("CLAIM_CAP","results")
    prov=d.get("source_provenance") or {}
    expected={
        "base_merge":"01871f7d2256b1eac2dbd7967346954367c8eef9",
        "base_tree":"c7749d37c4b63270818c3fb0d7fb5dbc22638790",
        "artifact_id":11282789337,
        "artifact_zip_sha256":"67a8dc2e766e2c7ea6ec02809ade4e4d530b055be382901637368e4cf9711e39",
        "discovery_sha256":"9cd30f99a1841e5ef70951f1339ff18b9b9492e5273659bb560fb5e457aedd0a",
        "arb_sha256":"e137b8db0c726085c1fc9875efa778ff115de705c26fd1205154133541baea29",
        "selected_panel_artifact_id":11282789337,
    }
    for k,v in expected.items():
        if prov.get(k)!=v: fail("PROVENANCE",f"{k} drift")
    _validate_dyadic_payload(d)
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
    keys=[repr(r.get("candidate")) for r in rows]
    if len(set(keys))!=len(keys):
        fail("SELECTION","duplicated selected replay row")
    balances=d.get("balance_rows")
    if not isinstance(balances,list) or len(balances)!=11:
        fail("BALANCE","balance rows missing")
    if not any(r.get("physical_remainder",{}).get("status")=="CERTIFIED" for r in balances):
        fail("N03","direct physical remainder lane is vacuous")
    if any(r.get("first_boundary_claimed") is not False for r in rows):
        fail("FIRST_BOUNDARY","finite replay may not claim first boundary")

    cal=d.get("calibration") or {}
    required_cal=(
        "value_overlap","first_overlap","second_overlap",
        "derivative_overlap","remainder_overlap","balance_overlap",
        "seam_balance_overlap","independent_balance_identity_overlap",
        "derivative_width_le_2^-80","remainder_width_le_2^-80",
        "balance_width_le_2^-80","width_le_2^-80"
    )
    if not all(cal.get(k) is True for k in required_cal):
        fail("N02","independent K2/log2 derivative/remainder/balance qualification incomplete")

    for i,row in enumerate(balances):
        contract=row.get("certification_contract") or {}
        required_contract={
            "shifted_eigenvalue_subtraction":True,
            "euler_correction_in_balance":True,
            "response_gauge":"ORTHOGONAL_TO_CERTIFIED_GROUND",
            "independent_physical_remainder":True,
            "midpoint_inverse_requires_rho_lt_one":True,
            "exact_interval_codec":"DYADIC_DIRECTED_ARB_ENDPOINTS",
            "theorem_promotion":False,
        }
        for k,v in required_contract.items():
            if contract.get(k)!=v:
                fail("N03",f"row {i}: certification contract drift: {k}")
        response=row.get("response") or {}
        _require_certified_payload(response,f"balance_rows[{i}].response")
        if response.get("status") in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}:
            inv=response.get("inverse_certificate")
            if not isinstance(inv,dict) or "rho_upper_exact" not in inv:
                fail("N03",f"row {i}: certified response lacks inverse certificate")
            if response.get("orthogonality") is None:
                fail("N03",f"row {i}: certified response lacks gauge residual")
        rem=row.get("physical_remainder") or {}
        _require_certified_payload(rem,f"balance_rows[{i}].physical_remainder")
        sat=row.get("saturation_gap") or {}
        if sat.get("status")=="CERTIFIED_INDEPENDENT_SIDES":
            if sat.get("delta_sat") is None or sat.get("kappa_plus_euler") is None:
                fail("EULER",f"row {i}: independent balance omitted one side")
            if sat.get("identity_overlap") is not True:
                fail("BALANCE",f"row {i}: certified independent sides do not overlap")
        abl=row.get("matched_ablations")
        if not isinstance(abl,list):
            fail("N04",f"row {i}: matched ablation dispositions missing")
        if response.get("status") in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}:
            modes={(a.get("name"),a.get("mode")) for a in abl}
            required={(f"DROP_{channel}",mode)
                for channel in ("POLE","ARCH","PRIME")
                for mode in ("FROZEN_STATE","REOPTIMIZED")}
            if modes!=required:
                fail("N04",f"row {i}: ablation family is not exact six-case matched set")
            for a in abl:
                if a.get("mode")=="FROZEN_STATE" and a.get("complete_model_inverse_used") is not True:
                    fail("N04",f"row {i}: frozen-state ablation did not receipt complete-model response")
                if (a.get("arithmetic_comparison") or {}).get("status")!="NOT_APPLICABLE_NO_MATCHED_PHYSICAL_FUNCTIONAL":
                    fail("N04",f"row {i}: unmatched ablation arithmetic comparison was promoted")
                _require_certified_payload(a,f"balance_rows[{i}].matched_ablations")

    hyp=d.get("hypothesis_dispositions") or {}
    x01=hyp.get("X01_INHERITED_RESPONSE_BALANCE") or {}
    if x01.get("status") not in {
        "NO_ELIGIBLE_INHERITED_CONTACT","ELIGIBLE_INHERITED_CONTACTS_EVALUATED"}:
        fail("X01","missing eligibility-derived disposition")
    if x01.get("status")=="NO_ELIGIBLE_INHERITED_CONTACT":
        if x01.get("eligible_count")!=0 or x01.get("rows_examined")!=11:
            fail("X01","no-eligible disposition is not backed by full panel scan")
        if not isinstance(x01.get("rejections"),list) or len(x01["rejections"])!=11:
            fail("X01","no-eligible disposition lacks per-row rejection receipts")
    if x01.get("theorem_promotion") is not False:
        fail("X01","experimental lane attempted theorem promotion")


def check_results(path:Path)->None:
    validate_results_dict(json.loads(path.read_text()))


def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument("--results")
    a=ap.parse_args()
    check_surface()
    if a.results: check_results(Path(a.results))
    print("POST282 CONTACT CALCULUS CONTRACT: PASS")
    return 0

if __name__=="__main__": raise SystemExit(main())
