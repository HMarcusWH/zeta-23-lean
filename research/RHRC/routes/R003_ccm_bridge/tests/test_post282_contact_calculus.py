from __future__ import annotations
import copy,json,sys,unittest
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROUTE=HERE.parent
RHRC=ROUTE.parents[1]
ROOT=RHRC.parents[1]
sys.path.insert(0,str(ROUTE))
sys.path.insert(0,str(RHRC/"closure_batch"))

from interval_codec import DyadicInterval,IntervalCodecError
import post282_contact_calculus as campaign
import canonical_contact_balance_arb as balance
import check_post282_contact_calculus_contract as contract


class ContactCalculusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.protocol_path=ROUTE/"fixtures/post282_contact_calculus_v1.json"
        cls.p=json.loads(cls.protocol_path.read_text())
        cls.out=balance.campaign(cls.p)

    def test_protocol(self):
        campaign.validate_protocol(self.p)

    def test_claim_firewall(self):
        self.assertEqual(self.p["terminal_claim"],"RH_OPEN")
        self.assertEqual(self.p["claim_cap"],"EXPERIMENTAL_SIGNAL_ONLY")

    def test_seam_scope_frozen(self):
        qs={x["q"] for x in self.p["seam_controls"]}
        self.assertTrue({2,4,8,9,16,6,10,14,15}.issubset(qs))

    def test_exact_selected_panel_is_frozen(self):
        rows=self.p["selected_neighborhoods"]
        self.assertEqual(len(rows),11)
        self.assertEqual(sum(x["reason"]=="sign_bracket" for x in rows),4)
        self.assertEqual(
            [(x["Q"],x["K"]) for x in rows[:4]],
            [(24,4),(9,5),(7,6),(24,4)])

    def test_interval_json_rejects_bool(self):
        with self.assertRaises(IntervalCodecError):
            DyadicInterval.from_json({"lo_num":False,"hi_num":1,"exp2":10})

    def test_interval_exact_sign(self):
        self.assertEqual(DyadicInterval(1,2,10).sign(),"POSITIVE")
        self.assertEqual(DyadicInterval(-2,-1,10).sign(),"NEGATIVE")
        self.assertEqual(DyadicInterval(-1,1,10).sign(),"CONTAINS_ZERO")

    def test_k2_log2_calibration_schema(self):
        out=balance.log2_seam_calibration(192)
        self.assertEqual(out["name"],"K2_LOG2_COMPRESSED_SEAM")
        self.assertEqual(out["K"],2)
        self.assertIn("qualified",out)

    def test_campaign_nonempty(self):
        out=self.out
        self.assertEqual(out["schema_version"],"POST282_CONTACT_BALANCE_ARB_v2")
        self.assertTrue(out["seam_controls"])
        self.assertFalse(out["summary"]["theorem_promotion"])
        self.assertEqual(out["summary"]["terminal_claim"],"RH_OPEN")
        contract.validate_results_dict(out)

    def test_ablation_contract_names(self):
        required={(f"DROP_{c}",m) for c in ("POLE","ARCH","PRIME")
                  for m in ("FROZEN_STATE","REOPTIMIZED")}
        self.assertEqual(len(required),6)


    def test_protocol_rejects_wrong_tree(self):
        p=copy.deepcopy(self.p);p["base_tree"]="0"*40
        with self.assertRaises(SystemExit): campaign.validate_protocol(p)

    def test_protocol_rejects_wrong_artifact_digest(self):
        p=copy.deepcopy(self.p);p["inherited_artifact"]["zip_sha256"]="0"*64
        with self.assertRaises(SystemExit): campaign.validate_protocol(p)

    def test_protocol_rejects_duplicate_selected_case(self):
        p=copy.deepcopy(self.p);p["selected_neighborhoods"][1]=copy.deepcopy(p["selected_neighborhoods"][0])
        with self.assertRaises(SystemExit): campaign.validate_protocol(p)

    def test_protocol_rejects_inexact_or_reversed_fraction(self):
        p=copy.deepcopy(self.p);p["selected_neighborhoods"][0]["fraction_left"]=[True,16]
        with self.assertRaises(SystemExit): campaign.validate_protocol(p)
        p=copy.deepcopy(self.p);p["selected_neighborhoods"][0]["fraction_left"]=[14,16]
        p["selected_neighborhoods"][0]["fraction_right"]=[13,16]
        with self.assertRaises(SystemExit): campaign.validate_protocol(p)

    def test_result_rejects_wrong_source_tree(self):
        out=copy.deepcopy(self.out);out["source_provenance"]["base_tree"]="0"*40
        with self.assertRaises(SystemExit): contract.validate_results_dict(out)

    def test_result_rejects_duplicate_selected_replay(self):
        out=copy.deepcopy(self.out);out["selected_replay"][1]=copy.deepcopy(out["selected_replay"][0])
        with self.assertRaises(SystemExit): contract.validate_results_dict(out)

    def test_result_rejects_fake_first_boundary(self):
        out=copy.deepcopy(self.out);out["selected_replay"][0]["first_boundary_claimed"]=True
        with self.assertRaises(SystemExit): contract.validate_results_dict(out)

    def test_result_rejects_omitted_euler_receipt(self):
        out=copy.deepcopy(self.out)
        out["balance_rows"][0]["certification_contract"]["euler_correction_in_balance"]=False
        with self.assertRaises(SystemExit): contract.validate_results_dict(out)

    def test_result_rejects_unreceipted_inverse(self):
        out=copy.deepcopy(self.out)
        row=next((r for r in out["balance_rows"]
                  if r.get("response",{}).get("status") in {
                      "CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}),None)
        if row is None:self.skipTest("no certified response in bounded fixture")
        row["response"].pop("inverse_certificate",None)
        with self.assertRaises(SystemExit): contract.validate_results_dict(out)

    def test_result_rejects_incomplete_ablation_family(self):
        out=copy.deepcopy(self.out)
        row=next((r for r in out["balance_rows"]
                  if r.get("response",{}).get("status") in {
                      "CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}),None)
        if row is None:self.skipTest("no certified response in bounded fixture")
        row["matched_ablations"]=row["matched_ablations"][:-1]
        with self.assertRaises(SystemExit): contract.validate_results_dict(out)

    def test_result_rejects_interval_sign_forgery(self):
        out=copy.deepcopy(self.out)
        rec=out["calibration"]["left"]["energy"]
        rec["sign"]="NEGATIVE" if rec["sign"]!="NEGATIVE" else "POSITIVE"
        with self.assertRaises(SystemExit): contract.validate_results_dict(out)

    def test_post284_premise_free_claims_promoted_individually(self):
        promoted={
            "R003_COMPRESSED_PRODUCTION_C2":"Zeta23.CCM.canonicalEvenCompressedC2_proved",
            "R003_INHERITED_FIRST_VARIATION_RESTRICTION":"Zeta23.CCM.GeneratedStrictEvenContact.firstVariation_eq_zero_of_inherited",
        }
        registry=json.loads((RHRC/"CLAIM_REGISTRY.json").read_text())
        claims={x["id"]:x for x in registry["claims"]}
        registered=json.loads((RHRC/"REGISTERED_THEOREM_BINDINGS.json").read_text())
        r003=json.loads((RHRC/"R003_PROMOTED_BINDINGS.json").read_text())
        for cid,theorem in promoted.items():
            self.assertEqual(claims[cid]["status"],"PROVED_UNCONDITIONAL")
            self.assertNotIn("candidate_binding",claims[cid])
            self.assertEqual(claims[cid]["theorem"],theorem)
            self.assertIn(cid,{x["id"] for x in registered["bindings"]})
            self.assertIn(cid,{x["id"] for x in r003["bindings"]})

    def test_post282_f04_conditional_claims_are_candidate_bound_not_promoted(self):
        expected={
            "R003_WEIGHTED_PRODUCTION_PAIR_BALANCE":"Zeta23.CCM.canonicalSecondPairing_euler_eq_productionSaturationGap",
            "R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER":"Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier",
        }
        registry=json.loads((RHRC/"CLAIM_REGISTRY.json").read_text())
        claims={x["id"]:x for x in registry["claims"]}
        for cid,theorem in expected.items():
            self.assertEqual(claims[cid]["status"],"OPEN")
            self.assertEqual(claims[cid]["promotion_cap"],"OPEN")
            self.assertTrue(claims[cid]["candidate_binding"])
            self.assertEqual(claims[cid]["theorem"],theorem)
        r003=json.loads((RHRC/"R003_PROMOTED_BINDINGS.json").read_text())
        self.assertEqual({x["id"] for x in r003["candidate_bindings"]},set(expected))
        registered=json.loads((RHRC/"REGISTERED_THEOREM_BINDINGS.json").read_text())
        self.assertEqual({x["id"] for x in registered["candidate_bindings"]},set(expected))
        proved_ids={x["id"] for x in registered["bindings"]}
        self.assertTrue(set(expected).isdisjoint(proved_ids))
        claim_lean=(ROOT/"Zeta23/CCM/ClaimBindings.lean").read_text()
        registered_lean=(ROOT/"Zeta23/RHRC/RegisteredClaimBindings.lean").read_text()
        for theorem in expected.values():
            self.assertIn(f"#check {theorem}",claim_lean)
            self.assertIn(f"#print axioms {theorem}",claim_lean)
            self.assertIn(f"#check {theorem}",registered_lean)
            self.assertIn(f"#print axioms {theorem}",registered_lean)

    def test_x01_is_eligibility_derived(self):
        x01=self.out["hypothesis_dispositions"]["X01_INHERITED_RESPONSE_BALANCE"]
        self.assertIn(x01["status"],{
            "NO_ELIGIBLE_INHERITED_CONTACT","ELIGIBLE_INHERITED_CONTACTS_EVALUATED"})
        if x01["status"]=="NO_ELIGIBLE_INHERITED_CONTACT":
            self.assertEqual(x01["eligible_count"],0)
            self.assertEqual(len(x01["rejections"]),11)

if __name__=="__main__": unittest.main()
