from __future__ import annotations
import json,sys,unittest
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROUTE=HERE.parent
sys.path.insert(0,str(ROUTE))
import post281_generated_contact_frontier as g
import check_post281_generated_contact_results as resultcheck
import certify_post281_generated_contact_frontier as cert
import write_post281_generated_contact_receipt as receipt_manifest

class GeneratedContactFrontierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.p=json.loads((ROUTE/"fixtures"/"post281_generated_contact_frontier_protocol_v1.json").read_text())


    def _minimal_valid_payloads(self):
        cand={"reason":"ground_magnitude","model":"CANONICAL","Q":13,"K":3,
              "L":2.5,"cell_fraction":[8,16],
              "cell_left_symbolic":"log(13)","cell_right_symbolic":"log(14)",
              "global_bottom":0.01,"parity_separation":0.1,"selected_sector_gap":0.2}
        discovery={
            "schema_version":"POST281_GENERATED_CONTACT_DISCOVERY_v1",
            "claim_cap":"EXPERIMENTAL_SIGNAL_ONLY",
            "protocol":{"discovery":{"additional_neighborhood_cap":12}},
            "measurements":[{"Q":13,"K":3,"L":2.5,"model":"canonical","x":0.0}],
            "selected_neighborhoods":[cand],
            "summary":{"terminal_claim":"RH_OPEN","contact_claimed":False,
                       "measurement_count":1,"selected_count":1},
        }
        attempt={
            "Q":13,"K":3,"L_float":2.5,"L_exact":"2.5",
            "precision_bits":192,"spectral_regime":"EVEN_STRICT",
            "claim_cap":"EXPERIMENTAL_SIGNAL_ONLY","terminal_claim":"RH_OPEN",
            "even":{"lambda_min":{"lower":0.01,"upper":0.02,
                       "lower_exact":"0.01","upper_exact":"0.02",
                       "mid":"0.015","rad":"0.005",
                       "certified_positive":True,"certified_negative":False},
                    "j1":{"lower":-0.2,"upper":-0.1,
                          "lower_exact":"-0.2","upper_exact":"-0.1",
                          "certified_positive":False,"certified_negative":True}},
            "odd":{"lambda_min":{"lower":0.2,"upper":0.3,
                      "lower_exact":"0.2","upper_exact":"0.3",
                      "mid":"0.25","rad":"0.05",
                      "certified_positive":True,"certified_negative":False}},
        }
        point={"L":2.5,
               "exact_cell_spec":{"Q":13,"K":3,"fraction":[8,16],
                                  "left":"log(13)","right":"log(14)"},
               "attempts":[attempt],"final":attempt,
               "global_bounds":{"lower":0.01,"upper":0.02},
               "global_sign":"POSITIVE",
               "resolution":{"ground_sign":"POSITIVE","j1_resolved":True}}
        controls=[{"control_name":"TRANSVERSE_CROSSING","model":"GENERIC_SYNTHETIC",
                   "contact_status":"CERTIFIED_SIGN_BRACKET",
                   "canonical_arithmetic_authority":False,"qualification_pass":True}]
        arb={"schema_version":"POST281_GENERATED_CONTACT_ARB_v1",
             "claim_cap":"EXPERIMENTAL_SIGNAL_ONLY",
             "rows":[{"candidate":cand,"point":point,"final":attempt,
                      "contact_status":"NEAR_CONTACT_PROXY",
                      "first_boundary_claimed":False}],
             "generic_control_certificates":controls,
             "summary":{"row_count":1,"generic_control_count":1,
                        "certified_sign_bracket_count":0,
                        "first_boundary_certified_count":0,
                        "terminal_claim":"RH_OPEN"}}
        return discovery,arb

    def test_protocol(self):
        g.validate_protocol(self.p)

    def test_all_integer_cells_and_k_are_frozen(self):
        d=self.p["discovery"]
        self.assertEqual((d["Q_min"],d["Q_max"]),(1,64))
        self.assertEqual(d["K"],[2,3,4,5,6])
        self.assertEqual(d["interior_fractions"]["numerators"],list(range(1,16)))

    def test_sign_brackets_keep_exact_cell_fractions(self):
        # Exact-cell provenance is required before Arb replay; floating L alone
        # must never be the only location identity.
        p=dict(self.p)
        out=g.discover(p)
        for row in out["sign_brackets"][:20]:
            self.assertIn("fraction_left",row)
            self.assertIn("fraction_right",row)
            self.assertEqual(row["fraction_left"][1],16)
            self.assertEqual(row["fraction_right"][1],16)

    def test_q1_starts_at_positive_base(self):
        lo,hi=g.cell_bounds(1)
        self.assertAlmostEqual(lo,1/512)
        self.assertGreater(hi,lo)

    def test_selection_quota_is_frozen(self):
        q=self.p["discovery"]["selection_quota"]
        self.assertEqual(sum(q.values()),self.p["discovery"]["additional_neighborhood_cap"])
        self.assertEqual(q["sign_bracket"],4)
        self.assertGreater(q["ground_magnitude"],0)
        self.assertGreater(q["parity_separation"],0)
        self.assertGreater(q["sector_gap"],0)

    def test_selection_firewall(self):
        forbidden=self.p["discovery"]["forbidden_selection_features"]
        self.assertIn("rho_distance_to_one",forbidden)
        self.assertIn("preferred_delta_sign",forbidden)


    def test_zero_weight_current_q_ablation_is_noop(self):
        L=(__import__("math").log(14.0)+__import__("math").log(15.0))/2
        rec=g.current_prime_interventions(L,14,3)
        self.assertEqual(rec["von_mangoldt_weight"],0.0)
        self.assertAlmostEqual(rec["atom_fro_norm"],0.0)

    def test_prime_power_current_q_ablation_is_nontrivial(self):
        L=(__import__("math").log(16.0)+__import__("math").log(17.0))/2
        rec=g.current_prime_interventions(L,16,3)
        self.assertGreater(rec["von_mangoldt_weight"],0.0)
        self.assertGreater(rec["atom_fro_norm"],0.0)

    def test_generic_controls_have_no_canonical_authority(self):
        controls=g.generic_contact_controls()
        self.assertGreaterEqual(len(controls),6)
        self.assertTrue(all(not x["canonical_arithmetic_authority"] for x in controls))
        self.assertIn("STATIONARY_CUBIC_CROSSING",{x["control_name"] for x in controls})
        self.assertIn("POSITIVE_QUARTIC_TOUCH",{x["control_name"] for x in controls})

    def test_result_checker_rejects_empty_payloads(self):
        bad={"claim_cap":"EXPERIMENTAL_SIGNAL_ONLY","summary":{"terminal_claim":"RH_OPEN","contact_claimed":False,"measurement_count":0,"selected_count":0},"measurements":[],"selected_neighborhoods":[],"protocol":{"discovery":{"additional_neighborhood_cap":12}}}
        with self.assertRaises(SystemExit):
            resultcheck.validate_discovery(bad)

    def test_certifier_rejects_nonintegral_and_reversed_coordinates(self):
        with self.assertRaises(ValueError):
            cert.require_fraction([1.5,16],"bad")
        with self.assertRaises(ValueError):
            cert.require_fraction([1,0],"bad")
        cand={"model":"CANONICAL","Q":13,"K":3,"fraction_left":[8,16],"fraction_right":[7,16]}
        with self.assertRaises(ValueError):
            cert.validate_candidate(cand,bracket=True)

    def test_generic_control_qualification_is_nonvacuous(self):
        rows=cert.certify_generic_controls(g.generic_contact_controls())
        self.assertTrue(rows)
        self.assertTrue(all(x["qualification_pass"] for x in rows))
        touch=next(x for x in rows if x["control_name"]=="POSITIVE_QUARTIC_TOUCH")
        self.assertEqual(touch["contact_status"],"NO_SIGN_CHANGE")


    def test_mutation_checker_rejects_all_known_bad_artifacts(self):
        import copy
        d,a=self._minimal_valid_payloads()
        resultcheck.validate_discovery(copy.deepcopy(d))
        resultcheck.validate_arb(copy.deepcopy(a),d["selected_neighborhoods"])

        mutations=[]
        x=copy.deepcopy(a); x["rows"]=[]; mutations.append(("empty_arb",d,x))
        x=copy.deepcopy(a); x["schema_version"]="WRONG"; mutations.append(("wrong_schema",d,x))
        x=copy.deepcopy(a); x["claim_cap"]="WRONG"; mutations.append(("wrong_claim_cap",d,x))
        x=copy.deepcopy(a); x["summary"]["row_count"]=999; mutations.append(("forged_count",d,x))
        x=copy.deepcopy(a); x["rows"].append(copy.deepcopy(x["rows"][0])); x["summary"]["row_count"]=2
        mutations.append(("duplicate_row",d,x))
        x=copy.deepcopy(a); x["rows"][0]["candidate"]["K"]=999
        mutations.append(("candidate_mismatch",d,x))
        x=copy.deepcopy(a); lm=x["rows"][0]["point"]["final"]["even"]["lambda_min"]
        lm["lower"],lm["upper"]=0.2,0.1
        mutations.append(("inverted_interval",d,x))
        x=copy.deepcopy(a); lm=x["rows"][0]["point"]["final"]["even"]["lambda_min"]
        lm["lower"]=lm["upper"]=0.015; lm["rad"]="0.005"
        mutations.append(("collapsed_interval",d,x))
        x=copy.deepcopy(a); lm=x["rows"][0]["point"]["final"]["even"]["lambda_min"]
        lm["lower"]=0.011; lm["upper"]=0.019
        mutations.append(("non_enclosing_serialization",d,x))
        x=copy.deepcopy(a); x["rows"][0]["point"]["final"]["even"]["lambda_min"]["mid"]="nan"
        mutations.append(("nonfinite_string",d,x))

        for name,dd,aa in mutations:
            with self.subTest(name=name):
                with self.assertRaises(SystemExit):
                    resultcheck.validate_arb(aa,dd["selected_neighborhoods"])

        x=copy.deepcopy(d); x["selected_neighborhoods"]=[]
        with self.assertRaises(SystemExit): resultcheck.validate_discovery(x)

    def test_checker_rejects_fake_certified_brackets(self):
        import copy
        d,a=self._minimal_valid_payloads()
        cand=copy.deepcopy(d["selected_neighborhoods"][0])
        cand.update({"reason":"sign_bracket","L_left":2.4,"L_right":2.5,
                     "fraction_left":[7,16],"fraction_right":[8,16]})
        d["selected_neighborhoods"]=[cand]
        point=copy.deepcopy(a["rows"][0]["point"])
        point["global_sign"]="POSITIVE"
        row={"candidate":cand,"left":copy.deepcopy(point),"right":copy.deepcopy(point),
             "final_bracket_exact":[[7,16],[8,16]],"final_bracket":[2.4,2.5],
             "contact_status":"CERTIFIED_SIGN_BRACKET","first_boundary_claimed":False}
        a["rows"]=[row]; a["summary"]["certified_sign_bracket_count"]=1
        with self.assertRaises(SystemExit):
            resultcheck.validate_arb(a,d["selected_neighborhoods"])

    def test_execution_receipt_tracks_only_existing_inputs(self):
        missing=[rel for rel in receipt_manifest.TRACKED if not (receipt_manifest.ROOT/rel).is_file()]
        self.assertEqual(missing,[])
        required={
            ".github/workflows/rhrc_post281_generated_contact_frontier.yml",
            "research/RHRC/routes/R003_ccm_bridge/post280_saturation_frontier.py",
            "research/RHRC/routes/R003_ccm_bridge/fixtures/post280_saturation_frontier_v1.json",
            "research/RHRC/routes/R003_ccm_bridge/contact_quotient/check_source_remainder_exact.py",
            "research/RHRC/routes/R003_ccm_bridge/contact_quotient/countermodel_controls.py",
            "research/RHRC/routes/R003_ccm_bridge/contact_quotient/tests/test_countermodel_controls.py",
            "research/RHRC/closure_batch/first_crossing_generic_falsifiers.py",
            "research/RHRC/countermodels/post204_pair_d_exact_geometry.py",
        }
        self.assertTrue(required.issubset(set(receipt_manifest.TRACKED)))

    def test_legacy_panel_is_preserved(self):
        legacy=self.p["legacy_replay"]
        self.assertEqual(legacy["offset_powers"],[8,10,12])
        self.assertEqual(len(legacy["cases"]),11)

    def test_dyadic_interval_codec_rejects_bool(self):
        sys.path.insert(0,str(g.ROOT/"research/RHRC/closure_batch"))
        from interval_codec import DyadicInterval, IntervalCodecError
        with self.assertRaises(IntervalCodecError):
            DyadicInterval.from_json({"lo_num":False,"hi_num":1,"exp2":10})

if __name__=="__main__": unittest.main()
