from __future__ import annotations
import json,sys,unittest
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROUTE=HERE.parent
sys.path.insert(0,str(ROUTE))
import post281_generated_contact_frontier as g

class GeneratedContactFrontierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.p=json.loads((ROUTE/"fixtures"/"post281_generated_contact_frontier_protocol_v1.json").read_text())

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

    def test_legacy_panel_is_preserved(self):
        legacy=self.p["legacy_replay"]
        self.assertEqual(legacy["offset_powers"],[8,10,12])
        self.assertEqual(len(legacy["cases"]),11)

if __name__=="__main__": unittest.main()
