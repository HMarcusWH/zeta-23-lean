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

    def test_legacy_panel_is_preserved(self):
        legacy=self.p["legacy_replay"]
        self.assertEqual(legacy["offset_powers"],[8,10,12])
        self.assertEqual(len(legacy["cases"]),11)

if __name__=="__main__": unittest.main()
