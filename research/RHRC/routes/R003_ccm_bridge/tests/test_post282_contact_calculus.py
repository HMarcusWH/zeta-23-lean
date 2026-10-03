from __future__ import annotations
import copy,json,sys,unittest
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROUTE=HERE.parent
RHRC=ROUTE.parents[1]
sys.path.insert(0,str(ROUTE))
sys.path.insert(0,str(RHRC/"closure_batch"))

from interval_codec import DyadicInterval,IntervalCodecError
import post282_contact_calculus as campaign
import canonical_contact_balance_arb as balance


class ContactCalculusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.protocol_path=ROUTE/"fixtures/post282_contact_calculus_v1.json"
        cls.p=json.loads(cls.protocol_path.read_text())

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
        out=balance.campaign(self.p)
        self.assertEqual(out["schema_version"],"POST282_CONTACT_BALANCE_ARB_v2")
        self.assertTrue(out["seam_controls"])
        self.assertFalse(out["summary"]["theorem_promotion"])
        self.assertEqual(out["summary"]["terminal_claim"],"RH_OPEN")


if __name__=="__main__": unittest.main()
