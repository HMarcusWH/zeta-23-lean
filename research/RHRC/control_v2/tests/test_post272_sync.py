import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent
SCOUT = RHRC / "routes" / "R003_ccm_bridge"


class Post272SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post272_is_merged_audit_authority_not_rh(self):
        t = self.state["merged_theorem_anchor"]
        self.assertEqual(t["pr"], 272)
        self.assertEqual(t["validated_head"], "d0cc3aad0181e58d486e464b685fc06559862923")
        self.assertEqual(t["merge_commit"], "bca1869e055b802e1099ed86e71314bf61a7a4a8")
        self.assertEqual(t["tree"], "53f659ff274bdf2218860e1a9dfeda50afcd0fe9")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")
        route = self.state["active_research_route"]
        self.assertEqual(route["post272_cofinal_arithmetic_rh_equivalence"], "PROVED_PR_272_AUDIT_ONLY")
        self.assertEqual(
            route["post272_direct_cofinal_construction_role"],
            "CONSUMED_AS_INDEPENDENT_SUB_RH_TARGET",
        )

    def test_exact_equivalence_theorem_is_audit_only(self):
        text = (
            ROOT / "Zeta23" / "ExceptionalZero" / "CofinalArithmeticEquivalenceAudit.lean"
        ).read_text(encoding="utf-8")
        self.assertIn("cofinalCanonicalArithmeticCertificates_of_riemannHypothesis", text)
        self.assertIn("cofinalCanonicalArithmeticCertificates_iff_riemannHypothesis", text)
        root = (ROOT / "Zeta23" / "ExceptionalZero.lean").read_text(encoding="utf-8")
        self.assertNotIn("CofinalArithmeticEquivalenceAudit", root)

    def test_first_contact_fixture_is_preregistered_and_nonadaptive(self):
        fixture = json.loads(
            (SCOUT / "fixtures" / "post272_first_contact_atlas_v1.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertFalse(fixture["adaptive_search"])
        self.assertEqual(fixture["offset_powers"], [8, 10, 12])
        self.assertEqual(
            [(x["q"], x["K"]) for x in fixture["primary_cases"]],
            [(13, 3), (16, 3), (17, 3), (19, 3), (14, 3), (15, 3), (18, 3)],
        )
        self.assertEqual(
            [(x["q"], x["K"]) for x in fixture["replication_cases"]],
            [(16, 4), (17, 4), (16, 6), (17, 6)],
        )
        note = (SCOUT / "POST272_FIRST_CONTACT_ATLAS_2026_09_26.md").read_text(
            encoding="utf-8"
        )
        self.assertIn("there is no value jump to discover at the seam", note)
        self.assertIn("PARITY_GAP_UNRESOLVED", note)
        self.assertIn("RH remains OPEN", note)

    def test_live_target_is_unconditional_first_contact_not_cofinal_certificates(self):
        route = self.state["active_research_route"]
        self.assertEqual(
            route["current_obstruction"],
            "OBS-060_GROUND_SPECTRUM_FIRST_CROSSING_BARRIER",
        )
        self.assertEqual(
            route["current_next_research_target"],
            "POST272_TRUE_GROUND_FIRST_CONTACT_ATLAS",
        )
        self.assertEqual(
            route["post271_cofinal_arithmetic_certificate_construction"],
            "OPEN_RH_EQUIVALENT_TERMINAL_PR_272",
        )


if __name__ == "__main__":
    unittest.main()
