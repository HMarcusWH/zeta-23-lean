import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post221SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post221_history_survives_later_theorem_promotion(self):
        merged = self.state["merged_theorem_anchor"]
        self.assertGreaterEqual(merged["pr"], 222)
        note = self.state["control_note"]
        for token in (
            "Exact PR #221 theorem delta head 20018c931f4516432ace5bd06788276be656641b",
            "tree bc82b7604d95ccce8f1a46e4b25e0485bf68a4c2",
            "PR #221",
        ):
            self.assertIn(token, note)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_route_is_branch_classified_not_closed(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["actual_shell_coupling_good_sector_annihilation"], "PROVED_PR_220")
        self.assertEqual(route["zero_shift_kernel_balance"], "PROVED_PR_220")
        self.assertEqual(route["zero_shift_schur_good_bad_classification"], "MERGED_PR_221")
        self.assertEqual(route["canonical_simultaneous_odd_bad_branch"], "OPEN_SCALAR_SIGN_CLASSIFIED_BY_PR_222")
        self.assertEqual(route["active_subobligation"], "OBS-059I")

    def test_post221_delta_has_required_post_green_sections(self):
        text = (RHRC / "RESEARCH_LEADS_POST_221_ZERO_SHIFT_SCHUR_CLASSIFICATION_DELTA.md").read_text(encoding="utf-8")
        for heading in (
            "# What became formally true",
            "# What changed",
            "# Upstream implications",
            "# Downstream implications",
            "# Resurrected routes",
            "# New RH-relevant clues",
            "# Falsification checks",
            "# Highest-leverage next moves",
            "# Standing questions",
        ):
            self.assertIn(heading, text)
        for token in (
            "parityBad_iff_cubicCouplingKernelPart_ne_zero_or_exists_zeroShiftEndpoint_neg",
            "not_parityBad_iff_exists_cubicZeroShiftPreimage_endpoint_nonnegative",
            "oddBad_iff_oddCubicCouplingResonant_or_zeroShiftEndpoint_neg",
            "RETAINED_BRANCH_ARITHMETIC_DISCRIMINATION",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_post221_obstruction_delta_keeps_obs059i_open(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_221_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-059I",
            "OPEN / BRANCH-CLASSIFIED / CANONICAL-ARITHMETIC-DISCRIMINATION REQUIRED",
            "actual shell coupling resonant",
            "regular with negative zero-shift endpoint",
            "K(b)",
            "#219 K(a)",
            "#220 K(d)",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_control_semantics_and_claim_surface_remain_frozen(self):
        action = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        registry = json.loads(
            (RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8")
        )
        r003 = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(action["current_frontier"], "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN")
        self.assertEqual([b["id"] for b in action["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]["first_breaks"]], ["E4A4-SCHUR-FB-05"])
        self.assertEqual(r003["phase"], "DISCOVERY")
        self.assertFalse(r003["confirmatory_execution_authorized"])
        self.assertIsNone(r003["route_spec_digest"])
        self.assertIsNone(r003["boundary_digest"])


if __name__ == "__main__":
    unittest.main()
