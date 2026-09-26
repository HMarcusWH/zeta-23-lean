import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent
sys.path.insert(0, str(RHRC / "tools"))
import arithmetic_firewall_lint  # noqa: E402

class Post245SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post245_provenance_survives_later_authority(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 272)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 272)
        note = self.state["control_note"]
        for token in (
            "PR #245", "NoArbitrarilyLargeWholeCellRetainedFamily",
            "GENERATED_FAMILY_FINAL_GATE", "PR #246", "PR #247",
            "RH remains OPEN",
        ):
            self.assertIn(token, note)
        route = self.state["active_research_route"]
        self.assertEqual(route["post245_no_regular_first_bad_certificates"], "RH_EQUIVALENT_PR_245")
        self.assertEqual(route["post245_generated_family_final_gate"], "RH_EQUIVALENT_PR_245")
        self.assertEqual(route["post245_sub_rh_gate_remaining_on_route"], "NONE")
        self.assertEqual(route["post245_canonical_prime_remainder_normal_form"], "CANDIDATE_POST245_ARITHMETIC_CRITERION_PR")

    def test_post245_documents_remain_frozen_complete_history(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_245_ARITHMETIC_CRITERION_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_245_DELTA.md",
            RHRC / "DEAD_ROUTES_POST_245_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)
            self.assertIn("RH remains OPEN", text)

    def test_arithmetic_modules_remain_exact_and_firewalled(self):
        remainder = (ROOT / "Zeta23" / "CCM" / "CanonicalPrimeRemainder.lean").read_text(encoding="utf-8")
        for name in (
            "canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum",
            "canonicalPolePrimeDiscrepancy_eq_neg_tail_sub_remainder",
            "canonicalPolePrimeDiscrepancyEnergy_eq_neg_tail_sub_remainder",
            "canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget",
            "canonicalSourceChannelEnergy_nonneg_iff_budget_le",
        ):
            self.assertIn(f"theorem {name}", remainder)
            self.assertIn(f"#print axioms Zeta23.CCM.{name}", remainder)
        self.assertNotIn("RiemannHypothesis", remainder)
        criterion = (ROOT / "Zeta23" / "ExceptionalZero" / "CanonicalArithmeticCriterion.lean").read_text(encoding="utf-8")
        for name in (
            "canonicalFiniteWeilPositivity_iff_riemannHypothesis",
            "canonicalRieszSixPositivity_iff_riemannHypothesis",
            "generatedRetainedRieszSixEventuallyNonnegative_iff_riemannHypothesis",
            "canonicalPrimeRemainderDominance_iff_riemannHypothesis",
            "generatedRetainedPrimeRemainderDominance_iff_riemannHypothesis",
            "exists_arbitrarilyLarge_primeRemainderDominance_failure_of_offLine_zero",
        ):
            self.assertIn(f"theorem {name}", criterion)
        self.assertEqual(arithmetic_firewall_lint.lint(), [])
        workflow = (ROOT / ".github" / "workflows" / "rhrc.yml").read_text(encoding="utf-8")
        self.assertIn("assert p['theorem_anchor']['pr'] == 272", workflow)

if __name__ == "__main__":
    unittest.main()
