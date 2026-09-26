import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

class Post246SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))

    def test_post246_is_proved_history_not_candidate(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post246_canonical_prime_remainder_normal_form"], "PROVED_PR_246")
        self.assertEqual(route["post246_canonical_prime_remainder_dominance_rh_equivalence"], "PROVED_PR_246")
        self.assertEqual(route["post246_generated_riesz_six_eventual_nonnegativity_rh_equivalence"], "PROVED_PR_246")
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 272)
        note = self.state["control_note"]
        self.assertIn("PR #246", note)
        self.assertIn("canonicalPrimeRemainderDominance_iff_riemannHypothesis", note)

    def test_exact_post246_files_and_theorems_exist(self):
        remainder=(ROOT/"Zeta23"/"CCM"/"CanonicalPrimeRemainder.lean").read_text(encoding="utf-8")
        criterion=(ROOT/"Zeta23"/"ExceptionalZero"/"CanonicalArithmeticCriterion.lean").read_text(encoding="utf-8")
        for name in (
            "canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum",
            "canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget",
            "canonicalSourceChannelEnergy_nonneg_iff_budget_le",
        ):
            self.assertIn(f"theorem {name}", remainder)
        for name in (
            "canonicalFiniteWeilPositivity_iff_riemannHypothesis",
            "canonicalRieszSixPositivity_iff_riemannHypothesis",
            "generatedRetainedRieszSixEventuallyNonnegative_iff_riemannHypothesis",
            "canonicalPrimeRemainderDominance_iff_riemannHypothesis",
            "generatedRetainedPrimeRemainderDominance_iff_riemannHypothesis",
        ):
            self.assertIn(f"theorem {name}", criterion)

    def test_medium_pnt_is_not_silently_promoted(self):
        route=self.state["active_research_route"]
        self.assertEqual(route["post245_medium_pnt_build_status"], "UNIMPORTED_NOT_BUILT_BY_CI")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

if __name__ == "__main__":
    unittest.main()
