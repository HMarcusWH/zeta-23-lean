import sys
import unittest
from decimal import Decimal
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.deformation_budget import (
    BudgetDecision,
    TailBudgetStatus,
    certified_headroom,
    certified_step_upper,
    diagnostic_two_by_two_drop,
    first_unexcluded_crossing_index,
    make_tail_budget_certificate,
    prune_decision,
)


class DeformationBudgetTests(unittest.TestCase):
    def test_diagnostic_drop_is_nonnegative(self):
        self.assertGreaterEqual(diagnostic_two_by_two_drop(2, 5, Decimal("0.5")), 0)

    def test_gap_bound_requires_positive_gap(self):
        self.assertIsNone(certified_step_upper(beta_upper=1, gap_lower=0))
        self.assertEqual(certified_step_upper(beta_upper=2, gap_lower=4), Decimal(1))

    def test_no_tail_bound_means_no_prune(self):
        cert = make_tail_budget_certificate(
            start_n=10, prefix_bounds=[Decimal("0.01")], prefix_end_n=11,
            tail_upper=None, in_trust_region=True, method="none", provenance=("test",)
        )
        self.assertEqual(cert.status, TailBudgetStatus.BOUND_UNAVAILABLE)
        self.assertIsNone(certified_headroom(1, cert))
        self.assertEqual(prune_decision(1, cert), BudgetDecision.UNRESOLVED)

    def test_positive_certified_headroom_prunes(self):
        cert = make_tail_budget_certificate(
            start_n=10, prefix_bounds=[Decimal("0.1"), Decimal("0.1")], prefix_end_n=12,
            tail_upper=Decimal("0.2"), in_trust_region=True,
            method="analytic majorant", provenance=("theorem-X",)
        )
        self.assertEqual(certified_headroom(Decimal("1.0"), cert), Decimal("0.6"))
        self.assertEqual(prune_decision(Decimal("1.0"), cert), BudgetDecision.PRUNE)

    def test_zero_future_deformation_after_negative_floor_does_not_prune(self):
        cert = make_tail_budget_certificate(
            start_n=10, prefix_bounds=[], prefix_end_n=10, tail_upper=0,
            in_trust_region=True, method="zero-tail", provenance=("test",)
        )
        self.assertEqual(prune_decision(Decimal("-0.1"), cert), BudgetDecision.UNRESOLVED)

    def test_earliest_name_is_semantically_one_sided(self):
        idx = first_unexcluded_crossing_index(Decimal("0.25"), [(10, Decimal("0.1")), (11, Decimal("0.2"))])
        self.assertEqual(idx, 12)


if __name__ == "__main__":
    unittest.main()
