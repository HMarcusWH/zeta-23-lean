import sys
import unittest
from decimal import Decimal
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.deformation_budget import (
    BudgetDecision,
    StepUpperBound,
    TailBudgetStatus,
    certified_headroom,
    certified_step_upper,
    certify_prune_decision,
    diagnostic_two_by_two_drop,
    first_unexcluded_crossing_index,
    make_tail_budget_certificate,
    prune_decision,
)
from ffbbp.v16_commutation import assess_decision
from ffbbp.v16_horizon import ResidualHorizonContract, certify_horizon


class DeformationBudgetTests(unittest.TestCase):
    def _horizon(self, propagated=0.2, tolerance=0.2, *, target_metric="remaining_deformation_budget"):
        contract = ResidualHorizonContract(
            model_class="deformation-tail-majorant",
            local_defect_upper=0.0,
            sensitivity_upper=1.0,
            requested_horizon=100.0,
            target_metric=target_metric,
            trust_region="declared-N-tail",
        )
        return certify_horizon(
            contract,
            in_trust_region=True,
            propagated_upper=propagated,
            tolerance=tolerance,
        )

    def _step(self, n, upper):
        return StepUpperBound.make(n, Decimal(upper), (f"step-{n}",))

    def _cert(self):
        return make_tail_budget_certificate(
            start_n=10,
            prefix_bounds=[self._step(10, "0.1")],
            prefix_end_n=11,
            tail_upper=Decimal("0.2"),
            in_trust_region=True,
            method="analytic majorant",
            provenance=("theorem-X",),
            horizon_certificate=self._horizon(),
        )

    def test_diagnostic_drop_is_nonnegative(self):
        self.assertGreaterEqual(diagnostic_two_by_two_drop(2, 5, Decimal("0.5")), 0)

    def test_gap_bound_requires_positive_gap(self):
        self.assertIsNone(certified_step_upper(beta_upper=1, gap_lower=0))
        self.assertEqual(certified_step_upper(beta_upper=2, gap_lower=4), Decimal(1))

    def test_no_tail_bound_means_no_prune(self):
        cert = make_tail_budget_certificate(
            start_n=10,
            prefix_bounds=[self._step(10, "0.01")],
            prefix_end_n=11,
            tail_upper=None,
            in_trust_region=True,
            method="none",
            provenance=("test",),
        )
        self.assertEqual(cert.status, TailBudgetStatus.BOUND_UNAVAILABLE)
        self.assertIsNone(certified_headroom(1, cert))
        self.assertEqual(prune_decision(1, cert), BudgetDecision.UNRESOLVED)

    def test_numeric_tail_without_horizon_certificate_does_not_prune(self):
        cert = make_tail_budget_certificate(
            start_n=10,
            prefix_bounds=[self._step(10, "0.1"), self._step(11, "0.1")],
            prefix_end_n=12,
            tail_upper=Decimal("0.2"),
            in_trust_region=True,
            method="analytic majorant",
            provenance=("theorem-X",),
            horizon_certificate=None,
        )
        self.assertEqual(cert.status, TailBudgetStatus.BOUND_UNAVAILABLE)
        self.assertEqual(prune_decision(1, cert), BudgetDecision.UNRESOLVED)

    def test_horizon_target_metric_must_match_budget(self):
        cert = make_tail_budget_certificate(
            start_n=10,
            prefix_bounds=[self._step(10, "0.1")],
            prefix_end_n=11,
            tail_upper=Decimal("0.2"),
            in_trust_region=True,
            method="analytic majorant",
            provenance=("theorem-X",),
            horizon_certificate=self._horizon(target_metric="unrelated_metric"),
        )
        self.assertEqual(cert.status, TailBudgetStatus.BOUND_UNAVAILABLE)
        self.assertEqual(cert.assurance_reason, "HORIZON_TARGET_METRIC_MISMATCH")

    def test_positive_assured_headroom_prunes(self):
        cert = make_tail_budget_certificate(
            start_n=10,
            prefix_bounds=[self._step(10, "0.1"), self._step(11, "0.1")],
            prefix_end_n=12,
            tail_upper=Decimal("0.2"),
            in_trust_region=True,
            method="analytic majorant",
            provenance=("theorem-X",),
            horizon_certificate=self._horizon(),
        )
        self.assertEqual(cert.status, TailBudgetStatus.CERTIFIED)
        self.assertEqual(certified_headroom(Decimal("1.0"), cert), Decimal("0.6"))
        self.assertEqual(prune_decision(Decimal("1.0"), cert), BudgetDecision.PRUNE)

    def test_required_decision_commutation_missing_fails_closed(self):
        result = certify_prune_decision(
            Decimal("1.0"), self._cert(), decision_commutation_required=True
        )
        self.assertEqual(result.decision, BudgetDecision.UNRESOLVED)
        self.assertEqual(result.reason, "DECISION_COMMUTATION_CERTIFICATE_MISSING")

    def test_failed_decision_commutation_fails_closed(self):
        mismatch = assess_decision(BudgetDecision.PRUNE, BudgetDecision.UNRESOLVED)
        self.assertEqual(
            prune_decision(
                Decimal("1.0"),
                self._cert(),
                decision_commutation_required=True,
                decision_commutation=mismatch,
            ),
            BudgetDecision.UNRESOLVED,
        )

    def test_commutation_that_agrees_on_unresolved_does_not_authorize_prune(self):
        unresolved_match = assess_decision(BudgetDecision.UNRESOLVED, BudgetDecision.UNRESOLVED)
        result = certify_prune_decision(
            Decimal("1.0"),
            self._cert(),
            decision_commutation_required=True,
            decision_commutation=unresolved_match,
        )
        self.assertEqual(result.decision, BudgetDecision.UNRESOLVED)
        self.assertEqual(result.reason, "DECISION_COMMUTATION_DOES_NOT_SUPPORT_PRUNE")

    def test_passed_prune_decision_commutation_allows_prune(self):
        match = assess_decision(BudgetDecision.PRUNE, BudgetDecision.PRUNE)
        self.assertEqual(
            prune_decision(
                Decimal("1.0"),
                self._cert(),
                decision_commutation_required=True,
                decision_commutation=match,
            ),
            BudgetDecision.PRUNE,
        )

    def test_prefix_requires_exact_contiguous_coverage(self):
        with self.assertRaises(ValueError):
            make_tail_budget_certificate(
                start_n=10,
                prefix_bounds=[self._step(10, "0.1"), self._step(12, "0.1")],
                prefix_end_n=12,
                tail_upper=0,
                in_trust_region=True,
                method="bad-gap",
                provenance=("test",),
                horizon_certificate=self._horizon(propagated=0, tolerance=0),
            )

    def test_prefix_rejects_duplicate_or_out_of_order_steps(self):
        with self.assertRaises(ValueError):
            make_tail_budget_certificate(
                start_n=10,
                prefix_bounds=[self._step(10, "0.1"), self._step(10, "0.1")],
                prefix_end_n=12,
                tail_upper=0,
                in_trust_region=True,
                method="duplicate",
                provenance=("test",),
                horizon_certificate=self._horizon(propagated=0, tolerance=0),
            )

    def test_direct_malformed_step_value_is_rejected(self):
        bad = StepUpperBound(n=10, upper=Decimal("-1"), provenance=("bad",))
        with self.assertRaises(ValueError):
            make_tail_budget_certificate(
                start_n=10,
                prefix_bounds=[bad],
                prefix_end_n=11,
                tail_upper=0,
                in_trust_region=True,
                method="malformed-step",
                provenance=("test",),
                horizon_certificate=self._horizon(propagated=0, tolerance=0),
            )

    def test_zero_future_deformation_after_negative_floor_does_not_prune(self):
        cert = make_tail_budget_certificate(
            start_n=10,
            prefix_bounds=[],
            prefix_end_n=10,
            tail_upper=0,
            in_trust_region=True,
            method="zero-tail",
            provenance=("test",),
            horizon_certificate=self._horizon(propagated=0, tolerance=0),
        )
        self.assertEqual(prune_decision(Decimal("-0.1"), cert), BudgetDecision.UNRESOLVED)

    def test_earliest_name_is_semantically_one_sided(self):
        idx = first_unexcluded_crossing_index(
            Decimal("0.25"), [(10, Decimal("0.1")), (11, Decimal("0.2"))]
        )
        self.assertEqual(idx, 12)

    def test_crossing_bounds_must_be_contiguous(self):
        with self.assertRaises(ValueError):
            first_unexcluded_crossing_index(
                Decimal("0.25"), [(10, Decimal("0.1")), (12, Decimal("0.2"))]
            )


if __name__ == "__main__":
    unittest.main()
