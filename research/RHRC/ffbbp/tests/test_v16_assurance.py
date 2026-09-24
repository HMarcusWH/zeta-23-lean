import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from ffbbp.v16_commutation import assess_decision, assess_diagnostic
from ffbbp.v16_contracts import ExplicitWitnessCertificate, MaskingStatus, XiMode, XiReductionContract
from ffbbp.v16_gates import reduction_assurance_gate
from ffbbp.v16_horizon import ResidualHorizonContract, HorizonStatus, certify_horizon
from ffbbp.v16_witness import assess_witness


class FFBBPV16AssuranceTests(unittest.TestCase):
    def test_overlay_does_not_inherit_run42c_qualification(self):
        overlay = json.loads((RHRC / "ffbbp" / "FFBBP_V16_ASSURANCE_REFERENCE.json").read_text())
        self.assertFalse(overlay["inherits_run42c_qualification"])
        old = json.loads((RHRC / "ffbbp" / "FFBBP_REFERENCE.json").read_text())
        self.assertIn("RUN42C", old["reference_architecture_version"])

    def test_diagnostic_close_can_still_flip_decision(self):
        diag = assess_diagnostic(1e-12, -1e-12, scale=1.0, absolute_max=1e-9, relative_max=1e-9)
        dec = assess_decision(True, False)
        self.assertTrue(diag.passed)
        self.assertFalse(dec.passed)

    def test_small_local_residual_is_not_horizon_certificate(self):
        contract = ResidualHorizonContract(
            "nested_spectral_floor", 1e-12, None, 100.0, "headroom", "declared-tail-model"
        )
        cert = certify_horizon(contract, in_trust_region=True, propagated_upper=None, tolerance=1e-6)
        self.assertEqual(cert.status, HorizonStatus.HORIZON_BOUND_UNAVAILABLE)
        self.assertFalse(cert.passed)

    def test_outside_trust_region_fails_closed(self):
        contract = ResidualHorizonContract(
            "nested_spectral_floor", 1e-4, 2.0, 10.0, "headroom", "N<=1000"
        )
        cert = certify_horizon(contract, in_trust_region=False, propagated_upper=1e-5, tolerance=1e-3)
        self.assertEqual(cert.status, HorizonStatus.OUTSIDE_TRUST_REGION)

    def test_witness_requires_masking_clearance(self):
        cert = ExplicitWitnessCertificate(
            "w1", True, 1.0, 0.1, MaskingStatus.UNRESOLVED, ("fixture",)
        )
        result = assess_witness(cert)
        self.assertFalse(result.passed)
        self.assertIn("WITNESS_MASKING_UNRESOLVED", result.blockers)

    def test_decision_gate_requires_decision_commutation(self):
        result = reduction_assurance_gate(
            diagnostic_commutation_pass=True,
            decision_bearing=True,
            decision_sufficiency_pass=True,
            decision_commutation_pass=False,
            stateful_reduction=False,
            transition_closure_pass=None,
            horizon_bearing=False,
            horizon_certificate=None,
            witness_bearing=False,
            witness_pass=None,
        )
        self.assertFalse(result.passed)
        self.assertIn("DECISION_COMMUTATION_NOT_ESTABLISHED", result.blockers)

    def test_decision_gate_requires_snapshot_sufficiency(self):
        result = reduction_assurance_gate(
            diagnostic_commutation_pass=True,
            decision_bearing=True,
            decision_sufficiency_pass=False,
            decision_commutation_pass=True,
            stateful_reduction=False,
            transition_closure_pass=None,
            horizon_bearing=False,
            horizon_certificate=None,
            witness_bearing=False,
            witness_pass=None,
        )
        self.assertFalse(result.passed)
        self.assertIn("DECISION_SUFFICIENCY_NOT_ESTABLISHED", result.blockers)

    def test_stateful_reduction_requires_transition_closure(self):
        result = reduction_assurance_gate(
            diagnostic_commutation_pass=True,
            decision_bearing=False,
            decision_sufficiency_pass=None,
            decision_commutation_pass=None,
            stateful_reduction=True,
            transition_closure_pass=None,
            horizon_bearing=False,
            horizon_certificate=None,
            witness_bearing=False,
            witness_pass=None,
        )
        self.assertFalse(result.passed)
        self.assertIn("STATEFUL_TRANSITION_CLOSURE_NOT_ESTABLISHED", result.blockers)

    def test_snapshot_contract_matches_v16_typed_surface(self):
        contract = XiReductionContract(
            reduction_id="r",
            xi_mode=XiMode.SNAPSHOT,
            source_state_schema="full",
            xi_schema="xi",
            reduction_map_version="1",
            reference_path_id="ref",
            diagnostic_map_id="diag",
            decision_map_id="decision",
            metric_refs=("exact-categorical",),
            clock_contract_refs=("not-applicable-static",),
            trust_region={"scope": "fixture"},
            claim_cap_ref="cap",
            provenance_hash="0" * 64,
        )
        contract.validate()


if __name__ == "__main__":
    unittest.main()
