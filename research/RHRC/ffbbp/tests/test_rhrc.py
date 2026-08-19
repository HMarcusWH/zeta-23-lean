import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from ffbbp.adapter import Observation, associate_source_only
from ffbbp.gates import collapse_gate, unknown_field_admission_gate
from ffbbp.nulls import assess_known_null
from ffbbp.ablation import candidate_aligned_ablation
from ffbbp.commutation import assess as assess_commutation
from ffbbp.replay import deterministic_split, assert_lockbox_disjoint
from ffbbp.transfer import require_positive_lift
from synthetic.gauntlet import build_worlds, distinguish_from_tightmult_only, positive_log_slope
from tools.claim_lint import lint
from interventions.intervention import InterventionSpec, run

class RHRCTests(unittest.TestCase):
    def test_ffbbp_reference_is_v1_5_1_with_closure_overlay(self):
        ref = json.loads((RHRC / "ffbbp" / "FFBBP_REFERENCE.json").read_text())
        self.assertEqual(ref["reference_architecture_version"], "1.5.1")
        self.assertEqual(ref["implementation_closure_overlay"], "research/RHRC/ffbbp/IMPLEMENTATION_CLOSURE_OVERLAY.json")
        self.assertEqual(ref["qualified_profile"]["name"], "RUN42B_A0")
        self.assertEqual(ref["unknown_field_admission"]["claim_cap"], "diagnostic_only")

    def test_run42b_profile_is_exactly_bound(self):
        profile = json.loads((RHRC / "ffbbp" / "configs" / "run42b_a0_v1_5_qualified_profile.json").read_text())
        self.assertEqual(profile["fresh_seeds"], [83, 101, 127, 149, 173])
        self.assertEqual(profile["benchmark"]["split"], {"calibration": 0.60, "validation": 0.20, "lockbox": 0.20})
        self.assertEqual(profile["association"]["temperature"], 0.015)
        self.assertTrue(profile["material_change_requires_requalification"])

    def test_unknown_field_admission_is_two_sided(self):
        blocked = unknown_field_admission_gate(
            known_null_pass=True, known_positive_pass=False, matched_artifact_pass=True,
            firewall_pass=True, profile_frozen=True, domain_adapter_frozen=True)
        self.assertFalse(blocked.passed)
        self.assertIn("V06P_KNOWN_POSITIVE_FAIL", blocked.blockers)
        admitted = unknown_field_admission_gate(
            known_null_pass=True, known_positive_pass=True, matched_artifact_pass=True,
            firewall_pass=True, profile_frozen=True, domain_adapter_frozen=True)
        self.assertTrue(admitted.passed)

    def test_source_target_firewall(self):
        prototypes = [(0.0, 0.0), (10.0, 10.0)]
        a = associate_source_only(Observation((0.1, 0.2), target=1e9), prototypes)
        b = associate_source_only(Observation((0.1, 0.2), target=-1e9), prototypes)
        self.assertEqual(a, b)

    def test_tightmult_sanity(self):
        w = build_worlds()
        self.assertEqual(distinguish_from_tightmult_only(w["G03"], w["G04"]), "INSUFFICIENT_INFORMATION")

    def test_new_channel_can_change_information(self):
        w = build_worlds()
        self.assertTrue(positive_log_slope(w["G06"].multiscale_probe))

    def test_run38_null_regression_remains_clean(self):
        res = assess_known_null([0.00045, 0.00030, 0.00044, 0.00035, 0.00060, 0.00045], mean_max=0.045, individual_max=0.070)
        self.assertTrue(res.passed)

    def test_best_null_gate_fails_closed(self):
        res = collapse_gate(candidate_rmse=0.00410, null_rmses={"adversarial": 0.00408}, known_null_pass=True,
                            firewall_pass=True, ablation_pass=True, transfer_pass=True, commutation_pass=True)
        self.assertFalse(res.passed)
        self.assertIn("BEST_NULL_NOT_BEATEN", res.blockers)

    def test_intervention_enforces_hold_fixed(self):
        spec = InterventionSpec("J_delta", "delta", ("gamma",), "growth", "diagnostic only")
        state = {"delta": 0.01, "gamma": 100.0}
        out = run(spec, state, lambda s: s.__setitem__("delta", 0.02), lambda s: s["delta"] * 2)
        self.assertNotEqual(out.before, out.after)

    def test_candidate_aligned_ablation(self):
        self.assertTrue(candidate_aligned_ablation(0.0040, 0.0042).passed)

    def test_commutation(self):
        self.assertTrue(assess_commutation(0.00400, 0.00401, scale=0.004, absolute_max=0.00002, relative_max=0.01).passed)

    def test_run42b_frozen_split(self):
        split = deterministic_split(tuple(range(100)), calibration_fraction=0.60, validation_fraction=0.20)
        assert_lockbox_disjoint(split)
        self.assertEqual((len(split.calibration), len(split.validation), len(split.lockbox)), (60,20,20))

    def test_transfer_fails_closed_on_missing_relock(self):
        result = require_positive_lift({"middle_to_late": 0.01, "late_to_late": None}, ("middle_to_late","late_to_late"))
        self.assertFalse(result.passed)

    def test_full_gauntlet_fixture_ids(self):
        self.assertEqual(set(build_worlds()), {f"G{i:02d}" for i in range(12)})

    def test_claim_registry(self):
        registry = RHRC / "CLAIM_REGISTRY.json"
        self.assertEqual(lint(registry), [])

if __name__ == "__main__":
    unittest.main()
