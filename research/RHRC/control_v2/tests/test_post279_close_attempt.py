import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post279CloseAttemptTests(unittest.TestCase):
    def test_first_crossing_formal_surface_exists(self):
        required = [
            "Zeta23/CCM/ParityFirstNegativeBoundary.lean",
            "Zeta23/CCM/ParityZeroPlateau.lean",
            "Zeta23/CCM/ParityKernelTower.lean",
            "Zeta23/CCM/CanonicalParityFirstCrossingShell.lean",
            "Zeta23/CCM/FirstCrossingSchurReduction.lean",
            "Zeta23/CCM/FirstCrossingSourceDynamics.lean",
            "Zeta23/CCM/CanonicalApertureLocation.lean",
            "Zeta23/CCM/CanonicalInteriorFirstCrossingBarrier.lean",
            "Zeta23/CCM/CanonicalSeamFirstCrossingBarrier.lean",
            "Zeta23/CCM/CanonicalFirstCrossingBarrier.lean",
            "Zeta23/ExceptionalZero/CanonicalParityFirstCrossingShell.lean",
            "Zeta23/ExceptionalZero/CanonicalFirstCrossingConditionalRH.lean",
        ]
        for rel in required:
            with self.subTest(rel=rel):
                self.assertTrue((ROOT / rel).is_file(), rel)

    def test_premise_free_rh_closure_is_absent_until_barriers_are_proved(self):
        self.assertFalse(
            (ROOT / "Zeta23/ExceptionalZero/GlobalParityBottomRHClosure.lean").exists()
        )
        self.assertFalse(
            (ROOT / "Zeta23/ExceptionalZero/GlobalParityBottomExactTypeAudit.lean").exists()
        )
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

    def test_scalar_barriers_are_explicit_open_targets(self):
        interior = (
            ROOT / "Zeta23/CCM/CanonicalInteriorFirstCrossingBarrier.lean"
        ).read_text(encoding="utf-8")
        seam = (
            ROOT / "Zeta23/CCM/CanonicalSeamFirstCrossingBarrier.lean"
        ).read_text(encoding="utf-8")
        conditional = (
            ROOT / "Zeta23/ExceptionalZero/CanonicalFirstCrossingConditionalRH.lean"
        ).read_text(encoding="utf-8")
        exceptional_root = (ROOT / "Zeta23/ExceptionalZero.lean").read_text(
            encoding="utf-8"
        )
        self.assertIn("def CanonicalInteriorRegularEndpointBarrier", interior)
        self.assertIn("def CanonicalSeamRegularEndpointBarrier", seam)
        self.assertIn("riemannHypothesis_of_regularEndpointBarriers", conditional)
        self.assertNotIn(
            "import Zeta23.ExceptionalZero.CanonicalFirstCrossingConditionalRH",
            exceptional_root,
        )

    def test_generic_contact_falsifiers_stay_claim_capped(self):
        from closure_batch.first_crossing_generic_falsifiers import harvest

        result = harvest()
        self.assertEqual(result["terminal_claim"], "RH_OPEN")
        self.assertEqual(
            result["claim_cap"],
            "SYNTHETIC_GENERIC_COUNTERMODEL_ONLY",
        )


if __name__ == "__main__":
    unittest.main()
