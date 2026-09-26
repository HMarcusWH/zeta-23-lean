import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

class Post247SyncTests(unittest.TestCase):
    def setUp(self):
        self.state=json.loads((RHRC/"control_v2"/"CONTROL_STATE.json").read_text(encoding="utf-8"))

    def test_post247_history_survives_post271_authority(self):
        t=self.state["merged_theorem_anchor"]
        self.assertEqual(t["pr"],271)
        note=self.state["control_note"]
        for token in (
            "PR #247",
            "7438f2a23750b1f4133c12b989eb9d81c1e99eea",
            "070c0a08a924d0c917d5366755f9c4d50067ce51",
            "1672e49e092682343a2eace1e8e6e4799c102f35",
        ):
            self.assertIn(token,note)
        self.assertEqual(self.state["merged_control_anchor"]["pr"],117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"],223)
        self.assertEqual(self.state["terminal_claim"],"RH_OPEN")

    def test_global_bottom_declarations_are_present(self):
        checks={
            ROOT/"Zeta23"/"CCM"/"GlobalParityBottomSpectrum.lean":(
                "theorem globalParitySuccessorBottom_neg_iff_anyParityBad",
            ),
            ROOT/"Zeta23"/"CCM"/"GlobalParityBottomBranchPackage.lean":(
                "inductive GlobalBottomBranchPackage",
                "theorem GlobalBottomResidualState.exists_branchPackage",
            ),
            ROOT/"Zeta23"/"CCM"/"GlobalParityBottomGroundTrial.lean":(
                "theorem GlobalBottomResidualState.groundTrial_ne_zero",
                "theorem GlobalBottomResidualState.groundTrial_eigenmode",
                "theorem GlobalBottomResidualState.groundTrial_channelEnergy_neg",
            ),
            ROOT/"Zeta23"/"CCM"/"GlobalParityBottomPrimeWeight.lean":(
                "def GlobalBottomResidualState.primeTestWeight",
                "theorem GlobalBottomResidualState.continuous_primeTestWeight",
                "theorem GlobalBottomResidualState.primeRemainderEnergy_eq_weight_integral",
            ),
            ROOT/"Zeta23"/"ExceptionalZero"/"GlobalParityBottomTerminalTarget.lean":(
                "exists_arbitrarilyLarge_globalBottomArithmeticResidual_of_offLine_zero",
            ),
            ROOT/"Zeta23"/"ExceptionalZero"/"GlobalParityBottomArithmeticEquivalenceAudit.lean":(
                "theorem globalBottomResidualExclusion_iff_riemannHypothesis",
            ),
        }
        for path,tokens in checks.items():
            text=path.read_text(encoding="utf-8")
            for token in tokens:
                self.assertIn(token,text)

    def test_audit_only_equivalence_is_not_active_exceptionalzero_root_import(self):
        root=(ROOT/"Zeta23"/"ExceptionalZero.lean").read_text(encoding="utf-8")
        self.assertNotIn("GlobalParityBottomArithmeticEquivalenceAudit",root)
        self.assertNotIn("GlobalParityBottomConditionalRH",root)
        self.assertNotIn("CofinalArithmeticConditionalRH",root)
        self.assertNotIn("CofinalArithmeticEquivalenceAudit",root)

    def test_glasses_v2_is_current_and_tautological_lanes_are_demoted(self):
        route=self.state["active_research_route"]
        self.assertEqual(route["post247_glasses_program"],"ACTIVE_RIEMANN_WEARING_GLASSES_V2")
        self.assertEqual(route["post247_unconditional_ground_spectrum_atlas"],"NEXT")
        self.assertEqual(route["post247_residual_only_universal_law"],"VACUITY_FIREWALL_REQUIRED")
        self.assertEqual(route["post247_pair_d_role"],"GENERIC_LINEAR_ALGEBRA_FILTER_ONLY")
        self.assertEqual(route["post247_exact_equality_holonomy"],"DROPPED_TAUTOLOGICAL")
        self.assertEqual(route["post247_ordinary_hilbert_gram_psd"],"DROPPED_TAUTOLOGICAL")
        self.assertEqual(route["post247_relation_zeta"],"PARKED_SPECULATIVE")
        program=(RHRC/"routes"/"R003_ccm_bridge"/"POST_247_RIEMANN_WEARING_GLASSES_PROGRAM.md").read_text(encoding="utf-8")
        for token in (
            "unconditional ground-spectrum atlas",
            "Residual-state vacuity firewall",
            "Threshold-local first crossing",
            "Relation-zeta",
            "RH remains OPEN",
        ):
            self.assertIn(token,program)

if __name__ == "__main__":
    unittest.main()
