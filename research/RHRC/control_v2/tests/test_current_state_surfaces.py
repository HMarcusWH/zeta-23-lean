import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

LIVING_SURFACES = (
    ROOT / "README.md", ROOT / "AUDIT.md", ROOT / "FORK_NOTES.md",
    RHRC / "CURRENT_RESEARCH_PLAN.md", RHRC / "DOCUMENTATION_AUTHORITY.md",
    RHRC / "FB05_INCOMPATIBILITY_PROGRAM.md", RHRC / "OBSTRUCTION_LEDGER.md",
    RHRC / "DEAD_ROUTES.md", RHRC / "README.md", RHRC / "RESEARCH_LEADS.md",
    RHRC / "VALIDATION_PROTOCOL.md", RHRC / "control_v2" / "README.md",
    RHRC / "routes" / "R003_ccm_bridge" / "README.md",
    RHRC / "countermodels" / "README.md",
)
BEGIN = "<!-- RHRC_CURRENT_STATE_BEGIN -->"
END = "<!-- RHRC_CURRENT_STATE_END -->"

def current_block(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise AssertionError(f"{path}: expected exactly one current-state marker pair")
    prefix, rest = text.split(BEGIN, 1)
    block, _suffix = rest.split(END, 1)
    if len(prefix.splitlines()) > 45:
        raise AssertionError(f"{path}: current-state block is not front-loaded")
    return block

class CurrentStateSurfaceTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_machine_state_is_merged_post247(self):
        theorem = self.state["merged_theorem_anchor"]
        self.assertEqual(theorem["pr"], 247)
        self.assertEqual(theorem["validated_head"], "7438f2a23750b1f4133c12b989eb9d81c1e99eea")
        self.assertEqual(theorem["merge_commit"], "070c0a08a924d0c917d5366755f9c4d50067ce51")
        self.assertEqual(theorem["tree"], "1672e49e092682343a2eace1e8e6e4799c102f35")
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 247)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        route = self.state["active_research_route"]
        self.assertEqual(route["post247_next_research_target"], "UNCONDITIONAL_GROUND_SPECTRUM_ATLAS")
        self.assertEqual(
            route["post247_required_new_information"],
            "NONVACUOUS_ARITHMETIC_CONTROL_OF_GROUND_SPECTRUM_ACROSS_PRIME_POWER_THRESHOLDS",
        )
        self.assertEqual(route["post246_canonical_prime_remainder_normal_form"], "PROVED_PR_246")
        self.assertEqual(route["post247_glasses_program"], "ACTIVE_RIEMANN_WEARING_GLASSES_V2")
        self.assertEqual(route["post247_global_aperture_loewner_monotonicity"], "QUARANTINED_DR_021")
        self.assertEqual(route["post247_global_minimizing_schur_monotonicity"], "QUARANTINED_DR_022")
        self.assertEqual(route["post247_relation_zeta"], "PARKED_SPECULATIVE")
        self.assertEqual(route["post249_zero_side_perturbation_control"], "BUILT_EXPERIMENTAL_PR_249")
        self.assertEqual(route["post249_globally_consistent_planted_zeta_control"], "OPEN")
        self.assertEqual(route["post249_ratio_asymptotic_rate"], "NOT_ESTABLISHED")
        self.assertEqual(route["post249_first_zero_scale_signal"], "COARSE_GRID_SEPARATION_NOT_EXACT_SWITCH")
        scout = self.state["post249_research_scout"]
        self.assertEqual(scout["pr"], 249)
        self.assertEqual(scout["validated_head"], "1758ed7fd1fd0bbae6b6929b3793fa8e97288b55")
        self.assertEqual(scout["merge_commit"], "caec6773664458bde0eac55cf1ad60446c385efd")
        self.assertEqual(scout["workflow_harvest"], "11_OF_11_ATTACHED_WORKFLOWS_SUCCESS")
        self.assertFalse(scout["theorem_promotion"])
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #247",
            "7438f2a23750b1f4133c12b989eb9d81c1e99eea",
            "070c0a08a924d0c917d5366755f9c4d50067ce51",
            "1672e49e092682343a2eace1e8e6e4799c102f35",
            "MERGED_VIA_PR_247",
            "11/11 ATTACHED WORKFLOWS COMPLETED SUCCESSFULLY",
            "terminal Mathlib RH seam = PROVED / PR #242",
            "PR #246 ARITHMETIC NORMAL FORM",
            "CanonicalPrimeRemainderDominance <-> RiemannHypothesis = PROVED / PR #246",
            "PR #247 GLOBAL-BOTTOM REDUCTION",
            "off-line zero -> arbitrarily-large GlobalBottomArithmeticResidual = PROVED / PR #247",
            "GlobalBottomResidualExclusion <-> RiemannHypothesis = PROVED / AUDIT-ONLY / PR #247",
            "active programme = RIEMANN_WEARING_GLASSES_V2",
            "next research target = UNCONDITIONAL_GROUND_SPECTRUM_ATLAS",
            "global aperture Loewner monotonicity = QUARANTINED / DR-021",
            "global minimizing-Schur monotonicity = QUARANTINED / DR-022",
            "relation zeta = PARKED / SPECULATIVE",
            "post-249 = FINITE_GRID_SHARP_CANCELLATION / ZERO_SIDE_PERTURBATION_CONTROL_BUILT / EXPERIMENTAL_SIGNAL_ONLY",
            "post-249 interpretation firewall = NO ASYMPTOTIC RATE / NO EXACT FIRST-ZERO SWITCH / SIGN-CHANGE BRACKETS NOT GLOBAL MINIMA",
            "planted zero-side perturbation control = BUILT / PR #249 / EXPERIMENTAL_SIGNAL_ONLY",
            "globally consistent planted zeta/Euler-product control = OPEN",
            "PR #117",
            "PR #223",
            "terminal claim = RH_OPEN",
        )
        forbidden = (
            "merged theorem authority = PR #245",
            "canonical prime-remainder normal form = CANDIDATE",
            "next research target = CANONICAL_PRIME_REMAINDER_DOMINANCE",
            "required new information = RH_STRENGTH_WEIGHTED_CHEBYSHEV_REMAINDER_INFORMATION",
            "planted off-line canonical-style control = TO BUILD / PRIMARY FALSIFIER",
            "RH = PROVED",
        )
        for path in LIVING_SURFACES:
            with self.subTest(path=path):
                block = current_block(path)
                for token in required:
                    self.assertIn(token, block)
                for token in forbidden:
                    self.assertNotIn(token, block)

    def test_control_semantics_remain_frozen(self):
        action_registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            action_registry["current_frontier"],
            "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN",
        )
        self.assertEqual(
            [b["id"] for b in action_registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]["first_breaks"]],
            ["E4A4-SCHUR-FB-05"],
        )

if __name__ == "__main__":
    unittest.main()
