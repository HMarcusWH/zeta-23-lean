import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent
sys.path.insert(0, str(RHRC / "control_v2"))

from render_current_state import (
    BEGIN,
    END,
    LIVING_SURFACES,
    render_current_state_block,
)

def current_block(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise AssertionError(f"{path}: expected exactly one current-state marker pair")
    prefix, rest = text.split(BEGIN, 1)
    block, _suffix = rest.split(END, 1)
    if len(prefix.splitlines()) > 45:
        raise AssertionError(f"{path}: current-state block is not front-loaded")
    return block.strip("\n")


class CurrentStateSurfaceTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_machine_state_is_merged_post271(self):
        theorem = self.state["merged_theorem_anchor"]
        self.assertEqual(theorem["pr"], 271)
        self.assertEqual(theorem["validated_head"], "3b1dfb8337125b10ce99febbb974ff8c7086394e")
        self.assertEqual(theorem["merge_commit"], "c9fb1a6462e5cc828acb951aefd4e9fae33ddaaa")
        self.assertEqual(theorem["tree"], "10ba766b13e63fb5e5567c3da7a3910f54fe6812")
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 271)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        route = self.state["active_research_route"]
        self.assertEqual(route["post267_n_flow_bottom_monotonicity"], "PROVED_PR_267")
        self.assertEqual(route["post268_canonical_carrier_bottom_hierarchy"], "PROVED_PR_268")
        self.assertEqual(
            route["post269_parity_split_ground_simplicity"],
            "PROVED_IFF_STRICT_PARITY_SEPARATION",
        )
        self.assertEqual(
            route["post269_carrier_source_weight_monotonicity"],
            "REFUTED_FORMALLY",
        )
        self.assertEqual(route["current_obstruction"], "OBS-061_RECLASSIFICATION_FIREWALL")
        self.assertEqual(
            route["current_next_research_target"],
            "GROUND_SPECIFIC_FIRST_CONTACT_ARITHMETIC_SEAM",
        )
        self.assertEqual(
            route["current_required_new_information"],
            "TRUE_GROUND_FIXED_CELL_AND_PRIME_POWER_SEAM_DISCRIMINANT",
        )
        self.assertEqual(route["post271_source_only_public_theorem_count"], 683)
        self.assertEqual(route["post271_ffbbp_source_only_module_cohort_count"], 198)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_exactly_matches_machine_renderer(self):
        expected = render_current_state_block(self.state)
        for path in LIVING_SURFACES:
            with self.subTest(path=path):
                self.assertEqual(current_block(path), expected)

    def test_renderer_preserves_claim_firewall(self):
        block = render_current_state_block(self.state)
        self.assertIn("RH = OPEN", block)
        self.assertIn("direct cofinal certificate construction = OPEN on merged theorem authority", block)
        self.assertIn(
            "current audit target = CofinalCanonicalArithmeticCertificates <-> RiemannHypothesis",
            block,
        )
        self.assertIn(
            "equivalence audit cannot promote RH; it only classifies the terminal premise",
            block,
        )
        self.assertNotIn("RH = PROVED", block)

    def test_control_semantics_remain_frozen(self):
        action_registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            action_registry["current_frontier"],
            "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN",
        )
        self.assertEqual(
            [
                b["id"]
                for b in action_registry["actions"][
                    "E4_A4_REGULAR_SCHUR_ENERGY_SIGN"
                ]["first_breaks"]
            ],
            ["E4A4-SCHUR-FB-05"],
        )


if __name__ == "__main__":
    unittest.main()
