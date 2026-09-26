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

    def test_machine_state_is_merged_post269(self):
        theorem = self.state["merged_theorem_anchor"]
        self.assertEqual(theorem["pr"], 269)
        self.assertEqual(theorem["validated_head"], "d228f35ca3338520131a883b9091fad16ef9c9b9")
        self.assertEqual(theorem["merge_commit"], "b7912d13801389a4c6e3236f98c28435254d685d")
        self.assertEqual(theorem["tree"], "9d2fff6ed5b0ecc3ea55e363de6df80410a720c3")
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 269)
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
        self.assertEqual(route["current_obstruction"], "OBS-061")
        self.assertEqual(
            route["current_next_research_target"],
            "COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES",
        )
        self.assertEqual(
            route["current_required_new_information"],
            "UNIFORM_ALL_VECTOR_CANONICAL_ARITHMETIC_DECAY_ON_COFINAL_APERTURES_AND_SIZES",
        )
        self.assertEqual(route["post270_source_only_public_theorem_count"], 707)
        self.assertEqual(route["post270_ffbbp_source_only_module_cohort_count"], 202)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_exactly_matches_machine_renderer(self):
        expected = render_current_state_block(self.state)
        for path in LIVING_SURFACES:
            with self.subTest(path=path):
                self.assertEqual(current_block(path), expected)

    def test_renderer_preserves_claim_firewall(self):
        block = render_current_state_block(self.state)
        self.assertIn("RH = OPEN", block)
        self.assertIn("cofinal arithmetic certificate construction = OPEN", block)
        self.assertIn(
            "CofinalCanonicalArithmeticCertificates -> RiemannHypothesis = CURRENT PR AUDIT TARGET",
            block,
        )
        self.assertIn(
            "no reverse RH-equivalence claim is made for CofinalCanonicalArithmeticCertificates",
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
