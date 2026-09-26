import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]

EXPECTED_R003_CLAIM_IDS = [
    "R003_DISPLACEMENT_TRANSFER",
    "R003_RESIDUAL_C2",
    "R003_TENT_ANALYTICS",
    "R003_TENT_MOLLIFIER_ARCHITECTURE",
    "R003_TENT_EF_EXTENSION",
    "R003_CCM_RHS_IDENTITY",
    "R003_KERNEL_EF_EXTENSION",
    "R003_CCM_BRIDGE",
    "R003_CUTOFF_FREE_MATRIX_MAP",
    "R003_WEIL_DISPLACEMENT",
    "R003_LOCALIZED_BASIS_CORRELATION",
    "R003_LOCALIZED_FINITE_SPACE_CORRELATION",
    "R003_LOCALIZED_ADDITIVE_RHS_RESTRICTION",
    "R003_SOURCE_WEIL_NORMALIZATION_FIREWALL",
    "R003_SOURCE_NORMALIZATION_REPAIR",
    "R003_SOURCE_KAPPA_FINITE_SECTOR",
    "R003_WEIL_PAIR_LITERATURE_BRIDGE",
    "R003_NEGATIVE_WEIL_TEST_CONTRACTION",
    "R003_STRICT_APERTURE_NEGATIVE_WEIL_TEST",
    "R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE",
    "R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS",
    "R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION",
    "R003_BOUNDARY_FLAT_PROJECTION",
    "R003_WEIL_COMMON_SUPPORT_BOUND",
    "R003_LOCALIZED_UNIFORM_C2_APPROXIMATION",
    "R003_BOUNDARY_FLAT_WCONT_APPROXIMATION",
    "R003_STRICT_FINITE_NEGATIVE_WEIL_TRANSFER",
    "R003_FINITE_CANONICAL_NEGATIVE_OBSTRUCTION",
    "R003_BOUNDARY_FLAT_MOMENT_FLAG",
    "R003_CANONICAL_SOURCE_HERMITIAN",
    "R003_CONSTRAINED_CANONICAL_DISPLACEMENT",
    "R003_UNIT_CONSTRAINED_CANONICAL_NEGATIVE_OBSTRUCTION",
    "R003_BOUNDARY_FLAT_EXACT_DIMENSION",
    "R003_EUCLIDEAN_BOUNDARY_FLAT_SECTOR",
    "R003_CANONICAL_EUCLIDEAN_SYMMETRIC",
    "R003_CANONICAL_EUCLIDEAN_QUADRATIC_BRIDGE",
    "R003_EUCLIDEAN_CONSTRAINED_NEGATIVE_OBSTRUCTION",
    "R003_EXACT_CENTERED_FINITE_NESTING",
    "R003_EUCLIDEAN_CONSTRAINED_NESTING",
    "R003_NESTED_EUCLIDEAN_NEGATIVE_OBSTRUCTION",
    "R003_CONSTRAINED_REVERSAL_SYMMETRY",
    "R003_EVEN_CONSTRAINED_DISPLACEMENT_COLLAPSE",
    "R003_CONSTRAINED_PARITY_LINEAR_EQUIV",
    "R003_CONSTRAINED_PARITY_EXACT_DIMENSION",
    "R003_PARITY_PRESERVING_EUCLIDEAN_NFLOW",
    "R003_PARITY_QUADRATIC_SPLIT",
    "R003_PARITY_BAD_NFLOW",
    "R003_LEAST_PARITY_BAD_SHELL",
    "R003_FIXED_PARITY_BAD_TAIL_FROM_OFFLINE_ZERO",
    "R003_FIRST_BAD_PARITY_ONE_DIM_SHELL",
    "R003_PARITY_CONSTRAINED_SPECTRAL_COMPRESSION",
    "R003_PARITY_BAD_NEGATIVE_EIGENMODE",
    "R003_SUCCESSOR_PREDECESSOR_NONNEGATIVITY",
    "R003_FIRST_BAD_NEGATIVE_EIGENMODE_NOT_INHERITED",
    "R003_FIRST_BAD_PARITY_NEGATIVE_EIGENMODE_FROM_OFFLINE_ZERO",
    "R003_FIRST_BAD_SHELL_PROJECTION",
    "R003_PARITY_NORMAL_KKT",
    "R003_FIRST_BAD_SHELL_KKT_FROM_OFFLINE_ZERO",
    "R003_PARITY_COMPRESSION_RANK_ONE_DEFECT",
]


class Post193SyncTests(unittest.TestCase):
    def test_authority_split_preserves_post193_history(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertGreaterEqual(state["merged_theorem_anchor"]["pr"], 184)
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

        note = state["control_note"]
        for token in (
            "PR #184",
            "6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e",
            "PR #192",
            "PR #193",
            "085634ca7dafe4d9f598b2b5e081be80e050ba8c",
            "fdd6606f85e92bf632b4cdaf1d4af85f6fa5b195",
            "db569150046459f4b87a931d3e8d01054bbbedff",
            "RHRC #1109",
            "Permansson #882",
            "canonical realizability audit #5",
            "parity trajectory rigidity #3",
            "TRAJECTORY_RIGIDITY_UNRESOLVED",
            "63/96",
            "33/96",
            "same frozen Q14 hull",
            "RH remain OPEN",
        ):
            self.assertIn(token, note)

    def test_living_docs_advance_through_193(self):
        paths = (
            RHRC.parent.parent / "README.md",
            RHRC.parent.parent / "AUDIT.md",
            RHRC.parent.parent / "FORK_NOTES.md",
            RHRC / "README.md",
            RHRC / "CURRENT_RESEARCH_PLAN.md",
            RHRC / "DOCUMENTATION_AUTHORITY.md",
            RHRC / "RESEARCH_LEADS.md",
            RHRC / "VALIDATION_PROTOCOL.md",
            RHRC / "FB05_INCOMPATIBILITY_PROGRAM.md",
            RHRC / "routes" / "R003_ccm_bridge" / "README.md",
            RHRC / "control_v2" / "README.md",
        )
        for path in paths:
            text = path.read_text(encoding="utf-8")
            with self.subTest(path=path):
                self.assertIn("#184", text)
                self.assertIn("#190", text)
                self.assertIn("#192", text)
                self.assertIn("#193", text)
                self.assertIn("canonical", text.lower())
                self.assertIn("RH remains OPEN", text)

    def test_current_plan_preserves_history_and_moves_frontier(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "Layer 0",
            "Layer 5",
            "canonical production realizability",
            "EXACT_TWIN_SURVIVES",
            "EXACT_TWIN_EXCLUDED_BY_IDENTITY",
            "UNRESOLVED",
            "TRAJECTORY_RIGIDITY_UNRESOLVED",
            "J = o'e - e'o",
            "P2 = L*J/(o*e)",
            "6/6",
            "63",
            "33",
            "higher-order canonical trajectory enclosure",
            "same frozen Q14 hull",
        ):
            self.assertIn(token, text)
        self.assertIn("Do **not** infer this from points", text)
        self.assertNotIn("J(L) > 0 throughout the exact frozen Q14 primary hull\n  PROVED", text)

    def test_action_registry_ids_scores_unchanged_and_rerouted(self):
        registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            registry["current_frontier"],
            "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN",
        )
        action = registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]
        self.assertEqual(action["concept_id"], "canonical_source_exclusion")
        self.assertEqual(
            action["score_inputs"],
            {
                "cost": 2.0,
                "information_gain": 5.0,
                "falsification_value": 5.0,
                "closure_value": 5.0,
                "residual_risk": 1.8,
                "dependency_debt": 0.8,
            },
        )
        self.assertEqual([b["id"] for b in action["first_breaks"]], ["E4A4-SCHUR-FB-05"])
        objections = "\n".join(action["surviving_objections"])
        for token in (
            "PR #192",
            "PR #193",
            "0/15 seven-vector overlaps",
            "all six inherited exact Q14 primary centers",
            "TRAJECTORY_RIGIDITY_UNRESOLVED",
            "63/96",
            "33/96",
            "same frozen Q14 hull",
            "second-order/Taylor",
        ):
            self.assertIn(token, objections)

    def test_r003_route_preserves_post193_claim_ids(self):
        registry = json.loads(
            (RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8")
        )
        route = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(route["phase"], "DISCOVERY")
        self.assertFalse(route["confirmatory_execution_authorized"])

        # Historical post-#193 synchronization promised not to mutate the then-current
        # claim surface. Later theorem PRs are allowed to append new reviewed claims.
        # Preserve the historical block exactly and in order, while permitting only
        # downstream additions after it.
        self.assertGreaterEqual(len(route["claim_ids"]), len(EXPECTED_R003_CLAIM_IDS))
        self.assertEqual(
            route["claim_ids"][: len(EXPECTED_R003_CLAIM_IDS)],
            EXPECTED_R003_CLAIM_IDS,
        )
        for current_claim in (
            "R003_PARITY_SPLIT_GROUND_SIMPLICITY",
            "R003_PARITY_TIE_GROUND_MULTIPLICITY",
            "R003_CANONICAL_ARITHMETIC_LOWER_BOUND_NORMAL_FORM",
            "R003_CANONICAL_ARITHMETIC_GLOBAL_BOTTOM_LOWER_BOUND",
            "R003_COFINAL_BOTTOM_NONNEGATIVITY",
            "R003_COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES",
        ):
            self.assertIn(current_claim, route["claim_ids"])

        self.assertIsNone(route["route_spec_digest"])
        self.assertIsNone(route["boundary_digest"])
        note = route["note"]
        for token in (
            "PR #192",
            "PR #193",
            "TRAJECTORY_RIGIDITY_UNRESOLVED",
            "same frozen Q14 hull",
            "No claim_ids are changed by this synchronization",
        ):
            self.assertIn(token, note)

    def test_post193_aliases_are_scoped(self):
        aliases = json.loads(
            (RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json").read_text(
                encoding="utf-8"
            )
        )
        terms = aliases["canonical_source_exclusion"]
        for term in (
            "parity Wronskian",
            "parity log-slope gap",
            "Q14 parity trajectory rigidity",
            "canonical aperture fingerprint",
            "first-order trajectory enclosure",
            "TRAJECTORY_RIGIDITY_UNRESOLVED",
        ):
            self.assertIn(term, terms)
        for generic in ("trajectory", "Wronskian", "monotonicity", "Taylor"):
            self.assertNotIn(generic, terms)

    def test_historical_post190_records_remain(self):
        delta = RHRC / "RESEARCH_LEADS_POST_190_JOINT_SELECTOR_SEPARABILITY_DELTA.md"
        obstruction = RHRC / "OBSTRUCTION_LEDGER_POST_190_DELTA.md"
        self.assertTrue(delta.exists())
        self.assertTrue(obstruction.exists())
        self.assertIn("JOINT_EXACT_VECTOR_SEPARABLE", delta.read_text(encoding="utf-8"))
        self.assertIn("OBS-054", obstruction.read_text(encoding="utf-8"))

    def test_post193_delta_has_required_post_green_sections(self):
        delta = (
            RHRC / "RESEARCH_LEADS_POST_193_PARITY_TRAJECTORY_DELTA.md"
        ).read_text(encoding="utf-8")
        for heading in (
            "# What became formally true",
            "# What became research-certified",
            "# What changed",
            "# Upstream implications",
            "# Downstream implications",
            "# Resurrected routes",
            "# New RH-relevant clues",
            "# Falsification checks",
            "# Highest-leverage next moves",
            "# Standing questions",
        ):
            self.assertIn(heading, delta)
        for token in (
            "J = o'e - e'o",
            "P2 = L*J/(o*e)",
            "TRAJECTORY_RIGIDITY_UNRESOLVED",
            "63 H1_UNRESOLVED",
            "33 J_UNRESOLVED",
            "RH remains OPEN",
        ):
            self.assertIn(token, delta)

    def test_obs055_is_narrow_representation_obstruction(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_193_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-055",
            "first-order centered parity-trajectory enclosure",
            "63 H1_UNRESOLVED",
            "33 J_UNRESOLVED",
            "0 J_NEGATIVE",
            "0 J_POSITIVE",
            "TRAJECTORY_RIGIDITY_UNRESOLVED",
            "does not falsify monotonicity",
            "OBS-054",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)


if __name__ == "__main__":
    unittest.main()
