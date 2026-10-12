import json
import re
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parents[1]
STATE = RHRC / "control_v2" / "CONTROL_STATE.json"
POST284 = RHRC / "integration" / "post284"

HEAD = "40495f39b7510b49a7fe3493b42d9fe3880d6d22"
MERGE = "ecc6450f28eb6aed944bda8fe9a09296d033fc3e"
TREE = "a105ffd52c96cd0c39712dcdba45e967282efc9d"

F04 = "Zeta23.CCM.productionContactF04DerivativeAuthority_of_pos"
PAIR = "Zeta23.CCM.canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos"
FRONTIER = "Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier_unconditional"
EXPECTED = {
    "R003_PRODUCTION_F04_DERIVATIVE_AUTHORITY": (F04, "Zeta23/CCM/CanonicalGlobalF04.lean"),
    "R003_WEIGHTED_PRODUCTION_PAIR_BALANCE": (PAIR, "Zeta23/CCM/CanonicalGlobalF04.lean"),
    "R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER": (
        FRONTIER,
        "Zeta23/CCM/CanonicalLocalBirdfishie.lean",
    ),
}


class Post287SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(STATE.read_text(encoding="utf-8"))
        self.registry = json.loads((RHRC / "CLAIM_REGISTRY.json").read_text(encoding="utf-8"))
        self.matrix = json.loads((POST284 / "CLAIM_MIGRATION_MATRIX.json").read_text(encoding="utf-8"))

    def test_merged_pr_287_is_the_theorem_anchor(self):
        anchor = self.state["merged_theorem_anchor"]
        self.assertEqual(anchor["pr"], 287)
        self.assertEqual(anchor["validated_head"], HEAD)
        self.assertEqual(anchor["merge_commit"], MERGE)
        self.assertEqual(anchor["tree"], TREE)
        self.assertEqual(anchor["status"], "MERGED_GREEN_THEOREM_STATE")
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(delta["pr"], 287)
        self.assertEqual(delta["final_pr_head"], HEAD)
        self.assertEqual(delta["merge_commit"], MERGE)
        self.assertEqual(delta["prior_theorem_authority_pr"], 285)
        self.assertEqual(delta["supporting_declarations"], [F04, PAIR, FRONTIER])
        self.assertIn("RH remain OPEN", delta["claim_firewall"])
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_no_candidate_pr_is_open(self):
        candidate = self.state["candidate_branch"]
        self.assertEqual(candidate["pr"], "NONE")
        self.assertEqual(candidate["status"], "NO_OPEN_CANDIDATE_PR")
        self.assertFalse(candidate["terminal_claim_change"])

    def test_post285_frontier_is_merged_and_hard_targets_stay_open(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post285_f04_production_derivative_authority"], "PROVED_MERGED_PR_287")
        self.assertEqual(route["post285_m74_canonical_secular_instantiation"], "PROVED_MERGED_PR_287")
        self.assertIn("PROVED_MERGED_PR_287", route["post285_general_omega_inertia"])
        self.assertIn("FILTERED_CARRIERS_OPEN", route["post285_general_omega_inertia"])
        self.assertEqual(route["post287_m70_m77_build"], "PROVED_MERGED_PR_287")
        self.assertEqual(route["post287_m76_opposite_side_and_arithmetic_composition"], "OPEN")
        self.assertEqual(
            route["current_active_subobligation"],
            "OBS-060O_CONTACT_CONDITIONED_PRODUCTION_SATURATION_EXCLUSION",
        )
        note = self.state["current_control_note"]
        for token in ("Post-#287 override", "PR #287", "No candidate PR is open", "RH remains OPEN"):
            self.assertIn(token, note)

    def test_post287_claims_are_bound_to_f04_free_theorems(self):
        by_id = {c["id"]: c for c in self.registry["claims"]}
        self.assertEqual(
            self.state["active_research_route"]["post287_registered_claims"],
            list(EXPECTED),
        )
        rows = {row["id"]: row for row in self.matrix["post287_claim_migration"]}
        self.assertEqual(set(rows), set(EXPECTED))
        registered = json.loads((RHRC / "REGISTERED_THEOREM_BINDINGS.json").read_text(encoding="utf-8"))
        r003 = json.loads((RHRC / "R003_PROMOTED_BINDINGS.json").read_text(encoding="utf-8"))
        self.assertEqual(registered["candidate_bindings"], [])
        self.assertEqual(r003["candidate_bindings"], [])
        proved = {row["id"]: row for row in registered["bindings"]}
        promoted = {row["id"]: row for row in r003["bindings"]}
        for lean_path in ("Zeta23/CCM/ClaimBindings.lean", "Zeta23/RHRC/RegisteredClaimBindings.lean"):
            lean = (ROOT / lean_path).read_text(encoding="utf-8")
            for theorem, _source in EXPECTED.values():
                self.assertRegex(lean, rf"(?m)^#check {re.escape(theorem)}$")
                self.assertRegex(lean, rf"(?m)^#print axioms {re.escape(theorem)}$")
        for cid, (theorem, source) in EXPECTED.items():
            claim = by_id[cid]
            self.assertEqual(claim["status"], "PROVED_UNCONDITIONAL")
            self.assertEqual(claim["promotion_cap"], "PROVED_UNCONDITIONAL")
            self.assertNotIn("candidate_binding", claim)
            self.assertEqual(claim["theorem"], theorem)
            self.assertEqual(claim["source"], source)
            self.assertEqual(claim["route"], "R003_ccm_bridge")
            self.assertIn(HEAD, claim["note"])
            self.assertIn("[propext, Classical.choice, Quot.sound]", claim["note"])
            self.assertIn("No contact exclusion and no RH.", claim["note"])
            self.assertEqual(proved[cid]["theorem"], theorem)
            self.assertEqual(promoted[cid]["theorem"], theorem)
            self.assertEqual(rows[cid]["theorem"], theorem)
            self.assertFalse(rows[cid]["F04_premise"])
            # The bound theorem must carry no F04 premise of its own.
            text = (ROOT / source).read_text(encoding="utf-8")
            short = theorem.split("Zeta23.CCM.", 1)[1]
            start = text.index(f"theorem {short}")
            end = min(i for i in (text.find(":=", start), text.find(" where", start)) if i > 0)
            signature = text[start:end]
            self.assertNotIn("hF04", signature)
            self.assertNotRegex(signature, r"\(\s*\w+\s*:\s*ProductionContactF04DerivativeAuthority")

    def test_conditional_predecessors_are_no_longer_bound(self):
        registered = json.loads((RHRC / "REGISTERED_THEOREM_BINDINGS.json").read_text(encoding="utf-8"))
        theorems = {row["theorem"] for row in registered["bindings"]}
        self.assertNotIn("Zeta23.CCM.canonicalSecondPairing_euler_eq_productionSaturationGap", theorems)
        self.assertNotIn("Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier", theorems)

    def test_open_claims_are_exactly_the_terminal_and_rh_equivalent_targets(self):
        open_ids = {c["id"] for c in self.registry["claims"] if c["status"] == "OPEN"}
        self.assertEqual(
            open_ids,
            {
                "C_RH",
                "R001_PRIME_UPPER",
                "R002_WINDOWED_VISIBILITY",
                "R003_COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES",
            },
        )


if __name__ == "__main__":
    unittest.main()
