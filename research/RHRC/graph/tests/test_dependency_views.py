from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

GRAPH = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("rhkg_views", GRAPH / "views.py")
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load views.py")
views = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(views)


class DependencyViewTests(unittest.TestCase):
    def claims(self) -> dict:
        return {
            "claims": [
                {"id": "A", "status": "PROVED_UNCONDITIONAL", "route": "R1"},
                {"id": "B", "status": "PROVED_UNCONDITIONAL", "route": "R1"},
                {"id": "C", "status": "PROVED_UNCONDITIONAL", "route": "R2"},
                {"id": "OPEN", "status": "OPEN", "route": "R2"},
            ]
        }

    def bindings(self) -> dict:
        return {
            "bindings": [
                {"id": "A", "theorem": "Zeta23.T.a"},
                {"id": "B", "theorem": "Zeta23.T.b"},
                {"id": "C", "theorem": "Zeta23.T.c"},
            ]
        }

    def routes(self) -> dict:
        return {"routes": [{"route_id": "R1"}, {"route_id": "R2"}]}

    def closure(self) -> dict:
        return {
            "entries": [
                {
                    "claim_id": "A",
                    "root_theorem": "Zeta23.T.a",
                    "transitive_local_dependencies": ["Zeta23.T.x", "Zeta23.T.y"],
                },
                {
                    "claim_id": "B",
                    "root_theorem": "Zeta23.T.b",
                    "transitive_local_dependencies": ["Zeta23.T.x", "Zeta23.T.y", "Zeta23.T.z"],
                },
                {
                    "claim_id": "C",
                    "root_theorem": "Zeta23.T.c",
                    "transitive_local_dependencies": ["Zeta23.T.x"],
                },
            ]
        }

    def test_route_and_explicit_cohorts_resolve_fail_closed(self) -> None:
        config = {
            "schema_version": "RHKG-phase2c-farming-cohorts-0.5",
            "route_cohorts": [{"id": "ROUTE_R1", "route_id": "R1"}],
            "explicit_cohorts": [{"id": "PAIR", "claim_ids": ["A", "C"]}],
        }
        got = views.resolve_dependency_farming_cohorts(
            self.claims(), self.bindings(), self.routes(), config
        )
        self.assertEqual(got[0]["claim_ids"], ["A", "C"])
        self.assertEqual(got[1]["claim_ids"], ["A", "B"])

        bad = {
            "schema_version": "RHKG-phase2c-farming-cohorts-0.5",
            "route_cohorts": [],
            "explicit_cohorts": [{"id": "BAD", "claim_ids": ["A", "OPEN"]}],
        }
        with self.assertRaises(ValueError):
            views.resolve_dependency_farming_cohorts(
                self.claims(), self.bindings(), self.routes(), bad
            )

    def test_overlap_shells_and_containment_are_exact(self) -> None:
        cohorts = [
            {"cohort_id": "AB", "kind": "EXPLICIT", "claim_ids": ["A", "B"]},
            {"cohort_id": "C", "kind": "EXPLICIT", "claim_ids": ["C"]},
        ]
        receipt = [
            {"declaration": "Zeta23.T.a", "graph_role": "REGISTERED_CLAIM_ROOT"},
            {"declaration": "Zeta23.T.b", "graph_role": "REGISTERED_CLAIM_ROOT"},
            {"declaration": "Zeta23.T.c", "graph_role": "REGISTERED_CLAIM_ROOT"},
        ]
        got = views.dependency_cohort_overlap_view(receipt, self.closure(), cohorts)
        ab = next(row for row in got["cohorts"] if row["cohort_id"] == "AB")
        self.assertEqual(ab["local_dependency_intersection"], ["Zeta23.T.x", "Zeta23.T.y"])
        shells = {row["claim_id"]: row for row in ab["member_shells"]}
        self.assertEqual(shells["A"]["shell_against_cohort_intersection"], [])
        self.assertEqual(shells["B"]["shell_against_cohort_intersection"], ["Zeta23.T.z"])
        pair = got["pairwise"][0]
        self.assertEqual(pair["containment"], "RIGHT_STRICT_SUBSET")

    def test_signature_classes_detect_equal_and_strict_containment(self) -> None:
        closure = self.closure()
        closure["entries"].append(
            {
                "claim_id": "D",
                "root_theorem": "Zeta23.T.d",
                "transitive_local_dependencies": ["Zeta23.T.x", "Zeta23.T.y"],
            }
        )
        got = views.dependency_signature_classes_view(closure)
        equal = got["exact_equal_closure_classes"]
        self.assertEqual(len(equal), 1)
        self.assertEqual(equal[0]["claim_ids"], ["A", "D"])
        pairs = {
            (row["subset_claim_id"], row["superset_claim_id"])
            for row in got["strict_local_closure_containments"]
        }
        self.assertIn(("C", "A"), pairs)
        self.assertIn(("A", "B"), pairs)


if __name__ == "__main__":
    unittest.main()
