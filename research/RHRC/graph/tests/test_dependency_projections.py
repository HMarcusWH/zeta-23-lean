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


def dep(
    constant: str,
    *,
    type_: bool = False,
    value: bool = False,
    structure: bool = False,
) -> dict:
    return {
        "constant": constant,
        "used_in_type": type_,
        "used_in_value": value,
        "used_in_structure": structure,
    }


def row(
    name: str,
    kind: str,
    dependencies: list[dict],
    *,
    role: str = "LOCAL_DEPENDENCY",
) -> dict:
    return {
        "declaration": name,
        "module": "Zeta23.Test",
        "repository_scope": "LOCAL",
        "graph_role": role,
        "declaration_kind": kind,
        "private_or_internal": False,
        "dependencies": dependencies,
    }


class DependencyProjectionTests(unittest.TestCase):
    def receipt(self) -> list[dict]:
        return [
            row(
                "Zeta23.Test.root",
                "THEOREM",
                [
                    dep("Zeta23.Test.typeDef", type_=True),
                    dep("Zeta23.Test.valueDef", value=True),
                    dep("Zeta23.Test.bothTheorem", type_=True, value=True),
                ],
                role="REGISTERED_CLAIM_ROOT",
            ),
            row(
                "Zeta23.Test.typeDef",
                "DEFINITION",
                [dep("Zeta23.Test.defBody", value=True)],
            ),
            row("Zeta23.Test.valueDef", "DEFINITION", []),
            row(
                "Zeta23.Test.bothTheorem",
                "THEOREM",
                [dep("Zeta23.Test.proofOnly", value=True)],
            ),
            row("Zeta23.Test.defBody", "DEFINITION", []),
            row("Zeta23.Test.proofOnly", "THEOREM", []),
        ]

    def test_theorem_value_erasure_keeps_types_and_definition_bodies(self) -> None:
        got = views.dependency_projection_closure_entry(
            self.receipt(),
            "Zeta23.Test.root",
            "THEOREM_VALUE_ERASED_SUPPORT",
        )
        self.assertEqual(
            set(got["transitive_local_dependencies"]),
            {
                "Zeta23.Test.typeDef",
                "Zeta23.Test.bothTheorem",
                "Zeta23.Test.defBody",
            },
        )
        self.assertNotIn("Zeta23.Test.valueDef", got["transitive_local_dependencies"])
        self.assertNotIn("Zeta23.Test.proofOnly", got["transitive_local_dependencies"])

    def test_type_and_value_projections_are_homogeneous_controls(self) -> None:
        type_only = views.dependency_projection_closure_entry(
            self.receipt(), "Zeta23.Test.root", "TYPE_ONLY"
        )
        value_only = views.dependency_projection_closure_entry(
            self.receipt(), "Zeta23.Test.root", "VALUE_ONLY"
        )
        self.assertEqual(
            set(type_only["transitive_local_dependencies"]),
            {"Zeta23.Test.typeDef", "Zeta23.Test.bothTheorem"},
        )
        self.assertEqual(
            set(value_only["transitive_local_dependencies"]),
            {
                "Zeta23.Test.valueDef",
                "Zeta23.Test.bothTheorem",
                "Zeta23.Test.proofOnly",
            },
        )

    def test_any_is_union_traversal_and_root_is_excluded(self) -> None:
        got = views.dependency_projection_closure_entry(
            self.receipt(), "Zeta23.Test.root", "ANY"
        )
        self.assertNotIn("Zeta23.Test.root", got["transitive_local_dependencies"])
        self.assertEqual(len(got["transitive_local_dependencies"]), 5)

    def test_theorem_type_plus_value_edge_survives_erasure(self) -> None:
        source = self.receipt()[0]
        both = source["dependencies"][2]
        self.assertTrue(
            views.dependency_edge_allowed(
                source, both, "THEOREM_VALUE_ERASED_SUPPORT"
            )
        )
        value_only = source["dependencies"][1]
        self.assertFalse(
            views.dependency_edge_allowed(
                source, value_only, "THEOREM_VALUE_ERASED_SUPPORT"
            )
        )

    def test_non_theorem_value_edge_survives_erasure(self) -> None:
        source = self.receipt()[1]
        edge = source["dependencies"][0]
        self.assertTrue(
            views.dependency_edge_allowed(
                source, edge, "THEOREM_VALUE_ERASED_SUPPORT"
            )
        )

    def test_pair_relation_classification_is_neutral(self) -> None:
        self.assertEqual(views._set_relation({"x"}, {"x"}), "EQUAL")
        self.assertEqual(
            views._set_relation({"x"}, {"x", "y"}), "LEFT_STRICT_SUBSET"
        )
        self.assertEqual(
            views._set_relation({"x", "y"}, {"x"}), "RIGHT_STRICT_SUBSET"
        )
        self.assertEqual(
            views._set_relation({"x"}, {"y"}), "INCOMPARABLE"
        )

    def test_unknown_projection_fails_closed(self) -> None:
        with self.assertRaises(ValueError):
            views.dependency_projection_closure_entry(
                self.receipt(), "Zeta23.Test.root", "SEMANTIC_MAGIC"
            )


if __name__ == "__main__":
    unittest.main()
