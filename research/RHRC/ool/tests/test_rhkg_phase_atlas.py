import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from ool.rhkg_phase_atlas import (
    PROJECTION,
    classify_disposition,
    dependency_closure,
    distinctive_supports,
)


class RHKGPhaseAtlasTests(unittest.TestCase):
    def test_theorem_value_erasure_drops_theorem_proof_body_edges(self):
        idx = {
            "T": {
                "declaration_kind": "THEOREM",
                "repository_scope": "LOCAL",
                "dependencies": [
                    {"constant": "TypeDep", "used_in_type": True, "used_in_value": False, "used_in_structure": False},
                    {"constant": "ProofOnly", "used_in_type": False, "used_in_value": True, "used_in_structure": False},
                ],
            },
            "TypeDep": {"declaration_kind": "DEFINITION", "repository_scope": "LOCAL", "dependencies": []},
            "ProofOnly": {"declaration_kind": "DEFINITION", "repository_scope": "LOCAL", "dependencies": []},
        }
        self.assertEqual(dependency_closure(idx, ["T"], PROJECTION), {"T", "TypeDep"})
        self.assertEqual(dependency_closure(idx, ["T"], "ANY"), {"T", "TypeDep", "ProofOnly"})

    def test_non_theorem_value_support_is_preserved(self):
        idx = {
            "T": {
                "declaration_kind": "THEOREM",
                "repository_scope": "LOCAL",
                "dependencies": [
                    {"constant": "D", "used_in_type": True, "used_in_value": False, "used_in_structure": False},
                ],
            },
            "D": {
                "declaration_kind": "DEFINITION",
                "repository_scope": "LOCAL",
                "dependencies": [
                    {"constant": "BodySupport", "used_in_type": False, "used_in_value": True, "used_in_structure": False},
                ],
            },
            "BodySupport": {"declaration_kind": "DEFINITION", "repository_scope": "LOCAL", "dependencies": []},
        }
        self.assertEqual(dependency_closure(idx, ["T"], PROJECTION), {"T", "D", "BodySupport"})

    def test_shared_kernel_is_not_distinctive_cross_interface_signal(self):
        supports = {
            "A": {"shared", "a_only"},
            "B": {"shared", "b_only"},
            "C": {"shared", "c_only"},
        }
        d = distinctive_supports(supports)
        self.assertEqual(d["A"], {"a_only"})
        self.assertEqual(d["B"], {"b_only"})
        self.assertEqual(d["C"], {"c_only"})

    def test_module_identity_cannot_create_contact(self):
        projected = {"A": set(), "B": set(), "C": set()}
        body_only = {"A": set(), "B": set(), "C": set()}
        self.assertEqual(
            classify_disposition(projected, body_only, set()),
            "NO_ACTIVE_INTERFACE_CONTACT",
        )

    def test_cross_interface_contact_is_discovery_only_class(self):
        projected = {"A": {"a"}, "B": {"b"}, "C": set()}
        body_only = {"A": set(), "B": set(), "C": set()}
        self.assertEqual(
            classify_disposition(projected, body_only, set()),
            "CROSS_INTERFACE_PROJECTED_CONTACT",
        )

    def test_frontier_contact_has_explicit_precedence(self):
        projected = {"A": {"a"}, "B": set(), "C": set()}
        body_only = {"A": set(), "B": set(), "C": set()}
        self.assertEqual(
            classify_disposition(projected, body_only, {"frontier"}),
            "THEOREM_VALUE_ERASED_FRONTIER_CONTACT",
        )


if __name__ == "__main__":
    unittest.main()
