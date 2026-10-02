from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "contact_quotient_view.py"
SPEC = importlib.util.spec_from_file_location("contact_quotient_view", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class ContactQuotientViewTests(unittest.TestCase):
    def test_theorem_value_erased_projection_ignores_theorem_value_only_edges(self):
        index = {
            "A": {
                "declaration": "A",
                "declaration_kind": "THEOREM",
                "repository_scope": "LOCAL",
                "dependencies": [{
                    "constant": "B",
                    "used_in_type": False,
                    "used_in_value": True,
                    "used_in_structure": False,
                }],
            },
            "B": {
                "declaration": "B",
                "declaration_kind": "THEOREM",
                "repository_scope": "LOCAL",
                "dependencies": [],
            },
        }
        self.assertEqual(MODULE.dependency_closure(index, ["A"]), {"A"})

    def test_non_theorem_value_edges_are_retained(self):
        index = {
            "A": {
                "declaration": "A",
                "declaration_kind": "DEFINITION",
                "repository_scope": "LOCAL",
                "dependencies": [{
                    "constant": "B",
                    "used_in_type": False,
                    "used_in_value": True,
                    "used_in_structure": False,
                }],
            },
            "B": {
                "declaration": "B",
                "declaration_kind": "THEOREM",
                "repository_scope": "LOCAL",
                "dependencies": [],
            },
        }
        self.assertEqual(MODULE.dependency_closure(index, ["A"]), {"A", "B"})


if __name__ == "__main__":
    unittest.main()
