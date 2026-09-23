from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[2] / "tools"
SPEC = importlib.util.spec_from_file_location(
    "rhrc_lean_dependency_extract",
    TOOLS / "lean_dependency_extract.py",
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load lean_dependency_extract.py")
extract = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(extract)


class LeanDependencyExtractTests(unittest.TestCase):
    def roots(self) -> list[dict]:
        return [{"id": "C_TEST", "theorem": "Zeta23.Test.root"}]

    def test_channel_sightings_collapse_to_one_dependency(self) -> None:
        stdout = "\n".join(
            [
                "RHKG_DEP_DECL\tZeta23.Test.root\tZeta23.Test\tTHEOREM\t0",
                "RHKG_DEP_DECL\tZeta23.Test.helper\tZeta23.Test\tTHEOREM\t0",
                "RHKG_DEP_EDGE\tZeta23.Test.root\tZeta23.Test.helper\tTYPE",
                "RHKG_DEP_EDGE\tZeta23.Test.root\tZeta23.Test.helper\tVALUE",
            ]
        )
        rows = extract.parse_output(stdout, self.roots())
        root = next(row for row in rows if row["declaration"] == "Zeta23.Test.root")
        self.assertEqual(len(root["dependencies"]), 1)
        dep = root["dependencies"][0]
        self.assertEqual(dep["constant"], "Zeta23.Test.helper")
        self.assertTrue(dep["used_in_type"])
        self.assertTrue(dep["used_in_value"])
        self.assertFalse(dep["used_in_structure"])

    def test_batched_channel_protocol_preserves_channel_union(self) -> None:
        stdout = "\n".join(
            [
                "RHKG_DEP_DECL\tZeta23.Test.root\tZeta23.Test\tTHEOREM\t0",
                "RHKG_DEP_DECL\tZeta23.Test.helper\tZeta23.Test\tTHEOREM\t0",
                "RHKG_DEP_CHANNEL\tZeta23.Test.root\tTYPE\tZeta23.Test.helper",
                "RHKG_DEP_CHANNEL\tZeta23.Test.root\tVALUE\tZeta23.Test.helper",
                "RHKG_DEP_CHANNEL\tZeta23.Test.root\tSTRUCTURE",
            ]
        )
        rows = extract.parse_output(stdout, self.roots())
        root = next(row for row in rows if row["declaration"] == "Zeta23.Test.root")
        self.assertEqual(len(root["dependencies"]), 1)
        dep = root["dependencies"][0]
        self.assertEqual(dep["constant"], "Zeta23.Test.helper")
        self.assertTrue(dep["used_in_type"])
        self.assertTrue(dep["used_in_value"])
        self.assertFalse(dep["used_in_structure"])

    def test_external_constant_is_boundary_only(self) -> None:
        stdout = "\n".join(
            [
                "RHKG_DEP_DECL\tZeta23.Test.root\tZeta23.Test\tTHEOREM\t0",
                "RHKG_DEP_DECL\tMathlib.Test.external\tMathlib.Test\tTHEOREM\t0",
                "RHKG_DEP_EDGE\tZeta23.Test.root\tMathlib.Test.external\tVALUE",
            ]
        )
        rows = extract.parse_output(stdout, self.roots())
        external = next(
            row for row in rows if row["declaration"] == "Mathlib.Test.external"
        )
        self.assertEqual(external["repository_scope"], "EXTERNAL")
        self.assertEqual(external["graph_role"], "EXTERNAL_BOUNDARY")
        self.assertEqual(external["dependencies"], [])
        self.assertNotIn("registered_claim_id", external)

    def test_expression_self_dependency_is_preserved(self) -> None:
        stdout = "\n".join(
            [
                "RHKG_DEP_DECL\tZeta23.Test.root\tZeta23.Test\tTHEOREM\t0",
                "RHKG_DEP_EDGE\tZeta23.Test.root\tZeta23.Test.root\tVALUE",
            ]
        )
        rows = extract.parse_output(stdout, self.roots())
        root = rows[0]
        self.assertEqual(root["dependencies"][0]["constant"], "Zeta23.Test.root")
        self.assertTrue(root["dependencies"][0]["used_in_value"])

    def test_private_internal_flag_is_fail_closed(self) -> None:
        stdout = "RHKG_DEP_DECL\tZeta23.Test.root\tZeta23.Test\tTHEOREM\tmaybe"
        with self.assertRaises(SystemExit):
            extract.parse_output(stdout, self.roots())


if __name__ == "__main__":
    unittest.main()
