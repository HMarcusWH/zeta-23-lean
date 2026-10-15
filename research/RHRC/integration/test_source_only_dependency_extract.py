"""Fail-closed source-only dependency export regression tests.

The bounded literal builder MUST preserve all roots in one global Lean
closure, not re-traverse them as independent compiler receipts. No RH claims.
"""
from __future__ import annotations

import re
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import source_only_dependency_extract as export


def fake_roots(n):
    return [
        {"resolved_full_name": f"Zeta23.Mock.t{i:04d}",
         "module": f"Zeta23.Mock.Mod{i % 7}",
         "source_declaration_id": f"src:{i:04d}"}
        for i in range(n)
    ]


class RootLiteralAndGraphTests(unittest.TestCase):
    def test_long_driver_one_global_closure(self):
        for n in (1, 64, 65, 128, 1360):
            with self.subTest(n=n):
                driver = export.render_driver(fake_roots(n))
                self.assertEqual(driver.count("Zeta23.RHRC.exportDependencies roots"), 1)
                self.assertEqual(driver.count("roots := roots ++ #["), (n + 63) // 64)
                names = re.findall(r"``(Zeta23\.Mock\.t[0-9]{4})", driver)
                self.assertEqual(names, [r["resolved_full_name"] for r in fake_roots(n)])
                self.assertIn("let mut roots : Array Lean.Name := #[]", driver)
                self.assertEqual(driver.count("import Zeta23.RHRC.DeclarationDependencyExport"), 1)
                self.assertEqual(driver.count("import Zeta23.Mock.Mod0\n"), 1)

    def test_invalid_root_inventory_fails_closed(self):
        with self.assertRaisesRegex(SystemExit, "empty"):
            export.render_driver([])
        rows = fake_roots(2)
        rows[1]["resolved_full_name"] = rows[0]["resolved_full_name"]
        with self.assertRaisesRegex(SystemExit, "duplicate"):
            export.render_driver(rows)
        row = fake_roots(1)
        row[0]["module"] = None
        with self.assertRaisesRegex(SystemExit, "module"):
            export.render_driver(row)

    def test_compiler_channels_and_all_roots(self):
        roots = [{"resolved_full_name": "Zeta23.Mock.a", "source_declaration_id": "src-A"},
                 {"resolved_full_name": "Zeta23.Mock.b", "source_declaration_id": "src-B"}]
        log = "\n".join([
            "RHKG_DEP_DECL\tZeta23.Mock.a\tZeta23.Mock\tTHEOREM\t0",
            "RHKG_DEP_DECL\tZeta23.Mock.b\tZeta23.Mock\tTHEOREM\t0",
            "RHKG_DEP_DECL\tZeta23.Mock.helper\tZeta23.Mock\tDEFINITION\t1",
            "RHKG_DEP_DECL\tMathlib.Util.c\tMathlib.Util\tDEFINITION\t0",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.a\tTYPE\tZeta23.Mock.helper",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.a\tVALUE\tZeta23.Mock.helper\tMathlib.Util.c",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.a\tSTRUCTURE",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.b\tTYPE",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.b\tVALUE\tZeta23.Mock.a",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.b\tSTRUCTURE",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.helper\tTYPE",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.helper\tVALUE",
            "RHKG_DEP_CHANNEL\tZeta23.Mock.helper\tSTRUCTURE",
        ])
        rows = {r["declaration"]: r for r in export.parse_output(log, roots)}
        self.assertEqual(len(rows), 4)
        self.assertEqual(rows["Zeta23.Mock.a"]["source_candidate_id"], "src-A")
        self.assertEqual(rows["Zeta23.Mock.b"]["graph_role"], "SOURCE_ONLY_ROOT")
        self.assertEqual(rows["Zeta23.Mock.helper"]["graph_role"], "LOCAL_DEPENDENCY")
        self.assertEqual(rows["Mathlib.Util.c"]["graph_role"], "EXTERNAL_BOUNDARY")
        deps = {d["constant"]: d for d in rows["Zeta23.Mock.a"]["dependencies"]}
        self.assertTrue(deps["Zeta23.Mock.helper"]["used_in_type"])
        self.assertTrue(deps["Zeta23.Mock.helper"]["used_in_value"])
        self.assertFalse(deps["Zeta23.Mock.helper"]["used_in_structure"])
        self.assertTrue(deps["Mathlib.Util.c"]["used_in_value"])

    def test_missing_root_and_edge_endpoint_rejected(self):
        root = [{"resolved_full_name": "Zeta23.Mock.a", "source_declaration_id": "src-A"}]
        node = "RHKG_DEP_DECL\tZeta23.Mock.a\tZeta23.Mock\tTHEOREM\t0"
        edge = "RHKG_DEP_CHANNEL\tZeta23.Mock.a\tVALUE\tZeta23.Mock.ghost"
        with self.assertRaisesRegex(SystemExit, "omitted"):
            export.parse_output("", root)
        with self.assertRaisesRegex(SystemExit, "target lacks declaration"):
            export.parse_output(node + "\n" + edge, root)
        with self.assertRaisesRegex(SystemExit, "inconsistent duplicate"):
            export.parse_output(node + "\n" + node.replace("\tZeta23.Mock\t", "\tMathlib.Mock\t"), root)


if __name__ == "__main__":
    unittest.main()
