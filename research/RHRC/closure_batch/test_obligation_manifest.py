from __future__ import annotations

import json
import re
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DECL_RE = re.compile(
    r"(?m)^\s*(theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_'.]+)"
)
THEOREM_KINDS = {"theorem", "lemma"}
ALLOWED_STATUSES = {"OPEN", "INTERFACE", "CANDIDATE_THEOREM", "PROVED"}


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


class ObligationManifestTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((HERE / "OBLIGATIONS.json").read_text(encoding="utf-8"))
        self.rows = self.data["obligations"]
        self.by_id = {row["id"]: row for row in self.rows}
        self.source_decls: dict[str, str] = {}
        for path in sorted((ROOT / "Zeta23").rglob("*.lean")):
            for kind, name in DECL_RE.findall(path.read_text(encoding="utf-8")):
                self.source_decls.setdefault(name, kind)

    def test_unique_ids_and_terminal_firewall(self):
        self.assertEqual(len(self.rows), len(self.by_id))
        self.assertEqual(self.data["terminal_claim"], "RH_OPEN")
        self.assertEqual(self.by_id["RH_FINAL"]["status"], "OPEN")
        self.assertNotIn("lean_target", self.by_id["RH_FINAL"])

    def test_status_vocabulary(self):
        self.assertEqual(set(self.data.get("status_vocabulary", [])), ALLOWED_STATUSES)
        for row in self.rows:
            self.assertIn(row["status"], ALLOWED_STATUSES, row["id"])

    def test_target_modules_exist(self):
        for row in self.rows:
            module = row.get("target_module")
            if module:
                self.assertTrue(module_path(module).is_file(), (row["id"], module))

    def test_dependencies_resolve(self):
        for row in self.rows:
            for dep in row.get("premises", []) + row.get("required_inputs", []):
                self.assertIn(dep, self.by_id, (row["id"], dep))
            for alt in row.get("alternative_premise_sets", []):
                for dep in alt:
                    self.assertIn(dep, self.by_id, (row["id"], dep))

    def test_dependency_graph_is_acyclic(self):
        edges = {
            row["id"]: list(row.get("premises", [])) + list(row.get("required_inputs", []))
            for row in self.rows
        }
        visiting: set[str] = set()
        done: set[str] = set()

        def visit(node: str) -> None:
            if node in done:
                return
            self.assertNotIn(node, visiting, f"dependency cycle through {node}")
            visiting.add(node)
            for dep in edges.get(node, []):
                visit(dep)
            visiting.remove(node)
            done.add(node)

        for node in edges:
            visit(node)

    def test_open_rows_do_not_pretend_to_be_proved_declarations(self):
        for row in self.rows:
            if row["status"] == "OPEN":
                self.assertNotIn("lean_target", row, row["id"])
                self.assertIn("required_statement", row, row["id"])
                self.assertIn("falsification_condition", row, row["id"])

    def test_interfaces_are_not_theorem_promotions(self):
        for row in self.rows:
            if row["status"] == "INTERFACE":
                self.assertNotIn("lean_target", row, row["id"])
                self.assertIn("interface_declaration", row, row["id"])
                leaf = row["interface_declaration"].rsplit(".", 1)[-1]
                self.assertIn(leaf, self.source_decls, row["interface_declaration"])

    def test_candidate_and_proved_targets_are_theorem_declarations(self):
        for row in self.rows:
            if row["status"] in {"CANDIDATE_THEOREM", "PROVED"}:
                target = row.get("lean_target")
                self.assertIsInstance(target, str, row["id"])
                leaf = target.rsplit(".", 1)[-1]
                self.assertIn(leaf, self.source_decls, target)
                self.assertIn(self.source_decls[leaf], THEOREM_KINDS, target)

    def test_proved_rows_have_explicit_target(self):
        for row in self.rows:
            if row["status"] == "PROVED":
                self.assertIn("lean_target", row, row["id"])


if __name__ == "__main__":
    unittest.main()
