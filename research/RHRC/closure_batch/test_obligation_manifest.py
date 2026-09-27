from __future__ import annotations
import json, re, unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DECL_RE = re.compile(r"(?m)^\s*(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_'.]+)")

class ObligationManifestTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((HERE / "OBLIGATIONS.json").read_text(encoding="utf-8"))
        self.rows = self.data["obligations"]
        self.by_id = {row["id"]: row for row in self.rows}

    def test_unique_ids_and_terminal_firewall(self):
        self.assertEqual(len(self.rows), len(self.by_id))
        self.assertEqual(self.data["terminal_claim"], "RH_OPEN")
        self.assertEqual(self.by_id["RH_FINAL"]["status"], "OPEN")
        self.assertNotIn("lean_target", self.by_id["RH_FINAL"])

    def test_dependencies_resolve(self):
        for row in self.rows:
            for dep in row.get("premises", []) + row.get("required_inputs", []):
                self.assertIn(dep, self.by_id, (row["id"], dep))
            for alt in row.get("alternative_premise_sets", []):
                for dep in alt:
                    self.assertIn(dep, self.by_id, (row["id"], dep))

    def test_open_rows_do_not_pretend_to_be_proved_declarations(self):
        for row in self.rows:
            if row["status"] == "OPEN":
                self.assertNotIn("lean_target", row, row["id"])
                self.assertIn("required_statement", row, row["id"])
                self.assertIn("falsification_condition", row, row["id"])

    def test_candidate_lean_targets_exist_in_source(self):
        source = "\n".join(p.read_text(encoding="utf-8") for p in sorted((ROOT / "Zeta23").rglob("*.lean")))
        names = set(DECL_RE.findall(source))
        for row in self.rows:
            if row["status"] == "CANDIDATE_LEAN":
                self.assertIn(row["lean_target"].rsplit(".", 1)[-1], names, row["lean_target"])

if __name__ == "__main__":
    unittest.main()
