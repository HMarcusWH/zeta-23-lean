from __future__ import annotations

from pathlib import Path
import re
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from ..opica_composition.canonical import ContractError
from . import source_scope as scope


class PaperScopeTests(unittest.TestCase):
    def setUp(self):
        self.old = ("100644", "blob", "a" * 40)
        self.new = ("100644", "blob", "b" * 40)
        self.archive_pdf = "papers/2026-11-26/archived.pdf"
        self.generated = "research/RHRC/graph/generated/REPOSITORY_COVERAGE.json"
        self.frozen = "research/RHRC/graph/generated/historical.json"
        self.allowed = {self.generated}
        self.base = dict.fromkeys(scope.EDIT_PATHS | {self.archive_pdf, self.generated, self.frozen}, self.old)
        self.changed = {**self.base, **dict.fromkeys(scope.ADD_PATHS | scope.EDIT_PATHS |
                        {scope.POLICY, scope.VALIDATOR, self.generated}, self.new)}
        self.policy = {"schema": scope.POLICY_SCHEMA, "added": dict.fromkeys(scope.ADD_PATHS, self.new[2]),
                       "edited": dict.fromkeys(scope.EDIT_PATHS, self.new[2]), "validator_template_sha256": "c" * 64}

    def test_exact_changes_and_declared_generated_refresh(self):
        result = scope.classify(self.base, self.changed, self.policy, self.allowed)
        self.assertEqual(result["deleted"], [])
        self.assertEqual(result["generated"], [self.generated])

    def test_production_freeze_requires_the_same_clean_source_as_the_coordinator(self):
        from ..opica_composition import cli, service

        self.assertIs(cli.validate_descendant, scope.validate_descendant)
        with patch.object(service, "worker_capability"), patch.object(
            cli, "validate_descendant", side_effect=ContractError("source admission rejected")
        ) as admission:
            with self.assertRaisesRegex(ContractError, "source admission rejected"):
                service.freeze(scope.REPO, {}, Path("unused.json"), worker=SimpleNamespace(production=True))
        admission.assert_called_once_with(scope.REPO, require_clean=True)

    def test_paper_and_frozen_history_may_not_change(self):
        for path in (self.archive_pdf, self.frozen):
            with self.subTest(path=path), self.assertRaises(ContractError):
                scope.classify(self.base, {**self.changed, path: self.new}, self.policy, self.allowed)

    def test_new_theorem_or_missing_archive_is_rejected(self):
        with self.assertRaisesRegex(ContractError, "Unexpected paper successor additions"):
            scope.classify(self.base, {**self.changed, "Zeta23/Wrong.lean": self.new}, self.policy, self.allowed)
        del self.changed[self.archive_pdf]
        with self.assertRaisesRegex(ContractError, "removed or renamed"):
            scope.classify(self.base, self.changed, self.policy, self.allowed)

    def test_changed_reviewed_bytecode_or_file_mode_is_rejected(self):
        path = sorted(scope.ADD_PATHS)[0]
        with self.assertRaisesRegex(ContractError, "Changed reviewed paper successor blob"):
            scope.classify(self.base, {**self.changed, path: self.old}, self.policy, self.allowed)
        with self.assertRaisesRegex(ContractError, "changed type or mode"):
            scope.classify(self.base, {**self.changed, path: ("120000", "blob", self.new[2])}, self.policy, self.allowed)

    def test_pdf_rule_is_exact_and_leaves_pdfs_as_binary_fixtures(self):
        pdfs = {p for p, row in scope.read_policy()["added"].items() if row["file_kind"] == "BINARY_PDF"}
        rule, executable_rule = scope.classification_rules()
        self.assertEqual(rule["file_class"], "RESEARCH_FIXTURE")
        self.assertEqual(rule["trust_zone"], "AUDIT_ONLY")
        self.assertEqual(len(pdfs), 6)
        for path in pdfs:
            self.assertIsNotNone(re.fullmatch(rule["pattern"], path))
            self.assertIsNone(re.fullmatch(rule["pattern"], path + ".unreviewed.pdf"))
        for path in scope.PYTHON_FILES:
            self.assertIsNotNone(re.fullmatch(executable_rule["pattern"], path))


if __name__ == "__main__":
    unittest.main()
