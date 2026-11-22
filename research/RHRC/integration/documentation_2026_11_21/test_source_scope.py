"""Negative controls for the exact archive/documentation source boundary."""
import unittest
import tempfile
from pathlib import Path

from . import source_scope as scope
from ..opica_composition.canonical import ContractError
from ..opica_composition.cli import classification_command
from ..opica_composition.descendant import preserve_agent_instructions, preserve_documentation_renderer


class DocumentationScopeTests(unittest.TestCase):
    def setUp(self):
        self.old = ("100644", "blob", "0" * 40)
        self.new = ("100644", "blob", "1" * 40)
        self.doc = "docs/EXAMPLES.md"
        self.math = "Zeta23/CCM/AbstractCubicSchur.lean"
        self.pdf = "papers/2026-11-21/paper-0.pdf"
        self.generated = "research/RHRC/graph/generated/repository_files.jsonl"
        self.parent = {name: self.old for name in ("README.md", self.math, self.pdf, self.generated)}
        self.current = {**self.parent, **{name: self.new for name in
                       (self.doc, "README.md", self.generated, scope.POLICY, scope.VALIDATOR)}}
        archive_paths = ["papers/README.md", "papers/MANIFEST_2026-11-21.json",
                         "docs/RESEARCH_ARCHIVE_2026-11-21.md"] + [
                         f"papers/2026-11-21/paper-{i}.pdf" for i in range(43)]
        self.policy = {
            "schema": scope.POLICY_SCHEMA, "parent": scope.PARENT, "parent_tree": scope.PARENT_TREE,
            "research_parent": scope.RESEARCH_PARENT, "research_parent_tree": scope.RESEARCH_PARENT_TREE,
            "validator_template_sha256": "a" * 64,
            "archive_added": {name: self.new[2] for name in archive_paths},
            "archive_edited": {"README.md": self.new[2]},
            "added": {self.doc: self.new[2]}, "edited": {"README.md": self.new[2]},
            "generated": [self.generated],
        }

    def test_exact_operations_and_existing_classification(self):
        result = scope.classify(self.parent, self.current, self.policy)
        self.assertEqual(result["edited"], ["README.md"])
        self.assertEqual(result["generated"], [self.generated])
        self.assertEqual(scope.classify(self.parent, {**self.current, self.generated: self.old},
                                       self.policy)["generated"], [])
        self.assertEqual(classification_command({"schema": scope.SCHEMA})[-2:],
                         [scope.__name__, "--check-classification"])
        self.assertEqual(classification_command({"schema": "OPICA6_CURRENT_SOURCE_INSPECTION_V1"})[-2:],
                         [scope.round6.__name__, "--check-classification"])

    def test_classification_rules_are_exact_and_audit_only(self):
        rules = scope.documentation_classification_rules(self.policy)
        self.assertEqual(len(rules), 4)
        self.assertTrue(all(row["trust_zone"] == "AUDIT_ONLY" for row in rules))
        for path in ("docs/examples/unreviewed.py", scope.PREFIX + "unlisted.py",
                     "papers/2026-11-21/unlisted.pdf", "Zeta23/Unlisted.lean"):
            self.assertFalse(any(scope.re.search(row["pattern"], path) for row in rules))

    def test_document_semantic_inputs_are_utf8(self):
        """Both graph document readers require text for their entire real corpus."""
        from ..opica_round2.tests.test_file_classes import graph

        contract = graph.load_classification_contract()
        documents = [path for path in graph.tracked_files()
                     if graph.classify(path, contract)[0] in {"DOCUMENTATION", "LIVING_SSOT"}]
        self.assertTrue(documents, "The real document corpus must not be empty")
        for path in documents:
            with self.subTest(path=path):
                (graph.REPO / path).read_text(encoding="utf-8")

    def test_undeclared_changes_fail_closed(self):
        cases = {
            "extra-document": {**self.current, "docs/unreviewed.md": self.new},
            "changed-mathematics": {**self.current, self.math: self.new},
            "changed-paper": {**self.current, self.pdf: self.new},
            "wrong-approved-bytes": {**self.current, self.doc: self.old},
            "generated-prefix-is-not-allowance": {**self.current, self.generated + ".extra.json": self.new},
            "deleted-parent": {k: v for k, v in self.current.items() if k != self.math},
            "missing-required-document": {k: v for k, v in self.current.items() if k != self.doc},
            "missing-policy": {k: v for k, v in self.current.items() if k != scope.POLICY},
            "executable-mode": {**self.current, self.doc: ("100755", "blob", self.new[2])},
            "symlink": {**self.current, self.doc: ("120000", "blob", self.new[2])},
        }
        for label, current in cases.items():
            with self.subTest(label=label), self.assertRaises(ContractError):
                scope.classify(self.parent, current, self.policy)

    def test_policy_cannot_expand_its_own_unpinned_authority(self):
        cases = [
            ("parent_tree", "f" * 40), ("research_parent", "f" * 40),
            ("schema", "unreviewed"), ("added", {self.doc: "1" * 39}),
            ("added", {"../outside": self.new[2]}),
            ("added", {scope.VALIDATOR: self.new[2]}),
            ("edited", {self.doc: self.new[2]}),
            ("generated", [self.generated, self.generated]),
            ("generated", [next(iter(scope.round6.FROZEN_PRODUCTS))]),
            ("generated", ["docs/anything.json"]),
            ("archive_edited", {"Zeta23.lean": self.new[2]}),
            ("archive_added", {"papers/unrecorded.pdf": self.new[2]}),
        ]
        for field, value in cases:
            with self.subTest(field=field, value=value), self.assertRaises(ContractError):
                scope.check_policy({**self.policy, field: value})

    def test_archive_accounts_for_every_operation(self):
        research = {"README.md": self.old, self.math: self.old}
        archive = {**research, **{p: self.new for p in
                   [*self.policy["archive_added"], *self.policy["archive_edited"]]}}
        scope.check_archive(research, archive, self.policy)
        for changed in ({**archive, self.math: self.new}, {**archive, self.pdf: self.old},
                        {**archive, "papers/unlisted.pdf": self.new}):
            with self.assertRaises(ContractError):
                scope.check_archive(research, changed, self.policy)

    def test_renderer_and_agent_tail_are_preserved(self):
        block = b"<!-- RHRC_CURRENT_STATE_BEGIN -->\nfrozen\n<!-- RHRC_CURRENT_STATE_END -->"
        preserve_documentation_renderer(b"new intro\n" + block, b"old intro\n" + block, path="README.md")
        with self.assertRaises(ContractError):
            preserve_documentation_renderer(block.replace(b"frozen", b"rewritten"), block, path="README.md")
        tail = b"Keep the original Markdown/JSON contracts\nprotected text\n"
        preserve_agent_instructions(b"new intro\n" + tail, b"old intro\n" + tail)
        with self.assertRaises(ContractError):
            preserve_agent_instructions(tail.replace(b"protected", b"changed"), tail)

    def test_validator_digest_cycle_has_one_exclusion(self):
        raw = b'POLICY_SHA256 = "aaa"\nprint(1)\n'
        digest = scope.round6.validator_template_hash(raw, "aaa")
        self.assertEqual(digest, scope.round6.validator_template_hash(raw.replace(b"aaa", b"bbb"), "bbb"))
        self.assertNotEqual(digest, scope.round6.validator_template_hash(raw.replace(b"1", b"2"), "aaa"))


class ProductionWorktreeTests(unittest.TestCase):
    """Exercise the real Git/index/filesystem boundary on a tiny repository."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        scope.git(self.repo, "init", "-q")
        scope.git(self.repo, "config", "user.name", "Documentation test fixture")
        scope.git(self.repo, "config", "user.email", "fixture@example.invalid")
        for name in ("changed-doc.md", "unchanged-source.lean"):
            (self.repo / name).write_text("original\n")
        scope.git(self.repo, "add", ".")
        scope.git(self.repo, "commit", "-qm", "Local source-boundary fixture")
        self.current = scope.round6.tree(self.repo, "HEAD")

    def test_complete_worktree_and_hidden_unchanged_source(self):
        scope.check_worktree(self.repo, self.current)
        scope.git(self.repo, "update-index", "--assume-unchanged", "unchanged-source.lean")
        (self.repo / "unchanged-source.lean").write_text("hidden modification\n")
        self.assertFalse(scope.git(self.repo, "status", "--porcelain"))
        with self.assertRaises(ContractError):
            scope.check_worktree(self.repo, self.current)

    def test_skipped_source_cannot_be_a_production_checkout(self):
        scope.git(self.repo, "update-index", "--skip-worktree", "unchanged-source.lean")
        (self.repo / "unchanged-source.lean").unlink()
        self.assertFalse(scope.git(self.repo, "status", "--porcelain"))
        with self.assertRaises(ContractError):
            scope.check_worktree(self.repo, self.current)

    def test_unflagged_missing_or_changed_source_is_detected(self):
        path = self.repo / "unchanged-source.lean"
        path.write_text("different bytes\n")
        with self.assertRaises(ContractError):
            scope.check_worktree(self.repo, self.current)
        path.unlink()
        with self.assertRaises(ContractError):
            scope.check_worktree(self.repo, self.current)

    def test_git_clean_filter_cannot_hide_changed_raw_source(self):
        (self.repo / ".git/info/attributes").write_text("*.lean filter=normalize\n")
        scope.git(self.repo, "config", "filter.normalize.clean", "sed s/modified/original/g")
        (self.repo / "unchanged-source.lean").write_text("modified\n")
        self.assertFalse(scope.git(self.repo, "status", "--porcelain"))
        with self.assertRaises(ContractError):
            scope.check_worktree(self.repo, self.current)


if __name__ == "__main__":
    unittest.main()
