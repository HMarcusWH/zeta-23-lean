"""Rejection controls for the separate direct-window source successor."""

from pathlib import Path
import re
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from ..opica_composition import cli
from ..opica_composition.canonical import ContractError
from . import direct_window_scope as scope


def regular(blob):
    return (*scope.combined.REGULAR, blob * 40)


class DirectWindowScopeTests(unittest.TestCase):
    def setUp(self):
        self.product = "research/RHRC/graph/generated/REPOSITORY_COVERAGE.json"
        self.protected = "Zeta23/RHReference/CompactEnergyAdapter.lean"
        self.frozen = next(iter(scope.combined.historical.round6.FROZEN_PRODUCTS))
        self.base = dict.fromkeys(scope.EDITED | {self.product, self.protected, self.frozen}, regular("a"))
        self.current = {**self.base, **dict.fromkeys(scope.ADDED | scope.EDITED, regular("b"))}
        self.policy = {"schema": scope.POLICY_SCHEMA,
                       "blobs": dict.fromkeys((scope.ADDED | scope.EDITED) - {scope.POLICY, scope.VALIDATOR}, "b" * 40),
                       "validator_template_sha256": "c" * 64}

    def check(self, current, policy=None):
        return scope.classify(self.base, current, {self.product}, self.policy if policy is None else policy)

    def test_exact_candidate_and_generated_only_refresh(self):
        self.assertEqual(self.check(self.current)["generated"], [])
        current = {**self.current, self.product: regular("c")}
        self.assertEqual(self.check(current)["generated"], [self.product])

    def test_reject_unlisted_overlay_extra_path_deletion_and_mode(self):
        cases = [
            {**self.current, scope.VERIFICATION + "epoch-lean-4.33.1/overlays/Unreviewed.lean": regular("c")},
            {**self.current, "Zeta23WindowArithmetic/Unreviewed.lean": regular("c")},
            {p: row for p, row in self.current.items() if p != self.protected},
            {**self.current, scope.WORKFLOW: ("100755", "blob", "b" * 40)},
        ]
        for current in cases:
            with self.subTest(delta=current.keys() - self.current.keys()), self.assertRaises(ContractError):
                self.check(current)

    def test_reject_historical_source_and_frozen_product_changes(self):
        for path in (self.protected, self.frozen):
            with self.subTest(path=path), self.assertRaises(ContractError):
                self.check({**self.current, path: regular("c")})

    def test_reject_unsealed_bytes_and_missing_policy_entry(self):
        for path in self.policy["blobs"]:
            with self.subTest(path=path), self.assertRaises(ContractError):
                self.check({**self.current, path: regular("c")})
        policy = {**self.policy, "blobs": dict(self.policy["blobs"])}
        policy["blobs"].pop(next(iter(policy["blobs"])))
        with self.assertRaises(ContractError):
            self.check(self.current, policy)

    def test_classification_rules_are_exact_and_cover_each_added_path_once(self):
        rules = scope.exact_rules()
        for path in scope.ADDED:
            self.assertEqual(sum(bool(re.fullmatch(row["pattern"], path)) for row in rules), 1, path)
        for path in ("Zeta23WindowArithmetic/Unreviewed.lean",
                     scope.VERIFICATION + "AuditHidden.lean", self.protected):
            self.assertFalse(any(re.fullmatch(row["pattern"], path) for row in rules), path)

    def test_current_dispatch_selects_only_the_new_validator_for_its_epoch(self):
        with patch.object(cli, "documentation_epoch", return_value="direct-window"), patch.object(
                scope, "validate_descendant", return_value={"schema": scope.SCHEMA}) as validator:
            self.assertEqual(cli.validate_descendant(Path("candidate"), require_clean=True),
                             {"schema": scope.SCHEMA})
            validator.assert_called_once_with(Path("candidate"), require_clean=True)
        self.assertIn("research.RHRC.integration.documentation_combined.direct_window_scope",
                      cli.classification_command({"schema": scope.SCHEMA}))

    def test_epoch_uses_policy_introduction_history_even_after_file_removal(self):
        def run(command, **_kwargs):
            if "log" in command:
                self.assertIn("--diff-filter=A", command)
                self.assertEqual(command[-1], scope.POLICY)
                return SimpleNamespace(returncode=0, stdout=b"a" * 40 + b"\n")
            return SimpleNamespace(returncode=0, stdout=b"")
        # The path need not exist: selecting the epoch must not depend on the
        # policy remaining present in the checkout.
        with patch.object(cli.subprocess, "run", side_effect=run):
            self.assertEqual(cli.documentation_epoch(Path("removed-policy-checkout")), "direct-window")
        with patch.object(cli.subprocess, "run", return_value=SimpleNamespace(returncode=0, stdout=b"")):
            self.assertEqual(cli.documentation_epoch(Path("strict-parent-checkout")), "strict-integration")


if __name__ == "__main__":
    unittest.main()
