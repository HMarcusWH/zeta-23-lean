"""Committed-tree controls for combined documentation source qualification."""
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from ..opica_composition import cli, service
from ..opica_composition.canonical import ContractError
from . import source_scope as scope


class CombinedScopeTests(unittest.TestCase):
    def setUp(self):
        self.old = (*scope.REGULAR, "a" * 40)
        self.new = (*scope.REGULAR, "b" * 40)
        self.pdf = "papers/2026-11-26/original.pdf"
        self.frozen = next(iter(scope.historical.round6.FROZEN_PRODUCTS))
        self.product = "research/RHRC/graph/generated/REPOSITORY_COVERAGE.json"
        self.source = "Zeta23/Independent.lean"
        self.base = dict.fromkeys(scope.EDITED | {self.pdf, self.frozen, self.product, self.source}, self.old)
        self.initial = {**self.base, **dict.fromkeys(scope.ADDED | scope.EDITED, self.new)}
        self.policy = {"schema": scope.POLICY_SCHEMA, "blobs": dict.fromkeys(scope.EDITED | {scope.TEST}, self.new[2]),
                       "validator_template_sha256": "c" * 64}

    def classify(self, current):
        return scope.classify(self.base, current, self.policy, {self.product}, self.initial)

    def test_canonical_only_successor(self):
        self.assertEqual(self.classify({**self.initial, self.product: self.new})["generated"], [self.product])

    def test_reject_source_or_frozen_edits(self):
        for path in (self.pdf, self.source, self.frozen):
            with self.subTest(path=path), self.assertRaises(ContractError):
                self.classify({**self.initial, path: self.new})

    def test_reject_extra_source_and_missing_parent(self):
        with self.assertRaises(ContractError):
            self.classify({**self.initial, "Zeta23/Extra.lean": self.new})
        with self.assertRaises(ContractError):
            self.classify({k: v for k, v in self.initial.items() if k != self.pdf})

    def test_reject_moved_mode_or_reviewed_blob(self):
        for path, row in [(self.product, ("120000", "blob", self.new[2])), (scope.CLI, self.old),
                          (scope.TEST, self.old)]:
            with self.subTest(path=path), self.assertRaises(ContractError):
                self.classify({**self.initial, path: row})

    def test_descendant_cannot_reseal_policy_and_validator(self):
        with self.assertRaisesRegex(ContractError, "since introduction"):
            self.classify({**self.initial, scope.POLICY: self.old, scope.VALIDATOR: self.old})

    def test_canonical_command_and_production_freeze_use_combined_gate(self):
        self.assertEqual(cli.documentation_epoch(scope.REPO), "combined")
        self.assertIn("research.RHRC.integration.documentation_combined.source_scope",
                      cli.classification_command({"schema": scope.SCHEMA}))
        with patch.object(service, "worker_capability"), patch.object(
                scope, "validate_descendant", side_effect=ContractError("combined source rejected")) as admission:
            with self.assertRaisesRegex(ContractError, "combined source rejected"):
                service.freeze(scope.REPO, {}, Path("unused.json"), worker=SimpleNamespace(production=True))
        admission.assert_called_once_with(scope.REPO, require_clean=True)

    def test_historical_selectors_still_forward_the_original_contracts(self):
        for epoch, module in (("registration", scope.registration), ("paper", scope.paper),
                              ("historical", scope.historical)):
            with self.subTest(epoch=epoch), patch.object(cli, "documentation_epoch", return_value=epoch), \
                    patch.object(module, "validate_descendant") as original:
                cli.validate_descendant(scope.REPO, require_clean=True)
                original.assert_called_once_with(scope.REPO, require_clean=True)


if __name__ == "__main__":
    unittest.main()
