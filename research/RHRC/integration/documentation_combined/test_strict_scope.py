"""Controls for the strict main import and its reviewed CI source epoch."""

from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from ..opica_composition import cli, service
from ..opica_composition.canonical import ContractError
from . import strict_scope as scope


def regular(blob):
    return (*scope.combined.REGULAR, blob * 40)


class StrictScopeTests(unittest.TestCase):
    def setUp(self):
        self.active = {"research/RHRC/graph/generated/REPOSITORY_COVERAGE.json"}
        self.product = next(iter(self.active))
        self.frozen = next(iter(scope.combined.historical.round6.FROZEN_PRODUCTS))
        self.proof = "Zeta23/RHReference/CompactEnergyAdapter.lean"
        self.pdf = "papers/2026-11-26/original.pdf"
        self.base = dict.fromkeys(scope.EDITED | {self.product, self.proof, self.frozen, self.pdf}, regular("a"))
        self.initial = {**self.base, **dict.fromkeys(scope.ADDED | scope.EDITED, regular("b"))}
        self.policy = {"schema": scope.POLICY_SCHEMA,
                       "blobs": dict.fromkeys((scope.ADDED | scope.EDITED) - {scope.POLICY, scope.VALIDATOR}, "b" * 40),
                       "validator_template_sha256": "c" * 64}

    def check(self, current, initial=None):
        return scope.classify(self.base, current, self.initial if initial is None else initial, self.active, self.policy)

    def test_generated_only_descendant(self):
        self.assertEqual(self.check(self.initial)["generated"], [])
        self.assertEqual(self.check({**self.initial, self.product: regular("c")})["generated"], [self.product])

    def test_reject_new_path_deleted_path_mode_and_changed_protected_bytes(self):
        for item in (self.proof, self.frozen, self.pdf):
            with self.subTest(item=item), self.assertRaises(ContractError):
                self.check({**self.initial, item: regular("c")})
        for current in ({**self.initial, "verification/Extra.lean": regular("a")},
                        {k: v for k, v in self.initial.items() if k != self.pdf},
                        {**self.initial, self.product: ("100755", "blob", "c" * 40)}):
            with self.assertRaises(ContractError):
                self.check(current)

    def test_authenticated_authored_files_and_initial_policy_are_immutable(self):
        for path in scope.ADDED | scope.EDITED:
            with self.subTest(path=path), self.assertRaises(ContractError):
                self.check({**self.initial, path: regular("c")})
        bad = {**self.initial, "README.md": regular("c")}
        with self.assertRaises(ContractError):
            self.check(bad, bad)

    def test_reject_product_publication_in_source_introduction(self):
        bad = {**self.initial, self.product: regular("c")}
        with self.assertRaises(ContractError):
            self.check(bad, bad)

    def test_import_binds_every_original_mode_and_blob_without_overwrites(self):
        added = {f"Zeta23Arithmetic/{i}.lean": regular("a") for i in range(952)}
        previous = {"lakefile.toml": regular("b")}
        baseline = {**previous, **added}
        self.assertEqual(scope.check_import(previous, added, baseline), added.keys())
        for bad in (previous, {**baseline, "lakefile.toml": regular("a")},
                    {**baseline, "Zeta23Arithmetic/0.lean": ("100755", "blob", "a" * 40)},
                    {**baseline, "Zeta23Arithmetic/0.lean": regular("c")}):
            with self.assertRaises(ContractError):
                scope.check_import(previous, added, bad)

    def test_registry_and_production_freeze_select_the_same_source(self):
        self.assertEqual(cli.documentation_epoch(scope.combined.REPO), "strict-integration")
        self.assertIn("research.RHRC.integration.documentation_combined.strict_scope",
                      cli.classification_command({"schema": scope.SCHEMA}))
        with patch.object(service, "worker_capability"), patch.object(
                scope, "validate_descendant", side_effect=ContractError("rejected strict source")) as actual:
            with self.assertRaisesRegex(ContractError, "rejected strict source"):
                service.freeze(scope.combined.REPO, {}, Path("unused.json"), worker=SimpleNamespace(production=True))
        actual.assert_called_once_with(scope.combined.REPO, require_clean=True)


if __name__ == "__main__":
    unittest.main()
