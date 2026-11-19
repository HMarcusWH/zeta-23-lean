"""Adversarial cases for the Round 6 exact-tree successor operation set."""
import unittest

from . import source_scope as scope
from ..opica_composition.canonical import ContractError
from ..opica_composition.cli import classification_command


class Round6PolicyTests(unittest.TestCase):
    def setUp(self):
        self.authored = scope.PREFIX + "constraints-fixture.json"
        self.historical = "Zeta23/OPICARound5/ParityMomentBridge.lean"
        self.generated = "research/RHRC/graph/generated/rhkg.json"
        self.edit = "research/RHRC/integration/opica_composition/cli.py"
        self.old = ("100644", "blob", "0" * 40)
        self.new = ("100644", "blob", "1" * 40)
        self.parent = {key: self.old for key in (self.historical, self.generated, self.edit)}
        self.current = {**self.parent, **{key: self.new for key in
                        (self.authored, self.generated, self.edit, scope.POLICY, scope.VALIDATOR)}}
        self.policy = {"schema": "OPICA6_CLOSED_SOURCE_POLICY_V1", "parent": scope.PARENT,
                       "validator_template_sha256": "a" * 64,
                       "parent_tree": scope.PARENT_TREE, "added": {self.authored: self.new[2]},
                       "edited": {self.edit: self.new[2]}, "generated": [self.generated]}

    def test_exact_operations_and_application(self):
        good = scope.classify(self.parent, self.current, self.policy)
        self.assertEqual(good["edited"], [self.edit])
        self.assertEqual(good["generated"], [self.generated])
        self.assertEqual(set(good["added"]), {self.authored, scope.POLICY, scope.VALIDATOR})
        unchanged = {**self.current, self.generated: self.old}
        self.assertEqual(scope.classify(self.parent, unchanged, self.policy)["generated"], [])
        command = classification_command({"schema": "OPICA6_CURRENT_SOURCE_INSPECTION_V1"})
        self.assertEqual(command[-2:], [scope.__name__, "--check-classification"])

    def test_tree_mutations_reject(self):
        hypothetical = {
            "unsigned-source": {**self.current, self.authored: self.old},
            "changed-legacy": {**self.current, self.historical: self.new},
            "unlisted-generated": {**self.current, self.generated + "l": self.new},
            "missing-generated": {k: v for k, v in self.current.items() if k != self.generated},
            "new-executable": {**self.current, self.authored: ("100755", "blob", self.new[2])},
            "linked-regular-name": {**self.current, self.authored: ("120000", "blob", self.new[2])},
            "missing-mandatory": {k: v for k, v in self.current.items() if k != self.authored},
            "removed-parent": {k: v for k, v in self.current.items() if k != self.historical},
        }
        for label, tree in hypothetical.items():
            with self.subTest(label=label), self.assertRaises(ContractError):
                scope.classify(self.parent, tree, self.policy)

    def test_bad_policy_fails_closed(self):
        for field, value in (("parent_tree", "3" * 40), ("schema", "OPICA5"),
                             ("generated", [self.generated, self.generated]),
                             ("generated", [self.authored]),
                             ("generated", [next(iter(scope.FROZEN_PRODUCTS))]),
                             ("added", {self.authored: "0" * 39}),
                             ("added", {"../outside": self.new[2]}),
                             ("added", {scope.VALIDATOR: self.new[2]}),
                             ("added", {self.edit: self.new[2]})):
            with self.subTest(field=field, value=value), self.assertRaises(ContractError):
                scope.check_policy({**self.policy, field: value})

    def test_validator_template_excludes_only_the_self_digest(self):
        original = b'POLICY_SHA256 = "aaa"\nprint(1)\n'
        digest = scope.validator_template_hash(original, "aaa")
        self.assertEqual(digest, scope.validator_template_hash(original.replace(b"aaa", b"bbb"), "bbb"))
        self.assertNotEqual(digest, scope.validator_template_hash(original.replace(b"1", b"2"), "aaa"))
        with self.assertRaises(ContractError):
            scope.validator_template_hash(original + original, "aaa")


if __name__ == "__main__":
    unittest.main()
