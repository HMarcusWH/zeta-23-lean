"""Adversarial source-policy controls; no compiler or theorem acceptance."""
import copy
import hashlib
import json
from pathlib import Path
import unittest

from ..opica_composition.canonical import ContractError
from . import source_scope as scope


class SuccessorSourcePolicyTests(unittest.TestCase):
    def setUp(self):
        self.old = ('100644', 'blob', '0' * 40)
        self.new = ('100644', 'blob', '1' * 40)
        self.added = scope.PREFIX + 'runtime_profile.py'
        self.edited = 'lean-toolchain'
        self.protected = 'research/RHRC/integration/opica_composition/config.py'
        self.product = 'research/RHRC/graph/generated/repository_files.jsonl'
        self.parent = {p: self.old for p in (self.edited, self.protected, self.product)}
        self.current = {**self.parent, **{p: self.new for p in
                        (self.edited, self.added, scope.POLICY, scope.VALIDATOR)}}
        self.policy = {'schema': scope.POLICY_SCHEMA, 'parent': scope.PARENT, 'parent_tree': scope.PARENT_TREE,
                       'purpose': scope.PURPOSE, 'runtime_profile': scope.COMMON_ID,
                       'validator_template_sha256': 'a' * 64,
                       'added': {self.added: self.new[2]}, 'edited': {self.edited: self.new[2]},
                       'generated': [self.product]}

    def test_exact_operations_and_generated_path(self):
        result = scope.classify(self.parent, self.current, self.policy)
        self.assertEqual(result['edited'], [self.edited])
        self.assertEqual(result['generated'], [])
        result = scope.classify(self.parent, {**self.current, self.product: self.new}, self.policy)
        self.assertEqual(result['generated'], [self.product])

    def test_unlisted_missing_mode_and_protected_changes_rejected(self):
        mutations = {
            'unlisted': {**self.current, scope.PREFIX + 'hidden.py': self.new},
            'protected': {**self.current, self.protected: self.new},
            'wrong-blob': {**self.current, self.added: self.old},
            'symlink': {**self.current, self.added: ('120000', 'blob', self.new[2])},
            'executable-mode': {**self.current, self.added: ('100755', 'blob', self.new[2])},
            'missing-required': {p: row for p, row in self.current.items() if p != self.added},
            'delete-parent': {p: row for p, row in self.current.items() if p != self.protected},
            'generated-prefix': {**self.current, self.product + '.extra.json': self.new},
        }
        for label, current in mutations.items():
            with self.subTest(label=label), self.assertRaises(ContractError): scope.classify(self.parent, current, self.policy)

    def test_bad_schema_parent_authority_and_operation_inventory_rejected(self):
        for field, value in (('schema', 'UNREVIEWED'), ('parent_tree', '3' * 40), ('purpose', 'STEP4_CLOSED'),
                             ('runtime_profile', 'ANY_LEAN_VERSION'), ('validator_template_sha256', 'a'),
                             ('generated', [self.product, self.product]),
                             ('added', {'../escape.py': '1' * 40}),
                             ('edited', {next(iter(scope.round6.FROZEN_PRODUCTS)): '1' * 40}),
                             ('added', {scope.VALIDATOR: '1' * 40})):
            with self.subTest(field=field), self.assertRaises(ContractError): scope.check_policy({**self.policy, field: value})

    def test_extra_claim_authority_rejected(self):
        with self.assertRaises(ContractError): scope.check_policy({**self.policy, 'Step4': 'CLOSED'})

    def test_exact_rules_do_not_admit_future_source(self):
        policy = copy.deepcopy(self.policy)
        policy['added'][scope.PREFIX + 'RUNTIME_PROFILES.json'] = '1' * 40
        policy['added'][scope.PREFIX + 'fixtures/common-manifest.json'] = '1' * 40
        rules = scope.classification_rules(policy)
        self.assertEqual(len(rules), 3)
        self.assertTrue(all(r['trust_zone'] == 'AUDIT_ONLY' for r in rules))
        for path in (scope.PREFIX + 'unlisted.py', scope.PREFIX + 'fixtures/unlisted.json', 'Zeta23/Unlisted.lean'):
            self.assertFalse(any(scope.round6.re.search(r['pattern'], path) for r in rules))

    def test_single_digest_exclusion_only(self):
        raw = b'POLICY_SHA256 = "aaa"\nprint(1)\n'
        digest = scope.round6.validator_template_hash(raw, 'aaa')
        self.assertEqual(digest, scope.round6.validator_template_hash(raw.replace(b'aaa', b'bbb'), 'bbb'))
        self.assertNotEqual(digest, scope.round6.validator_template_hash(raw.replace(b'1', b'2'), 'aaa'))
        with self.assertRaises(ContractError): scope.round6.validator_template_hash(raw + raw, 'aaa')

    def test_delivered_policy_and_validator_are_sealed(self):
        directory = Path(__file__).parent
        raw = (directory / 'SOURCE_SCOPE.json').read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), scope.POLICY_SHA256)
        policy = json.loads(raw); scope.check_policy(policy)
        self.assertEqual(scope.round6.validator_template_hash((directory / 'source_scope.py').read_bytes(), scope.POLICY_SHA256),
                         policy['validator_template_sha256'])
        self.assertEqual(policy['purpose'], 'COMMON_PIN_PREPARATION_NOT_STEP4_ACCEPTANCE')
        changed = raw.replace(scope.PURPOSE.encode(), b'STEP4_CLOSED')
        self.assertNotEqual(hashlib.sha256(changed).hexdigest(), scope.POLICY_SHA256)


if __name__ == '__main__': unittest.main()
