import unittest
from dataclasses import replace
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from source_context import SourceContext, context_differences, require_identical_context

class ContextTest(unittest.TestCase):
    def setUp(self):
        self.context=SourceContext(
            commit='8'*40,source_blob='a'*40,source_object='canonicalSourceMatrix',
            carrier='physical pole-neutral',parity='even',normalization='canonical direct',
            witness_kind='unit shell',aperture='L',cutoff='K',spectral_domain='lambda < odd bottom',
            quantifiers=('forall L > L0', 'exists K >= 3'))

    def test_same_context(self):
        require_identical_context(self.context, self.context)
        self.assertEqual(len(self.context.fingerprint()),64)

    def test_catches_normalization(self):
        self.assertEqual(context_differences(self.context,replace(self.context,normalization='legacy')),
                         ('normalization',))

    def test_catches_witness(self):
        self.assertIn('witness_kind',context_differences(self.context,
            replace(self.context,witness_kind='negative Schur witness')))

    def test_preserves_quantifier_order(self):
        other=replace(self.context,quantifiers=tuple(reversed(self.context.quantifiers)))
        self.assertEqual(context_differences(self.context,other),('quantifiers',))

    def test_rejects_short_commit(self):
        with self.assertRaises(ValueError):replace(self.context,commit='8109728')

    def test_rejects_mutable_quantifiers(self):
        with self.assertRaises(ValueError):replace(self.context,quantifiers=['L'])

    def test_rejects_ambiguous_field(self):
        with self.assertRaises(ValueError):replace(self.context,source_object=' ')

    def test_diff_requires_adapter(self):
        with self.assertRaises(ValueError):require_identical_context(self.context,replace(self.context,parity='odd'))

    def test_bool_parity_rejected(self):
        with self.assertRaises(ValueError):replace(self.context,parity=True)
