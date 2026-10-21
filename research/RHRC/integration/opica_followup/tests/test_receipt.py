"""The child must retain complete private TYPE/VALUE/STRUCTURE provenance."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('followup_receipt', HERE / 'build_receipt.py')
receipt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(receipt)


class DependencyReceiptTests(unittest.TestCase):
    def setUp(self):
        self.root = 'Zeta23.OPICAFollowup.fixture'
        self.private = '_private.Zeta23.OPICAFollowup.Fixture.0.helper'
        self.external = 'Real.log'
        module = 'Zeta23.OPICAFollowup.NormFirstTransfer'
        self.public = [{'name': self.root, 'module': module, 'kind': 'THEOREM'}]
        self.nodes = [
            {'name': self.root, 'module': module, 'kind': 'THEOREM', 'internal': False},
            {'name': self.private, 'module': module, 'kind': 'THEOREM', 'internal': True},
            {'name': self.external, 'module': 'Mathlib.Analysis.SpecialFunctions.Log.Basic',
             'kind': 'DEFINITION', 'internal': False}]
        self.channels = [{'source': source, 'channel': channel, 'targets': targets}
                         for source, value in [(self.root, self.private), (self.private, self.external)]
                         for channel, targets in [('TYPE', []), ('VALUE', [value]), ('STRUCTURE', [])]]

    def check(self):
        receipt.validate_dependency_closure(self.public, self.nodes, self.channels)

    def reject(self):
        with self.assertRaises(ValueError):
            self.check()

    def test_complete_private_closure(self):
        self.check()

    def test_private_type_channel_cannot_be_omitted(self):
        self.channels = [row for row in self.channels if not
                         (row['source'] == self.private and row['channel'] == 'TYPE')]
        self.reject()

    def test_structure_channel_cannot_be_omitted(self):
        self.channels.pop()
        self.reject()

    def test_unknown_dependency_target(self):
        self.channels[1]['targets'] = ['unexported.hiddenPremise']
        self.reject()

    def test_private_node_cannot_disappear(self):
        self.nodes.pop(1)
        self.reject()

    def test_duplicate_channel_rejected(self):
        self.channels.append(deepcopy(self.channels[0]))
        self.reject()

    def test_external_boundaries_cannot_be_fabricated_project_expansions(self):
        self.channels.append({'source': self.external, 'channel': 'TYPE', 'targets': []})
        self.reject()

    def test_unreachable_metadata_rejected(self):
        self.nodes.append({'name': 'Unrelated', 'module': '-', 'kind': 'AXIOM', 'internal': False})
        self.reject()

    def test_all_implemented_roots_remain_original_names(self):
        self.assertEqual(len(receipt.IMPLEMENTED_ROOT_NAMES), 11)
        self.assertTrue(all(name.startswith('Zeta23.OPICAFollowup.')
                            for name in receipt.IMPLEMENTED_ROOT_NAMES))


if __name__ == '__main__':
    unittest.main()
