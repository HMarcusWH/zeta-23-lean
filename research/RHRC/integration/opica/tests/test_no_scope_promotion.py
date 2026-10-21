from __future__ import annotations
import importlib.util
from pathlib import Path
import tempfile
import json
import unittest

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('opica_protection', HERE/'validate_contract.py')
contract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contract)


class ProtectedHistory(unittest.TestCase):
    def test_all_original_source_bytes_and_registry_objects(self):
        protection = contract.read_json(HERE/'PROTECTED_STATE.json')
        self.assertEqual(contract.protected_errors(contract.REPO, protection), [])
        self.assertEqual(len(protection['claim_objects_all_existing']), 122)
        self.assertEqual(len(protection['registered_bindings_all_existing']), 118)

    def test_historical_object_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            target = repo/'research/RHRC'
            target.mkdir(parents=True)
            (target/'CLAIM_REGISTRY.json').write_text(json.dumps({'claims':[{'id':'C_RH','status':'PROVED'}]}))
            (target/'REGISTERED_THEOREM_BINDINGS.json').write_text(json.dumps({'bindings':[]}))
            protection = {'byte_protected_files':[],
                'claim_objects_all_existing':[{'id':'C_RH','status':'OPEN'}],
                'registered_bindings_all_existing':[]}
            self.assertIn('historical registry object changed: C_RH', contract.protected_errors(repo, protection))

    def test_duplicate_registry_identity_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            target = repo/'research/RHRC'
            target.mkdir(parents=True)
            (target/'CLAIM_REGISTRY.json').write_text(json.dumps({'claims':[{'id':'C_RH'},{'id':'C_RH'}]}))
            (target/'REGISTERED_THEOREM_BINDINGS.json').write_text(json.dumps({'bindings':[]}))
            protection = {'byte_protected_files':[], 'claim_objects_all_existing':[],
                'registered_bindings_all_existing':[]}
            self.assertTrue(any('duplicate' in e for e in contract.protected_errors(repo, protection)))


if __name__ == '__main__':
    unittest.main()
