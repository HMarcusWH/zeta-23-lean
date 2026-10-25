"""Adversarial tests for the exact Stage1 documentation-only exception."""
from __future__ import annotations
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('opica_documentation_review',HERE/'validate_contract.py')
contract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contract)


class DocumentationReview(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        for relative in contract.FOLLOWUP_DOCUMENTATION_PATHS:
            target = self.repo/relative
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(contract.REPO/relative,target)
        registry = self.repo/'research/RHRC'
        (registry/'CLAIM_REGISTRY.json').write_text(json.dumps({'claims':[]}))
        (registry/'REGISTERED_THEOREM_BINDINGS.json').write_text(json.dumps({'bindings':[]}))

    def review(self):
        return contract.reviewed_documentation_paths(self.repo)

    def test_exact_seven_reviewed_files_pass(self):
        paths,errors = self.review()
        self.assertEqual(errors,[])
        self.assertEqual(paths,contract.FOLLOWUP_DOCUMENTATION_PATHS)
        self.assertEqual(len(paths),7)

    def test_any_changed_reviewed_byte_rejects_entire_exception(self):
        for relative in sorted(contract.FOLLOWUP_DOCUMENTATION_PATHS):
            with self.subTest(path=relative):
                path = self.repo/relative
                original = path.read_bytes()
                path.write_bytes(original+b'\nforged navigation\n')
                paths,errors = self.review()
                self.assertEqual(paths,set())
                self.assertTrue(any('bytes changed' in e for e in errors))
                path.write_bytes(original)

    def test_missing_file_rejects_entire_exception(self):
        (self.repo/'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md').unlink()
        paths,errors = self.review()
        self.assertEqual(paths,set())
        self.assertTrue(any('missing' in e for e in errors))

    def test_unlisted_readme_source_and_registry_never_gain_byte_exception(self):
        for relative in ['README.md','Zeta23/OPICA/Example.lean','research/RHRC/CLAIM_REGISTRY.json']:
            with self.subTest(path=relative):
                path = self.repo/relative
                path.parent.mkdir(parents=True,exist_ok=True)
                old = b'{"claims":[]}' if relative.endswith('.json') else b'frozen bytes\n'
                new = b'{"claims":[],"forgery":true}' if relative.endswith('.json') else b'changed bytes\n'
                path.write_bytes(new)
                protection = {'byte_protected_files':[{'path':relative,'bytes':len(old),
                    'sha256':hashlib.sha256(old).hexdigest()}],
                    'claim_objects_all_existing':[],'registered_bindings_all_existing':[]}
                errors = contract.protected_errors(self.repo,protection)
                self.assertIn('protected bytes changed: '+relative,errors)

    def test_historical_registry_objects_still_reject_mutation(self):
        (self.repo/'research/RHRC/CLAIM_REGISTRY.json').write_text(json.dumps({'claims':[{'id':'OLD','status':'PROVED'}]}))
        protection = {'byte_protected_files':[],
            'claim_objects_all_existing':[{'id':'OLD','status':'OPEN'}],
            'registered_bindings_all_existing':[]}
        self.assertIn('historical registry object changed: OLD',contract.protected_errors(self.repo,protection))

    def test_edited_manifest_or_register_cannot_repin_document(self):
        target = self.repo/'AUDIT.md'
        target.write_bytes(target.read_bytes()+b'\nforged\n')
        forged = [{'path':relative,'bytes':(self.repo/relative).stat().st_size,
            'sha256':hashlib.sha256((self.repo/relative).read_bytes()).hexdigest()}
            for relative in sorted(contract.FOLLOWUP_DOCUMENTATION_PATHS)]
        folder = self.repo/contract.FOLLOWUP_FOLDER
        folder.mkdir(parents=True)
        for name in ['SOURCE_REGISTER.json','CONTINUATION_MANIFEST.json','DOCUMENTATION_REVIEW.json']:
            (folder/name).write_text(json.dumps({'artifacts':forged,'documentation_review':forged}))
        self.assertEqual(self.review()[0],set())
        self.assertTrue(self.review()[1])

    def test_protection_object_cannot_self_repin_changed_document(self):
        protection = contract.read_json(HERE/'PROTECTED_STATE.json')
        original = copy.deepcopy(protection)
        target = self.repo/'AUDIT.md'
        target.write_bytes(target.read_bytes()+b'\nforged\n')
        for entry in protection['byte_protected_files']:
            if entry['path']=='AUDIT.md':
                entry.update(bytes=target.stat().st_size,sha256=hashlib.sha256(target.read_bytes()).hexdigest())
        errors = contract.protected_errors(self.repo,protection)
        self.assertIn('frozen protection object changed',errors)
        self.assertTrue(any('documentation review rejected' in e for e in errors))
        self.assertEqual(contract.read_json(HERE/'PROTECTED_STATE.json'),original)

    def test_table_cannot_self_repin_without_separate_seal(self):
        target = self.repo/'AUDIT.md'
        target.write_bytes(target.read_bytes()+b'\nforged\n')
        forged = tuple((p,target.stat().st_size,hashlib.sha256(target.read_bytes()).hexdigest())
            if p=='AUDIT.md' else (p,n,h) for p,n,h in contract.FOLLOWUP_DOCUMENTATION_REVIEW)
        with patch.object(contract,'FOLLOWUP_DOCUMENTATION_REVIEW',forged):
            self.assertEqual(self.review()[0],set())
            self.assertTrue(any('sealed seven-path' in e for e in self.review()[1]))

    def test_traversal_case_and_duplicate_table_paths_rejected(self):
        first = contract.FOLLOWUP_DOCUMENTATION_REVIEW[0]
        for relative in ['../AUDIT.md','audit.md','research/../AUDIT.md','C:/AUDIT.md','AUDIT.md/extra','FORK_NOTES.md']:
            with self.subTest(path=relative):
                forged = ((relative,*first[1:]),*contract.FOLLOWUP_DOCUMENTATION_REVIEW[1:])
                with patch.object(contract,'FOLLOWUP_DOCUMENTATION_REVIEW',forged):
                    self.assertEqual(self.review()[0],set())
                    self.assertTrue(self.review()[1])

    def test_symlink_rejected_even_if_target_has_exact_reviewed_bytes(self):
        path = self.repo/'AUDIT.md'
        target = self.repo/'exact-audit-copy.md'
        path.rename(target)
        try:
            path.symlink_to(target)
        except OSError as exc:
            self.skipTest('host cannot create symlink: '+str(exc))
        self.assertEqual(self.review()[0],set())
        self.assertTrue(any('symlink' in e for e in self.review()[1]))

    def test_hardlink_alias_rejected_even_with_exact_bytes(self):
        path = self.repo/'AUDIT.md'
        alias = self.repo/'exact-audit-alias.md'
        try:
            os.link(path,alias)
        except OSError as exc:
            self.skipTest('host cannot create hardlink: '+str(exc))
        self.assertEqual(self.review()[0],set())
        self.assertTrue(any('aliased' in e for e in self.review()[1]))

    def test_symlink_guard_without_host_link_privilege(self):
        target = self.repo/'AUDIT.md'
        original = Path.is_symlink
        with patch.object(Path,'is_symlink',lambda path: path==target or original(path)):
            self.assertEqual(self.review()[0],set())
            self.assertTrue(any('symlink' in e for e in self.review()[1]))

    def test_hardlink_guard_without_host_link_privilege(self):
        target = self.repo/'AUDIT.md'
        original = Path.stat
        def aliased_stat(path,*args,**kwargs):
            result = original(path,*args,**kwargs)
            if path==target:
                fields = list(result)
                fields[3] = 2
                return os.stat_result(fields)
            return result
        with patch.object(Path,'stat',aliased_stat):
            self.assertEqual(self.review()[0],set())
            self.assertTrue(any('aliased' in e for e in self.review()[1]))

    def test_full_root_extension_still_rejects_absent_full_reviewed_types(self):
        with self.assertRaisesRegex(ValueError,'full child reviewed type table absent'):
            contract._source_bound_followup_context(contract.REPO)


if __name__=='__main__':unittest.main()
