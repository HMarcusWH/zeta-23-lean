from __future__ import annotations
import json
from pathlib import Path
import hashlib
import contextlib
import io
import sys
import tempfile
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from verify_support import (ROOTS, CONSUMERS, verify_axioms, validate_manifest,
                            PREFIX, git_blob, strict_json_loads,
                            verify_mutation_diagnostics, require_pinned_parent,
                            BASE, PINNED_TREE)
from run_python_tests import run

class VerificationGuardTests(unittest.TestCase):
    def make_good_lean_log(self):
        entries = [f"'Zeta23.OPICARound4.{s}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                   for s in ROOTS]
        entries += [f"'Zeta23.OPICARound4.Validation.{s}' does not depend on any axioms"
                    for s in CONSUMERS]
        return '\n'.join(entries)

    def test_axiom_inventory_exact(self):
        result=verify_axioms(self.make_good_lean_log())
        self.assertEqual(len(result),len(ROOTS)+len(CONSUMERS))

    def test_missing_axiom_record_rejected(self):
        with self.assertRaises(RuntimeError):
            verify_axioms('\n'.join(self.make_good_lean_log().splitlines()[1:]))

    def test_project_axiom_rejected(self):
        log=self.make_good_lean_log().replace('Quot.sound','sorryAx',1)
        with self.assertRaises(RuntimeError):verify_axioms(log)

    def test_duplicate_axiom_record_rejected(self):
        log=self.make_good_lean_log()
        with self.assertRaises(RuntimeError):verify_axioms(log+'\n'+log.splitlines()[0])

    def test_empty_test_inventory_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'expected.json'; p.write_text('[]')
            with self.assertRaises(ValueError):run(p)

    def test_wrong_test_inventory_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'expected.json';p.write_text('["fake.test"]')
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(run(p),2)

    def test_complete_overlay_inventory(self):
        with tempfile.TemporaryDirectory() as temp:
            repo=Path(temp)
            support=repo/PREFIX
            root=repo/'Zeta23'/'OPICARound4'
            support.mkdir(parents=True);root.mkdir(parents=True)
            modules={'Zeta23/OPICARound4.lean':b'import Mathlib\n',
                     'Zeta23/OPICARound4/Example.lean':b'import Mathlib\n',
                     (PREFIX/'check.py').as_posix():b'print(1)\n'}
            for name,data in modules.items():
                p=repo/name;p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(data)
            manifest={'schema':'OPICA4_SUPPORT_PACKAGE_MANIFEST_V3',
                      'parent_head':BASE,'self_hash_policy':'manifest excluded from its own hash',
                      'files':[{'path':p,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
                               for p,data in sorted(modules.items())]}
            (support/'PACKAGE_MANIFEST.json').write_text(json.dumps(manifest))
            recovered, paths=validate_manifest(repo)
            self.assertEqual(len(paths),3)
            (root/'unlisted.lean').write_text('import Mathlib\n')
            with self.assertRaises(ValueError):validate_manifest(repo)

    def test_bad_manifest_digest_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            repo=Path(temp); support=repo/PREFIX;support.mkdir(parents=True)
            root=repo/'Zeta23'/'OPICARound4';root.mkdir(parents=True)
            (repo/'Zeta23/OPICARound4.lean').write_bytes(b'import Mathlib\n')
            manifest={'schema':'OPICA4_SUPPORT_PACKAGE_MANIFEST_V3',
                      'parent_head':BASE,'self_hash_policy':'manifest excluded from its own hash',
                      'files':[{'path':'Zeta23/OPICARound4.lean','sha256':'0'*64,'bytes':15}]}
            (support/'PACKAGE_MANIFEST.json').write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):validate_manifest(repo)

    def test_name_suffix_substitution_rejected(self):
        exact='Zeta23.OPICARound4.shell_sub_norm_sq'
        forged=exact+'_not_the_expected_theorem'
        log=self.make_good_lean_log().replace(f"'{exact}'",f"'{forged}'",1)
        with self.assertRaisesRegex(RuntimeError,'AXIOM'):
            verify_axioms(log)

    def test_unexpected_extra_declaration_rejected(self):
        log=self.make_good_lean_log()+"\n'Zeta23.OPICARound4.unexpected_lemma' does not depend on any axioms"
        with self.assertRaisesRegex(RuntimeError,'UNEXPECTED_AXIOM_RECORD'):
            verify_axioms(log)

    def test_axioms_support_multiline_pretty_print(self):
        log=self.make_good_lean_log().replace(
            '[propext, Classical.choice, Quot.sound]',
            '[propext,\n Classical.choice, Quot.sound]')
        self.assertEqual(len(verify_axioms(log)),len(ROOTS)+len(CONSUMERS))

    def test_axiom_record_needs_quoted_exact_name(self):
        log=self.make_good_lean_log().replace(
            "'Zeta23.OPICARound4.shell_sub_norm_sq'",
            "'Zeta23.OPICARound4.shell_sub_norm_sq_but_close'",1)
        with self.assertRaisesRegex(RuntimeError,'UNEXPECTED_AXIOM_RECORD|AXIOM_INVENTORY_MISMATCH'):
            verify_axioms(log)

    def test_duplicate_json_keys_rejected(self):
        with self.assertRaisesRegex(ValueError,'DUPLICATE_JSON_KEY'):
            strict_json_loads('{"source":1,"source":2}')

    def test_nonfinite_json_rejected(self):
        with self.assertRaisesRegex(ValueError,'NONFINITE_JSON_CONSTANT'):
            strict_json_loads('{"x":NaN}')

    def test_good_mutation_failure(self):
        verify_mutation_diagnostics(1,'foo.lean:5:1: error: type mismatch\n')

    def test_mutation_unexpected_exit_rejected(self):
        with self.assertRaisesRegex(RuntimeError,'MUTATION_EXIT_NOT_EXPECTED'):
            verify_mutation_diagnostics(2,'foo.lean:5:1: error: type mismatch')

    def test_mutation_import_failure_rejected(self):
        with self.assertRaisesRegex(RuntimeError,'MUTATION_FAILED_FOR_ENVIRONMENT'):
            verify_mutation_diagnostics(1,
              'foo.lean:5:1: error: type mismatch\nfoo.lean:1:0: error: unknown module')

    def test_mutation_other_error_rejected(self):
        with self.assertRaisesRegex(RuntimeError,'MUTATION_EXTRA_UNEXPECTED_ERROR'):
            verify_mutation_diagnostics(1,
              'foo.lean:5:1: error: type mismatch\nfoo.lean:1:0: error: bad proof')

    def test_mutation_no_error_marker_rejected(self):
        with self.assertRaisesRegex(RuntimeError,'MUTATION_DID_NOT_REJECT_STRONGER_TYPE'):
            verify_mutation_diagnostics(1,'type mismatch listed as a comment only')

    def test_pinned_head_and_tree_required(self):
        require_pinned_parent(BASE,PINNED_TREE)
        for head,tree in ((BASE,'f'*40),('f'*40,PINNED_TREE)):
            with self.subTest(head=head,tree=tree), self.assertRaisesRegex(
                    RuntimeError,'EXACT_PINNED_PARENT_AND_TREE_REQUIRED'):
                require_pinned_parent(head,tree)

    def test_package_schema_mismatch_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            repo=Path(temp);support=repo/PREFIX;support.mkdir(parents=True)
            root=repo/'Zeta23'/'OPICARound4';root.mkdir(parents=True)
            (repo/'Zeta23/OPICARound4.lean').write_text('import Mathlib\n')
            raw=b'import Mathlib\n'
            manifest={'schema':'OPICA4_SUPPORT_PACKAGE_MANIFEST_V2',
                      'parent_head':BASE,'self_hash_policy':'manifest excluded from its own hash',
                      'files':[{'path':'Zeta23/OPICARound4.lean',
                        'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}]}
            (support/'PACKAGE_MANIFEST.json').write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError,'INVALID_MANIFEST_SCHEMA'):
                validate_manifest(repo)

    def test_lean_consumer_axioms_expected(self):
        self.assertIn('regular_witness_rayleigh_consumer',CONSUMERS)
        self.assertIn('resonant_witness_rayleigh_consumer',CONSUMERS)
        self.assertIn('common_scalar_shift_consumer',CONSUMERS)
