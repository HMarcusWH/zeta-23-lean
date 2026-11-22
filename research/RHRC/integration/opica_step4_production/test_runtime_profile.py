"""Exact tuple rejection tests; these tests do not run or qualify a compiler."""
import json
from pathlib import Path
import tempfile
import unittest

from ..opica_composition.canonical import ContractError
from . import runtime_profile as runtime


class ExactRuntimeProfileTests(unittest.TestCase):
    def setUp(self):
        self.rows = runtime.registry()['profiles']
        self.fixtures = Path(__file__).with_name('fixtures')
        self.data = {
            runtime.LEGACY_ID: (self.fixtures / 'legacy-manifest.json').read_bytes(),
            runtime.COMMON_ID: (self.fixtures / 'common-manifest.json').read_bytes(),
        }

    def test_both_exact_profiles_and_compilers(self):
        for identity, row in self.rows.items():
            with self.subTest(identity=identity):
                profile = runtime.select_profile(row['lean_toolchain'].encode(), self.data[identity])
                self.assertEqual(profile.identity, identity)
                self.assertEqual(dict(profile.package_revisions), {k: v['rev'] for k, v in row['packages'].items()})
                self.assertEqual(len(profile.package_revisions), 9)
                profile.check_compiler('Lean (version ' + row['compiler_version'] + ', x86_64-unknown-linux-gnu, commit ' + row['compiler_commit'] + ', Release)')
                self.assertEqual(profile.record()['authority'], 'RUNTIME_IDENTITY_ONLY_NO_PROOF_ACCEPTANCE')

    def test_mixed_tuple_rejected(self):
        for lean_id, manifest_id in ((runtime.LEGACY_ID, runtime.COMMON_ID), (runtime.COMMON_ID, runtime.LEGACY_ID)):
            with self.subTest(lean=lean_id), self.assertRaises(ContractError):
                runtime.select_profile(self.rows[lean_id]['lean_toolchain'].encode(), self.data[manifest_id])

    def test_unknown_lean_or_changed_raw_pin_rejected(self):
        raw = self.data[runtime.COMMON_ID]
        for lean in (b'leanprover/lean4:v4.33.2\n', b'leanprover/lean4:v4.34.0\n',
                     b'leanprover/lean4:v4.33.1', b'leanprover/lean4:v4.33.1\n\n'):
            with self.subTest(lean=lean), self.assertRaises(ContractError):
                runtime.select_profile(lean, raw)

    def test_package_revision_url_extra_missing_and_input_revision_rejected(self):
        for identity in self.rows:
            original = json.loads(self.data[identity])
            for mutation in ('rev', 'url', 'extra', 'missing', 'inputRev', 'location'):
                value = json.loads(self.data[identity])
                if mutation == 'extra': value['packages'].append(value['packages'][0])
                elif mutation == 'missing': value['packages'].pop()
                elif mutation == 'location': value['packagesDir'] = '/unreviewed'
                else: value['packages'][0][mutation] = '0' * 40
                with self.subTest(profile=identity, mutation=mutation), self.assertRaises(ContractError):
                    runtime.select_profile(self.rows[identity]['lean_toolchain'].encode(), json.dumps(value).encode())

    def test_manifest_whitespace_is_part_of_identity(self):
        row = self.rows[runtime.COMMON_ID]
        with self.assertRaises(ContractError):
            runtime.select_profile(row['lean_toolchain'].encode(), self.data[runtime.COMMON_ID] + b'\n')

    def test_swapped_root_metadata_rejected(self):
        for identity, row in self.rows.items():
            for field, value in (('name', 'opica_step4_integration'), ('lakeDir', '.other-lake'),
                                 ('version', 'unreviewed'), ('fixedToolchain', False)):
                changed = json.loads(self.data[identity]); changed[field] = value
                with self.subTest(profile=identity, field=field), self.assertRaises(ContractError):
                    runtime.select_profile(row['lean_toolchain'].encode(), json.dumps(changed).encode())

    def test_other_compiler_and_newline_rejected(self):
        common = runtime.select_profile(self.rows[runtime.COMMON_ID]['lean_toolchain'].encode(), self.data[runtime.COMMON_ID])
        for text in ('Lean (version 4.33.0-rc2, ' + self.rows[runtime.LEGACY_ID]['compiler_commit'] + ')',
                     'Lean (version 4.33.1, ' + '0' * 40 + ')',
                     'Lean (version 4.33.1, ' + common.compiler_commit + ')\nignored'):
            with self.subTest(text=text), self.assertRaises(ContractError): common.check_compiler(text)

    def test_registry_cannot_authorize_its_own_expansion(self):
        value = runtime.registry()
        value['profiles']['UNREVIEWED'] = value['profiles'][runtime.COMMON_ID]
        with self.assertRaises(ContractError): runtime.registry(json.dumps(value).encode())

    def test_wrong_commit_with_appended_expected_hash_cannot_pass(self):
        row = self.rows[runtime.COMMON_ID]
        profile = runtime.select_profile(row['lean_toolchain'].encode(), self.data[runtime.COMMON_ID])
        valid = 'Lean (version ' + profile.compiler_version + ', x86_64-unknown-linux-gnu, commit ' + profile.compiler_commit + ', Release)'
        wrong = valid.replace(profile.compiler_commit, '0' * 40)
        for text in (wrong + ' ' + profile.compiler_commit,
                     wrong.replace('x86_64-unknown-linux-gnu', profile.compiler_commit),
                     valid + ' arbitrary suffix', valid.replace(', Release)', ', Debug)')):
            with self.subTest(text=text), self.assertRaises(ContractError): profile.check_compiler(text)

    def test_source_file_binding_and_missing_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            row = self.rows[runtime.COMMON_ID]
            (repo / 'lean-toolchain').write_bytes(row['lean_toolchain'].encode())
            with self.assertRaises(FileNotFoundError): runtime.runtime_for(repo)
            (repo / 'lake-manifest.json').write_bytes(self.data[runtime.COMMON_ID])
            self.assertEqual(runtime.runtime_for(repo).identity, runtime.COMMON_ID)


if __name__ == '__main__': unittest.main()
