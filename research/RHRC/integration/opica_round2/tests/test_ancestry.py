"""The descendant cannot enlarge its policy or overwrite a source directory."""
import copy
import hashlib
import importlib.util
import json
from contextlib import ExitStack
from pathlib import Path, PurePosixPath, PureWindowsPath
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
TEMP_ROOT = HERE.parents[3].parent/'opica-round2-test-temp'
sys.path.insert(0, str(HERE))
import ancestor_projection as projection
import capture_ancestor as capture
from certificate_io import InvalidCertificate, load_strict_json


class ProjectionGuards(unittest.TestCase):
    def setUp(self):
        self.manifest = load_strict_json(HERE/'BUILD_MANIFEST.json', 8*1024*1024)
        TEMP_ROOT.mkdir(exist_ok=True)

    def test_audited_exact_path_policy(self):
        policy = projection.path_policy(self.manifest)
        self.assertEqual(tuple(len(policy[k]) for k in ('create','edit','generated')), (102,15,81))

    def test_candidate_cannot_add_provider_and_recount(self):
        bad = copy.deepcopy(self.manifest)
        bad['create'].append({'path':'Zeta23/CCM/ReplacementSource.lean'})
        bad['counts']['required_new_paths'] += 1
        with self.assertRaises(InvalidCertificate):
            projection.path_policy(bad)

    def test_candidate_cannot_move_protected_math_to_edit_scope(self):
        bad = copy.deepcopy(self.manifest)
        bad['edit'][0]['path'] = 'Zeta23/CCM/NativeFloorCompletionSource.lean'
        with self.assertRaises(InvalidCertificate):
            projection.path_policy(bad)

    def test_duplicate_or_traversing_path_rejected(self):
        for relative in ('../outside.lean','C:/outside.lean','Zeta23\\Outside.lean'):
            bad = copy.deepcopy(self.manifest)
            bad['create'][0]['path'] = relative
            with self.assertRaises(InvalidCertificate):
                projection.path_policy(bad)
        bad = copy.deepcopy(self.manifest)
        bad['create'].append(copy.deepcopy(bad['create'][0]))
        with self.assertRaises(InvalidCertificate):
            projection.path_policy(bad)

    def test_projection_destination_guards_run_before_mutation(self):
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            self.assertTrue(Path(tmp).resolve().is_relative_to(TEMP_ROOT.resolve()))
            root = Path(tmp)
            repo = root/'repo'
            repo.mkdir()
            occupied = root/'occupied'
            occupied.mkdir()
            marker = occupied/'keep'
            marker.write_text('untouched')
            for target in (repo,repo/'child',root.parent/'escape',occupied):
                with patch.object(projection, 'inspect_descendant') as inspect:
                    with patch.object(projection.subprocess, 'run') as run:
                        with self.assertRaises(InvalidCertificate):
                            projection.create_projection(repo,target)
                        inspect.assert_not_called()
                        run.assert_not_called()
            self.assertEqual(marker.read_text(),'untouched')

    def test_failure_is_not_a_receipt_or_compatibility_pass(self):
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            self.assertTrue(Path(tmp).resolve().is_relative_to(TEMP_ROOT.resolve()))
            with self.assertRaises(InvalidCertificate):
                projection.verify_projection(Path(tmp)/'absent')

    def test_full_population_commands_retain_unchanged_legacy_producers(self):
        for population, (script,base) in capture.LEGACY.items():
            argv=capture.legacy_command(population,Path('external'),python='python',lake='lake')
            self.assertEqual(argv[2],script)
            self.assertEqual(argv[argv.index('--requested-head')+1],projection.contract.FROZEN_COMMIT)
            self.assertEqual(argv[argv.index('--requested-base')+1],base)
            self.assertNotIn('--preparation-only',argv)

    def test_unknown_population_cannot_select_arbitrary_executable(self):
        with self.assertRaises(InvalidCertificate):
            capture.legacy_command('../other',Path('external'),python='python',lake='lake')

    def test_capture_cannot_write_artifacts_into_source(self):
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            self.assertTrue(Path(tmp).resolve().is_relative_to(TEMP_ROOT.resolve()))
            root=Path(tmp)
            with patch.object(projection,'create_projection') as create:
                with self.assertRaises(InvalidCertificate):
                    capture.capture(root/'repo',root/'source',root/'repo'/'outputs')
                create.assert_not_called()

    def test_ignored_file_cannot_enter_verified_ancestor_view(self):
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            self.assertTrue(Path(tmp).resolve().is_relative_to(TEMP_ROOT.resolve()))
            root=Path(tmp)
            source=root/'source'
            source.mkdir()
            source_file=source/'frozen.lean'
            source_file.write_bytes(b'theorem frozen : True := True.intro\n')
            size,blob,digest=projection.contract.actual_blob_identity(source_file)
            lockdir=root/'locks'
            lockdir.mkdir()
            row={'path':'frozen.lean','mode':'100644','git_blob':blob,'bytes':size,'sha256':digest}
            import json
            (lockdir/'ANCESTOR_LOCK.json').write_text(json.dumps({'frozen_ancestor':{'source_manifest':[row]}}))
            def git(_repo,*args):
                if args==('rev-parse','HEAD'):
                    return projection.contract.FROZEN_COMMIT
                if args and args[0]=='rev-parse':
                    return projection.contract.FROZEN_TREE
                if args and args[0]=='status':
                    return ''  # Simulate Git ignoring a hidden source provider.
                if args and args[0]=='ls-tree':
                    return '100644 blob '+blob+'\tfrozen.lean'
                raise RuntimeError(args)
            with patch.object(projection.contract,'git',side_effect=git):
                valid=projection.verify_projection(source,reference_repo=source,here=lockdir)
                self.assertEqual(valid['status'],'PASS_EXACT_FROZEN_SOURCE_ONLY')
                (source/'.ignored-provider.lean').write_text('axiom hidden : False')
                with self.assertRaises(InvalidCertificate):
                    projection.verify_projection(source,reference_repo=source,here=lockdir)


class CurrentCompilerProducerGuards(unittest.TestCase):
    def test_actual_frozen_query_populations_and_reviewed_types(self):
        import dependency_delta as delta
        repo=HERE.parents[3]
        for population,query_count in ((76,76),(100,303)):
            plan=delta.current_export_plan(repo,population)
            self.assertEqual(len(plan['roots']),population)
            self.assertEqual(len(plan['queries']),query_count)
            self.assertTrue(all('expected_type_sha256' in r for r in plan['queries']))
            self.assertNotIn(b'Zeta23.OPICARound2',plan['driver'])

    def test_wrong_population_never_selects_an_exporter(self):
        import dependency_delta as delta
        for value in (True,0,77,99,'100'):
            with self.assertRaises(InvalidCertificate): delta.current_export_plan(HERE.parents[3],value)

    def test_current_command_has_real_current_build_and_frozen_queries(self):
        import dependency_delta as delta
        for population in (76,100):
            plan=delta.current_export_plan(HERE.parents[3],population)
            output=Path('/external/current-exports')
            commands=delta.current_export_commands(plan,output,'pinned-lake')
            self.assertEqual([name for _,name in commands],['lean-version','build','bindings'])
            self.assertEqual(commands[1][0],['pinned-lake','build',*plan['targets']])
            self.assertNotIn('validate_contract.py',' '.join(commands[-1][0]))
            self.assertNotIn('--requested-head',' '.join(commands[-1][0]))
            if population==76:
                self.assertEqual(commands[-1][0][-1],'Zeta23/RHRC/OpicaBindings.lean')
            else:
                self.assertIn('-R',commands[-1][0])

    def test_foreign_current_head_is_rejected_before_reparse(self):
        import dependency_delta as delta
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as temp:
            root=Path(temp)
            path=root/'current-compiler-receipt.json'
            path.write_text(__import__('json').dumps({'schema':'OPICA2_CURRENT_ANCESTOR_EXPORT_V1',
                'population':76,'checked_commit':'b'*40,'checked_tree':'c'*40}))
            with patch.object(delta.contract,'git',return_value='a'*40):
                with self.assertRaises(InvalidCertificate):
                    delta.verify_current_export(root,path,root,population=76,
                                                expected_commit='a'*40,expected_tree='c'*40)

    def test_current_producer_preserves_failed_raw_logs_without_receipt(self):
        import dependency_delta as delta
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as temp:
            root=Path(temp);repo=root/'repo';repo.mkdir();output=root/'evidence'
            def run(repo,argv,output,name,tree,**kwargs):
                (output/(name+'.stdout.log')).write_bytes(b'failed native command\n')
                (output/(name+'.stderr.log')).write_bytes(b'compiler error\n')
                return {'argv':argv,'returncode':1,'working_tree_sha':tree}
            fake={'population':76,'driver':b'-- frozen source','roots':[],
                  'queries':[],'targets':['Zeta23.OPICA'],'relative_exporter':'frozen.lean'}
            with patch.object(delta.contract,'git',return_value='a'*40), \
                 patch.object(projection,'inspect_descendant',return_value={'status':'source scope'}), \
                 patch.object(delta.compiler,'source_manifest',return_value=[]), \
                 patch.object(delta.compiler,'validate_environment',return_value={}), \
                 patch.object(delta.compiler,'validate_packages',return_value=[]), \
                 patch.object(delta,'current_export_plan',return_value=fake), \
                 patch.object(delta.compiler,'run_command',side_effect=run):
                with self.assertRaises(InvalidCertificate): delta.produce_current_export(repo,output,population=76)
            self.assertEqual((output/'lean-version.stderr.log').read_bytes(),b'compiler error\n')
            self.assertFalse((output/'current-compiler-receipt.json').exists())

    def test_current_export_refuses_artifacts_inside_source(self):
        import dependency_delta as delta
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as temp:
            repo=Path(temp)
            with self.assertRaises(InvalidCertificate): delta.produce_current_export(repo,repo/'artifacts',population=76)


class CurrentArtifactReparseBoundaries(unittest.TestCase):
    """Producer-shaped artifact fixtures, never counterfeit compiler authority.

    The actual immutable root/query/driver plan is used. Native parsing and the
    external source/package census are mocked only to exercise the independent
    artifact boundary. These fixtures do not count as fresh Lean execution.
    """
    @classmethod
    def setUpClass(cls):
        import dependency_delta as delta
        cls.delta = delta
        cls.plans = {p: delta.current_export_plan(HERE.parents[3], p) for p in (76, 100)}

    def setUp(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=TEMP_ROOT)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.repo = self.root / 'current-source'
        self.repo.mkdir()
        self.head, self.tree = 'a' * 40, 'b' * 40
        self.environment = {'lean_toolchain': 'leanprover/lean4:v4.33.0-rc2',
            'mathlib_commit': '51e6992efd06126df61a496bebf8f49482a4e129'}
        self.packages = [{'name': 'mathlib', 'commit': self.environment['mathlib_commit']}]
        self.sources = [{'path': 'Zeta23/Fixture.lean', 'mode': '100644',
            'git_blob': 'c' * 40, 'bytes': 19, 'sha256': 'd' * 64}]
        self.scope = {'schema': 'OPICA2_TEST_SOURCE_SCOPE_BOUNDARY_ONLY',
            'checked_commit': self.head, 'checked_tree': self.tree}
        self.parsed = {'declarations': [{'name': 'fixture_only', 'type_sha256': 'e' * 64}],
            'constructors': [], 'generated_equations': {}, 'dependency_declarations': [], 'dependencies': []}

    def fixture(self, *, population=76, producer_root=None, name='downloaded-artifacts'):
        delta = self.delta
        plan = self.plans[population]
        artifacts = self.root / name
        artifacts.mkdir()
        original = producer_root or PurePosixPath('/provider/original/compiler-artifacts')
        (artifacts / 'CurrentAncestorExport.lean').write_bytes(plan['driver'])
        (artifacts / 'CurrentAncestorExport.olean').write_bytes(b'fixture object; not Lean compiler evidence')
        (artifacts / 'source-manifest.json').write_bytes(json.dumps(self.sources).encode('utf-8'))
        commands = []
        for argv, label in delta.current_export_commands(plan, original, 'pinned-lake'):
            stdout = (b'Lean (version 4.33.0-rc2, x86_64, commit d8b18978322de05a8f3dba51ef03cf5461676c17)\n'
                      if label == 'lean-version' else (label + ' fixture native-parser boundary\n').encode())
            (artifacts / (label + '.stdout.log')).write_bytes(stdout)
            (artifacts / (label + '.stderr.log')).write_bytes(b'')
            commands.append({'argv': argv, 'returncode': 0, 'working_tree_sha': self.tree,
                'stdout_sha256': hashlib.sha256(stdout).hexdigest(), 'stderr_sha256': hashlib.sha256(b'').hexdigest()})
        data = {'schema': 'OPICA2_CURRENT_ANCESTOR_EXPORT_V1', 'status': 'PASS_CURRENT_NATIVE_COMPILER_EXPORT',
            'checked_commit': self.head, 'checked_tree': self.tree, **self.environment,
            'population': population, 'root_names': [r['full_name'] for r in plan['roots']],
            'query_inventory_sha256': delta.canonical_sha256(plan['queries']),
            'source_manifest_sha256': delta.canonical_sha256(self.sources), 'source_manifest_path': 'source-manifest.json',
            'exporter_source_sha256': hashlib.sha256(plan['driver']).hexdigest(),
            'compiled_export_sha256': delta.contract.digest(artifacts / 'CurrentAncestorExport.olean'),
            'commands': commands, 'pinned_packages': self.packages, 'parsed': copy.deepcopy(self.parsed),
            'producer_artifact_root': str(original), 'descendant_source_scope': self.scope,
            'build_mode': 'WARM_PROJECT_OBJECTS_ALLOWED_FRESH_COMPILER_PROCESSES',
            'fresh_compiler_process_executed': True, 'frozen_legacy_release_gate_rebound': False,
            'ancestor_baseline_replay': False, 'ancestor_current_compatibility': False,
            'full_core_accepted': False, 'full_release_accepted': False, 'RH': 'OPEN', 'Step4': 'OPEN'}
        receipt = artifacts / 'current-compiler-receipt.json'
        self.write_receipt(receipt, data)
        return receipt, artifacts, data

    @staticmethod
    def write_receipt(path, data):
        path.write_bytes(json.dumps(data).encode('utf-8'))

    def verify(self, receipt, artifacts, *, population=76):
        delta = self.delta
        def git(_repo, *args):
            if args == ('rev-parse', 'HEAD'):
                return self.head
            if args == ('rev-parse', 'HEAD^{tree}'):
                return self.tree
            raise AssertionError('Unexpected Git census request: ' + repr(args))
        with ExitStack() as stack:
            stack.enter_context(patch.object(delta.contract, 'git', side_effect=git))
            stack.enter_context(patch.object(delta.compiler, 'source_manifest', return_value=copy.deepcopy(self.sources)))
            stack.enter_context(patch.object(delta.compiler, 'validate_environment', return_value=dict(self.environment)))
            stack.enter_context(patch.object(delta.compiler, 'validate_packages', return_value=copy.deepcopy(self.packages)))
            stack.enter_context(patch.object(projection, 'inspect_descendant', return_value=dict(self.scope)))
            stack.enter_context(patch.object(delta, 'current_export_plan', return_value=dict(self.plans[population])))
            parser = stack.enter_context(patch.object(delta, '_parse_current', return_value=copy.deepcopy(self.parsed)))
            result = delta.verify_current_export(self.repo, receipt, artifacts, population=population,
                expected_commit=self.head, expected_tree=self.tree)
            parser.assert_called_once()
            return result

    def test_valid_relocated_both_os_paths_and_original_populations(self):
        for population in (76, 100):
            for platform, original in [('posix', PurePosixPath('/original/worker/evidence')),
                                       ('windows', PureWindowsPath(r'C:\original\worker\evidence'))]:
                with self.subTest(population=population, platform=platform):
                    receipt, artifacts, data = self.fixture(population=population, producer_root=original,
                        name=str(population) + '-' + platform)
                    result = self.verify(receipt, artifacts, population=population)
                    self.assertEqual(result['population'], population)
                    self.assertFalse(result['fresh_compiler_replay'])
                    self.assertFalse(result['provider_authenticity_established_here'])
                    self.assertIn('RAW_LOG_REPARSE_ONLY', result['authority'])

    def test_missing_raw_log_rejected(self):
        receipt, artifacts, _ = self.fixture()
        (artifacts / 'build.stderr.log').unlink()
        with self.assertRaises((InvalidCertificate, OSError)):
            self.verify(receipt, artifacts)

    def test_altered_log_object_driver_and_source_inventory_rejected(self):
        for index, relative in enumerate(('bindings.stdout.log', 'CurrentAncestorExport.olean',
                                         'CurrentAncestorExport.lean', 'source-manifest.json')):
            with self.subTest(relative=relative):
                receipt, artifacts, _ = self.fixture(name='tamper-' + str(index))
                (artifacts / relative).write_bytes(b'altered artifact')
                with self.assertRaises((InvalidCertificate, OSError)):
                    self.verify(receipt, artifacts)

    def test_substituted_parsed_proof_record_rejected(self):
        receipt, artifacts, data = self.fixture()
        data['parsed']['declarations'][0]['type_sha256'] = '0' * 64
        self.write_receipt(receipt, data)
        with self.assertRaisesRegex(InvalidCertificate, 'raw-log reparse'):
            self.verify(receipt, artifacts)

    def test_stale_head_and_tree_in_valid_shaped_receipt_rejected(self):
        for index, field in enumerate(('checked_commit', 'checked_tree')):
            receipt, artifacts, data = self.fixture(name='stale-' + str(index))
            data[field] = '0' * 40
            self.write_receipt(receipt, data)
            with self.assertRaisesRegex(InvalidCertificate, 'mixes source heads'):
                self.verify(receipt, artifacts)

    def test_wrong_recorded_toolchain_mathlib_and_package_rejected(self):
        for index, field in enumerate(('lean_toolchain', 'mathlib_commit', 'pinned_packages')):
            receipt, artifacts, data = self.fixture(name='environment-' + str(index))
            data[field] = [] if field == 'pinned_packages' else 'wrong pin'
            self.write_receipt(receipt, data)
            with self.assertRaises(InvalidCertificate):
                self.verify(receipt, artifacts)

    def test_false_authority_caps_empty_commands_and_unknown_fields_rejected(self):
        changes = [('status', 'PASS_FULL_RELEASE'), ('fresh_compiler_process_executed', False),
            ('frozen_legacy_release_gate_rebound', True), ('ancestor_baseline_replay', True),
            ('ancestor_current_compatibility', True), ('full_core_accepted', True), ('full_release_accepted', True),
            ('RH', 'PROVED'), ('Step4', 'CLOSED'), ('commands', []), ('invented_review_approval', True)]
        for index, (field, value) in enumerate(changes):
            receipt, artifacts, data = self.fixture(name='authority-' + str(index))
            data[field] = value
            self.write_receipt(receipt, data)
            with self.assertRaises(InvalidCertificate):
                self.verify(receipt, artifacts)

    def test_source_and_descendant_scope_substitutions_rejected(self):
        for index, field in enumerate(('source_manifest_sha256', 'query_inventory_sha256', 'descendant_source_scope')):
            receipt, artifacts, data = self.fixture(name='scope-' + str(index))
            data[field] = {} if field == 'descendant_source_scope' else '0' * 64
            self.write_receipt(receipt, data)
            with self.assertRaises(InvalidCertificate):
                self.verify(receipt, artifacts)

    def test_original_argv_root_and_filename_substitution_rejected(self):
        receipt, artifacts, data = self.fixture()
        data['commands'][-1]['argv'][-2] = '/substituted/CurrentAncestorExport.olean'
        self.write_receipt(receipt, data)
        with self.assertRaises(InvalidCertificate):
            self.verify(receipt, artifacts)

    def test_wrong_executed_compiler_version_even_with_matching_log_hash_rejected(self):
        receipt, artifacts, data = self.fixture()
        version = artifacts / 'lean-version.stdout.log'
        version.write_bytes(b'Lean (version 4.34.0, wrong compiler commit)\n')
        data['commands'][0]['stdout_sha256'] = hashlib.sha256(version.read_bytes()).hexdigest()
        self.write_receipt(receipt, data)
        with self.assertRaisesRegex(InvalidCertificate, 'compiler pin differs'):
            self.verify(receipt, artifacts)

    def test_producer_root_requires_absolute_traversal_free_original_path(self):
        for index, value in enumerate(('relative/artifacts', '/original/../escape', r'C:\original\..\escape', '/bad\x00root')):
            receipt, artifacts, data = self.fixture(name='bad-root-' + str(index))
            data['producer_artifact_root'] = value
            self.write_receipt(receipt, data)
            with self.assertRaises(InvalidCertificate):
                self.verify(receipt, artifacts)

    def test_symlinked_receipt_refused_before_resolve(self):
        receipt, artifacts, _ = self.fixture()
        real_is_symlink = Path.is_symlink
        with patch.object(Path, 'is_symlink', autospec=True,
                side_effect=lambda path: path == receipt or real_is_symlink(path)):
            with self.assertRaisesRegex(InvalidCertificate, 'Linked current evidence'):
                self.verify(receipt, artifacts)

    def test_symlinked_artifact_file_is_not_hashed_as_regular_evidence(self):
        receipt, artifacts, _ = self.fixture()
        linked = artifacts / 'CurrentAncestorExport.olean'
        real_is_symlink = Path.is_symlink
        with patch.object(Path, 'is_symlink', autospec=True,
                side_effect=lambda path: path == linked or real_is_symlink(path)):
            with self.assertRaisesRegex(InvalidCertificate, '[Ss]ymlink'):
                self.verify(receipt, artifacts)


if __name__ == '__main__':
    unittest.main()
