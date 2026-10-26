"""The descendant cannot enlarge its policy or overwrite a source directory."""
import copy
import hashlib
import importlib.util
from pathlib import Path
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


if __name__ == '__main__':
    unittest.main()
