"""Adversarial regressions for the complete post268 execution harvest."""
from __future__ import annotations
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('post268_runner', Path(__file__).resolve().parents[1] / 'run_tests.py')
r = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(r)


class PipelineTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.out = Path(self.tmp.name)
        self.test = next(x for x in r.load_inventory() if x['id'] == r.POST222)

    def execute(self, commands, timeout=5):
        test = {**self.test, 'timeout_seconds': timeout}
        with patch.object(r, 'command_plan', return_value=commands):
            return r.run_one(test, self.out)

    def test_production_plan_binds_same_fixture_and_schedule(self):
        producer, checker = r.command_plan(self.test, self.out)
        self.assertTrue(producer[1].endswith('probe_post222_fb05_biregular_zero_shift_scalar_scope.py'))
        self.assertEqual(producer[3], checker[3])
        self.assertEqual(producer[-1], checker[-1])
        self.assertEqual(checker[-2], '--schedule')
        self.assertTrue(Path(producer[3]).is_file())

    def test_real_schedule_producer_replays_frozen_centers(self):
        # Does not require FLINT; the independent numerical consumer runs in CI.
        import subprocess
        producer, _ = r.command_plan(self.test, self.out)
        subprocess.run(producer, cwd=r.REPO, check=True, stdout=subprocess.PIPE)
        payload = json.loads((self.out / r.SCHEDULE).read_text())
        fixture = json.loads(Path(producer[3]).read_text())
        self.assertEqual(payload['status'], 'PASS')
        self.assertEqual(len(payload['points']), len(fixture['inherited_points']))
        self.assertFalse(payload['adaptive_point_search'])
        self.assertFalse(payload['target_sign_selection'])

    def test_failed_producer_never_runs_checker(self):
        sentinel = self.out / 'checker-ran'
        row = self.execute([[sys.executable, '-c', 'raise SystemExit(7)'],
                            [sys.executable, '-c', f'open({str(sentinel)!r}, "w").close()']])
        self.assertEqual(row['execution_disposition'], 'FAIL')
        self.assertEqual(row['returncode'], 7)
        self.assertEqual(len(row['steps']), 1)
        self.assertFalse(sentinel.exists())

    def test_zero_exit_without_schedule_rejects_stale_file(self):
        (self.out / r.SCHEDULE).write_text('{"stale": true}')
        row = self.execute([[sys.executable, '-c', 'pass'], [sys.executable, '-c', 'pass']])
        self.assertEqual(row['execution_disposition'], 'MISSING_GENERATED_INPUT')
        self.assertEqual(len(row['steps']), 1)
        self.assertFalse((self.out / r.SCHEDULE).exists())

    def test_success_requires_both_processes_and_hashes_schedule(self):
        path = self.out / r.SCHEDULE
        row = self.execute([[sys.executable, '-c', f'open({str(path)!r}, "w").write("{{}}")'],
                            [sys.executable, '-c', f'assert open({str(path)!r}).read() == "{{}}"']])
        self.assertEqual(row['execution_disposition'], 'PASS')
        self.assertEqual(len(row['steps']), 2)
        self.assertEqual(row['generated_inputs'], [{'path': r.SCHEDULE, 'sha256': r.digest(path)}])
        self.assertEqual(row['log_sha256'], r.digest(self.out / row['log']))

    def test_checker_failure_is_not_masked_by_successful_producer(self):
        path = self.out / r.SCHEDULE
        row = self.execute([[sys.executable, '-c', f'open({str(path)!r}, "w").write("{{}}")'],
                            [sys.executable, '-c', 'raise SystemExit(9)']])
        self.assertEqual(row['execution_disposition'], 'FAIL')
        self.assertEqual(row['returncode'], 9)

    def test_timeout_is_failure_and_preserves_log(self):
        row = self.execute([[sys.executable, '-c', 'import time; time.sleep(10)']], timeout=0.1)
        self.assertEqual(row['execution_disposition'], 'TIMEOUT')
        self.assertIn('AUDIT_TIMEOUT', row['tail'])
        self.assertFalse(row['theorem_promotion'])

    def test_spawn_failure_is_recorded_not_raised(self):
        row = self.execute([[str(self.out / 'missing-executable')]])
        self.assertEqual(row['execution_disposition'], 'FAIL')
        self.assertIn('AUDIT_SPAWN_ERROR', row['tail'])


class HarvestTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.out = Path(self.tmp.name)
        self.shards = self.out / 'shards'
        self.shards.mkdir()
        self.inventory = r.load_inventory()
        self.source = {'commit': 'fixture-commit', 'tree': 'fixture-tree',
                       'inventory_sha256': r.digest(r.INVENTORY), 'working_tree_dirty': False}
        self.reports = []
        for shard in range(8):
            folder = self.shards / str(shard)
            folder.mkdir()
            tests = [test for i, test in enumerate(self.inventory) if i % 8 == shard]
            rows = []
            for test in tests:
                logfile = folder / (test['id'] + '.log')
                logfile.write_text('synthetic successful execution\n')
                steps = [{'returncode': 0, 'execution_disposition': 'PASS', 'command': cmd}
                         for cmd in r.command_plan(test, folder)]
                inputs = []
                if test['id'] == r.POST222:
                    schedule = folder / r.SCHEDULE
                    schedule.write_text('{"fixture": true}')
                    inputs = [{'path': r.SCHEDULE, 'sha256': r.digest(schedule)}]
                rows.append({**test, 'steps': steps, 'generated_inputs': inputs,
                             'returncode': 0, 'execution_disposition': 'PASS',
                             'log': logfile.name, 'log_sha256': r.digest(logfile), 'theorem_promotion': False})
            p = {'schema': 'POST268_EXECUTION_v2', 'source': self.source, 'source_after': self.source,
                 'shard': shard, 'shards': 8, 'expected_ids': [t['id'] for t in tests], 'results': rows,
                 'terminal_claim': 'RH_OPEN', 'theorem_promotion': False}
            path = folder / f'extended-{shard}.json'
            r.write_json(path, p)
            self.reports.append(path)

    def harvest(self):
        with patch.object(r, 'anchor', return_value=self.source), contextlib.redirect_stdout(io.StringIO()):
            return r.harvest(self.shards, self.out / 'harvest.json')

    def mutate(self, index, mutation):
        p = json.loads(self.reports[index].read_text())
        mutation(p)
        r.write_json(self.reports[index], p)

    def test_complete_population_passes_without_theorem_promotion(self):
        self.assertEqual(self.harvest(), 0)
        p = json.loads((self.out / 'harvest.json').read_text())
        self.assertEqual(len(p['results']), 44)
        self.assertFalse(p['theorem_promotion'])
        self.assertEqual(p['terminal_claim'], 'RH_OPEN')

    def test_missing_shard_fails(self):
        self.reports[-1].unlink()
        self.assertEqual(self.harvest(), 1)

    def test_missing_result_fails(self):
        self.mutate(0, lambda p: p['results'].pop())
        self.assertEqual(self.harvest(), 1)

    def test_duplicate_shard_fails(self):
        clone = self.reports[0].with_name('extended-duplicate.json')
        clone.write_bytes(self.reports[0].read_bytes())
        self.assertEqual(self.harvest(), 1)

    def test_forged_passing_row_with_failed_pipeline_fails(self):
        self.mutate(0, lambda p: p['results'][0]['steps'][0].update(returncode=7))
        self.assertEqual(self.harvest(), 1)

    def test_log_tampering_fails(self):
        p = json.loads(self.reports[0].read_text())
        (self.reports[0].parent / p['results'][0]['log']).write_text('altered')
        self.assertEqual(self.harvest(), 1)

    def test_missing_or_changed_schedule_fails(self):
        schedule = next(self.shards.rglob(r.SCHEDULE))
        schedule.write_text('changed')
        self.assertEqual(self.harvest(), 1)
        schedule.unlink()
        self.assertEqual(self.harvest(), 1)

    def test_other_commit_fails(self):
        self.mutate(0, lambda p: p['source'].update(commit='other'))
        self.assertEqual(self.harvest(), 1)

    def test_dirty_tree_fails(self):
        self.mutate(0, lambda p: p['source_after'].update(working_tree_dirty=True))
        self.assertEqual(self.harvest(), 1)

    def test_old_schema_cannot_inherit_new_pipeline_authority(self):
        self.mutate(0, lambda p: p.update(schema='POST268_EXECUTION_v1'))
        self.assertEqual(self.harvest(), 1)

    def test_authority_drift_fails(self):
        self.mutate(0, lambda p: p.update(theorem_promotion=True))
        self.assertEqual(self.harvest(), 1)

    def test_path_escape_is_rejected(self):
        outside = self.out / 'outside.log'
        outside.write_text('not the checker log')
        def modify(p):
            p['results'][0].update(log='../../outside.log', log_sha256=r.digest(outside))
        self.mutate(0, modify)
        self.assertEqual(self.harvest(), 1)


if __name__ == '__main__':
    unittest.main()
