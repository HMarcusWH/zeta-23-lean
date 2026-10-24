"""Adversarial execution, scope and scientific-disposition harvest tests."""
from __future__ import annotations

import base64
from copy import deepcopy
import hashlib
import importlib.util
from pathlib import Path
import unittest
from urllib.parse import parse_qs, urlsplit

SPEC = importlib.util.spec_from_file_location('followup_harvest',
    Path(__file__).resolve().parents[1] / 'harvest_workflows.py')
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)
HEAD, TREE, MERGE, OTHER = 'a' * 40, 'b' * 40, 'c' * 40, 'd' * 40
PATH = '.github/workflows/frozen_research.yml'


def page(field, rows):
    return {'total_count': len(rows), field: rows}


def run(identity=1, event='pull_request', number=1):
    return {'id': identity, 'path': PATH, 'event': event, 'head_sha': HEAD,
            'run_attempt': 1, 'run_number': number, 'status': 'completed', 'conclusion': 'success'}


def job(identity=10, run_id=1, name='research', attempt=1):
    return {'id': identity, 'name': name, 'run_id': run_id, 'run_attempt': attempt,
            'head_sha': HEAD, 'status': 'completed', 'conclusion': 'success', 'steps': []}


def policy(name='research', required=True, event='pull_request'):
    return {'workflow': PATH, 'event': event, 'name': name, 'required': required,
            'classification': 'RESEARCH_PRODUCING_CHECK', 'head_sha': HEAD}


def snapshot():
    return {'head_sha': HEAD, 'head_tree': TREE, 'commit_trees': {HEAD: TREE},
            'run_pages': [page('workflow_runs', [run()])],
            'check_pages': [page('check_runs', [])],
            'job_pages': [{'run_id': 1, 'attempt': 1, 'pages': [page('jobs', [job()])]}],
            'artifact_pages': [{'run_id': 1, 'pages': [page('artifacts', [])]}],
            'job_policies': [policy()]}


def review(identity=10, run_id=1, attempt=1, disposition='UNRESOLVED'):
    return {'run_id': run_id, 'attempt': attempt, 'event': 'pull_request', 'head_sha': HEAD,
            'checked_sha': HEAD, 'checked_tree': TREE,
            'classification': 'RESEARCH_PRODUCING_CHECK',
            'commands': [{'command': 'python exact_frozen_check.py --budget 600', 'exit_code': 0}],
            'fixture_id': 'same-frozen-rational-inputs', 'fixture_sha256': 'e' * 64,
            'mathematical_disposition': {'gate': disposition, 'RH': 'OPEN'}}


class HarvestMutations(unittest.TestCase):
    def setUp(self):
        self.data = snapshot()

    def test_success_is_execution_only_and_input_is_unchanged(self):
        before = deepcopy(self.data)
        result = M.harvest(self.data)
        self.assertEqual(result['execution_status'], 'PASS')
        self.assertEqual(result['review_status'], 'INCOMPLETE')
        self.assertFalse(result['independent_review_approved'])
        self.assertFalse(result['theorem_promotion'])
        self.assertEqual((result['RH'], result['Step4']), ('OPEN', 'OPEN'))
        self.assertEqual(self.data, before)

    def test_each_unsuccessful_required_job_blocks_without_losing_disposition(self):
        for status, conclusion in [('completed', 'skipped'), ('completed', 'cancelled'),
                                   ('completed', 'failure'), ('completed', 'timed_out'),
                                   ('queued', None), ('in_progress', None)]:
            with self.subTest(status=status, conclusion=conclusion):
                data = deepcopy(self.data)
                data['job_pages'][0]['pages'][0]['jobs'][0].update(status=status, conclusion=conclusion)
                result = M.harvest(data)
                self.assertEqual(result['execution_status'], 'BLOCKED')
                self.assertEqual(result['effective_jobs'][0]['status'], status)
                self.assertEqual(result['effective_jobs'][0]['conclusion'], conclusion)

    def test_optional_cancelled_skipped_and_running_jobs_are_retained(self):
        for status, conclusion in [('completed', 'cancelled'), ('completed', 'skipped'), ('in_progress', None)]:
            with self.subTest(conclusion=conclusion):
                data = deepcopy(self.data)
                optional = job(11, name='optional')
                optional.update(status=status, conclusion=conclusion)
                data['job_pages'][0]['pages'][0] = page('jobs', [job(), optional])
                data['job_policies'].append(policy('optional', False))
                result = M.harvest(data)
                self.assertEqual(result['execution_status'], 'PASS')
                self.assertEqual(result['effective_jobs'][1]['conclusion'], conclusion)

    def test_optional_cancelled_workflow_does_not_fail_required_other_scope(self):
        self.add_run(run(2, 'push'), job(20, 2, 'optional'))
        self.data['run_pages'][0]['workflow_runs'][1]['conclusion'] = 'cancelled'
        self.data['job_policies'].append(policy('optional', False, 'push'))
        self.assertEqual(M.harvest(self.data)['execution_status'], 'PASS')

    def test_required_cancelled_workflow_blocks_even_if_job_reported_success(self):
        self.data['run_pages'][0]['workflow_runs'][0]['conclusion'] = 'cancelled'
        self.assertEqual(M.harvest(self.data)['blockers'][0]['reason'], 'REQUIRED_WORKFLOW_NOT_SUCCESSFUL')

    def test_push_success_does_not_satisfy_required_pr_job(self):
        self.data['run_pages'][0]['workflow_runs'][0]['event'] = 'push'
        result = M.harvest(self.data)
        self.assertEqual(result['execution_status'], 'BLOCKED')
        self.assertEqual(result['effective_jobs'][0]['event'], 'push')

    def add_run(self, provider_run, provider_job):
        rows = self.data['run_pages'][0]['workflow_runs']
        rows.append(provider_run)
        self.data['run_pages'][0]['total_count'] = len(rows)
        self.data['job_pages'].append({'run_id': provider_run['id'], 'attempt': 1,
                                      'pages': [page('jobs', [provider_job])]})
        self.data['artifact_pages'].append({'run_id': provider_run['id'], 'pages': [page('artifacts', [])]})

    def test_push_and_pr_scopes_remain_distinct(self):
        self.add_run(run(2, 'push'), job(20, 2))
        self.data['job_policies'].append(policy(event='push'))
        result = M.harvest(self.data)
        self.assertEqual(len(result['effective_jobs']), 2)
        self.assertEqual({j['event'] for j in result['effective_jobs']}, {'push', 'pull_request'})

    def test_latest_failed_run_cannot_choose_older_success(self):
        newer = job(20, 2)
        newer['conclusion'] = 'failure'
        self.add_run(run(2, number=2), newer)
        result = M.harvest(self.data)
        self.assertEqual(result['execution_status'], 'BLOCKED')
        self.assertEqual(result['effective_jobs'][0]['id'], 20)
        self.assertEqual(len(result['all_job_attempts']), 2)

    def test_duplicate_old_run_number_cannot_hide_behind_newer_run(self):
        self.add_run(run(2, number=2), job(20, 2))
        self.add_run(run(3, number=1), job(30, 3))
        with self.assertRaisesRegex(ValueError, 'conflicting workflow run number'):
            M.harvest(self.data)

    def test_latest_is_run_number_not_favorable_id_order(self):
        self.data['run_pages'][0]['workflow_runs'][0].update(id=90, run_number=3)
        self.data['job_pages'][0]['run_id'] = 90
        self.data['job_pages'][0]['pages'][0]['jobs'][0]['run_id'] = 90
        self.data['artifact_pages'][0]['run_id'] = 90
        newer = job(20, 2)
        newer['conclusion'] = 'failure'
        self.add_run(run(2, number=4), newer)
        self.assertEqual(M.harvest(self.data)['effective_jobs'][0]['id'], 20)

    def rerun(self, rerun_name='research'):
        self.data['run_pages'][0]['workflow_runs'][0]['run_attempt'] = 2
        self.data['job_pages'][0]['pages'][0]['jobs'][0]['conclusion'] = 'failure'
        self.data['job_pages'].append({'run_id': 1, 'attempt': 2,
                                      'pages': [page('jobs', [job(20, name=rerun_name, attempt=2)])]})

    def test_successful_rerun_supersedes_exact_job_and_preserves_failed_history(self):
        self.rerun()
        result = M.harvest(self.data)
        self.assertEqual(result['execution_status'], 'PASS')
        self.assertEqual(result['effective_jobs'][0]['attempt'], 2)
        self.assertEqual(result['all_job_attempts'][0]['conclusion'], 'failure')

    def test_partial_rerun_keeps_unrerun_failure_effective(self):
        self.rerun('different job')
        result = M.harvest(self.data)
        self.assertEqual(result['execution_status'], 'BLOCKED')
        self.assertEqual(result['effective_jobs'][0]['conclusion'], 'failure')

    def test_missing_historical_attempt_rejected(self):
        self.rerun()
        self.data['job_pages'].pop(0)
        with self.assertRaisesRegex(ValueError, 'missing historical'):
            M.harvest(self.data)

    def test_old_job_id_cannot_be_reused_as_a_new_attempt(self):
        self.rerun()
        self.data['job_pages'][1]['pages'][0]['jobs'][0]['id'] = 10
        with self.assertRaisesRegex(ValueError, 'identity reused across attempts'):
            M.harvest(self.data)

    def test_truncated_and_duplicate_pages_rejected(self):
        for field in ('run_pages', 'check_pages'):
            with self.subTest(field=field):
                data = deepcopy(self.data)
                data[field][0]['total_count'] += 1
                with self.assertRaisesRegex(ValueError, 'incomplete'):
                    M.harvest(data)
        self.data['run_pages'].append(deepcopy(self.data['run_pages'][0]))
        self.data['run_pages'][0]['total_count'] = self.data['run_pages'][1]['total_count'] = 2
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            M.harvest(self.data)

    def test_boolean_total_not_integer_and_totals_cannot_change(self):
        with self.assertRaisesRegex(ValueError, 'invalid provider total'):
            M.complete_pages([{'total_count': True, 'jobs': [job()]}], 'jobs')
        with self.assertRaisesRegex(ValueError, 'unstable'):
            M.complete_pages([page('jobs', [job()]), {'total_count': 2, 'jobs': []}], 'jobs')

    def test_job_identity_mutations_rejected(self):
        for key, value, message in [('head_sha', OTHER, 'head mismatch'),
                                    ('run_attempt', 2, 'attempt mismatch'),
                                    ('event', 'push', 'event mismatch')]:
            with self.subTest(key=key):
                data = deepcopy(self.data)
                data['job_pages'][0]['pages'][0]['jobs'][0][key] = value
                with self.assertRaisesRegex(ValueError, message):
                    M.harvest(data)

    def test_query_source_mismatch_and_foreign_tree_rejected(self):
        self.data['run_pages'][0]['workflow_runs'][0]['head_sha'] = OTHER
        with self.assertRaisesRegex(ValueError, 'source/query mismatch'):
            M.harvest(self.data)
        self.data = snapshot()
        self.data['commit_trees'][HEAD] = OTHER
        with self.assertRaisesRegex(ValueError, 'foreign head tree'):
            M.harvest(self.data)

    def test_completed_job_with_missing_conclusion_rejected(self):
        self.data['job_pages'][0]['pages'][0]['jobs'][0]['conclusion'] = None
        with self.assertRaisesRegex(ValueError, 'no conclusion'):
            M.harvest(self.data)

    def test_empty_or_demoted_required_policy_rejected(self):
        for policies in ([], [policy(required=False)]):
            data = deepcopy(self.data)
            data['job_policies'] = policies
            with self.assertRaisesRegex(ValueError, 'policy'):
                M.harvest(data)

    def test_required_child_proof_cannot_be_made_optional(self):
        self.data['run_pages'][0]['workflow_runs'][0]['path'] = M.WORKFLOW
        self.data['job_policies'][0].update(workflow=M.WORKFLOW, name='followup-formal (heat)',
                                          required=False, classification='FORMAL_VALIDITY_GATE')
        # An inherited required row ensures the attempted child demotion is the
        # problem, rather than an otherwise vacuous policy.
        self.data['job_policies'].append(policy())
        with self.assertRaisesRegex(ValueError, 'child lane demoted'):
            M.harvest(self.data)

    def test_scientific_unresolved_and_falsified_are_not_changed_by_process_success(self):
        for disposition in ('UNRESOLVED', 'COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED', 'CONTINUE'):
            with self.subTest(disposition=disposition):
                data = deepcopy(self.data)
                data['job_reviews'] = {'1:1:10': review(disposition=disposition)}
                result = M.harvest(data)
                self.assertEqual(result['execution_status'], 'PASS')
                self.assertEqual(result['effective_jobs'][0]['review']['mathematical_disposition']['gate'], disposition)
                self.assertFalse(result['theorem_promotion'])

    def test_review_source_event_and_attempt_are_bound(self):
        for key, value in [('head_sha', OTHER), ('event', 'push'), ('attempt', 2), ('run_id', 2)]:
            with self.subTest(key=key):
                data = deepcopy(self.data)
                altered = review()
                altered[key] = value
                data['job_reviews'] = {'1:1:10': altered}
                with self.assertRaisesRegex(ValueError, 'mixed-source review identity'):
                    M.harvest(data)

    def test_absent_job_review_is_not_silently_ignored(self):
        self.data['job_reviews'] = {'9:1:90': review()}
        with self.assertRaisesRegex(ValueError, 'absent job attempt'):
            M.harvest(self.data)

    def test_checked_tree_cannot_be_relabelled(self):
        self.data['checked_tree'] = OTHER
        with self.assertRaisesRegex(ValueError, 'checked source/tree mismatch'):
            M.harvest(self.data)

    def test_pending_job_without_conclusion_is_reported(self):
        current = self.data['job_pages'][0]['pages'][0]['jobs'][0]
        current['status'] = 'queued'
        del current['conclusion']
        result = M.harvest(self.data)
        self.assertEqual(result['execution_status'], 'BLOCKED')
        self.assertIsNone(result['effective_jobs'][0]['conclusion'])

    def test_stale_merge_parent_rejected(self):
        self.data.update(collected_shas=[HEAD, MERGE], commit_parents={MERGE: [OTHER, TREE]})
        self.data['commit_trees'][MERGE] = TREE
        with self.assertRaisesRegex(ValueError, 'stale synthetic merge'):
            M.harvest(self.data)

    def test_mixed_tree_artifact_review_rejected(self):
        record = review()
        record['artifacts'] = [{'checked_sha': HEAD, 'checked_tree': OTHER, 'sha256': 'f' * 64}]
        self.data['job_reviews'] = {'1:1:10': record}
        with self.assertRaisesRegex(ValueError, 'mixed-source artifacts'):
            M.harvest(self.data)

    def test_required_nonzero_command_blocks(self):
        record = review()
        record['commands'][0]['exit_code'] = 7
        self.data['job_reviews'] = {'1:1:10': record}
        self.assertIn('NONZERO_REQUIRED_COMMAND', [x['reason'] for x in M.harvest(self.data)['blockers']])

    def test_previous_fixture_compared_without_relabeling_success(self):
        self.data['job_reviews'] = {'1:1:10': review(disposition='UNRESOLVED')}
        previous = M.harvest(self.data)
        current = M.harvest(self.data, previous)
        self.assertEqual(current['effective_jobs'][0]['fixture_comparison']['status'], 'UNCHANGED')
        self.data['job_reviews']['1:1:10']['mathematical_disposition']['gate'] = 'FALSIFIED'
        current = M.harvest(self.data, previous)
        self.assertEqual(current['effective_jobs'][0]['fixture_comparison']['status'], 'CHANGED')
        self.data['job_reviews']['1:1:10']['fixture_sha256'] = 'f' * 64
        current = M.harvest(self.data, previous)
        self.assertEqual(current['effective_jobs'][0]['fixture_comparison']['status'], 'NOT_COMPARABLE')

    def test_optional_attached_failure_retained_required_attached_failure_blocks(self):
        check = {'id': 100, 'name': 'external', 'app': {'id': 1}, 'head_sha': HEAD,
                 'status': 'completed', 'conclusion': 'failure', 'started_at': '2026-10-21T00:00:00Z'}
        self.data['check_pages'] = [page('check_runs', [check])]
        self.assertEqual(M.harvest(self.data)['execution_status'], 'PASS')
        self.data['required_checks'] = [{'app_id': 1, 'name': 'external', 'head_sha': HEAD}]
        self.assertEqual(M.harvest(self.data)['execution_status'], 'BLOCKED')

    def test_newer_queued_attached_check_does_not_select_older_success(self):
        older = {'id': 100, 'name': 'external', 'app': {'id': 1}, 'head_sha': HEAD,
                 'status': 'completed', 'conclusion': 'success', 'started_at': '2026-10-21T00:00:00Z'}
        newer = {**older, 'id': 101, 'status': 'queued', 'conclusion': None, 'started_at': None}
        self.data['check_pages'] = [page('check_runs', [newer, older])]
        self.data['required_checks'] = [{'app_id': 1, 'name': 'external', 'head_sha': HEAD}]
        result = M.harvest(self.data)
        self.assertEqual(result['execution_status'], 'BLOCKED')
        self.assertEqual(result['effective_checks'][0]['id'], 101)

    def test_missing_or_duplicate_artifact_pages_rejected(self):
        self.data['artifact_pages'] = []
        with self.assertRaisesRegex(ValueError, 'missing artifact'):
            M.harvest(self.data)
        self.data = snapshot()
        self.data['artifact_pages'].append(deepcopy(self.data['artifact_pages'][0]))
        with self.assertRaisesRegex(ValueError, 'duplicate artifact'):
            M.harvest(self.data)

    def test_foreign_artifact_run_and_digest_are_rejected(self):
        artifact = {'id': 99, 'workflow_run': {'id': 1, 'head_sha': HEAD}, 'digest': 'sha256:' + 'f' * 64}
        self.data['artifact_pages'][0]['pages'] = [page('artifacts', [artifact])]
        record = review()
        record['artifacts'] = [{'id': 99, 'checked_sha': HEAD, 'checked_tree': TREE, 'sha256': 'e' * 64}]
        self.data['job_reviews'] = {'1:1:10': record}
        with self.assertRaisesRegex(ValueError, 'provider digest mismatch'):
            M.harvest(self.data)
        self.data['job_reviews']['1:1:10']['artifacts'][0]['sha256'] = 'f' * 64
        self.assertTrue(M.harvest(self.data)['effective_jobs'][0]['review']['artifacts'][0]['provider_digest_matches'])
        artifact['workflow_run']['id'] = 2
        with self.assertRaisesRegex(ValueError, 'artifact run mismatch'):
            M.harvest(self.data)


class CollectionTests(unittest.TestCase):
    def test_paginates_beyond_first_page_and_detects_drift(self):
        responses = [page('jobs', [job()]), page('jobs', [job(11)])]
        responses[0]['total_count'] = responses[1]['total_count'] = 2
        calls = []
        def fetch(url):
            calls.append(url)
            return responses[len(calls) - 1]
        pages = M.fetch_pages(fetch, 'https://api.github.com/a?filter=all', 'jobs')
        self.assertEqual(len(M.complete_pages(pages, 'jobs')), 2)
        self.assertIn('page=2', calls[1])
        responses[1]['total_count'] = 3
        calls.clear()
        with self.assertRaisesRegex(ValueError, 'total changed'):
            M.fetch_pages(fetch, 'https://api.github.com/a', 'jobs')

    def fake_api(self, change=False):
        calls, run_queries = [], [0]
        source = b'name: frozen research\njobs:\n  research:\n    run: python frozen.py\n'
        blob = hashlib.sha1(b'blob ' + str(len(source)).encode() + b'\0' + source).hexdigest()
        provider_run = run()
        provider_run['run_attempt'] = 2
        def fetch(url):
            calls.append(url)
            p = urlsplit(url)
            if '/git/commits/' in p.path:
                return {'sha': HEAD, 'tree': {'sha': TREE}, 'parents': []}
            if p.path.endswith('/actions/runs'):
                run_queries[0] += 1
                current = deepcopy(provider_run)
                if change and run_queries[0] > 1:
                    current['run_attempt'] = 3
                return page('workflow_runs', [current])
            if p.path.endswith('/check-runs'):
                self.assertEqual(parse_qs(p.query)['filter'], ['all'])
                return page('check_runs', [])
            if '/attempts/' in p.path:
                attempt = int(p.path.split('/attempts/')[1].split('/')[0])
                return page('jobs', [job(10 + attempt, attempt=attempt)])
            if p.path.endswith('/artifacts'):
                return page('artifacts', [])
            if '/contents/' in p.path:
                self.assertEqual(parse_qs(p.query)['ref'], [HEAD])
                return {'path': PATH, 'encoding': 'base64', 'content': base64.b64encode(source).decode(), 'sha': blob}
            self.fail('unexpected API URL: ' + url)
        return fetch, calls

    def test_collects_every_attempt_and_freezes_exact_workflow_source(self):
        fetch, calls = self.fake_api()
        data = M.collect(fetch, 'owner/repo', HEAD)
        self.assertEqual([x['attempt'] for x in data['job_pages']], [1, 2])
        self.assertEqual(data['workflow_sources'][0]['source_tree'], TREE)
        self.assertTrue(any('/attempts/1/jobs' in c for c in calls))
        self.assertTrue(any('/attempts/2/jobs' in c for c in calls))
        self.assertEqual(sum('/actions/runs?' in c for c in calls), 2)
        data['job_policies'] = [policy()]
        self.assertEqual(M.harvest(data)['execution_status'], 'PASS')

    def test_mid_collection_rerun_rejected(self):
        fetch, unused = self.fake_api(change=True)
        with self.assertRaisesRegex(ValueError, 'inventory changed'):
            M.collect(fetch, 'owner/repo', HEAD)

    def test_corrupted_workflow_bytes_rejected(self):
        original, unused = self.fake_api()
        def fetch(url):
            value = original(url)
            if '/contents/' in url:
                value['content'] = base64.b64encode(b'wrong source').decode()
            return value
        with self.assertRaisesRegex(ValueError, 'blob content mismatch'):
            M.collect(fetch, 'owner/repo', HEAD)

    def test_offline_source_tampering_is_rejected(self):
        fetch, unused = self.fake_api()
        data = M.collect(fetch, 'owner/repo', HEAD)
        data['job_policies'] = [policy()]
        data['workflow_sources'][0]['content'] += '# changed after snapshot\n'
        with self.assertRaisesRegex(ValueError, 'source digest mismatch'):
            M.harvest(data)

    def test_invalid_head_and_non_github_network_url_rejected(self):
        with self.assertRaisesRegex(ValueError, '40-hex'):
            M.collect(lambda url: self.fail('network unexpectedly reached'), 'owner/repo', '$HEAD')
        with self.assertRaisesRegex(ValueError, 'only GitHub'):
            M.public_github_json('https://example.com/steal')


if __name__ == '__main__':
    unittest.main()
