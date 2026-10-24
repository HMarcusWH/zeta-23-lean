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


# Exact parent-intake mutations; injected reviews remain FIXTURE_ONLY.
import json, os, sys, tempfile, zipfile
from unittest.mock import patch
acceptance_REPO = Path(__file__).resolve().parents[5]
acceptance_spec = importlib.util.spec_from_file_location('opica_acceptance_intake_tests',
    Path(__file__).resolve().parents[1]/'capture_parent.py')
acceptance_intake = importlib.util.module_from_spec(acceptance_spec)
sys.modules[acceptance_spec.name] = acceptance_intake
acceptance_spec.loader.exec_module(acceptance_intake)
acceptance_legacy = sys.modules[__name__]

class AcceptanceWorkflowEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.folder=Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.fetch,_=acceptance_legacy.CollectionTests().fake_api()
        self.raw=M.collect(self.fetch,acceptance_intake.REPOSITORY,acceptance_legacy.HEAD)
        self.raw['job_policies']=[acceptance_legacy.policy()]
        self.logs={11:b'FIXTURE_ONLY first actual command log\n',12:b'FIXTURE_ONLY second actual command log\n'}
        self.raw['job_reviews']={}
        for attempt,identity in [(1,11),(2,12)]:
            data=self.logs[identity]
            (self.folder/('job-'+str(identity)+'.log')).write_bytes(data)
            review=acceptance_legacy.review(identity=identity,attempt=attempt)
            review['job_log']={'file':'job-'+str(identity)+'.log','bytes':len(data),
                'sha256':hashlib.sha256(data).hexdigest()}
            self.raw['job_reviews']['1:'+str(attempt)+':'+str(identity)]=review
        self.path=self.folder/'harvest.json'
        self.write()

    def write(self):
        report=M.harvest(self.raw)
        report['raw_collection']=self.raw
        report['review_provenance']={'author':'FIXTURE_ONLY_NONAUTHOR','not_actual_review':True}
        self.path.write_text(json.dumps(report),encoding='utf-8')

    def check(self, *, fresh=None, log_bytes=None, expected_head=None, expected_tree=None, refresh=False, previous=None):
        fetch=fresh or acceptance_legacy.CollectionTests().fake_api()[0]
        source=self.raw['workflow_sources'][0]['content'].encode()
        with patch.object(acceptance_intake,'load_evidence_tool',return_value=M),\
             patch.object(acceptance_intake,'git_bytes',return_value=source):
            return acceptance_intake.verify_workflow_evidence(acceptance_REPO,self.path,
                expected_head=expected_head or acceptance_legacy.HEAD,expected_tree=expected_tree or acceptance_legacy.TREE,
                fetch_json=fetch,fetch_bytes=log_bytes or (lambda url:self.logs[int(url.split('/')[-2])]),
                refresh_output_bytes=refresh,previous_harvest=previous)

    def test_actual_collector_replays_all_attempts_and_actual_output_bytes(self):
        result=self.check()
        self.assertTrue(result['fresh_provider_scope_verified'])
        self.assertEqual(result['all_attempt_job_count'],2)
        self.assertEqual(len(result['external_evidence']),2)
        self.assertFalse(result['independent_review_approved_by_validator'])
        self.assertEqual(result['human_review'],'NOT_ESTABLISHED')

    def test_serialized_pass_does_not_supply_missing_review(self):
        report=json.loads(self.path.read_bytes())
        report['raw_collection']['job_reviews']={}
        report['execution_status']='PASS'
        report['review_status']='RECORDED_NOT_INDEPENDENT_APPROVAL'
        self.path.write_text(json.dumps(report),encoding='utf-8')
        with self.assertRaisesRegex(ValueError,'job review is missing'):self.check()

    def test_completed_summary_in_progress_cannot_be_blessed_by_review(self):
        self.raw['job_pages'][-1]['pages'][0]['jobs'][0]['status']='in_progress'
        self.raw['job_pages'][-1]['pages'][0]['jobs'][0]['conclusion']=None
        self.raw['job_reviews'].pop('1:2:12')
        self.write()
        with self.assertRaisesRegex(ValueError,'execution is incomplete'):self.check()

    def test_latest_failed_attempt_is_not_hidden_by_old_success(self):
        self.raw['job_pages'][-1]['pages'][0]['jobs'][0]['conclusion']='failure';self.write()
        with self.assertRaisesRegex(ValueError,'execution is incomplete'):self.check()

    def test_serialized_job_disposition_must_equal_raw_review(self):
        report=json.loads(self.path.read_bytes())
        report['effective_jobs'][0]['review']['mathematical_disposition']={'RH':'PROVED'}
        self.path.write_text(json.dumps(report),encoding='utf-8')
        with self.assertRaisesRegex(ValueError,'serialized harvest differs'):self.check()

    def test_missing_old_attempt_output_is_not_silently_dropped(self):
        self.raw['job_reviews'].pop('1:1:11');self.write()
        with self.assertRaisesRegex(ValueError,'historical attempt lacks'):self.check()

    def test_external_log_hash_and_size_are_actually_checked(self):
        (self.folder/'job-12.log').write_bytes(b'forged')
        with self.assertRaisesRegex(ValueError,'log bytes differ'):self.check()

    def test_remote_job_log_must_equal_the_actual_reviewed_input(self):
        with self.assertRaisesRegex(ValueError,'actual GitHub job log differs'):
            self.check(log_bytes=lambda url:b'FORGED_DIFFERENT_PROVIDER_LOG',refresh=True)

    def test_no_log_record_cannot_be_replaced_by_commands_or_status(self):
        for review in self.raw['job_reviews'].values():review.pop('job_log')
        self.write()
        with self.assertRaisesRegex(ValueError,'explicit reviewed limitation'):self.check()

    def test_reviewed_log_cannot_escape_its_artifact_folder(self):
        for review in self.raw['job_reviews'].values():review['job_log']['file']='../elsewhere.log'
        self.write()
        with self.assertRaisesRegex(ValueError,'unsafe workflow artifact'):self.check()

    def test_fresh_rerun_is_rejected_instead_of_using_old_favorable_data(self):
        fetch,_=acceptance_legacy.CollectionTests().fake_api(change=True)
        with self.assertRaisesRegex(ValueError,'inventory changed'):self.check(fresh=fetch)

    def test_fresh_actual_job_failure_or_scope_drift_is_detected(self):
        original,_=acceptance_legacy.CollectionTests().fake_api()
        def altered(url):
            value=original(url)
            if '/attempts/2/' in url:value['jobs'][0]['conclusion']='failure'
            return value
        with self.assertRaisesRegex(ValueError,'fresh GitHub workflow scope'):self.check(fresh=altered)

    def test_foreign_checked_commit_and_same_tree_child_relaxation_are_rejected(self):
        with self.assertRaisesRegex(ValueError,'head does not match'):
            self.check(expected_head='e'*40)

    def test_actual_workflow_git_bytes_are_required(self):
        with patch.object(acceptance_intake,'load_evidence_tool',return_value=M),\
             patch.object(acceptance_intake,'git_bytes',return_value=b'wrong source'):
            with self.assertRaisesRegex(ValueError,'actual Git bytes'):
                acceptance_intake.verify_workflow_evidence(acceptance_REPO,self.path,expected_head=acceptance_legacy.HEAD,
                    expected_tree=acceptance_legacy.TREE,fetch_json=acceptance_legacy.CollectionTests().fake_api()[0],
                    fetch_bytes=lambda url:self.logs[int(url.split('/')[-2])])

    def test_file_alias_is_rejected_with_actual_linux_symlink(self):
        link=self.folder/'alias.json'
        link.symlink_to(self.path)
        with self.assertRaisesRegex(ValueError,'regular evidence'):
            acceptance_intake.regular_artifact(link)

    def test_json_duplicate_keys_and_nonfinite_values_are_not_accepted(self):
        for data in ['{"status":"PASS","status":"FAIL"}','{"seconds":NaN}']:
            with self.assertRaises(ValueError):acceptance_intake.unique_json(data)

    def test_provider_identity_does_not_confuse_review_text_with_actual_execution(self):
        other=deepcopy(self.raw);other['job_reviews']['1:2:12']['commands'][0]['exit_code']=99
        self.assertEqual(acceptance_intake.workflow_provider_identity(self.raw,M),acceptance_intake.workflow_provider_identity(other,M))
        other['job_pages'][-1]['pages'][0]['jobs'][0]['conclusion']='failure'
        self.assertNotEqual(acceptance_intake.workflow_provider_identity(self.raw,M),acceptance_intake.workflow_provider_identity(other,M))

    def test_additional_synthetic_scope_does_not_relabel_the_checked_head(self):
        original=acceptance_legacy.CollectionTests().fake_api()[0]
        from urllib.parse import parse_qs,urlsplit
        def extra(url):
            p=urlsplit(url)
            if p.path.endswith('/git/commits/'+acceptance_legacy.MERGE):
                return {'sha':acceptance_legacy.MERGE,'tree':{'sha':acceptance_legacy.TREE},
                    'parents':[{'sha':acceptance_legacy.HEAD},{'sha':acceptance_legacy.OTHER}]}
            if p.path.endswith('/actions/runs') and parse_qs(p.query)['head_sha']==[acceptance_legacy.MERGE]:
                return acceptance_legacy.page('workflow_runs',[])
            if p.path.endswith('/commits/'+acceptance_legacy.MERGE+'/check-runs'):return acceptance_legacy.page('check_runs',[])
            return original(url)
        raw=M.collect(extra,acceptance_intake.REPOSITORY,acceptance_legacy.HEAD,acceptance_legacy.MERGE)
        raw['checked_sha']=acceptance_legacy.HEAD;raw['checked_tree']=acceptance_legacy.TREE
        raw['job_policies']=self.raw['job_policies'];raw['job_reviews']=self.raw['job_reviews']
        self.raw=raw;self.write()
        self.assertEqual(self.check(fresh=extra)['source_bridge']['checked_commit'],acceptance_legacy.HEAD)

    def test_archive_is_reparsed_without_extraction_and_unsafe_paths_fail(self):
        path=self.folder/'reviewed.zip'
        with zipfile.ZipFile(path,'w') as archive:archive.writestr('science/result.json','{"RH":"OPEN"}')
        members=acceptance_intake.workflow_archive_members(path)
        self.assertEqual(members[0]['path'],'science/result.json')
        self.assertEqual(members[0]['sha256'],hashlib.sha256(b'{"RH":"OPEN"}').hexdigest())
        with zipfile.ZipFile(path,'w') as archive:archive.writestr('../unreviewed.json','forged')
        with self.assertRaisesRegex(ValueError,'unsafe workflow archive'):acceptance_intake.workflow_archive_members(path)

    def test_archive_case_alias_and_symlink_members_fail_closed(self):
        path=self.folder/'alias.zip'
        with zipfile.ZipFile(path,'w') as archive:
            archive.writestr('Result.json','{}');archive.writestr('result.json','{}')
        with self.assertRaisesRegex(ValueError,'case-aliased'):acceptance_intake.workflow_archive_members(path)
        info=zipfile.ZipInfo('link');info.create_system=3;info.external_attr=(0o120777<<16)
        with zipfile.ZipFile(path,'w') as archive:archive.writestr(info,'elsewhere')
        with self.assertRaisesRegex(ValueError,'symlink member'):acceptance_intake.workflow_archive_members(path)

    def test_real_parent_same_tree_merge_bridge_requires_actual_git_parent(self):
        source=self.raw['workflow_sources'][0]['content'].encode()
        def git(repo,*args):
            if args[0]=='rev-list':return ('e'*40+' '+'d'*40+' '+acceptance_legacy.HEAD).encode()
            if args[0]=='rev-parse':return acceptance_legacy.TREE.encode()
            if args[0]=='show':return source
            self.fail('unexpected Git operation')
        with patch.object(acceptance_intake,'load_evidence_tool',return_value=M),patch.object(acceptance_intake,'git_bytes',side_effect=git),\
             patch.object(acceptance_intake,'ACCEPTED_PARENT','e'*40),patch.object(acceptance_intake,'PINNED_HEAD',acceptance_legacy.HEAD),\
             patch.object(acceptance_intake,'PINNED_TREE',acceptance_legacy.TREE):
            result=acceptance_intake.verify_workflow_evidence(acceptance_REPO,self.path,expected_head='e'*40,expected_tree=acceptance_legacy.TREE,
                allow_parent_same_tree=True,fetch_json=acceptance_legacy.CollectionTests().fake_api()[0],
                fetch_bytes=lambda url:self.logs[int(url.split('/')[-2])])
            self.assertFalse(result['source_bridge']['merge_sha_ci_run_invented'])
            with patch.object(acceptance_intake,'git_bytes',return_value=('e'*40+' '+'d'*40+' '+'f'*40).encode()):
                with self.assertRaisesRegex(ValueError,'does not contain original'):
                    acceptance_intake.verify_workflow_evidence(acceptance_REPO,self.path,expected_head='e'*40,expected_tree=acceptance_legacy.TREE,
                        allow_parent_same_tree=True,fetch_json=acceptance_legacy.CollectionTests().fake_api()[0])

    def test_immutable_p0_reader_cannot_be_replaced_by_any_json_status(self):
        with tempfile.TemporaryDirectory() as temp:
            repo=Path(temp);relative='research/RHRC/integration/opica/build_receipt.py'
            path=repo/relative;path.parent.mkdir(parents=True);path.write_text('status="COMPILER_VERIFIED"')
            with self.assertRaisesRegex(ValueError,'immutable evidence reader changed'):
                acceptance_intake.load_evidence_tool(repo,relative,'FIXTURE_ONLY',acceptance_intake.PARENT_READER_SHA256)

    def artifact_fixture(self):
        path=self.folder/'reviewed.zip'
        with zipfile.ZipFile(path,'w') as archive:archive.writestr('science/result.json','{"RH":"OPEN"}')
        data=path.read_bytes();digest=hashlib.sha256(data).hexdigest()
        original=acceptance_legacy.CollectionTests().fake_api()[0]
        def fetch(url):
            if url.split('?')[0].endswith('/artifacts'):
                return acceptance_legacy.page('artifacts',[{'id':123,'name':'actual-fixture-science',
                    'size_in_bytes':len(data),'digest':'sha256:'+digest,'expired':False,
                    'workflow_run':{'id':1,'head_sha':acceptance_legacy.HEAD}}])
            return original(url)
        raw=M.collect(fetch,acceptance_intake.REPOSITORY,acceptance_legacy.HEAD)
        raw['job_policies']=self.raw['job_policies'];raw['job_reviews']=self.raw['job_reviews']
        raw['job_reviews']['1:2:12']['artifacts']=[{'id':123,'file':'reviewed.zip',
            'sha256':digest,'checked_sha':acceptance_legacy.HEAD,'checked_tree':acceptance_legacy.TREE}]
        self.raw=raw;self.write()
        return fetch,data

    def test_archive_is_bound_to_provider_bytes_digest_and_member_reparse(self):
        fetch,data=self.artifact_fixture()
        def output(url):
            return data if url.endswith('/zip') else self.logs[int(url.split('/')[-2])]
        result=self.check(fresh=fetch,log_bytes=output)
        archive=next(row for row in result['external_evidence'] if row['kind']=='WORKFLOW_ARCHIVE')
        self.assertEqual(archive['members'][0]['path'],'science/result.json')

    def test_remote_artifact_drift_cannot_be_blessed_by_local_review(self):
        fetch,data=self.artifact_fixture()
        def output(url):
            return b'FORGED_DIFFERENT_ARCHIVE' if url.endswith('/zip') else self.logs[int(url.split('/')[-2])]
        with self.assertRaisesRegex(ValueError,'actual GitHub artifact differs'):
            self.check(fresh=fetch,log_bytes=output,refresh=True)

    def test_artifact_provider_digest_is_not_replaced_by_review_hash(self):
        fetch,data=self.artifact_fixture()
        self.raw['job_reviews']['1:2:12']['artifacts'][0]['sha256']='f'*64
        with self.assertRaisesRegex(ValueError,'provider digest mismatch'):self.write()

    def step_only_fixture(self, *, classification='FORMAL_VALIDITY_GATE'):
        original=acceptance_legacy.CollectionTests().fake_api()[0]
        source=b'name: frozen research\njobs:\n  research:\n    runs-on: ubuntu-latest\n    steps:\n      - name: Actual compiler step\n        run: python frozen.py\n'
        import base64
        def fetch(url):
            value=original(url)
            if '/contents/' in url:
                value['content']=base64.b64encode(source).decode()
                value['sha']=hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest()
            if '/attempts/' in url:
                for job in value['jobs']:
                    job['steps']=[{'number':3,'name':'Actual compiler step',
                        'status':'completed','conclusion':'success'}]
            return value
        raw=M.collect(fetch,acceptance_intake.REPOSITORY,acceptance_legacy.HEAD)
        raw['job_policies']=[{**acceptance_legacy.policy(),'classification':classification}]
        raw['job_reviews']=self.raw['job_reviews']
        source_row=raw['workflow_sources'][0]
        for review in raw['job_reviews'].values():
            review.pop('job_log');review['classification']=classification
            review['stdout_disposition']={'available':False,'reason':'FIXTURE_ONLY actual transport failure'}
            review['commands']=[{'command':'python frozen.py','exit_code':0,
                'exit_code_provenance':'CI_STEP_CONCLUSION','provider_step_number':3,
                'provider_step_name':'Actual compiler step','workflow_sha256':source_row['sha256'],
                'source_lines':[7,7]}]
        self.raw=raw;self.write()
        return fetch

    def test_unavailable_full_stdout_can_preserve_exact_compiler_ci_disposition(self):
        fetch=self.step_only_fixture()
        result=self.check(fresh=fetch,log_bytes=lambda url:self.fail('stdout is unavailable; must not request it'))
        self.assertTrue(all(row['full_stdout_claimed'] is False for row in result['external_evidence']))
        self.assertEqual(result['external_evidence'][0]['commands'][0]['exit_code_provenance'],'CI_STEP_CONCLUSION')

    def test_step_only_success_cannot_invent_a_scientific_json_result(self):
        fetch=self.step_only_fixture(classification='RESEARCH_PRODUCING_CHECK')
        with self.assertRaisesRegex(ValueError,'missing scientific outputs'):self.check(fresh=fetch)

    def test_missing_stdout_does_not_authorize_forged_command_or_step(self):
        fetch=self.step_only_fixture()
        review=self.raw['job_reviews']['1:2:12']
        review['commands'][0]['command']='lake build invented_target';self.write()
        with self.assertRaisesRegex(ValueError,'entire run body'):self.check(fresh=fetch)
        review['commands'][0]['command']='python frozen.py'
        review['commands'][0]['provider_step_name']='Invented successful step';self.write()
        with self.assertRaisesRegex(ValueError,'actual named CI step'):self.check(fresh=fetch)

    def test_step_exit_provenance_and_exact_source_hash_are_mandatory(self):
        fetch=self.step_only_fixture()
        self.raw['job_reviews']['1:2:12']['commands'][0]['exit_code_provenance']='GUESSED_FROM_GREEN';self.write()
        with self.assertRaisesRegex(ValueError,'honest source/CI-step'):self.check(fresh=fetch)

    def test_failed_actual_step_cannot_be_replaced_by_job_status(self):
        fetch=self.step_only_fixture()
        self.raw['job_pages'][-1]['pages'][0]['jobs'][0]['steps'][0]['conclusion']='failure';self.write()
        # Fresh collection catches the mismatch before reviewing the named step.
        with self.assertRaisesRegex(ValueError,'fresh GitHub workflow scope'):self.check(fresh=fetch)

    def test_proof_command_cannot_be_paired_with_wrong_successful_checkout_step(self):
        # Nonauthor review reproduced this exact hole in the rejected 60e draft.
        source='jobs:\n  build:\n    runs-on: ubuntu-latest\n    steps:\n      - name: Checkout\n        uses: actions/checkout@fixed\n      - name: Proof never executed\n        if: false\n        run: lake build Zeta23.RequiredProof\n'
        digest=hashlib.sha256(source.encode()).hexdigest()
        job={'id':1,'name':'build','workflow':acceptance_legacy.PATH,'head_sha':acceptance_legacy.HEAD,
            'steps':[{'number':1,'name':'Checkout','status':'completed','conclusion':'success'}],
            'review':{'stdout_disposition':{'available':False,'reason':'FIXTURE_ONLY'},'commands':[
                {'command':'lake build Zeta23.RequiredProof','exit_code':0,'exit_code_provenance':'CI_STEP_CONCLUSION',
                 'provider_step_number':1,'provider_step_name':'Checkout','workflow_sha256':digest,'source_lines':[9,9]}]}}
        with self.assertRaisesRegex(ValueError,'no unique shell run body'):
            acceptance_intake.source_and_provider_command_evidence(job,[{'path':acceptance_legacy.PATH,'source_sha':acceptance_legacy.HEAD,
                'sha256':digest,'content':source}])

    def test_run_span_must_match_whole_selected_job_and_named_step(self):
        source='jobs:\n  selected:\n    steps:\n      - name: Proof\n        run: |\n          echo selected\n          lake build Actual\n  elsewhere:\n    steps:\n      - name: Proof\n        run: lake build Other\n'
        span,body=acceptance_intake.named_job_step_run_body(source,'selected','Proof')
        self.assertEqual(span,[6,7]);self.assertEqual(body,'echo selected\nlake build Actual')
        other_span,other_body=acceptance_intake.named_job_step_run_body(source,'elsewhere','Proof')
        self.assertNotEqual(span,other_span);self.assertNotEqual(body,other_body)
        with self.assertRaisesRegex(ValueError,'selected static workflow job'):
            acceptance_intake.named_job_step_run_body(source,'unknown','Proof')

    def test_authorization_is_not_forwarded_to_signed_blob_redirect(self):
        from urllib.request import HTTPRedirectHandler
        captured=[]
        class Response:
            def __enter__(self):return self
            def __exit__(self,*args):return False
            def read(self):return b'FIXTURE_ONLY'
        def opened(request,timeout):captured.append(request);return Response()
        with patch.dict(os.environ,{'GITHUB_TOKEN':'FIXTURE_ONLY_TOKEN'}),patch.object(acceptance_intake,'urlopen',side_effect=opened):
            acceptance_intake.public_github_bytes('https://api.github.com/repos/'+acceptance_intake.REPOSITORY+'/actions/artifacts/1/zip')
        origin=captured[0]
        self.assertEqual(origin.get_header('Authorization'),'Bearer FIXTURE_ONLY_TOKEN')
        redirected=HTTPRedirectHandler().redirect_request(origin,None,302,'Found',{},'https://signed-artifact.example.invalid/archive')
        self.assertFalse(any(key.lower()=='authorization' for key,value in redirected.header_items()))

    def test_official_archive_digest_and_actual_local_zip_do_not_need_duplicate_download(self):
        fetch,data=self.artifact_fixture()
        result=self.check(fresh=fetch,log_bytes=lambda url:self.fail('unnecessary duplicate blob GET'))
        archive=next(row for row in result['external_evidence'] if row['kind']=='WORKFLOW_ARCHIVE')
        self.assertFalse(archive['fresh_blob_download_compared'])
        self.assertEqual(archive['fresh_official_digest'],'sha256:'+hashlib.sha256(data).hexdigest())

    def test_previous_harvest_foreign_or_missing_repository_is_rejected(self):
        for repository in ['foreign-owner/foreign-repository', None]:
            with self.subTest(repository=repository):
                raw=deepcopy(self.raw)
                if repository is None:raw.pop('repository')
                else:raw['repository']=repository
                previous=M.harvest(raw);previous['raw_collection']=raw
                with self.assertRaisesRegex(ValueError,'foreign previous workflow repository'):
                    self.check(previous=previous)

    def test_original_previous_harvest_comparisons_are_revalidated_and_bound(self):
        prior=deepcopy(self.raw)
        for review in prior['job_reviews'].values():review['mathematical_disposition']={'gate':'OLDER_FIXTURE_ONLY_RESULT'}
        previous=M.harvest(prior);previous['raw_collection']=prior
        document=M.harvest(self.raw,previous);document['raw_collection']=self.raw
        self.path.write_text(json.dumps(document),encoding='utf-8')
        result=self.check(previous=previous)
        self.assertIsNotNone(result['previous_harvest_sha256'])
        self.assertTrue(all(job['fixture_comparison']['status']=='CHANGED' for job in document['effective_jobs']))
        with self.assertRaisesRegex(ValueError,'serialized harvest differs'):self.check()
        previous['effective_jobs'][0]['review']['mathematical_disposition']={'gate':'FORGED_OLD_SCIENCE'}
        with self.assertRaisesRegex(ValueError,'previous reviewed job/output'):
            self.check(previous=previous)




class AcceptanceIntakeCLITests(unittest.TestCase):
    def test_acceptance_without_actual_inputs_emits_rejection_not_source_acceptance(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp)/'rejection.json'
            argv=['capture_parent.py','--parent-pr','293','--expected-head',acceptance_intake.ACCEPTED_PARENT,
                '--expected-tree',acceptance_intake.PINNED_TREE,'--phase','acceptance',
                '--repo',str(acceptance_REPO),'--output',str(output)]
            with patch.object(sys,'argv',argv):self.assertEqual(acceptance_intake.main(),1)
            report=json.loads(output.read_bytes())
            self.assertEqual(report['phase'],'ACCEPTANCE_REJECTED')
            self.assertFalse(report['compiler_validated_here'])
            self.assertFalse(report['full_child_release_accepted'])

    def test_historical_tested_head_is_not_relabelled_accepted_parent(self):
        with self.assertRaisesRegex(ValueError,'accepted-parent amendment'):
            acceptance_intake.acceptance_from_evidence(acceptance_REPO,acceptance_intake.PINNED_HEAD,
                acceptance_intake.PINNED_TREE,None,None)




if __name__ == '__main__':
    unittest.main()
