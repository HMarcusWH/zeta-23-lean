from __future__ import annotations
import copy
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('opica_harvest',HERE/'harvest_workflows.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class WorkflowMutations(unittest.TestCase):
    def setUp(self):
        head,tree = 'a'*40,'b'*40
        self.names = ['opica-contract','opica-formal','opica-regression','opica-dependency-delta','opica-component-summary']
        run = {'id':1,'path':'.github/workflows/rhrc_opica.yml','run_attempt':1,'run_number':1,
            'head_sha':head,'event':'pull_request','status':'completed','conclusion':'success'}
        jobs = [{'id':10+i,'run_id':1,'run_attempt':1,'name':name,'status':'completed','conclusion':'success'}
            for i,name in enumerate(self.names)]
        checks = [{'id':100+i,'head_sha':head,'name':name,'app':{'id':1},'status':'completed',
            'conclusion':'success','started_at':'2026-10-21T00:00:00Z'} for i,name in enumerate(self.names)]
        self.data = {'head_sha':head,'head_tree':tree,'checked_sha':head,'checked_tree':tree,
            'commit_trees':{head:tree},'run_pages':[{'total_count':1,'workflow_runs':[run]}],
            'check_pages':[{'total_count':5,'check_runs':checks}],
            'job_pages':[{'run_id':1,'attempt':1,'pages':[{'total_count':5,'jobs':jobs}]}],
            'expected_jobs':[{'workflow':run['path'],'name':name} for name in self.names]}

    def test_complete_success(self):
        result = module.harvest(self.data)
        self.assertEqual(result['status'],'PASS')
        self.assertFalse(result['independent_review_approved'])
        self.assertTrue(all(j['event']=='pull_request' and j['head_sha']==self.data['head_sha']
            for j in result['effective_jobs']+result['all_job_attempts']))

    def test_push_jobs_cannot_satisfy_required_pr_event(self):
        self.data['run_pages'][0]['workflow_runs'][0]['event'] = 'push'
        for job in self.data['expected_jobs']:
            job['event'] = 'pull_request'
        with self.assertRaisesRegex(ValueError,'required workflow/job absent'):
            module.harvest(self.data)

    def test_merge_jobs_cannot_satisfy_required_head_scope(self):
        merge = 'c'*40
        self.data.update(checked_sha=merge,checked_parents=[self.data['head_sha']])
        self.data['commit_trees'][merge] = self.data['checked_tree']
        self.data['run_pages'][0]['workflow_runs'][0]['head_sha'] = merge
        for job in self.data['expected_jobs']:
            job['head_sha'] = self.data['head_sha']
        with self.assertRaisesRegex(ValueError,'required workflow/job absent'):
            module.harvest(self.data)

    def test_explicit_event_and_head_selectors_accept_exact_scope(self):
        for job in self.data['expected_jobs']:
            job.update(event='pull_request',head_sha=self.data['head_sha'])
        self.assertEqual(module.harvest(self.data)['status'],'PASS')

    def test_job_event_cannot_disagree_with_its_run(self):
        self.data['job_pages'][0]['pages'][0]['jobs'][0]['event'] = 'push'
        with self.assertRaisesRegex(ValueError,'job event mismatch'):
            module.harvest(self.data)

    def test_running_required_job(self):
        self.data['job_pages'][0]['pages'][0]['jobs'][0]['status'] = 'in_progress'
        with self.assertRaisesRegex(ValueError,'running'): module.harvest(self.data)

    def test_skipped_new_job(self):
        self.data['job_pages'][0]['pages'][0]['jobs'][0]['conclusion'] = 'skipped'
        self.data['reviewed_skips'] = {'1:1:10':'reviewed'}
        with self.assertRaisesRegex(ValueError,'OPICA job skipped'): module.harvest(self.data)

    def test_cancelled_run(self):
        self.data['run_pages'][0]['workflow_runs'][0]['conclusion'] = 'cancelled'
        with self.assertRaisesRegex(ValueError,'cancelled'): module.harvest(self.data)

    def test_partial_rerun_retains_failed_history(self):
        run = self.data['run_pages'][0]['workflow_runs'][0]
        run['run_attempt'] = 2
        original = self.data['job_pages'][0]['pages'][0]['jobs'][0]
        original['conclusion'] = 'failure'
        replacement = {**original,'id':20,'run_attempt':2,'conclusion':'success'}
        self.data['job_pages'].append({'run_id':1,'attempt':2,'pages':[{'total_count':1,'jobs':[replacement]}]})
        result = module.harvest(self.data)
        self.assertEqual(len(result['all_job_attempts']),6)
        self.assertTrue(any(j['conclusion']=='failure' for j in result['all_job_attempts']))
        self.assertTrue(any(j['id']==20 and j['attempt']==2 for j in result['effective_jobs']))

    def test_latest_failed_rerun_does_not_choose_old_success(self):
        run = self.data['run_pages'][0]['workflow_runs'][0]
        run['run_attempt'] = 2
        replacement = {**self.data['job_pages'][0]['pages'][0]['jobs'][0],
            'id':20,'run_attempt':2,'conclusion':'failure'}
        self.data['job_pages'].append({'run_id':1,'attempt':2,'pages':[{'total_count':1,'jobs':[replacement]}]})
        with self.assertRaisesRegex(ValueError,'unsuccessful'): module.harvest(self.data)

    def test_missing_attempt(self):
        self.data['run_pages'][0]['workflow_runs'][0]['run_attempt'] = 2
        with self.assertRaisesRegex(ValueError,'historical attempt'): module.harvest(self.data)

    def test_incomplete_pagination(self):
        self.data['run_pages'][0]['total_count'] = 2
        with self.assertRaisesRegex(ValueError,'incomplete'): module.harvest(self.data)

    def test_duplicate_run_identity(self):
        page = self.data['run_pages'][0]
        page['workflow_runs'].append(copy.deepcopy(page['workflow_runs'][0]))
        page['total_count'] = 2
        with self.assertRaisesRegex(ValueError,'duplicate provider'): module.harvest(self.data)

    def test_foreign_head(self):
        self.data['run_pages'][0]['workflow_runs'][0]['head_sha'] = 'c'*40
        with self.assertRaisesRegex(ValueError,'foreign'): module.harvest(self.data)

    def test_foreign_tree(self):
        self.data['checked_tree'] = 'd'*40
        with self.assertRaisesRegex(ValueError,'foreign checked tree'): module.harvest(self.data)

    def test_stale_synthetic_merge(self):
        self.data['checked_sha'] = 'c'*40
        self.data['commit_trees']['c'*40] = self.data['checked_tree']
        self.data['checked_parents'] = ['e'*40,'f'*40]
        with self.assertRaisesRegex(ValueError,'stale synthetic merge'): module.harvest(self.data)

    def test_failed_attached_check(self):
        self.data['check_pages'][0]['check_runs'][0]['conclusion'] = 'failure'
        with self.assertRaisesRegex(ValueError,'not green'): module.harvest(self.data)

    def test_self_consistent_foreign_harvest_rejected_at_cli_boundary(self):
        self.assertEqual(module.harvest(self.data)['status'],'PASS')
        with patch.object(module.subprocess,'check_output',return_value='c'*40):
            with self.assertRaisesRegex(ValueError,'foreign requested head'):
                module.validate_source_identity(HERE,self.data,'HEAD')

    def test_provider_tree_map_cannot_override_real_git_tree(self):
        with patch.object(module.subprocess,'check_output',side_effect=['a'*40,'c'*40]):
            with self.assertRaisesRegex(ValueError,'actual Git source'):
                module.validate_source_identity(HERE,self.data,'HEAD')

    def test_real_synthetic_merge_parents_required(self):
        merge = 'c'*40
        self.data.update(checked_sha=merge,checked_parents=['a'*40,'d'*40])
        self.data['commit_trees'][merge] = self.data['checked_tree']
        self.assertEqual(module.harvest(self.data)['status'],'PASS')
        git_results = ['a'*40,'b'*40,'b'*40,merge+' '+'e'*40+' '+'d'*40]
        with patch.object(module.subprocess,'check_output',side_effect=git_results):
            with self.assertRaisesRegex(ValueError,'parent claims differ'):
                module.validate_source_identity(HERE,self.data,'HEAD')

    def test_current_checkout_and_merge_git_objects_accept(self):
        merge = 'c'*40
        self.data.update(checked_sha=merge,checked_parents=['d'*40,'a'*40])
        self.data['commit_trees'][merge] = self.data['checked_tree']
        git_results = ['a'*40,'b'*40,'b'*40,merge+' '+'d'*40+' '+'a'*40]
        with patch.object(module.subprocess,'check_output',side_effect=git_results):
            self.assertEqual(module.validate_source_identity(HERE,self.data,'HEAD'),'a'*40)

    def test_normal_one_parent_commit_cannot_be_a_synthetic_merge(self):
        merge = 'c'*40
        self.data.update(checked_sha=merge,checked_parents=['a'*40])
        self.data['commit_trees'][merge] = self.data['checked_tree']
        git_results = ['a'*40,'b'*40,'b'*40,merge+' '+'a'*40]
        with patch.object(module.subprocess,'check_output',side_effect=git_results):
            with self.assertRaisesRegex(ValueError,'exactly two actual parents'):
                module.validate_source_identity(HERE,self.data,'HEAD')


if __name__ == '__main__':
    unittest.main()
