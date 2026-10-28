import unittest
from research.RHRC.integration.opica_composition.harvest import paginate,harvest_workflows
from research.RHRC.integration.opica_composition.canonical import ContractError

class HarvestTests(unittest.TestCase):
    def test_paginates_past_one_hundred(self):
        calls=[]
        def get(path):
            from urllib.parse import urlparse,parse_qs
            calls.append(path)
            return {'jobs':[{'id':i} for i in range(100)] if parse_qs(urlparse(path).query)['page']==['1'] else [{'id':100}]}
        self.assertEqual(len(paginate(get,'/repos/a/b/jobs','jobs')),101)
        self.assertEqual(len(calls),2)
    def fixture(self,conclusion='success',status='completed'):
        head='a'*40
        runs=[{'id':1,'head_sha':head,'path':'workflow.yml','event':e,'run_attempt':2} for e in ['pull_request']]
        jobs=[{'id':10,'name':'research','run_attempt':1,'status':status,'conclusion':conclusion}]
        def get(path):return {'workflow_runs':runs} if '/jobs' not in path else {'jobs':jobs}
        return head,get
    def test_green_falsifier_preserves_negative_result(self):
        head,get=self.fixture()
        r=harvest_workflows('a/b',head,get=get,classification={'workflow.yml':{'research':'RESEARCH-PRODUCING CHECK'}},
            scientific_records={'10':'FALSIFIED'},previous={'10':'FALSIFIED'})
        self.assertEqual(r['jobs'][0]['scientific_disposition'],'FALSIFIED')
        self.assertFalse(r['jobs'][0]['disposition_changed'])
        self.assertEqual(r['jobs'][0]['run_attempt'],1)
    def test_running_job_cannot_be_complete(self):
        head,get=self.fixture(None,'in_progress')
        r=harvest_workflows('a/b',head,get=get,classification={},scientific_records={})
        self.assertFalse(r['complete_process_accounting']);self.assertFalse(r['scientific_review_complete'])
    def test_green_wrapper_without_artifacts_needs_review(self):
        head,get=self.fixture()
        r=harvest_workflows('a/b',head,get=get,classification={'workflow.yml':{'research':'RESEARCH-PRODUCING CHECK'}},scientific_records={})
        self.assertEqual(r['jobs'][0]['scientific_disposition'],'ARTIFACT_REVIEW_REQUIRED')
    def test_invalid_head_rejected(self):
        with self.assertRaises(ContractError):harvest_workflows('a/b','head',get=lambda _:None,classification={},scientific_records={})

if __name__=='__main__':unittest.main()
