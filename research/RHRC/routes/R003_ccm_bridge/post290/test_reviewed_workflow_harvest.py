#!/usr/bin/env python3
"""Read-only synthetic adversarial workflow review tests."""
import copy,unittest
from verify_workflow_harvest import validate_jobs,reviewer_receipt,digest
from derive_acceptance_manifest import harvest_complete
H="a"*40
def fixture():
    j={"run_id":11,"workflow":"mock workflow","job_id":19,"name":"example",
       "attempt":1,"latest_attempt":True,"status":"completed","conclusion":"success",
       "head":H,"head_tree":"b"*40,"evidence_scope":"EXACT_PROOF_HEAD",
       "required":False,"url":"https://github.com/mock/jobs/19","steps":[],
       "classification":"REGRESSION_GATE","output_reviewed":False,
       "scientific_disposition":"READ_JOB_OUTPUT_REQUIRED","scientific_acceptance":False}
    raw={"head":H,"claim_cap":"RH_OPEN","review_phase":"PRE_RELEASE_PREREQUISITES",
         "includes_release_run":False,"excluded_administrative_runs":[],"jobs":[j]}
    reviewed=copy.deepcopy(raw);reviewed["jobs"][0].update(
        output_reviewed=True,scientific_disposition="REPLAY_PRESERVED",
        review_reason="Synthetic human-reviewed fixture only",review_source_url=j["url"])
    return raw,reviewed
class ReviewedHarvestTests(unittest.TestCase):
    def test_control_only(self):self.assertTrue(validate_jobs(*fixture()))
    def test_result_edit(self):
        raw,re=fixture();re["jobs"][0]["conclusion"]="failure"
        with self.assertRaises(ValueError):validate_jobs(raw,re)
    def test_missing_review(self):
        raw,re=fixture();re["jobs"][0]["output_reviewed"]=False
        with self.assertRaises(ValueError):validate_jobs(raw,re)
    def test_missing_job(self):
        raw,re=fixture();re["jobs"]=[]
        with self.assertRaises(ValueError):validate_jobs(raw,re)
    def test_false_success_after_failure(self):
        raw,re=fixture()
        raw["jobs"][0]["conclusion"]=re["jobs"][0]["conclusion"]="failure"
        re["jobs"][0]["scientific_acceptance"]=True
        with self.assertRaises(ValueError):validate_jobs(raw,re)
    def test_false_success_after_skip(self):
        raw,re=fixture()
        raw["jobs"][0]["conclusion"]=re["jobs"][0]["conclusion"]="skipped"
        re["jobs"][0]["scientific_acceptance"]=True
        with self.assertRaises(ValueError):validate_jobs(raw,re)
    def test_false_success_while_running(self):
        raw,re=fixture()
        raw["jobs"][0]["status"]=re["jobs"][0]["status"]="in_progress"
        raw["jobs"][0]["conclusion"]=re["jobs"][0]["conclusion"]=None
        re["jobs"][0]["scientific_acceptance"]=True
        with self.assertRaises(ValueError):validate_jobs(raw,re)
    def test_self_reference(self):
        raw,re=fixture();re["includes_release_run"]=True
        with self.assertRaises(ValueError):validate_jobs(raw,re)
def receipt_fixture():
    _,re=fixture();url="https://github.com/HMarcusWH/zeta-23-lean/pull/292#pullrequestreview-7"
    re.update(reviewer_identity="independent_review_test",external_review_reference=url)
    pr={"number":292,"head":{"sha":H},"user":{"login":"source_author"}}
    reviews=[{"id":7,"html_url":url,"state":"APPROVED","commit_id":H,
              "submitted_at":"2026-10-15T12:00:00Z","user":{"login":"independent_review_test"},
              "body":"PR292-WORKFLOW-HARVEST-SHA256="+digest(re)}]
    return re,pr,reviews,[{"author":{"login":"source_author"}}]
class HarvestReviewerTests(unittest.TestCase):
    def test_signed_approval_control(self):
        self.assertEqual(reviewer_receipt(*receipt_fixture())["integrity_status"],"PASS")
    def test_later_changes_requested_revokes(self):
        re,pr,reviews,commits=receipt_fixture()
        reviews.append({"id":8,"html_url":"https://example.invalid/8","state":"CHANGES_REQUESTED",
            "commit_id":H,"submitted_at":"2026-10-15T13:00:00Z",
            "user":{"login":"independent_review_test"},"body":"Retracted"})
        with self.assertRaises(ValueError):reviewer_receipt(re,pr,reviews,commits)
def completed_harvest():
    _,re=fixture();job=re["jobs"][0]
    job.update(required=True,scientific_acceptance=True)
    return re
class HarvestCompletionTests(unittest.TestCase):
    def test_latest_success_completes(self):
        self.assertTrue(harvest_complete(completed_harvest(),H))
    def test_superseded_failure_does_not_block(self):
        re=completed_harvest();old=copy.deepcopy(re["jobs"][0])
        old.update(attempt=1,latest_attempt=False,conclusion="failure",scientific_acceptance=False)
        re["jobs"][0].update(attempt=2);re["jobs"].insert(0,old)
        self.assertTrue(harvest_complete(re,H))
    def test_latest_failure_blocks(self):
        re=completed_harvest();re["jobs"][0].update(conclusion="failure",scientific_acceptance=False)
        self.assertFalse(harvest_complete(re,H))
    def test_unreviewed_superseded_attempt_blocks(self):
        re=completed_harvest();old=copy.deepcopy(re["jobs"][0])
        old.update(attempt=1,latest_attempt=False,output_reviewed=False)
        re["jobs"].insert(0,old)
        self.assertFalse(harvest_complete(re,H))
if __name__=="__main__":unittest.main()
