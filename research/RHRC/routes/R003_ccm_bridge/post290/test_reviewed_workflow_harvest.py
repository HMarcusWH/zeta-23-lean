#!/usr/bin/env python3
"""Read-only synthetic adversarial workflow review tests."""
import copy,unittest
from verify_workflow_harvest import validate_jobs
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
    def test_review_both_attempts_without_promoting_old_failure(self):
        raw, reviewed = fixture()
        old_raw = copy.deepcopy(raw["jobs"][0])
        old_raw.update(job_id=18, attempt=1, latest_attempt=False,
                       conclusion="failure", scientific_disposition="GATE_FAILED",
                       scientific_acceptance=False)
        old_review = copy.deepcopy(reviewed["jobs"][0])
        old_review.update(job_id=18, attempt=1, latest_attempt=False,
                          conclusion="failure", scientific_disposition="GATE_FAILED",
                          scientific_acceptance=False, review_reason="Historical failed attempt honestly reviewed")
        raw["jobs"][0]["attempt"] = reviewed["jobs"][0]["attempt"] = 2
        raw["jobs"].append(old_raw)
        reviewed["jobs"].append(old_review)
        self.assertTrue(validate_jobs(raw, reviewed))
        reviewed["jobs"][1]["scientific_acceptance"] = True
        with self.assertRaises(ValueError):
            validate_jobs(raw, reviewed)

    def test_inconsistent_effective_flag_rejected(self):
        raw, reviewed = fixture()
        raw["jobs"][0]["latest_attempt"] = reviewed["jobs"][0]["latest_attempt"] = "true"
        with self.assertRaisesRegex(ValueError, "latest_attempt"):
            validate_jobs(raw, reviewed)

    def test_result_edit(self):
        raw,re=fixture();re["jobs"][0]["conclusion"]="failure"
        with self.assertRaises(ValueError):validate_jobs(raw,re)
    def test_completed_optional_failure_and_skip_are_honest_reviews(self):
        for conclusion in ("failure", "skipped"):
            with self.subTest(conclusion=conclusion):
                raw, reviewed = fixture()
                raw["jobs"][0]["conclusion"] = reviewed["jobs"][0]["conclusion"] = conclusion
                reviewed["jobs"][0]["scientific_disposition"] = "COMPLETED_WITHOUT_SCIENTIFIC_ACCEPTANCE"
                self.assertTrue(validate_jobs(raw, reviewed))
    def test_optional_effective_job_must_have_a_terminal_result(self):
        for status, conclusion in (("queued", None), ("in_progress", None),
                                   ("completed", None), ("completed", " ")):
            with self.subTest(status=status, conclusion=conclusion):
                raw, reviewed = fixture()
                for packet in (raw, reviewed):
                    packet["jobs"][0].update(status=status, conclusion=conclusion)
                reviewed["jobs"][0]["scientific_disposition"] = "INTERIM_RESULT_UNRESOLVED"
                with self.assertRaisesRegex(ValueError, "terminal result"):
                    validate_jobs(raw, reviewed)
    def test_superseded_interim_status_remains_historical(self):
        raw, reviewed = fixture()
        for packet in (raw, reviewed):
            old = copy.deepcopy(packet["jobs"][0])
            old.update(job_id=18, latest_attempt=False, status="in_progress", conclusion=None)
            packet["jobs"][0]["attempt"] = 2
            packet["jobs"].append(old)
        reviewed["jobs"][1].update(scientific_disposition="SUPERSEDED_INTERIM_RESULT_REVIEWED",
                                   review_reason="Synthetic archived observation; newer attempt completed.")
        self.assertTrue(validate_jobs(raw, reviewed))
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
if __name__=="__main__":unittest.main()
