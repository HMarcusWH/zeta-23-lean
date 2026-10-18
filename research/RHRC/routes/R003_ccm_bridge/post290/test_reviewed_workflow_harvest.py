#!/usr/bin/env python3
"""Read-only synthetic adversarial workflow review tests."""
import copy,unittest
from verify_workflow_harvest import validate_jobs,reviewer_receipt,digest
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

def provenance_fixture():
    _, reviewed = fixture()
    url = "https://github.com/mock/review/23"
    reviewed.update(reviewer_identity="synthetic-workflow-reviewer", external_review_reference=url)
    pr = {"number":292,"head":{"sha":H},"user":{"login":"source-author"}}
    github = [{"id":23,"html_url":url,"state":"APPROVED","commit_id":H,
               "submitted_at":"2026-10-18T00:00:00Z",
               "user":{"login":"synthetic-workflow-reviewer","type":"User"},
               "author_association":"COLLABORATOR",
               "body":"PR292-WORKFLOW-HARVEST-SHA256="+digest(reviewed)}]
    commits = [{"author":{"login":"source-author"},"committer":None}]
    return reviewed,pr,github,commits

class ReviewedHarvestTests(unittest.TestCase):
    def test_control_only(self):self.assertTrue(validate_jobs(*fixture()))
    def test_authorized_independent_repository_associations(self):
        for association in ("OWNER", "MEMBER", "COLLABORATOR"):
            with self.subTest(association=association):
                args = provenance_fixture()
                args[2][0]["author_association"] = association
                receipt = reviewer_receipt(*args)
                self.assertEqual(receipt["integrity_status"], "PASS")
                self.assertEqual(receipt["reviewer_author_association"], association)
                self.assertEqual(receipt["reviewer_account_type"], "User")
    def test_unauthorized_or_malformed_repository_association_rejected(self):
        for association in ("NONE", "CONTRIBUTOR", "FIRST_TIMER", "FIRST_TIME_CONTRIBUTOR",
                            "BOT", "UNKNOWN", "collaborator", "COLLABORATOR ",
                            None, True, 1, [], {}):
            with self.subTest(association=association):
                args = provenance_fixture()
                args[2][0]["author_association"] = association
                with self.assertRaisesRegex(ValueError, "not repository-authorized"):
                    reviewer_receipt(*args)
        args = provenance_fixture()
        del args[2][0]["author_association"]
        with self.assertRaisesRegex(ValueError, "not repository-authorized"):
            reviewer_receipt(*args)
    def test_authorized_association_does_not_make_nonhuman_account_eligible(self):
        for account_type in ("Bot", "Mannequin", "Organization", "user", None, True, []):
            with self.subTest(account_type=account_type):
                args = provenance_fixture()
                args[2][0]["user"]["type"] = account_type
                with self.assertRaisesRegex(ValueError, "not an authenticated GitHub User"):
                    reviewer_receipt(*args)
        args = provenance_fixture()
        del args[2][0]["user"]["type"]
        with self.assertRaisesRegex(ValueError, "not an authenticated GitHub User"):
            reviewer_receipt(*args)
    def test_unauthorized_latest_review_cannot_fall_back_to_older_authorized(self):
        for changes in ({"author_association":"NONE"},
                        {"user":{"login":"synthetic-workflow-reviewer","type":"Bot"}}):
            with self.subTest(changes=changes):
                args = provenance_fixture()
                args[2].append(dict(args[2][0], id=24,
                    submitted_at="2026-10-18T01:00:00Z", **changes))
                with self.assertRaisesRegex(ValueError, "not repository-authorized|not an authenticated GitHub"):
                    reviewer_receipt(*args)
    def test_repository_owner_is_still_ineligible_as_source_author(self):
        args = provenance_fixture()
        args[0]["reviewer_identity"] = "source-author"
        args[2][0].update(author_association="OWNER", user={"login":"source-author","type":"User"})
        with self.assertRaisesRegex(ValueError, "source author self-reviewed"):
            reviewer_receipt(*args)
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
