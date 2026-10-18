#!/usr/bin/env python3
"""Synthetically exercise prerequisite/post-release harvest phase separation."""
import copy
import unittest
from harvest_workflows import harvest,RELEASE_WORKFLOW,ADMIN_EVIDENCE_WORKFLOWS

H="a"*40
def job(name="lean-components",state="completed",conclusion="success"):
    return {"id":7,"name":name,"status":state,"conclusion":conclusion,
            "html_url":"https://github.com/example/job/7","steps":[]}
def run(name="RHRC post290 source and output proof components",j=None):
    return {"id":11,"name":name,"head_sha":H,"run_attempt":1,
            "attempt_inventory":[{"attempt":1,"jobs":[j or job()]}],
            "head_commit":{"tree_id":"b"*40}}
def snap(phase="PRE_RELEASE_PREREQUISITES"):
    return {"head":H,"review_phase":phase,"external_d2_run_id":None,
            "excluded_administrative_runs":[],
            "runs":[run()]}
class WorkflowHarvestPhases(unittest.TestCase):
    def test_raw_success_never_auto_promoted(self):
        record=harvest(snap())["jobs"][0]
        self.assertFalse(record["scientific_acceptance"])
        self.assertFalse(record["output_reviewed"])
        self.assertEqual(record["classification"],"FORMAL_VALIDITY_GATE")
    def test_failed_required_job_cannot_be_success(self):
        s=snap();s["runs"]=[run(j=job(conclusion="failure"))]
        record=harvest(s)["jobs"][0]
        self.assertEqual(record["scientific_disposition"],"GATE_FAILED")
        self.assertFalse(record["scientific_acceptance"])
    def test_skipped_job_keeps_failure_of_evidence(self):
        s=snap();s["runs"]=[run(j=job(state="completed",conclusion="skipped"))]
        self.assertEqual(harvest(s)["jobs"][0]["scientific_disposition"],"NOT_EXECUTED")
    def test_prerelease_excludes_release_job(self):
        s=snap();s["runs"].append(run(name=RELEASE_WORKFLOW))
        with self.assertRaisesRegex(ValueError,"administrative"):
            harvest(s)
    def test_explicit_admin_exclusion_is_recorded(self):
        s=snap()
        s["excluded_administrative_runs"]=[{
            "run_id":99,"workflow":RELEASE_WORKFLOW,
            "status":"in_progress","conclusion":None,"head":H,
            "exclusion_reason":"ADMINISTRATIVE_INTAKE_NOT_PREREQUISITE"}]
        res=harvest(s)
        self.assertEqual(len(res["excluded_administrative_runs"]),1)
        self.assertFalse(res["includes_release_run"])
    def test_postrelease_must_not_hide_any_job(self):
        s=snap("POST_RELEASE_EVERY_JOB")
        s["excluded_administrative_runs"]=[{"workflow":RELEASE_WORKFLOW,
            "exclusion_reason":"ADMINISTRATIVE_INTAKE_NOT_PREREQUISITE"}]
        with self.assertRaisesRegex(ValueError,"cannot exclude"):
            harvest(s,"POST_RELEASE_EVERY_JOB")
    def test_postrelease_includes_release_job(self):
        s=snap("POST_RELEASE_EVERY_JOB")
        s["runs"].append(run(name=RELEASE_WORKFLOW))
        self.assertTrue(harvest(s,"POST_RELEASE_EVERY_JOB")["includes_release_run"])
    def test_manifest_requires_all_effective_mandatory_jobs(self):
        from derive_acceptance_manifest import reviewed_prerequisite_harvest_complete
        from output_contract_check import FORMAL_JOB, REGRESSION_JOB, NATIVE_JOB, ACTIVE_D2_JOB
        duties = (FORMAL_JOB, REGRESSION_JOB, NATIVE_JOB, ACTIVE_D2_JOB)
        jobs = [
            dict(run_id=i + 40, job_id=i + 70, attempt=1, latest_attempt=True,
                 workflow=w, name=n, required=True, status="completed",
                 conclusion="success", scientific_acceptance=True,
                 output_reviewed=True, classification="RESEARCH_PRODUCING_CHECK")
            for i,(w,n) in enumerate(duties)
        ]
        packet = dict(head=H, claim_cap="RH_OPEN", jobs=jobs,
                      review_phase="PRE_RELEASE_PREREQUISITES",
                      includes_release_run=False)
        self.assertTrue(reviewed_prerequisite_harvest_complete(packet, H))
        # Partial rerun: the successful unrerun formal job stays effective.
        old = dict(jobs[1], attempt=1, latest_attempt=False, conclusion="failure",
                   scientific_acceptance=False, job_id=97)
        jobs[1]["attempt"] = 2
        packet["jobs"].append(old)
        self.assertTrue(reviewed_prerequisite_harvest_complete(packet, H))
        self.assertEqual(old["conclusion"], "failure")
        # A missing mandatory job, even when three others pass, is incomplete.
        without_formal = dict(packet, jobs=[j for j in packet["jobs"]
                                           if (j["workflow"],j["name"]) != FORMAL_JOB])
        self.assertFalse(reviewed_prerequisite_harvest_complete(without_formal, H))
        # A different run ID must not erase a required failed job.
        failed_other_run = dict(jobs[1], run_id=999, job_id=999,
                                conclusion="failure", scientific_acceptance=False)
        packet["jobs"].append(failed_other_run)
        self.assertFalse(reviewed_prerequisite_harvest_complete(packet, H))

    def test_manifest_rejects_missing_or_forged_attempt_flags(self):
        from derive_acceptance_manifest import reviewed_prerequisite_harvest_complete
        from output_contract_check import FORMAL_JOB, REGRESSION_JOB, NATIVE_JOB, ACTIVE_D2_JOB
        jobs = [
            dict(run_id=i+20, job_id=i+30, attempt=1, latest_attempt=True,
                 workflow=w, name=n, required=True, status="completed",
                 conclusion="success", scientific_acceptance=True,
                 output_reviewed=True, classification="FORMAL_VALIDITY_GATE")
            for i,(w,n) in enumerate((FORMAL_JOB, REGRESSION_JOB, NATIVE_JOB, ACTIVE_D2_JOB))
        ]
        packet = dict(head=H, claim_cap="RH_OPEN", jobs=jobs,
                      review_phase="PRE_RELEASE_PREREQUISITES", includes_release_run=False)
        self.assertTrue(reviewed_prerequisite_harvest_complete(packet, H))
        jobs[0].pop("latest_attempt")
        self.assertFalse(reviewed_prerequisite_harvest_complete(packet, H))
        jobs[0]["latest_attempt"] = "true"
        self.assertFalse(reviewed_prerequisite_harvest_complete(packet, H))

    def test_phase_forgery_rejected(self):
        s=snap()
        with self.assertRaisesRegex(ValueError,"phase"):
            harvest(s,"POST_RELEASE_EVERY_JOB")
if __name__=="__main__":
    unittest.main()
