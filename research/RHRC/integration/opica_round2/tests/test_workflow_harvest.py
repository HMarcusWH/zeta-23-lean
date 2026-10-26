"""Provider protocol fixtures preserve pending, skipped and unverified outcomes."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(HERE))
import harvest_workflows as harvest
import certificate_io as io

HEAD="1"*40
TREE="2"*40
WORKFLOW=".github/workflows/example.yml"


def fixtures():
    run={"id":11,"run_attempt":1,"head_sha":HEAD,"status":"completed","event":"push",
         "path":WORKFLOW,"html_url":"https://github.com/example/repo/actions/runs/11"}
    job={"id":21,"run_id":11,"head_sha":HEAD,"name":"formal","status":"completed","conclusion":"success",
         "html_url":"https://github.com/example/repo/actions/runs/11/job/21"}
    snapshot={"schema":"OPICA2_PROVIDER_ACTIONS_SNAPSHOT_V1","head":HEAD,
              "observed_at_utc":"2026-10-25T22:00:00+00:00","run_pages":[{"total_count":1,"workflow_runs":[run]}],
              "job_collections":[{"run_id":11,"attempt":1,"pages":[{"total_count":1,"jobs":[job]}]}]}
    rules={"jobs":[{"workflow_path":WORKFLOW,"name":"formal","classification":"FORMAL_VALIDITY_GATE",
                    "on_success":"Compiler job completed; exact theorem authority requires raw compiler receipt",
                    "on_failure":"No successful compiler evidence","evidence_scope":"Exact named compiler job"}]}
    return snapshot,rules


class WorkflowEvidenceTests(unittest.TestCase):
    def test_success_is_provider_execution_not_theorem_or_final_self_snapshot(self):
        snapshot,rules=fixtures()
        result=harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules)
        self.assertTrue(result["all_pages_read"])
        self.assertFalse(result["is_final_post_run_snapshot"])
        self.assertIn("PROVIDER_SUCCESS_ONLY",result["jobs"][0]["scientific_disposition"])
        self.assertEqual(result["RH"],"OPEN")
        final=harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules,snapshot_mode="post-run")
        self.assertTrue(final["is_final_post_run_snapshot"])
        with self.assertRaises(ValueError):harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules,
                                                         snapshot_mode="post-run",current_run_id=11)

    def test_pending_and_uninstantiated_required_job_not_pass(self):
        snapshot,rules=fixtures()
        job=snapshot["job_collections"][0]["pages"][0]["jobs"][0]
        job.update(status="in_progress",conclusion=None)
        snapshot["run_pages"][0]["workflow_runs"][0]["status"]="in_progress"
        rules["jobs"].append({**rules["jobs"][0],"name":"aggregate"})
        required=[{"workflow_path":WORKFLOW,"name":"aggregate"}]
        result=harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules,required_jobs=required)
        self.assertEqual([r["execution"] for r in result["jobs"]],["in_progress","NOT_YET_INSTANTIATED"])
        with self.assertRaises(ValueError):harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules,
                                                         required_jobs=required,snapshot_mode="post-run")

    def test_skipped_failure_and_changed_prior_dispositions(self):
        snapshot,rules=fixtures()
        prior=harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules)
        job=snapshot["job_collections"][0]["pages"][0]["jobs"][0]
        job["conclusion"]="failure"
        changed=harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules,previous=prior)
        self.assertIn("CHANGED_EXECUTION",changed["jobs"][0]["comparison"])
        job["conclusion"]="skipped"
        skipped=harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules)
        self.assertIn("no execution evidence",skipped["jobs"][0]["scientific_disposition"])

    def test_pagination_duplicate_unstable_missing_and_ambiguous_ids_fail(self):
        valid=[{"total_count":2,"jobs":[{"id":1}]},{"total_count":2,"jobs":[{"id":2}]}]
        self.assertEqual(len(harvest.complete_pages(valid,"jobs")),2)
        for bad in (valid[:1],[valid[0],{**valid[1],"total_count":3}],
                    [valid[0],{"total_count":2,"jobs":[{"id":1}]}],
                    [{"total_count":1,"jobs":[{"id":True}]}]):
            with self.subTest(bad=bad),self.assertRaises(ValueError):harvest.complete_pages(bad,"jobs")
        calls=[]
        def fetch(url):calls.append(url);return valid[len(calls)-1]
        pages=harvest.fetch_pages(fetch,"https://api.github.com/example?head_sha="+HEAD,"jobs")
        self.assertEqual(len(pages),2)
        self.assertIn("page=2",calls[1])

    def test_wrong_source_missing_classification_and_forged_artifacts_fail(self):
        snapshot,rules=fixtures()
        bad=deepcopy(snapshot);bad["run_pages"][0]["workflow_runs"][0]["head_sha"]="0"*40
        with self.assertRaises(ValueError):harvest.harvest(bad,head=HEAD,tree=TREE,classifications=rules)
        with self.assertRaises(ValueError):harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications={"jobs":[]})
        proof={"21":{"head":HEAD,"run_id":11,"attempt":1,"artifact_hashes":["3"*64],
                     "scientific_disposition":"Forged theorem disposition"}}
        with self.assertRaises(ValueError):harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules,
                                                         artifact_evidence=proof)

    def test_missing_workflow_and_unknown_execution_fail_closed(self):
        snapshot,rules=fixtures()
        with self.assertRaises(ValueError):harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules,
            required_jobs=[{"workflow_path":".github/workflows/absent.yml","name":"required"}])
        snapshot["job_collections"][0]["pages"][0]["jobs"][0]["status"]="mysterious_success"
        with self.assertRaises(ValueError):harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules)

    def test_all_rerun_attempts_are_required_and_remain_distinct(self):
        snapshot,rules=fixtures()
        snapshot["run_pages"][0]["workflow_runs"][0]["run_attempt"]=2
        with self.assertRaises(ValueError):harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules)
        second=deepcopy(snapshot["job_collections"][0]);second["attempt"]=2
        second["pages"][0]["jobs"][0]["id"]=22
        snapshot["job_collections"].append(second)
        result=harvest.harvest(snapshot,head=HEAD,tree=TREE,classifications=rules,snapshot_mode="post-run")
        self.assertEqual([j["attempt"] for j in result["jobs"]],[1,2])


if __name__=="__main__":unittest.main()
