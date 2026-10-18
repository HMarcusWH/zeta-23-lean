"""Synthetic native artifact-origin controls, never observations or approval."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import derive_acceptance_manifest as manifest_builder
import materialize_step123_outputs as materializer
from output_contract_check import (native_input_binding, validate_native_input_binding,
                                   release_gaps, NATIVE_JOB)
from test_output_mutations import (fixture, SYNTHETIC_PANEL_BYTES, SYNTHETIC_CHECKER_BYTES,
                                  SYNTHETIC_NATIVE_INPUTS, synthetic_verify_d2,
                                  D2_RUN_ID)
from verify_workflow_harvest import validate_jobs, digest


class NativeInputBindingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="native-input-synthetic-")
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.panel = self.directory / "SYNTHETIC_PANEL_NOT_OBSERVATIONS.json"
        self.checker = self.directory / "SYNTHETIC_CHECKER_NOT_CERTIFICATE.json"
        self.panel.write_bytes(SYNTHETIC_PANEL_BYTES)
        self.checker.write_bytes(SYNTHETIC_CHECKER_BYTES)
        self.args = fixture()
        self.binding = native_input_binding(self.panel, self.checker, 103)

    def release(self, args=None, binding=None):
        values = self.args if args is None else args
        with (patch("output_contract_check.exact_numeric_source",
                    return_value={"integrity_status":"PASS","d2_run_id":D2_RUN_ID}),
              patch("output_contract_check.verify_d2_receipt", side_effect=synthetic_verify_d2)):
            return release_gaps(*values, native_inputs=self.binding if binding is None else binding)

    def test_actual_file_hashes_and_selected_run_match_synthetic_signed_review(self):
        self.assertEqual(self.binding, SYNTHETIC_NATIVE_INPUTS)
        self.assertEqual(validate_native_input_binding(self.binding,self.args[3],"a"*40),self.binding)
        self.assertEqual(self.release(), [])

    def test_changed_panel_or_checker_bytes_cannot_reuse_review(self):
        for key,path in (("panel_sha256",self.panel),("checker_sha256",self.checker)):
            with self.subTest(key=key):
                original=path.read_bytes()
                # Even semantically identical JSON with another newline has a
                # different original byte identity and needs its own review.
                path.write_bytes(original+b"\n")
                altered=native_input_binding(self.panel,self.checker,103)
                self.assertNotEqual(altered[key],self.binding[key])
                self.assertTrue(any("bytes differ" in gap for gap in self.release(binding=altered)))
                path.write_bytes(original)

    def test_selected_run_substitution_rejected_even_when_hashes_and_source_match(self):
        altered=native_input_binding(self.panel,self.checker,900103)
        self.assertTrue(any("effective configured native job" in gap for gap in self.release(binding=altered)))

    def test_missing_actual_binding_or_forged_manifest_binding_blocks_full_release(self):
        with (patch("output_contract_check.exact_numeric_source",
                    return_value={"integrity_status":"PASS","d2_run_id":D2_RUN_ID}),
              patch("output_contract_check.verify_d2_receipt",side_effect=synthetic_verify_d2)):
            self.assertTrue(any("native input provenance not bound" in gap
                                for gap in release_gaps(*self.args)))
        for replacement in (None, [], {"native":dict(self.binding,checker_sha256="0"*64)}):
            with self.subTest(replacement=replacement):
                altered=deepcopy(self.args)
                altered[0]["input_bindings"]=replacement
                self.assertTrue(any("manifest native input binding" in gap for gap in self.release(altered)))

    def test_malformed_run_or_digest_metadata_rejected(self):
        for run in (None,True,False,0,-1,"103",103.0):
            with self.subTest(run=run),self.assertRaises(ValueError):
                native_input_binding(self.panel,self.checker,run)
        for value in (None,True,103,[],{},"g"*64,"A"*64,"f"*63):
            for key in ("panel_sha256","checker_sha256"):
                with self.subTest(key=key,value=value):
                    jobs=deepcopy(self.args[3]); jobs[-1]["native_output_review"][key]=value
                    with self.assertRaises(ValueError):
                        validate_native_input_binding(self.binding,jobs,"a"*40)
        for key in ("panel_sha256","checker_sha256"):
            jobs=deepcopy(self.args[3]); del jobs[-1]["native_output_review"][key]
            with self.assertRaises(ValueError):validate_native_input_binding(self.binding,jobs,"a"*40)

    def test_multiple_native_runs_preserved_but_selected_run_is_unique(self):
        jobs=deepcopy(self.args[3])
        other=deepcopy(jobs[-1]); other.update(run_id=104,job_id=204)
        jobs.append(other)
        self.assertEqual(validate_native_input_binding(self.binding,jobs,"a"*40),self.binding)
        self.assertEqual(self.release(args=self.args[:3]+[jobs]),[])
        duplicate=deepcopy(jobs[-2]); duplicate["job_id"]=999
        jobs.append(duplicate)
        with self.assertRaises(ValueError):validate_native_input_binding(self.binding,jobs,"a"*40)

    def test_superseded_native_attempt_cannot_supply_selected_hashes(self):
        jobs=deepcopy(self.args[3])
        old=deepcopy(jobs[-1]); old.update(latest_attempt=False)
        jobs[-1].update(attempt=2,job_id=999)
        jobs[-1]["native_output_review"]["panel_sha256"]="1"*64
        jobs.append(old)
        with self.assertRaisesRegex(ValueError,"bytes differ"):
            validate_native_input_binding(self.binding,jobs,"a"*40)

    def test_wrong_job_source_or_unaccepted_review_cannot_match(self):
        for changes in ({"name":"another-job"},{"required":False},{"output_reviewed":False},
                        {"scientific_acceptance":False},{"conclusion":"failure"},
                        {"runner_checked_head":"d"*40}):
            with self.subTest(changes=changes):
                jobs=deepcopy(self.args[3]); jobs[-1].update(changes)
                with self.assertRaises(ValueError):
                    validate_native_input_binding(self.binding,jobs,"a"*40)

    def test_reviewed_synthetic_merge_identity_is_preserved(self):
        jobs=deepcopy(self.args[3]); job=jobs[-1]
        branch,merge,base,tree="c"*40,"e"*40,"f"*40,"a"*40
        job.update(runner_checked_head=merge)
        review=job["checkout_identity_review"]
        review.update(runner_checked_head=merge,checkout_kind="PR_SYNTHETIC_MERGE",reviewed_pr_base_head=base,
                      runner_git_commit={"sha":merge,"tree":{"sha":tree},"parents":[{"sha":base},{"sha":branch}]})
        job["native_output_review"]["head"]=merge
        binding=dict(self.binding,source_head=merge)
        self.assertEqual(validate_native_input_binding(binding,jobs,tree),binding)
        job["checkout_identity_review"]["runner_git_commit"]["parents"]=[{"sha":base},{"sha":"d"*40}]
        with self.assertRaises(ValueError):validate_native_input_binding(binding,jobs,tree)

    def test_native_job_review_requires_hashes_and_signature_digest_covers_them(self):
        job=deepcopy(self.args[3][-1])
        url="https://github.com/synthetic/jobs/203"
        job.update(url=url,steps=[],review_source_url=url,review_reason="Synthetic source-bound file review only",
                   scientific_disposition="SYNTHETIC_REPLAY_CONTROL")
        reviewed={"head":"c"*40,"claim_cap":"RH_OPEN","review_phase":"PRE_RELEASE_PREREQUISITES",
                  "includes_release_run":False,"excluded_administrative_runs":[],"jobs":[job]}
        raw=deepcopy(reviewed)
        self.assertTrue(validate_jobs(raw,reviewed))
        signed=digest(reviewed)
        for key in ("panel_sha256","checker_sha256"):
            changed=deepcopy(reviewed); changed["jobs"][0]["native_output_review"][key]="2"*64
            self.assertNotEqual(digest(changed),signed)
            del changed["jobs"][0]["native_output_review"][key]
            with self.assertRaisesRegex(ValueError,"byte hashes"):
                validate_jobs(raw,changed)

    def test_materialized_binding_and_manifest_preserve_original_hashes(self):
        directory=self.directory/"SYNTHETIC_PRODUCTS_NOT_RELEASE"; directory.mkdir()
        for name in manifest_builder.EXPECTED_PRODUCTS:
            if name!="MATERIALIZATION_RECEIPT.json":
                (directory/name).write_bytes(b'{"synthetic_product_only":true}')
        receipt={"head":"c"*40,"tree":"a"*40,"producer_complete":True,
                 "input_bindings":{"native":deepcopy(self.binding)},
                 "outputs":{name:hashlib.sha256((directory/name).read_bytes()).hexdigest()
                            for name in manifest_builder.EXPECTED_PRODUCTS if name!="MATERIALIZATION_RECEIPT.json"}}
        path=directory/"MATERIALIZATION_RECEIPT.json"
        path.write_text(json.dumps(receipt),encoding="utf-8")
        self.assertTrue(manifest_builder.verified_outputs(directory,"c"*40,"a"*40,self.args[3]))
        with (patch.object(manifest_builder,"get_commit",return_value=("c"*40,"a"*40)),
              patch.object(manifest_builder,"validate_receipt",return_value=False),
              patch.object(manifest_builder,"exact_numeric_source",return_value={"integrity_status":"PASS"}),
              patch.object(manifest_builder,"verify_d2_receipt",return_value=None)):
            result=manifest_builder.derive(self.args[1],{},self.args[2],{"jobs":self.args[3]},directory,{})
        self.assertEqual(result["input_bindings"]["native"],self.binding)
        self.assertEqual(result["status"],"PARTIAL_OUTPUT_RH_OPEN")
        receipt["input_bindings"]["native"]["run_id"]=999
        path.write_text(json.dumps(receipt),encoding="utf-8")
        self.assertFalse(manifest_builder.verified_outputs(directory,"c"*40,"a"*40,self.args[3]))

    def test_unsigned_partial_materializer_records_actual_bytes_without_approval(self):
        from test_symbolic_step123_artifacts import test_actual_materializer,IDENTITY
        test_actual_materializer(self.directory)
        original=json.loads((self.directory/"synthetic-bundle/MATERIALIZATION_RECEIPT.json").read_text(encoding="utf-8"))
        self.assertIsNone(original["input_bindings"]["native"])
        keys=("formal","lineage","panel","checker","comparison","survival","d2","harvest","cuts")
        inputs={key:self.directory/(key+".json") for key in keys}
        out=self.directory/"SYNTHETIC_UNSIGNED_PARTIAL"
        with patch.object(materializer,"git",side_effect=lambda *args:
                          IDENTITY["tree"] if args[-1]=="HEAD^{tree}" else IDENTITY["head"]):
            receipt_path=materializer.materialize(inputs,out,native_run_id=103)
            # A caller asking for provenance promotion must bind inputs to an
            # accepted signed job review; this fixture has no such approval.
            with self.assertRaises(ValueError):
                materializer.materialize(inputs,self.directory/"REJECT_UNBOUND_PROMOTION",
                                         reviewer_provenance=self.directory/"ABSENT_APPROVAL.json")
        receipt=json.loads(receipt_path.read_text(encoding="utf-8"))
        expected=native_input_binding(inputs["panel"],inputs["checker"],103)
        self.assertEqual(receipt["input_bindings"]["native"],expected)
        self.assertEqual(receipt["verified_fields"],0)
        self.assertIs(receipt["producer_complete"],False)
        self.assertFalse((out/"REVIEW_PROVENANCE_VERIFIED.json").exists())

    def test_semantic_context_provenance_is_required_beyond_legacy_field_digest(self):
        from test_mandatory_mutation_matrix import semantic_fixture
        from verify_semantic_review_provenance import validate,field_digest
        review,pr,github,commits,head,tree,roots,_=semantic_fixture()
        provenance=validate(review,pr,github,commits,head,tree)
        self.assertTrue(manifest_builder.accepted_review(review,head,tree,roots,provenance))
        self.assertFalse(manifest_builder.accepted_review(review,head,tree,roots))
        changed=deepcopy(review)
        changed["synthetic_extra_scope"]=True
        self.assertEqual(field_digest(changed["field_reviews"]),field_digest(review["field_reviews"]))
        self.assertFalse(manifest_builder.accepted_review(changed,head,tree,roots,provenance))
        for changes in ({"semantic_review_sha256":None},{"reviewer":"another-reviewer"},
                        {"github_review_url":"https://github.com/synthetic/another-review"}):
            with self.subTest(changes=changes):
                forged=dict(provenance,**changes)
                self.assertFalse(manifest_builder.accepted_review(review,head,tree,roots,forged))
        path=self.directory/"SYNTHETIC_PROVENANCE_NOT_APPROVAL.json"
        path.write_text(json.dumps(provenance),encoding="utf-8")
        with patch.object(materializer,"git",side_effect=lambda *args:
                          tree if args[-1]=="HEAD^{tree}" else head):
            with self.assertRaisesRegex(ValueError,"exact signed semantic context"):
                materializer.materialize({},self.directory/"REJECT_CHANGED_CONTEXT",changed,path)
        self.assertFalse((self.directory/"REJECT_CHANGED_CONTEXT").exists())


if __name__=="__main__":
    unittest.main()
