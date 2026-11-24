"""Negative controls for new-source OPICA proof admission in both Python modes."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from research.RHRC.integration.opica_next_acceptance import gate as s
from research.RHRC.integration.opica_composition.canonical import ContractError

class SourceProofAdmissionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.policy=json.loads((s.REPO/s.POLICY).read_text())

    def test_exact_new_source_admission_is_not_a_proof(self):
        r=s.check(require_clean=True)
        self.assertEqual(r["status"],"PASS_SOURCE_SCOPE_ONLY")
        self.assertEqual(r["schema"],"OPICA_NEXT_SOURCE_ACCEPTANCE_ADMISSION_V1")
        self.assertEqual(r["base"],s.BASE)
        self.assertEqual(r["canonical_product_count"],77)
        self.assertEqual(r["unchanged_historical_product_count"],4)
        self.assertEqual(r["new_source_11_lane_status"],
                         "PENDING_ACTUAL_PRODUCER_AND_INDEPENDENT_REPLAY")
        self.assertFalse(r["proof_acceptance"])
        self.assertEqual((r["RH"],r["C1"],r["Step4"]),("OPEN",)*3)
        self.assertEqual(r["delta"]["added"],sorted(s.ADDED))
        self.assertEqual(r["delta"]["edited"],sorted(s.EDITED))
        self.assertEqual(s.validate_descendant()["checked_commit"],r["checked_commit"])

    def test_source_11_lane_adapter_only(self):
        c=(s.REPO/"research/RHRC/integration/opica_composition/cli.py").read_text()
        self.assertIn("from ..opica_next_acceptance.gate import validate_descendant",c)
        self.assertIn("OPICA_NEXT_SOURCE_ACCEPTANCE_ADMISSION_V1",c)
        old=(s.REPO/"research/RHRC/integration/documentation_2026_11_21/source_scope.py")
        self.assertEqual(s.git(s.REPO,"rev-parse",s.BASE+":research/RHRC/integration/documentation_2026_11_21/source_scope.py"),
                         s.git(s.REPO,"rev-parse","HEAD:research/RHRC/integration/documentation_2026_11_21/source_scope.py"))
        self.assertTrue(old.is_file())
        self.assertEqual(s.check_classification()["status"],"PASS_NEW_SOURCE_CLASSIFICATION_ONLY")

    def test_adversarial_policy_claims_and_path_migration(self):
        source=self.policy
        active=s.expected_generated(s.REPO)
        s.validate_policy(source,active)
        for key,value in [
            ("parent_source_head","0"*40),
            ("parent_source_tree","0"*40),
            ("toolchain","leanprover/lean4:v4.36.0"),
            ("proof_acceptance",True),
            ("scientific_claims",{"RH":"PROVED","C1":"OPEN","Step4":"OPEN"}),
            ("allowed_added",source["allowed_added"]+["UNREVIEWED.lean"]),
            ("allowed_edited",[]),
            ("allowed_generated",active+["Zeta23/Unreviewed.lean"]),
            ("unchanged_frozen_products",[]),
            ("original_round4_acceptance","ACCEPTED"),
            ("new_11_lane_acceptance","PASS"),
            ("parent_accepted_by","ASSUMED"),
        ]:
            with self.subTest(mutated=key):
                altered=copy.deepcopy(source);altered[key]=value
                with self.assertRaises(s.ScopeError):
                    s.validate_policy(altered,active)

    def test_adversarial_worktree_ancestry_and_source_blob(self):
        original=s.git
        def change_parent(repo,*args):
            if args==("rev-parse",s.BASE+"^{tree}"): return "0"*40
            return original(repo,*args)
        with patch.object(s,"git",side_effect=change_parent):
            with self.assertRaises(s.ScopeError):
                s.check()
        native=s.round6.tree
        def edit_lean(repo,ref):
            out=native(repo,ref)
            if ref!=s.BASE:
                out=dict(out)
                p="Zeta23/OPICARound6/NextSearch/SourceEnergies.lean"
                out[p]=(out[p][0],out[p][1],"0"*40)
            return out
        with patch.object(s.round6,"tree",side_effect=edit_lean):
            with self.assertRaises(s.ScopeError):
                s.check()
        def unreviewed(repo,ref):
            out=native(repo,ref)
            if ref!=s.BASE:
                out=dict(out);out["NEW_PROOF.lean"]=("100644","blob","0"*40)
            return out
        with patch.object(s.round6,"tree",side_effect=unreviewed):
            with self.assertRaises(s.ScopeError):
                s.check()
        p=next(iter(sorted(s.FROZEN)))
        def rewrite_history(repo,ref):
            out=native(repo,ref)
            if ref!=s.BASE:
                out=dict(out);out[p]=(out[p][0],out[p][1],"0"*40)
            return out
        with patch.object(s.round6,"tree",side_effect=rewrite_history):
            with self.assertRaises(s.ScopeError):
                s.check()

    def test_original_eleven_lanes_and_independent_partition_unchanged(self):
        from research.RHRC.integration.opica_composition.accept import (
            ROUND4_LANES, REPLAY_GROUP_IDS, group_lanes, verify_gate_inventory)
        self.assertEqual(len(ROUND4_LANES),11)
        self.assertEqual(REPLAY_GROUP_IDS,("CORE","AUXILIARY","CANONICAL"))
        self.assertEqual(tuple(verify_gate_inventory(ROUND4_LANES)),ROUND4_LANES)
        joined=tuple(name for group in REPLAY_GROUP_IDS for name in group_lanes(group))
        self.assertEqual(len(joined),len(set(joined)))
        self.assertEqual(set(joined),set(ROUND4_LANES))
        self.assertIn("MATHEMATICAL_SUPPORT",joined)
        self.assertIn("SOURCE_NUMERICS",joined)
        self.assertIn("GENERATED_STATE",joined)
        with self.assertRaises(ContractError):
            verify_gate_inventory(ROUND4_LANES[:-1])

    def test_service_freeze_calls_new_source_admission(self):
        from types import SimpleNamespace
        from research.RHRC.integration.opica_composition import service
        # Exercise the actual freeze entry point through its admission boundary.
        # No mocked worker may be described as a production compiler pass.
        with patch.object(service,"worker_capability",return_value=None):
            with patch.object(s,"validate_descendant",side_effect=s.ScopeError("FREEZE_ROUTING_SENTINEL")) as called:
                with self.assertRaisesRegex(s.ScopeError,"FREEZE_ROUTING_SENTINEL"):
                    service.freeze(s.REPO,{},Path("/nonexistent-opica-test-output"),
                                   worker=SimpleNamespace(production=True))
                called.assert_called_once_with(s.REPO,require_clean=True)

    def test_registered_signed_targets_require_explicit_frozen_experiment(self):
        from types import SimpleNamespace
        from research.RHRC.integration.opica_composition import service
        from research.RHRC.integration.opica_next_acceptance import targets
        from research.RHRC.integration.opica_composition.snapshot import file_hash
        r=targets.registry(s.REPO)
        self.assertEqual(len(r["targets"]),3)
        self.assertEqual(len(r["source_theorems"]),2)
        self.assertEqual(len(r["scalar_pending_compiler_type_review"]),2)
        self.assertFalse(r["proof_acceptance"])
        digest=file_hash(s.REPO/targets.REGISTRY)
        chosen=SimpleNamespace(repo=str(s.REPO),source_policy="REVIEWED_FROZEN",
                               environment={targets.SELECTION:digest},
                               files={targets.REGISTRY:digest},generation="0"*64)
        for item in r["targets"]:
            target,table=service._target(s.REPO,chosen,item["id"])
            self.assertEqual(target.expected_type_hash,item["expected_type_sha256"])
            self.assertEqual(set(target.allowed_constants.values()),set(targets.THEOREM_NAMES))
            self.assertEqual(len(table),2)
        missing=SimpleNamespace(repo=str(s.REPO),environment={},files={})
        with self.assertRaises(ContractError):
            service._target(s.REPO,missing,targets.TARGET_IDS[0])
        chosen.files={}
        with self.assertRaises(ContractError):
            targets.selected(chosen)

    def test_dual_type_review_registration_is_authenticated(self):
        from types import SimpleNamespace
        from research.RHRC.integration.opica_next_acceptance import targets as t
        from research.RHRC.integration.opica_composition.canonical import ContractError
        from copy import deepcopy
        h,tr,rid,attempt="a"*40,"b"*40,"123",1
        rec={"schema":"OPICA_NEXT_DUAL_COMPILER_TYPES_V1","status":"PASS_TYPES_ONLY",
             "head":h,"tree":tr,"run_id":rid,"attempt":attempt,"role":"reviewer",
             "expected_types_checked":True,"target_values":[
                 {"declaration":n,"expected_type_sha256":"a"*64} for n in t.SCALAR_NAMES],
             "support_types":[{"declaration":n,"module":m,"type_sha256":"b"*64,"axioms":["propext"]}
                              for n,m in t.EXTRA_SUPPORT],"compiler_log_sha256":"c"*64,
             "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
        kw=dict(head=h,tree=tr,run_id=rid,attempt=attempt,role="reviewer")
        t._validate_type_receipt(rec,**kw)
        for key,value in (("head","d"*40),("expected_types_checked",False),("RH","PROVED"),("support_types",[])):
            bad=deepcopy(rec);bad[key]=value
            with self.assertRaises(ContractError): t._validate_type_receipt(bad,**kw)
        s1=SimpleNamespace(repo=str(s.REPO),commit=h,tree=tr,environment={})
        self.assertEqual(len(t.reviewed_registry(s1)["targets"]),3)
        auth={"run_id":rid,"head":h,"tree":tr,"target_values":rec["target_values"],
              "support_types":rec["support_types"]}
        s1.environment[t.TYPE_REVIEW]=auth
        with patch.object(t,"authenticate_type_review",return_value=auth):
            ext=t.reviewed_registry(s1)
            self.assertEqual(len(ext["targets"]),5)
            self.assertEqual(len(ext["source_theorems"]),6)
            self.assertEqual(len(ext["targets"][0]["approved_constants"]),5)
            self.assertEqual(len(ext["targets"][-1]["approved_constants"]),1)
            s1.environment[t.TYPE_REVIEW]={**auth,"tree":"e"*40}
            with self.assertRaises(ContractError): t.reviewed_registry(s1)

    def test_reviewed_allowed_file_content_is_sealed(self):
        native=s.round6.tree
        def changed_allowed(repo,ref):
            out=native(repo,ref)
            if ref!=s.BASE:
                out=dict(out)
                p="research/RHRC/integration/opica_composition/service.py"
                out[p]=(out[p][0],out[p][1],"0"*40)
            return out
        with patch.object(s.round6,"tree",side_effect=changed_allowed):
            with self.assertRaisesRegex(s.ScopeError,"reviewed source blob"):
                s.check()

    def test_bounded_attempt_menu_is_distinct_and_failure_is_not_acceptance(self):
        from types import SimpleNamespace
        from research.RHRC.integration.opica_next_acceptance.targets import run_bounded_menu
        menu={"proposals":{"a":{},"b":{}},"candidates":{"complete":True,"disposition":"ENUMERATED"}}
        calls=[]
        def dispatch(i,credits):
            calls.append((i,credits))
            if credits==0:
                return {"kind":"STOP"}
            return {"choice":{"action_id":("a","b")[i]},"status":"TYPE_REJECTED_THIS_APPLICATION"}
        outcome=run_bounded_menu(menu,dispatch,lambda *_:self.fail("rejected attempt was verified"))
        self.assertEqual(calls,[(0,1),(1,1),(2,0)])
        self.assertEqual(outcome["attempted_action_ids"],["a","b"])
        self.assertEqual(outcome["status"],"NO_KERNEL_ACCEPTED_APPLICATION_IN_ENUMERATED_MENU")
        bad=run_bounded_menu(menu,lambda *_:{"choice":{"action_id":"a"},"status":"RESOURCE_EXHAUSTED"},lambda *_:None)
        self.assertEqual(bad["status"],"INCOMPLETE_EXECUTION")
        self.assertEqual(bad["independent_verified_conditional_applications"],0)
        forged=run_bounded_menu(menu,lambda *_:{"choice":{"action_id":"a"},"status":"PROVED_CONDITIONAL"},
                                lambda *_:SimpleNamespace(status="PROVED_CONDITIONAL",publication_eligible=False))
        self.assertEqual(forged["status"],"INCOMPLETE_EXECUTION")
        self.assertEqual(forged["independent_verified_conditional_applications"],0)
        with self.assertRaises(ContractError):
            run_bounded_menu(menu,lambda *_:{"choice":{"action_id":"a"},"status":"TYPE_REJECTED_THIS_APPLICATION"},lambda *_:None)


    def test_qualification_rejects_missing_stale_and_incomplete(self):
        from research.RHRC.integration.opica_next_acceptance import targets as t
        from research.RHRC.integration.opica_composition.accept import ROUND4_LANES, REPLAY_GROUP_IDS, group_lanes
        from types import SimpleNamespace
        from copy import deepcopy
        head, tree, profile, run = "a"*40, "b"*40, "c"*64, "123"
        exp = {"run_id":run,"attempt":1,"requested_commit":head,"requested_tree":tree,"profile_digest":profile}
        receipt = {"schema":"OPICA4_INTEGRATED_ACCEPTANCE_V1","status":"PASS_DECLARED_INTEGRATED_SCOPE",
                   "experiment":exp,"RH":"OPEN","Step4":"OPEN",
                   "independently_reconstructed_lanes":[{"id":l,"evidence_digest":"d"*64} for l in ROUND4_LANES],
                   "independent_groups":[{"group_id":g,"conclusion":"success","lanes":list(group_lanes(g)),
                                          "evidence_digest":"e"*64} for g in REPLAY_GROUP_IDS]}
        kw = dict(head=head,tree=tree,run_id=run,attempt=1,profile=profile)
        t._verify_round4_receipt(receipt,**kw)
        for mutation in ("lane","group","head","claim","status"):
            bad=deepcopy(receipt)
            if mutation=="lane": bad["independently_reconstructed_lanes"].pop()
            if mutation=="group": bad["independent_groups"][0]["conclusion"]="failure"
            if mutation=="head": bad["experiment"]["requested_commit"]="0"*40
            if mutation=="claim": bad["RH"]="PROVED"
            if mutation=="status": bad["status"]="INCOMPLETE"
            with self.assertRaises(ContractError): t._verify_round4_receipt(bad,**kw)
        with patch.object(t,"selected",return_value=True):
            with self.assertRaises(ContractError):
                t.enforce_qualification(SimpleNamespace(environment={}))
        with self.assertRaises(ContractError): t._run_id("123/../../artifacts")

    def test_qualification_authenticates_exact_actions_attempt(self):
        from research.RHRC.integration.opica_next_acceptance import targets as t
        from copy import deepcopy
        run={"id":123,"head_sha":"a"*40,"path":".github/workflows/test.yml",
             "repository":{"full_name":t.RUN_REPOSITORY},"head_repository":{"full_name":t.RUN_REPOSITORY},
             "event":"push","status":"completed","conclusion":"success","run_attempt":2}
        jobs={"total_count":1,"jobs":[{"name":"source","status":"completed","conclusion":"success",
                                     "run_id":123,"run_attempt":2}]}
        kw=dict(run_id="123",head="a"*40,workflow=".github/workflows/test.yml",required_jobs=("source",))
        self.assertEqual(t._verify_run(run,jobs,**kw),2)
        for mutate in ("missing","wrong_attempt","failure","duplicate"):
            bad=deepcopy(jobs)
            if mutate=="missing": bad["total_count"]=2
            if mutate=="wrong_attempt": bad["jobs"][0]["run_attempt"]=1
            if mutate=="failure": bad["jobs"][0]["conclusion"]="failure"
            if mutate=="duplicate": bad["jobs"]*=2;bad["total_count"]=2
            with self.assertRaises(ContractError): t._verify_run(run,bad,**kw)

    def test_historical_workflows_select_stacked_successor(self):
        root=s.REPO
        for name,count in (("rhrc_opica.yml",4),("rhrc_opica_followup.yml",7),
                           ("rhrc_opica_round2.yml",8),("rhrc_opica_round3.yml",5),
                           ("rhrc.yml",1)):
            body=(root/".github/workflows"/name).read_text()
            self.assertIn("research/opica-next-source-epoch-v1-20261123",body)
            self.assertEqual(body.count("python -B -m research.RHRC.integration.opica_next_acceptance.gate --output"),count)
            self.assertEqual(body.count("python -B -m research.RHRC.integration.opica_composition.cli inspect --repo . --output"),count)
            self.assertEqual(body.count("# R4_PARENT_SCOPE_V1"),count)
        for name in ("documentation.yml","rhrc_opica_round6.yml"):
            self.assertIn("research/opica-next-source-epoch-v1-20261123",
                          (root/".github/workflows"/name).read_text())

    def test_historical_source_validator_fails_closed(self):
        # Earlier frozen source epoch is NOT enlarged retroactively.
        with self.assertRaises(ContractError):
            s.historical.inspect_committed_tree(s.REPO)

    def test_end_to_end_replay_uses_exact_epoch_admission(self):
        from types import SimpleNamespace
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import cli
        from research.RHRC.integration.opica_composition.canonical import ContractError
        from research.RHRC.integration.opica_composition.tests.test_end_to_end import _validate_replay_source
        self.assertIs(cli.validate_descendant, s.validate_descendant)
        report = s.check(require_clean=True)
        snapshot = SimpleNamespace(repo=str(s.REPO), commit=report["checked_commit"],
                                   tree=report["checked_tree"])
        actual = _validate_replay_source(snapshot)
        self.assertEqual(actual["schema"], "OPICA_NEXT_SOURCE_ACCEPTANCE_ADMISSION_V1")
        self.assertEqual(actual, report)
        self.assertFalse(actual["proof_acceptance"])
        for field in ("commit", "tree"):
            bad = SimpleNamespace(**vars(snapshot))
            setattr(bad, field, "0" * 40)
            with self.assertRaisesRegex(ContractError, "differs from exact snapshot"):
                _validate_replay_source(bad)
        with patch.object(cli, "validate_descendant",
                          side_effect=ContractError("REPLAY_ADMISSION_REJECTED")) as called:
            with self.assertRaisesRegex(ContractError, "REPLAY_ADMISSION_REJECTED"):
                _validate_replay_source(snapshot)
            called.assert_called_once_with(Path(snapshot.repo), require_clean=True)
        # The frozen earlier source gate still rejects this newer tree.
        with self.assertRaises(ContractError):
            s.historical.inspect_committed_tree(s.REPO)

if __name__=="__main__":
    unittest.main()
