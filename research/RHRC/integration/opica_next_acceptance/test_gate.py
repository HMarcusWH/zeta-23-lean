"""Negative controls for new-source OPICA proof admission in both Python modes."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from research.RHRC.integration.opica_next_acceptance import gate as s

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
            if ref=="HEAD":
                out=dict(out)
                p="Zeta23/OPICARound6/NextSearch/SourceEnergies.lean"
                out[p]=(out[p][0],out[p][1],"0"*40)
            return out
        with patch.object(s.round6,"tree",side_effect=edit_lean):
            with self.assertRaises(s.ScopeError):
                s.check()
        def unreviewed(repo,ref):
            out=native(repo,ref)
            if ref=="HEAD":
                out=dict(out);out["NEW_PROOF.lean"]=("100644","blob","0"*40)
            return out
        with patch.object(s.round6,"tree",side_effect=unreviewed):
            with self.assertRaises(s.ScopeError):
                s.check()
        p=next(iter(sorted(s.FROZEN)))
        def rewrite_history(repo,ref):
            out=native(repo,ref)
            if ref=="HEAD":
                out=dict(out);out[p]=(out[p][0],out[p][1],"0"*40)
            return out
        with patch.object(s.round6,"tree",side_effect=rewrite_history):
            with self.assertRaises(s.ScopeError):
                s.check()

    def test_historical_source_validator_fails_closed(self):
        # Earlier frozen source epoch is NOT enlarged retroactively.
        with self.assertRaises(Exception):
            s.historical.inspect_committed_tree(s.REPO)

if __name__=="__main__":
    unittest.main()
