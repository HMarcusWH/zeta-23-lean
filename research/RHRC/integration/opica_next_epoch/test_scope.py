"""Successor source-policy regression and optimized-Python negative controls."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch
import scope as epoch

class JointEpochScopeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.policy=json.loads((Path(__file__).resolve().parent/"SOURCE_EPOCH.json").read_text())

    def test_exact_reviewed_source_epoch(self):
        result=epoch.check()
        self.assertEqual(result["status"],"PASS_REVIEWED_COMBINED_EPOCH_V1")
        self.assertEqual(result["reviewed_added_paths"],23)
        self.assertEqual(result["reviewed_modified_paths"],2)
        self.assertEqual(result["original_sources"],18)
        self.assertEqual(result["RH"],"OPEN")
        self.assertEqual(result["C1"],"OPEN")
        self.assertEqual(result["Step4"],"OPEN")
        self.assertFalse(result["proof_acceptance"])
        self.assertEqual(set(result["source_lean_blobs"]),{
            "Zeta23/OPICARound6/NextSearch/SourceEnergies.lean",
            "Zeta23/OPICARound6/NextSearch/Verify.lean",
            "Zeta23/OPICARound6/PrimeDeficit/Source.lean",
            "Zeta23/OPICARound6/PrimeDeficit/Verify.lean",
        })

    def test_frozen_legacy_source_not_modified(self):
        for name in epoch.FROZEN:
            self.assertEqual(epoch.git("rev-parse","HEAD:"+name),
                             epoch.git("rev-parse",epoch.BASE+":"+name))
        self.assertEqual((epoch.REPO/"lean-toolchain").read_text().strip(),epoch.LEAN_PIN)

    def test_policy_mutations_fail_closed(self):
        c=self.policy
        epoch.contract(c)
        mutations=[
           ("claims",{"RH":"PROVED","C1":"OPEN","Step4":"OPEN"}),
           ("proof_acceptance",True),
           ("native_base","0"*40),
           ("native_base_tree","0"*40),
           ("toolchain","leanprover/lean4:v4.36.0"),
           ("source_development_heads",{"PR307":"0"*40,"PR308":epoch.ORIGINAL_SOURCE_HEADS["PR308"]}),
           ("historical_round4_11_lane_acceptance","SUCCESS"),
           ("new_source_round4_11_lane_acceptance","SUCCESS"),
           ("frozen_historical_source_policies","MUTATED"),
           ("allowed_added_paths",c["allowed_added_paths"]+["UNREVIEWED.py"]),
           ("allowed_edited_paths",[]),
           ("reviewed_integration_overrides",c["reviewed_integration_overrides"]+["Zeta23/OPICARound6/PrimeDeficit/Source.lean"]),
           ("required_standalone_module_roles",{}),
           ("source_pr_original_blob_oids",{**c["source_pr_original_blob_oids"],
                 "Zeta23/OPICARound6/PrimeDeficit/Source.lean":"0"*40}),
        ]
        for field,value in mutations:
            with self.subTest(field=field):
                altered=copy.deepcopy(c)
                altered[field]=value
                with self.assertRaises(epoch.ScopeError):
                    epoch.contract(altered)

    def test_git_tree_mutations_fail_closed(self):
        original=epoch.git
        def unreviewed_path(*args):
            if args==("diff","--name-status",epoch.BASE,"HEAD"):
                return original(*args)+"\nA\tUNREVIEWED_SOURCE.lean"
            return original(*args)
        with patch.object(epoch,"git",side_effect=unreviewed_path):
            with self.assertRaises(epoch.ScopeError):
                epoch.check()
        def changed_math_blob(*args):
            if args==("rev-parse","HEAD:Zeta23/OPICARound6/PrimeDeficit/Source.lean"):
                return "0"*40
            return original(*args)
        with patch.object(epoch,"git",side_effect=changed_math_blob):
            with self.assertRaises(epoch.ScopeError):
                epoch.check()
        def changed_legacy(*args):
            if args==("rev-parse","HEAD:research/RHRC/integration/opica_composition/PUBLIC_TARGETS.json"):
                return "0"*40
            return original(*args)
        with patch.object(epoch,"git",side_effect=changed_legacy):
            with self.assertRaises(epoch.ScopeError):
                epoch.check()

    def test_original_source_guards_still_refuse_unreviewed_extension(self):
        # The current epoch has a new gate; historical scopes are never
        # automatically made to accept it by widening their frozen manifests.
        from research.RHRC.integration.documentation_2026_11_21 import source_scope as old
        with self.assertRaises(Exception):
            old.inspect_committed_tree(epoch.REPO)

if __name__=="__main__":
    unittest.main()
