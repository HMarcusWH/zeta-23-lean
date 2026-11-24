"""Exact scope and mutation tests; do not imply mathematical acceptance."""
import copy
import json
import unittest
from pathlib import Path
from research.RHRC.integration.opica_dispatch_registration import gate as g

class RegistrationTests(unittest.TestCase):
    def test_exact_source_boundary(self):
        result=g.check()
        self.assertEqual(result["schema"],"OPICA_DISPATCH_REGISTRATION_INSPECTION_V1")
        self.assertFalse(result["proof_acceptance"])
        self.assertEqual((result["RH"],result["C1"],result["Step4"]),("OPEN",)*3)
        self.assertEqual(result["canonical_product_count"],77)
        self.assertEqual(result["unchanged_historical_product_count"],4)
        self.assertEqual(g.check_classification()["status"],"PASS_REGISTRATION_CLASSIFICATION_ONLY")

    def test_mutated_tree_fails_closed(self):
        parent=g.round6.tree(g.REPO,g.BASE)
        current=g.round6.tree(g.REPO,"HEAD")
        policy=json.loads((g.REPO/g.POLICY).read_text())
        manifest=json.loads((g.REPO/"research/RHRC/integration/opica_round4/BUILD_MANIFEST.json").read_text())
        active={r["path"] for r in manifest["generated"]}-g.FROZEN
        vid=current[g.VALIDATOR][2]
        g.validate_delta(parent,current,policy,active,vid)
        for key in ("proof_acceptance","RH","base_tree"):
            altered=copy.deepcopy(policy)
            altered[key]=True if key=="proof_acceptance" else "bad"
            with self.assertRaises(g.Reject): g.validate_delta(parent,current,altered,active,vid)
        for name in (".github/workflows/opica-next-acceptance.yml",next(iter(g.FROZEN)),"lean-toolchain"):
            modified={**current,name:("100644","blob","0"*40)}
            with self.assertRaises(g.Reject):g.validate_delta(parent,modified,policy,active,vid)
        for modified in ({**current,"unexpected.lean":("100644","blob","0"*40)},
                         {p:v for p,v in current.items() if p!="lean-toolchain"}):
            with self.assertRaises(g.Reject):g.validate_delta(parent,modified,policy,active,vid)
    def test_stubs_are_nonexecuting(self):
        for name in (".github/workflows/opica-next-acceptance.yml",".github/workflows/opica-next-source-epoch.yml"):
            body=(g.REPO/name).read_text()
            self.assertIn("workflow_dispatch:",body)
            self.assertIn("REGISTRATION_ONLY; NO_PROOF_ACCEPTANCE",body)
            self.assertIn("exit 2",body)
            self.assertNotIn("uses:",body)
            self.assertNotIn("self-hosted",body)

    def test_end_to_end_replay_uses_exact_epoch_admission(self):
        from types import SimpleNamespace
        from unittest.mock import patch
        from research.RHRC.integration.opica_composition import cli
        from research.RHRC.integration.opica_composition.canonical import ContractError
        from research.RHRC.integration.opica_composition.tests.test_end_to_end import _validate_replay_source
        self.assertIs(cli.validate_descendant, g.validate_descendant)
        report = g.check(require_clean=True)
        snapshot = SimpleNamespace(repo=str(g.REPO), commit=report["checked_commit"],
                                   tree=report["checked_tree"])
        actual = _validate_replay_source(snapshot)
        self.assertEqual(actual["schema"], "OPICA_DISPATCH_REGISTRATION_INSPECTION_V1")
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
            g.historical.inspect_committed_tree(g.REPO)

if __name__=="__main__":
    unittest.main()
