"""Exact synthetic falsifiers and source-policy mutations, effective under -O.

These controls reject invalid inference patterns. They are not experiments on
the actual zeta source and cannot prove any arithmetic sign restriction.
"""
from __future__ import annotations

import copy
from fractions import Fraction as F
import importlib.util
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("round3_contract_under_test", HERE / "validate_contract.py")
contract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contract)


def descriptor_fixture():
    policy = {"base": contract.BASE, "base_tree": contract.BASE_TREE,
              "additions": sorted(contract.ADDITIONS), "edits": sorted(contract.EDITS),
              "generated": [f"generated/{i:02d}.json" for i in range(81)]}
    paths = (contract.ADDITIONS | contract.EDITS) - {contract.DESCRIPTOR}
    doc = {"schema": "OPICA3_DESCENDANT_EXTENSION_V1", "state": "FROZEN", "policy": policy,
           "path_policy_sha256": contract.policy_digest(policy), "files": [
               {"path": p, "bytes": 0, "sha256": "0" * 64} for p in sorted(paths)],
           "premise_contracts": copy.deepcopy(contract.PREMISES), "authority": "SOURCE_SCOPE_ONLY",
           **contract.CAPS}
    return policy, doc


def public_fixture():
    return contract.read_json(HERE / "PUBLIC_ROOTS.json")


class SourcePolicyMutationTests(unittest.TestCase):
    def test_complete_closed_descriptor_positive(self):
        policy, doc = descriptor_fixture()
        self.assertEqual(len(contract.validate_descriptor(doc, policy)), len(doc["files"]))
        self.assertTrue(set(policy["generated"]).isdisjoint(r["path"] for r in doc["files"]))
        self.assertEqual(len(contract.EDITS), 17)
        self.assertTrue({contract.R2+"tests/test_file_classes.py", contract.R2+"tests/test_receipt.py"} <= contract.EDITS)

    def test_unknown_path_refused(self):
        policy, doc = descriptor_fixture()
        doc["files"][0]["path"] = "Zeta23/Unreviewed.lean"
        with self.assertRaises(contract.InvalidContract):
            contract.validate_descriptor(doc, policy)

    def test_self_authorized_larger_policy_refused(self):
        policy, doc = descriptor_fixture()
        doc["policy"] = copy.deepcopy(policy)
        doc["policy"]["edits"].append("lean-toolchain")
        doc["path_policy_sha256"] = contract.policy_digest(doc["policy"])
        with self.assertRaises(contract.InvalidContract):
            contract.validate_descriptor(doc, policy)

    def test_unknown_descriptor_field_refused(self):
        policy, doc = descriptor_fixture()
        doc["compiler_authority"] = True
        with self.assertRaises(contract.InvalidContract):
            contract.validate_descriptor(doc, policy)

    def test_pending_descriptor_refused(self):
        policy, doc = descriptor_fixture()
        doc["state"] = "PENDING"
        with self.assertRaises(contract.InvalidContract):
            contract.validate_descriptor(doc, policy)

    def test_duplicate_missing_and_bad_source_pin_refused(self):
        for mode in ("duplicate", "missing", "hash", "boolean_length"):
            with self.subTest(mode=mode):
                policy, doc = descriptor_fixture()
                if mode == "duplicate":
                    doc["files"][0] = copy.deepcopy(doc["files"][1])
                elif mode == "missing":
                    doc["files"].pop()
                elif mode == "hash":
                    doc["files"][0]["sha256"] = "A" * 64
                else:
                    doc["files"][0]["bytes"] = False
                with self.assertRaises(contract.InvalidContract):
                    contract.validate_descriptor(doc, policy)

    def test_claim_and_human_promotion_refused(self):
        for key, value in (("RH", "PROVED"), ("Step4", "CLOSED"), ("full_core_accepted", True),
                           ("full_release_accepted", 1), ("human_review", "APPROVED")):
            with self.subTest(key=key):
                policy, doc = descriptor_fixture()
                doc[key] = value
                with self.assertRaises(contract.InvalidContract):
                    contract.validate_descriptor(doc, policy)

    def test_original_open_claim_and_binding_cannot_drift(self):
        public = public_fixture()
        old = {"schema": "fixture", "claims": [{"id": "RH", "status": "OPEN"}]}
        new = copy.deepcopy(old)
        for row in public["roots"]:
            new["claims"].append({"id": row["claim_id"], "theorem": row["theorem"],
                "source": row["source"], "status": "PROVED_UNCONDITIONAL",
                "promotion_cap": "PROVED_UNCONDITIONAL"})
        contract.check_claim_extension(old, new, "claims", public)
        new["claims"][0]["status"] = "PROVED_UNCONDITIONAL"
        with self.assertRaises(contract.InvalidContract):
            contract.check_claim_extension(old, new, "claims", public)

    def test_only_four_exact_new_binding_identities(self):
        public = public_fixture()
        old = {"schema": "fixture", "bindings": [{"id": "old", "theorem": "Old.actual"}]}
        new = copy.deepcopy(old)
        new["bindings"] += [{"id": r["claim_id"], "theorem": r["theorem"], "source": r["source"]}
                            for r in public["roots"]]
        contract.check_claim_extension(old, new, "bindings", public)
        for mutation in ("old_drift", "extra", "new_identity"):
            trial = copy.deepcopy(new)
            if mutation == "old_drift":
                trial["bindings"][0]["theorem"] = "Old.replacement"
            elif mutation == "extra":
                trial["bindings"].append({"id": "OPICA3_D05"})
            else:
                trial["bindings"][-1]["theorem"] = "Synthetic.desired"
            with self.assertRaises(contract.InvalidContract):
                contract.check_claim_extension(old, trial, "bindings", public)

    def test_four_actual_public_consumers_positive_and_mutations(self):
        doc = public_fixture()
        contract.check_public(doc)
        for field, value in (("consumer_declaration", "Synthetic.assumed"), ("required", 1),
                             ("theorem", "Zeta23.riemannHypothesis")):
            trial = copy.deepcopy(doc)
            trial["roots"][0][field] = value
            with self.assertRaises(contract.InvalidContract):
                contract.check_public(trial)

    def test_noncanonical_paths_and_duplicate_json_refused(self):
        for path in ("../escape", "./a", "a\\b", "/absolute", "a//b", "C:/a", "a/../b"):
            with self.subTest(path=path), self.assertRaises(contract.InvalidContract):
                contract.relative(path)
        with self.assertRaises(contract.InvalidContract):
            contract.strict_json(b'{"RH":"OPEN","RH":"PROVED"}')

    def test_parent_compatibility_does_not_satisfy_round2_acceptance(self):
        from research.RHRC.integration.opica_round2 import validate_contract as parent
        child = {"status": "PASS_SOURCE_SCOPE_ONLY", **contract.CAPS}
        with patch.object(parent, "round3_extension_context", return_value=child):
            report = parent.preflight()
            self.assertEqual(report["status"], "PASS_PARENT_SOURCE_SCOPE_ONLY")
            self.assertFalse(report["full_release_accepted"])
            with self.assertRaises(ValueError):
                parent.acceptance(formal_receipt=Path("must_not_be_opened.json"))

    def test_parent_bridge_requires_reviewed_provider_before_execution(self):
        from research.RHRC.integration.opica_round2 import validate_contract as parent
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            folder = repo / contract.PREFIX
            folder.mkdir(parents=True)
            (folder / "DESCENDANT_EXTENSION.json").write_text("{}", encoding="utf-8")
            provider = folder / "validate_contract.py"
            provider.write_text("raise AssertionError('unreviewed code must never execute')\n", encoding="utf-8")
            with patch.object(parent, "ROUND3_PROVIDER_SHA256", "0" * 64), \
                 patch.object(parent, "ROUND3_PATH_POLICY_SHA256", "1" * 64):
                with self.assertRaises(ValueError):
                    parent.round3_extension_context(repo)

    def test_parent_bridge_rejects_enlarged_policy_before_inspection(self):
        from research.RHRC.integration.opica_round2 import validate_contract as parent
        raw = ("def path_policy(repo): return {}\n"
               "def policy_digest(policy): return '" + "f"*64 + "'\n"
               "def inspect_descendant(repo): raise AssertionError('wrong policy must not execute')\n").encode()
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            folder = repo / contract.PREFIX
            folder.mkdir(parents=True)
            (folder / "DESCENDANT_EXTENSION.json").write_text("{}", encoding="utf-8")
            (folder / "validate_contract.py").write_bytes(raw)
            with patch.object(parent, "ROUND3_PROVIDER_SHA256", hashlib.sha256(raw).hexdigest()), \
                 patch.object(parent, "ROUND3_PATH_POLICY_SHA256", "0"*64):
                with self.assertRaises(ValueError):
                    parent.round3_extension_context(repo)


class PremiseFirewallTests(unittest.TestCase):
    def test_complete_premises_are_declaration_only(self):
        for cid, premises in contract.PREMISES.items():
            report = contract.check_premise_firewall(cid, list(premises), [])
            self.assertEqual(report["authority"], "NO_COMPILER_AUTHORITY")
            self.assertFalse(report["full_core_accepted"])

    def test_each_required_premise_is_required(self):
        for cid, premises in contract.PREMISES.items():
            for lost in premises:
                with self.subTest(cid=cid, lost=lost), self.assertRaises(contract.InvalidContract):
                    contract.check_premise_firewall(cid, [p for p in premises if p != lost], [])

    def test_each_forbidden_inference_is_refused(self):
        for shortcut in contract.FORBIDDEN:
            with self.subTest(shortcut=shortcut), self.assertRaises(contract.InvalidContract):
                contract.check_premise_firewall("R3-D04", contract.PREMISES["R3-D04"], [shortcut])


class NativeProtocolTests(unittest.TestCase):
    def test_compiler_crash_cannot_count_as_semantic_rejection(self):
        contract.require_compiler_exit(0, True)
        contract.require_compiler_exit(1, False)
        for code in (-11, -9, 255, 2, 0, True, None):
            with self.subTest(code=code), self.assertRaises(contract.InvalidContract):
                contract.require_compiler_exit(code, False)

    def test_exact_axiom_and_type_output_positive(self):
        text = ("Zeta23.actual (x : Nat) : x = x\n"
                "'Zeta23.actual' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n")
        self.assertEqual(contract.parse_axiom_audit(text, ["Zeta23.actual"]),
                         {"Zeta23.actual": ["propext", "Classical.choice", "Quot.sound"]})

    def test_missing_duplicate_or_project_axiom_export_refused(self):
        for text in ("Zeta23.actual : True\n", "'Zeta23.actual' depends on axioms: [propext]",
                     "Zeta23.actual : True\n'Zeta23.actual' depends on axioms: [Project.assumed]\n",
                     "Zeta23.actual : True\n'Zeta23.actual' depends on axioms: [sorryAx]\n",
                     "Zeta23.actual : True\n'Zeta23.actual' depends on axioms: [propext, propext]\n",
                     "Zeta23.actual : True\n" + "'Zeta23.actual' does not depend on any axioms\n"*2):
            with self.subTest(text=text), self.assertRaises(contract.InvalidContract):
                contract.parse_axiom_audit(text, ["Zeta23.actual"])

    def test_semantic_negative_cannot_be_import_syntax_resource_or_name_failure(self):
        contract.require_semantic_rejection("error: Type mismatch: actual witness has a weaker type")
        for error in ("unknown identifier", "unknown namespace", "unknown module", "unexpected token",
                      "object file unavailable", "maximum number of heartbeats", "failed to synthesize",
                      "file not found", "invalid syntax", "out of memory"):
            with self.subTest(error=error), self.assertRaises(contract.InvalidContract):
                contract.require_semantic_rejection("type mismatch\n" + error)
        with self.assertRaises(contract.InvalidContract):
            contract.require_semantic_rejection("error: generic failure without semantic evidence")

    def test_literal_native_pairs_are_changed_semantics_with_identical_imports(self):
        for index in range(4):
            positive, negative, scope = contract.semantic_control_pair(index)
            self.assertNotEqual(positive, negative)
            self.assertEqual(positive.splitlines()[0], negative.splitlines()[0])
            self.assertIn(contract.ROOT_NAMES[index] + "_consumer", positive)
            self.assertNotIn("sorry", positive + negative)
            self.assertTrue(scope.startswith(f"D{index+1:02d}_"))


class ExactFalsificationTests(unittest.TestCase):
    def test_cofinality_without_union_cover_does_not_force_overlap(self):
        # A=union_n(3n,3n+1), B=union_n(3n+2,3n+5/2).
        # Each family has arbitrarily late intervals, but every midpoint below
        # misses their union. Both openness and cofinality leave cover missing.
        for n in (0, 1, 10, 10**6):
            a, b = (F(3*n), F(3*n+1)), (F(3*n+2), F(6*n+5, 2))
            hole = F(6*n+3, 2)
            self.assertLess(a[1], b[0])
            self.assertFalse(a[0] < hole < a[1] or b[0] < hole < b[1])
            self.assertGreater(a[0] + F(1, 2), 3*n - 1)

    def test_disconnected_domain_defeats_open_cover_overlap(self):
        # On X=(-2,-1) union (1,2), its two components are disjoint nonempty
        # relatively open sets covering X. Connectedness cannot be omitted.
        x, y = F(-3, 2), F(3, 2)
        self.assertLess(x, -1)
        self.assertGreater(y, 1)
        self.assertLess(x, 0)
        self.assertGreater(y, 0)

    def test_output_residual_requires_projection(self):
        normal, residual = (F(1), F(0)), (F(1), F(1))
        dot = sum(a*b for a, b in zip(normal, residual))
        projected = tuple(b - dot*a for a, b in zip(normal, residual))
        self.assertEqual(projected, (0, 1))
        self.assertEqual(sum(v*v for v in residual), 2)
        self.assertEqual(sum(v*v for v in projected), 1)
        self.assertNotEqual(residual, projected)

    def test_regular_one_shell_schur_actual_quadratic_witness(self):
        a, b, c = F(2), F(1), F(0)
        schur = c - b*b/a
        x, y = -b/a, F(1)
        self.assertGreaterEqual(a, 0)
        self.assertLess(schur, 0)
        self.assertEqual(a*x*x + 2*b*x*y + c*y*y, schur)

    def test_resonant_kernel_coupling_defeats_positive_diagonals(self):
        # A=diag(0,2), b=(1,1), c=3. All diagonal entries are nonnegative;
        # P_ker(A)b=(1,0) supplies a negative direction without an inverse.
        x0, x1, y = F(-3), F(0), F(1)
        q = 2*x1*x1 + 2*(x0+x1)*y + 3*y*y
        self.assertEqual((F(1), F(0)), (1, 0))
        self.assertLess(q, 0)

    def test_singular_regular_positive_control(self):
        # A=diag(0,2), b=(0,1), c=1 has no kernel coupling and Schur=1/2.
        for x0 in range(-3, 4):
            for x1 in range(-3, 4):
                for y in range(-3, 4):
                    q = 2*x1*x1 + 2*x1*y + y*y
                    self.assertGreaterEqual(q, 0)
        self.assertEqual(F(1)-F(1, 2), F(1, 2))

    def test_only_newborn_predecessor_is_psd_with_unequal_arrivals(self):
        ke, ko = 3, 5
        both = max(ke, ko)
        even_negative = lambda k: k >= ke
        odd_negative = lambda k: k >= ko
        self.assertTrue(even_negative(both) and odd_negative(both))
        self.assertTrue(even_negative(both-1))
        self.assertFalse(odd_negative(both-1))
        self.assertFalse(even_negative(2))  # Empty K=2 neutral predecessor.

    def test_equal_cutoffs_do_not_imply_spectral_tie(self):
        # Distinct successor blocks can have their first negative eigenvalue
        # at the same K while the actual negative eigenvalues differ.
        predecessor_even, predecessor_odd = (F(1),), (F(2),)
        successor_even, successor_odd = (F(1), F(-1)), (F(2), F(-3))
        self.assertGreaterEqual(min(predecessor_even), 0)
        self.assertGreaterEqual(min(predecessor_odd), 0)
        self.assertLess(min(successor_even), 0)
        self.assertLess(min(successor_odd), 0)
        self.assertNotEqual(min(successor_even), min(successor_odd))

    def test_local_negative_intervals_do_not_give_global_eta(self):
        # f(L)=-1/(L+1) is strictly negative. For every proposed eta>0,
        # choosing L=1/eta already violates f(L)<=-eta.
        for eta in (F(1), F(1, 2), F(1, 10**6)):
            aperture = 1/eta
            self.assertGreater(-1/(aperture+1), -eta)
            local_eta = 1/(aperture+2)
            for point in (aperture, aperture+F(1, 2), aperture+1):
                self.assertLessEqual(-1/(point+1), -local_eta)


if __name__ == "__main__":
    unittest.main()
