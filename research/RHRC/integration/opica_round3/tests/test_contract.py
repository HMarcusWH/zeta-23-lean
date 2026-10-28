"""Exact synthetic falsifiers and source-policy mutations, effective under -O.

These controls reject invalid inference patterns. They are not experiments on
the actual zeta source and cannot prove any arithmetic sign restriction.
"""
from __future__ import annotations

import copy
from fractions import Fraction as F
import importlib.util
import hashlib
import json
import io
from contextlib import redirect_stdout
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

    def test_only_five_exact_new_binding_identities(self):
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
                trial["bindings"].append({"id": "OPICA3_D06"})
            else:
                trial["bindings"][-1]["theorem"] = "Synthetic.desired"
            with self.assertRaises(contract.InvalidContract):
                contract.check_claim_extension(old, trial, "bindings", public)

    def test_five_actual_public_consumers_positive_and_mutations(self):
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
        for index in range(5):
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


def write_fixture(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(value if isinstance(value, bytes) else
                     (json.dumps(value, indent=2) + "\n").encode("utf-8"))


def unit_log(ids):
    return "\n".join(name.rsplit(".", 1)[1] + " (" + name + ") ... ok" for name in ids) + (
        "\n\n----------------------------------------------------------------------\nRan " + str(len(ids)) + " tests in 0.001s\n\nOK\n")


def formal_artifact_fixture(root, names):
    """Protocol bytes for parser tests only; these objects are not Lean evidence."""
    source = {"checked_commit": "a" * 40, "checked_tree": "b" * 40}
    environment = {"lean_toolchain": "leanprover/lean4:v4.33.0-rc2", "mathlib_commit": "c" * 40}
    packages = [{"name": "fixture", "commit": "d" * 40}]
    report = {"schema": "OPICA3_CURRENT_COMPILER_GATE_V1", "status": "PASS_CURRENT_COMPILER_SCOPE_ONLY",
              **source, "scope": "CURRENT_FIVE_ROOTS_AND_CONSUMERS_PLUS_CURRENT_ORIGINAL_FORTY",
              "build_mode": "FRESH_CI_PROJECT_BUILD_PACKAGE_CACHE_ALLOWED", "commands": [],
              "current_tree_compiler_accepted": True, "environment": environment, "pinned_packages": packages,
              "source_manifest_sha256": "e" * 64,
              "lean_version": "Lean (version 4.33.0-rc2, commit d8b18978322de05a8f3dba51ef03cf5461676c17)",
              "axioms": {name: ["propext", "Classical.choice", "Quot.sound"] for name in names},
              "semantic_controls": [], **contract.CAPS}
    producer = "/original-ci-root/formal"
    def command(argv, label, text, positive=True):
        write_fixture(root / (label + ".log"), text.encode())
        report["commands"].append({"argv": argv, "exit_code": 0 if positive else 1, "timeout": False,
                                   "log": label + ".log", "log_sha256": contract.sha(root / (label + ".log"))})
    command(["lake", "env", "lean", "--version"], "lean-version", report["lean_version"] + "\n")
    command(["lake", "build", "Zeta23.OPICARound2.All", "Zeta23.OPICARound2.Validation",
             "Zeta23.RHRC.OpicaRound2Bindings", "Zeta23.OPICARound3.All", "Zeta23.OPICARound3.Validation",
             "Zeta23.RHRC.OpicaRound3Bindings"], "current-build", "fixture build\n")
    write_fixture(root / "CurrentRootAudit.lean", contract.render_current_audit(names))
    write_fixture(root / "CurrentRootAudit.olean", b"PARSER UNIT FIXTURE, NOT A LEAN OBJECT")
    report["query_sha256"] = contract.sha(root / "CurrentRootAudit.lean")
    report["object_sha256"] = contract.sha(root / "CurrentRootAudit.olean")
    text = "".join(name + " : True\n'" + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for name in names)
    command(["lake", "env", "lean", "-R", producer, "-o", producer + "/CurrentRootAudit.olean",
             producer + "/CurrentRootAudit.lean"], "current-root-audit", text)
    for index in range(5):
        positive, negative, scope = contract.semantic_control_pair(index)
        pair = {"id": f"R3-D{index+1:02d}", "scope": scope,
                "negative_authority": "PRODUCER_TYPE_REJECTION_ONLY_NOT_SOURCE_FALSE_THEOREM"}
        for mode, content in (("positive", positive), ("negative", negative)):
            name = "Control" + str(index + 1) + mode
            write_fixture(root / (name + ".lean"), content.encode())
            if mode == "positive":
                write_fixture(root / (name + ".olean"), b"UNIT PARSER OBJECT")
            pair[mode] = {"source": name + ".lean", "sha256": contract.sha(root / (name + ".lean")),
                          "command_index": len(report["commands"]),
                          "object_sha256": contract.sha(root / (name + ".olean")) if mode == "positive" else None}
            command(["lake", "env", "lean", "-R", producer, "-o", producer + "/" + name + ".olean",
                     producer + "/" + name + ".lean"], f"D{index+1:02d}-{mode}",
                    "" if mode == "positive" else "error: Type mismatch: expected stronger type\n", mode == "positive")
        report["semantic_controls"].append(pair)
    write_fixture(root / "result.json", report)
    return report, source, environment, packages


class CurrentPhase1AggregateTests(unittest.TestCase):
    def test_arithmetic_uncertainty_writes_an_open_failed_acceptance_receipt(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            output = folder / "acceptance"
            argv = ["validate_contract.py", "--aggregate-artifacts", str(folder / "inputs"),
                    "--required-needs-json", str(folder / "needs.json"), "--aggregate-output", str(output)]
            with patch.object(contract.sys, "argv", argv), \
                 patch.object(contract, "aggregate_phase1", side_effect=ArithmeticError("Independent quadrature unresolved")), \
                 redirect_stdout(io.StringIO()):
                self.assertEqual(contract.main(), 1)
            result = contract.read_json(output / "result.json")
            self.assertEqual(result["status"], "FAIL_CURRENT_BUILD_AGGREGATE")
            self.assertEqual(result["authority"], "NO_ACCEPTANCE")
            self.assertFalse(result["full_release_accepted"])
            self.assertEqual(result["RH"], "OPEN")

    def test_four_required_jobs_fail_closed_on_all_non_success_states(self):
        data = {name: {"result": "success", "outputs": {}} for name in contract.PHASE1_JOBS}
        contract.require_phase1_needs(data)
        for mode in ("missing", "extra", "skipped", "failure", "cancelled", "pending", None, True):
            trial = copy.deepcopy(data)
            if mode == "missing":
                trial.pop("current-formal")
            elif mode == "extra":
                trial["historical-baseline"] = {"result": "success"}
            else:
                trial["current-formal"]["result"] = mode
            with self.subTest(mode=mode), self.assertRaises(contract.InvalidContract):
                contract.require_phase1_needs(trial)

    def test_raw_unit_population_docstrings_and_summary_are_exact(self):
        ids = ["test_module.Cases.test_a", "test_module.Cases.test_b"]
        contract.verify_unit_log(unit_log(ids), ids)
        text = unit_log(ids).replace("test_a (test_module.Cases.test_a) ... ok",
                                     "test_a (test_module.Cases.test_a)\nLiteral current source description. ... ok")
        contract.verify_unit_log(text, ids, {ids[0]: "Literal current source description."})
        for trial in (text, unit_log(ids[:1]), unit_log(ids + ids[:1]), unit_log(ids).replace("Ran 2", "Ran 1"),
                      unit_log(ids).replace("... ok", "... skipped 'missing prerequisites'", 1),
                      unit_log(ids).replace("\nOK\n", "\nFAILED (failures=1)\n")):
            with self.subTest(trial=trial), self.assertRaises(contract.InvalidContract):
                contract.verify_unit_log(trial, ids)

    def test_added_lane_cannot_be_missing_or_fail_while_old_three_are_green(self):
        data = {name: {"result": "success", "outputs": {}} for name in contract.PHASE1_JOBS}
        for state in ("missing", "skipped", "failure", "cancelled", "queued"):
            trial = copy.deepcopy(data)
            if state == "missing":
                trial.pop("source-evaluator")
            else:
                trial["source-evaluator"]["result"] = state
            with self.subTest(state=state), self.assertRaises(contract.InvalidContract):
                contract.require_phase1_needs(trial)

    def test_every_round3_test_file_has_exactly_one_lane(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            for index, name in enumerate(contract.CONTRACT_TEST_FILES + contract.EVALUATOR_TEST_FILES):
                write_fixture(folder / name, ("import unittest\nclass Cases(unittest.TestCase):\n"
                    f"    def test_case_{index}(self): pass\n").encode())
            self.assertEqual(len(contract.selected_test_descriptions(folder, contract.CONTRACT_TEST_FILES)), 2)
            self.assertEqual(len(contract.selected_test_descriptions(folder, contract.EVALUATOR_TEST_FILES)), 1)
            write_fixture(folder / "test_unexecuted.py", b"import unittest\nclass Cases(unittest.TestCase):\n    def test_hidden(self): pass\n")
            with self.assertRaises(contract.InvalidContract):
                contract.selected_test_descriptions(folder, contract.CONTRACT_TEST_FILES)

    def test_current_literal_212_inventory_keeps_native_case_separate(self):
        names = contract.test_inventory(HERE.parent / "opica_round2/tests")
        self.assertEqual(len(names), 212)
        self.assertEqual(names.count(contract.NATIVE_CASE), 1)
        self.assertEqual(len(set(names) - {contract.NATIVE_CASE}), 211)

    def test_integer_identity_does_not_accept_boolean_or_float_substitution(self):
        self.assertTrue(contract.same_json({"bytes": 0}, {"bytes": 0}))
        self.assertFalse(contract.same_json({"bytes": False}, {"bytes": 0}))
        self.assertFalse(contract.same_json({"bytes": 0.0}, {"bytes": 0}))
        for data in ({**contract.CAPS, "full_core_accepted": 0}, {**contract.CAPS, "human_review": "APPROVED"}):
            with self.assertRaises(contract.InvalidContract):
                contract.require_open_caps(data)

    def test_formal_raw_protocol_reparse_survives_artifact_relocation(self):
        names = contract.current_audit_names(HERE.parents[3])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            report, source, env, packages = formal_artifact_fixture(root, names)
            parsed = contract.verify_current_formal(root, report, names, source, "e" * 64, env, packages)
            self.assertEqual(parsed["roots_and_consumers"], 50)
            self.assertEqual(parsed["semantic_pairs"], 5)
            self.assertNotEqual(str(root), report["commands"][2]["argv"][4])

    def test_formal_head_caps_axiom_recipe_exit_and_pin_mutations_rejected(self):
        names = contract.current_audit_names(HERE.parents[3])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            original, source, env, packages = formal_artifact_fixture(root, names)
            def mutate(report, mode):
                if mode == "head": report["checked_commit"] = contract.BASE
                elif mode == "caps": report["full_release_accepted"] = True
                elif mode == "environment": report["environment"] = {}
                elif mode == "manifest": report["source_manifest_sha256"] = "0" * 64
                elif mode == "command": report["commands"][2]["argv"][4] = "/another-root"
                elif mode == "boolean": report["commands"][0]["exit_code"] = False
                elif mode == "timeout": report["commands"][3]["timeout"] = True
                elif mode == "missing_pair": report["semantic_controls"].pop()
                elif mode == "axioms": report["axioms"][names[0]] = ["Project.assumed"]
                elif mode == "index": report["semantic_controls"][0]["positive"]["command_index"] = True
                elif mode == "fields": report["accepted"] = True
            for mode in ("head", "caps", "environment", "manifest", "command", "boolean", "timeout",
                         "missing_pair", "axioms", "index", "fields"):
                report = copy.deepcopy(original)
                mutate(report, mode)
                with self.subTest(mode=mode), self.assertRaises(contract.InvalidContract):
                    contract.verify_current_formal(root, report, names, source, "e" * 64, env, packages)

    def test_formal_sources_logs_objects_and_semantic_failure_are_reparsed(self):
        names = contract.current_audit_names(HERE.parents[3])
        for mode in ("query", "source", "log", "object", "negative_object", "infrastructure", "project_axiom", "missing_type"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                report, source, env, packages = formal_artifact_fixture(root, names)
                if mode == "query":
                    write_fixture(root / "CurrentRootAudit.lean", b"#check True\n")
                    report["query_sha256"] = contract.sha(root / "CurrentRootAudit.lean")
                elif mode == "source":
                    write_fixture(root / "Control1positive.lean", b"example : True := by trivial\n")
                    report["semantic_controls"][0]["positive"]["sha256"] = contract.sha(root / "Control1positive.lean")
                elif mode == "log":
                    write_fixture(root / "current-root-audit.log", b"changed raw output")
                elif mode == "object":
                    write_fixture(root / "CurrentRootAudit.olean", b"changed object")
                elif mode == "negative_object":
                    write_fixture(root / "Control1negative.olean", b"unexpected object")
                elif mode == "infrastructure":
                    write_fixture(root / "D01-negative.log", b"error: type mismatch; unknown identifier\n")
                    report["commands"][4]["log_sha256"] = contract.sha(root / "D01-negative.log")
                else:
                    text = (root / "current-root-audit.log").read_text()
                    text = text.replace("propext, Classical.choice, Quot.sound", "Project.assumed", 1) if mode == "project_axiom" else text.replace(names[0] + " : True\n", "", 1)
                    write_fixture(root / "current-root-audit.log", text.encode())
                    report["commands"][2]["log_sha256"] = contract.sha(root / "current-root-audit.log")
                with self.assertRaises(contract.InvalidContract):
                    contract.verify_current_formal(root, report, names, source, "e" * 64, env, packages)

    def test_artifact_closed_budget_and_plain_paths(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with self.assertRaises(contract.InvalidContract):
                contract.artifact_inventory(root)
            write_fixture(root / "one.json", {})
            self.assertEqual(len(contract.artifact_inventory(root)), 1)
            with self.assertRaises(contract.InvalidContract):
                contract.evidence_file(root, "../one.json")
            with patch.object(Path, "is_symlink", return_value=True):
                with self.assertRaises(contract.InvalidContract):
                    contract.artifact_inventory(root)

    def aggregate_fixture(self, base):
        """Mock only checkout/package and protected native engines, never their verdict inputs."""
        from research.RHRC.integration.opica_round2 import build_receipt as compiler, controls
        repo, artifacts = base / "repo", base / "artifacts"
        ordinary = [f"test_fixture.Cases.test_case_{index:03d}" for index in range(211)]
        write_fixture(repo / contract.R2 / "tests/test_fixture.py", ("import unittest\nclass Cases(unittest.TestCase):\n" +
            "".join(f"    def test_case_{index:03d}(self): pass\n" for index in range(211))).encode())
        write_fixture(repo / contract.R2 / "tests/test_claim_firewall.py", (
            "import unittest\nclass NativeTypedSemanticControls(unittest.TestCase):\n"
            "    def test_seven_positive_and_wrong_type_native_fixtures(self): pass\n").encode())
        guard = ["test_contract.Cases.test_guard", "test_constraint_atlas.Cases.test_atlas"]
        write_fixture(repo / contract.PREFIX / "tests/test_contract.py",
                      b"import unittest\nclass Cases(unittest.TestCase):\n    def test_guard(self): pass\n")
        write_fixture(repo / contract.PREFIX / "tests/test_constraint_atlas.py",
                      b"import unittest\nclass Cases(unittest.TestCase):\n    def test_atlas(self): pass\n")
        evaluator_ids = ["test_source_evaluator.Cases.test_evaluator"]
        write_fixture(repo / contract.PREFIX / "tests/test_source_evaluator.py",
                      b"import unittest\nclass Cases(unittest.TestCase):\n    def test_evaluator(self): pass\n")
        names = contract.current_audit_names(HERE.parents[3])
        formal, identity, environment, packages = formal_artifact_fixture(artifacts / "formal/formal", names)
        source = {**identity, "status": "PASS_SOURCE_SCOPE_ONLY", "descriptor_sha256": "f" * 64,
                  "path_policy_sha256": "1" * 64, **contract.CAPS}
        manifest = [{"path": "fixture", "mode": "100644", "git_blob": "2" * 40, "bytes": 0, "sha256": "3" * 64}]
        frozen = {"schema": "OPICA2_WORKFLOW_SOURCE_FREEZE_V1", **identity, "sources": manifest,
                  "authority": "SOURCE_IDENTITY_ONLY", "full_core_accepted": False,
                  "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
        for job in contract.ARTIFACT_JOBS:
            write_fixture(artifacts / job / "source/before.json", frozen)
        for suffix, optimized in (("", False), ("-optimized", True)):
            write_fixture(artifacts / ("contract/preflight" + suffix + ".json"), {**source, "python_optimized": optimized})
        registry = {"fixture": "protected native engine is mocked in this parser-only unit fixture"}
        write_fixture(repo / contract.R2 / "CONTROL_REGISTRY.json", registry)
        native_result = {"status": "PASS_SOURCE_BOUND_TYPED_PAIR_REPARSE", "ids": [str(i) for i in range(7)],
                         "receipt_sha256": "4" * 64, "fresh_compiler_replay": False,
                         "provider_authenticity_established_here": False}
        for mode in ("normal", "optimized"):
            for lane, test_ids in (("contract", guard), ("evaluator", evaluator_ids)):
                write_fixture(artifacts / f"{lane}/{lane}-tests-{mode}.log", unit_log(test_ids).encode())
                write_fixture(artifacts / f"{lane}/{lane}-tests-{mode}.json", {
                    "schema": "OPICA3_CURRENT_UNIT_LANE_V1", "lane": lane, "mode": mode,
                    "python_optimized": mode == "optimized", **identity, "test_ids": sorted(test_ids),
                    "run": len(test_ids), "errors": 0, "failures": 0, "skipped": 0, "successful": True,
                    "scope": "EXACT_CURRENT_LITERAL_TEST_PARTITION", **contract.CAPS})
            report = {"schema": "OPICA3_CURRENT_ROUND2_RUNTIME_REGRESSION_V1", "mode": mode,
                      "python_optimized": mode == "optimized", **identity,
                      "discovered": 212, "selected": 211, "selected_test_ids": ordinary,
                      "held_native_case": {"id": contract.NATIVE_CASE, "execution": "NOT_EXECUTED_HERE_REQUIRED_SEPARATE_CURRENT_NATIVE_GATE"},
                      "run": 211, "errors": 0, "failures": 0, "skipped": 0, "successful": True,
                      "scope": "ALL_CURRENT211_NON_LEAN_TESTS_INCLUDING_ACTUAL_ARB_256_512_PRODUCER_GRAM_SCHEMA_AND_ADVERSARIES",
                      "full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
            write_fixture(artifacts / f"runtime/runtime-{mode}.json", report)
            write_fixture(artifacts / f"runtime/runtime-{mode}.log", unit_log(ordinary).encode())
            write_fixture(artifacts / f"formal/current-native-{mode}/one/receipt.json", {"unit_parser_fixture": True})
            native = {"schema": "OPICA3_CURRENT_NATIVE_ROUND2_UNIT_V1", "mode": mode,
                      "python_optimized": mode == "optimized", "test_id": contract.NATIVE_CASE, "run": 1,
                      "skipped": 0, **identity, "raw_artifacts": f"/original-ci/current-native-{mode}/one",
                      "independent_protected_reparse": native_result,
                      "scope": "CURRENT_SINGLE_NATIVE_UNIT_ACTUAL_SEVEN_POSITIVE_AND_SEVEN_TYPE_REJECTION_COMMANDS",
                      "full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
            write_fixture(artifacts / f"formal/current-native-{mode}.json", native)
            write_fixture(artifacts / f"formal/current-native-{mode}.log", unit_log([contract.NATIVE_CASE]).encode())
        formal["source_manifest_sha256"] = compiler.canonical_sha256(manifest)
        write_fixture(artifacts / "formal/formal/result.json", formal)
        # Deliberately not sorted: the actual canonical producer follows manifest order.
        paths = [f"generated/product-{i:02d}.json" for i in reversed(range(81))]
        write_fixture(repo / contract.R2 / "BUILD_MANIFEST.json", {"generated": [{"path": name} for name in paths]})
        for name in paths:
            write_fixture(repo / name, {"fixture": name})
        products = [{"path": name, "bytes": (repo / name).stat().st_size, "sha256": contract.sha(repo / name)} for name in paths]
        canonical = artifacts / "formal/current-canonical/generated"
        command = {"argv": ["/ci/python", "-B", "research/RHRC/tools/materialize_derived_state.py", "--check"],
                   "returncode": 0, "working_tree_sha": identity["checked_tree"]}
        for channel in ("stdout", "stderr"):
            write_fixture(canonical / ("canonical-generated-check." + channel + ".log"), b"UNIT CANONICAL LOG")
            command[channel + "_sha256"] = contract.sha(canonical / ("canonical-generated-check." + channel + ".log"))
        write_fixture(canonical / "result.json", {"schema": "OPICA2_GENERATED_CHECK_V1",
            "status": "PASS_CANONICAL_CHECK_WITHOUT_REWRITE", "before": products, "after": products,
            "command": command, "transport": {"mode": "DIRECT_FROZEN_CLI_PLATFORM_DEFAULT_UNCHANGED", "original_argv": command["argv"]},
            "full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"})
        needs = base / "needs.json"
        write_fixture(needs, {job: {"result": "success", "outputs": {}} for job in contract.PHASE1_JOBS})
        return repo, artifacts, needs, source, manifest, environment, packages, names, native_result, compiler, controls

    def run_aggregate_fixture(self, fixture, *, statuses=("", "")):
        from research.RHRC.integration.opica_round3 import constraint_atlas, source_checker
        repo, artifacts, needs, source, manifest, env, packages, names, native_result, compiler, controls = fixture
        with patch.object(contract, "inspect_descendant", return_value=source), \
             patch.object(contract, "git_text", side_effect=statuses) as clean, \
             patch.object(contract, "current_audit_names", return_value=names), \
             patch.object(contract, "path_policy", return_value={"generated": sorted(
                 r["path"] for r in contract.read_json(repo / contract.R2 / "BUILD_MANIFEST.json")["generated"])}), \
             patch.object(compiler, "source_manifest", return_value=manifest), \
             patch.object(compiler, "validate_environment", return_value=env), \
             patch.object(compiler, "validate_packages", return_value=packages), \
             patch.object(controls, "verify_typed_control_artifacts", return_value=native_result) as native, \
             patch.object(constraint_atlas, "check_atlas", return_value={"status": "PASS_PARSER_UNIT_FIXTURE", **source}) as atlas, \
             patch.object(source_checker, "verify_evaluator_evidence", return_value={"status": "PASS_PARSER_UNIT_FIXTURE", **source}) as evaluator, \
             patch.dict(contract.os.environ, {"REQUESTED_HEAD": source["checked_commit"]}):
            result = contract.aggregate_phase1(repo, artifacts, needs)
            self.assertEqual(clean.call_count, 2)
            self.assertEqual([call.kwargs["optimized"] for call in native.call_args_list], [False, True])
            self.assertEqual(atlas.call_args.args, (repo, artifacts / "formal/atlas"))
            self.assertEqual(evaluator.call_args.args, (repo, artifacts / "evaluator"))
            self.assertEqual(evaluator.call_args.kwargs, {"expected_head": source["checked_commit"],
                "expected_tree": source["checked_tree"], "recompute": True,
                "artifact_collection_root": artifacts})
            return result

    def test_full_phase1_composition_preserves_open_release_and_manifest_order(self):
        with tempfile.TemporaryDirectory() as temporary:
            result = self.run_aggregate_fixture(self.aggregate_fixture(Path(temporary)))
            self.assertEqual(result["status"], "PASS_CURRENT_BUILD_AGGREGATE")
            self.assertEqual(result["canonical_products"], 81)
            self.assertEqual(result["ordinary_tests_per_mode"], 211)
            self.assertFalse(result["full_core_accepted"])
            self.assertFalse(result["full_release_accepted"])
            self.assertFalse(result["fresh_compiler_replay"])
            self.assertFalse(result["provider_authenticity_established_here"])

    def test_full_composition_rejects_dirty_source_at_entry_and_finish(self):
        for statuses in ((" M tracked.py",), ("", "?? untracked.py")):
            with self.subTest(statuses=statuses), tempfile.TemporaryDirectory() as temporary:
                fixture = self.aggregate_fixture(Path(temporary))
                with self.assertRaises(contract.InvalidContract):
                    self.run_aggregate_fixture(fixture, statuses=statuses)

    def test_full_composition_rejects_stale_missing_or_forged_lane_evidence(self):
        for mode in ("baseline_freeze", "numeric_freeze", "preflight_mode", "runtime_mode", "runtime_bool",
                     "runtime_ids", "runtime_log", "canonical_tree", "canonical_write", "canonical_number", "native_mode", "failed_needs"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                fixture = self.aggregate_fixture(Path(temporary))
                repo, artifacts, needs = fixture[:3]
                path = None
                if mode in ("baseline_freeze", "numeric_freeze"):
                    path = artifacts / "formal/source/before.json"
                    data = contract.read_json(path)
                    if mode == "baseline_freeze": data["checked_commit"] = contract.BASE
                    else: data["sources"][0]["bytes"] = False
                elif mode == "preflight_mode":
                    path = artifacts / "contract/preflight-optimized.json"
                    data = contract.read_json(path); data["python_optimized"] = False
                elif mode.startswith("runtime_") and mode != "runtime_log":
                    path = artifacts / "runtime/runtime-optimized.json"
                    data = contract.read_json(path)
                    if mode == "runtime_mode": data["python_optimized"] = False
                    elif mode == "runtime_bool": data["errors"] = False
                    else: data["selected_test_ids"][-1] = data["selected_test_ids"][0]
                elif mode == "runtime_log":
                    path = artifacts / "runtime/runtime-normal.log"
                    write_fixture(path, b"Ran 211 tests in 0.1s\n\nOK\n")
                    path = None
                elif mode.startswith("canonical_"):
                    path = artifacts / "formal/current-canonical/generated/result.json"
                    data = contract.read_json(path)
                    if mode == "canonical_tree": data["command"]["working_tree_sha"] = "0" * 40
                    elif mode == "canonical_write": data["command"]["argv"][-1] = "--write"
                    else: data["before"][0]["bytes"] = float(data["before"][0]["bytes"])
                elif mode == "native_mode":
                    path = artifacts / "formal/current-native-optimized.json"
                    data = contract.read_json(path); data["python_optimized"] = False
                else:
                    path = needs; data = contract.read_json(path); data["current-formal"]["result"] = "skipped"
                if path is not None: write_fixture(path, data)
                with self.assertRaises(contract.InvalidContract):
                    self.run_aggregate_fixture(fixture)

    def test_added_unit_modes_populations_and_fourth_source_freeze_are_checked(self):
        for mode in ("contract_mode", "evaluator_mode", "evaluator_tests", "evaluator_freeze", "evaluator_log"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                fixture = self.aggregate_fixture(Path(temporary))
                artifacts = fixture[1]
                if mode == "evaluator_freeze":
                    path = artifacts / "evaluator/source/before.json"
                    data = contract.read_json(path); data["checked_commit"] = contract.BASE
                elif mode == "evaluator_log":
                    path = artifacts / "evaluator/evaluator-tests-normal.log"
                    write_fixture(path, b"Ran 1 test in 0.001s\n\nOK\n")
                    path = None
                else:
                    lane = "contract" if mode == "contract_mode" else "evaluator"
                    path = artifacts / f"{lane}/{lane}-tests-optimized.json"
                    data = contract.read_json(path)
                    if mode == "evaluator_tests": data["test_ids"] = []
                    else: data["python_optimized"] = False
                if path is not None: write_fixture(path, data)
                with self.assertRaises(contract.InvalidContract):
                    self.run_aggregate_fixture(fixture)


if __name__ == "__main__":
    unittest.main()
