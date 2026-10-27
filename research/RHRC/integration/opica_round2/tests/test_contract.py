from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import certificate_io as io
import controls
import validate_contract as contract


class ContractBoundaryTests(unittest.TestCase):
    def test_canonical_safe_paths(self):
        self.assertEqual(contract.safe_relative("a/b.json"), "a/b.json")
        for value in ("../escape", "/absolute", "C:/drive", r"a\b", "a/./b", "a//b", "", True):
            with self.subTest(value=value), self.assertRaises(io.InvalidCertificate):
                contract.safe_relative(value)

    def test_package_census_binds_nested_manifests(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            nested = root/"nested"
            nested.mkdir()
            data = nested/"PACKAGE_MANIFEST.json"
            data.write_text('{"historical":true}', encoding="utf-8")
            (root/"PACKAGE_MANIFEST.json").write_text("{}", encoding="utf-8")
            row = {"path": "nested/PACKAGE_MANIFEST.json", "bytes": data.stat().st_size,
                   "sha256": hashlib.sha256(data.read_bytes()).hexdigest()}
            manifest = {"files": [row]}
            contract.validate_package_inventory(root, manifest)
            data.write_text('{"historical":false}', encoding="utf-8")
            with self.assertRaises(io.InvalidCertificate):
                contract.validate_package_inventory(root, manifest)

    def test_extra_package_file_and_duplicate_records_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root/"data.json"
            path.write_text("{}", encoding="utf-8")
            row = {"path": "data.json", "bytes": 2, "sha256": hashlib.sha256(b"{}").hexdigest()}
            contract.validate_package_inventory(root, {"files": [row]})
            with self.assertRaises(io.InvalidCertificate):
                contract.validate_package_inventory(root, {"files": [row, row]})
            (root/"unlisted.py").write_text("raise RuntimeError('never executed')", encoding="utf-8")
            with self.assertRaises(io.InvalidCertificate):
                contract.validate_package_inventory(root, {"files": [row]})

    def test_original_registry_rows_cannot_be_replaced_or_duplicated(self):
        frozen = {"claims": [{"id": "C_RH", "status": "OPEN", "statement": "RH"}]}
        good = {"claims": frozen["claims"] + [{"id": "NEW", "status": "OPEN"}]}
        contract.check_original_rows(good, frozen, "claims")
        wrong = deepcopy(good)
        wrong["claims"][0]["status"] = "PROVED_UNCONDITIONAL"
        with self.assertRaises(io.InvalidCertificate):
            contract.check_original_rows(wrong, frozen, "claims")
        wrong = deepcopy(good)
        wrong["claims"].append(deepcopy(wrong["claims"][1]))
        with self.assertRaises(io.InvalidCertificate):
            contract.check_original_rows(wrong, frozen, "claims")

    def test_merged_base_requires_real_tree_and_merge_parents(self):
        lock = {"frozen_ancestor": {"commit": contract.FROZEN_COMMIT, "tree": contract.FROZEN_TREE},
                "build_base": {"commit": contract.MERGED_BASE, "tree": contract.FROZEN_TREE, "merged": True}}
        def fake_git(_, *args):
            if args[0] == "show":
                return "d"*40 + " " + contract.FROZEN_COMMIT
            if args[0] == "merge-base":
                return ""
            return contract.FROZEN_TREE if args[-1].endswith("^{tree}") else contract.MERGED_BASE
        with patch.object(contract, "git", side_effect=fake_git):
            self.assertEqual(contract.check_merged_base(HERE, lock)["build_base"], contract.MERGED_BASE)
            bad = deepcopy(lock)
            bad["build_base"]["merged"] = False
            with self.assertRaises(io.InvalidCertificate):
                contract.check_merged_base(HERE, bad)
            bad = deepcopy(lock)
            bad["frozen_ancestor"]["commit"] = "0"*40
            with self.assertRaises(io.InvalidCertificate):
                contract.check_merged_base(HERE, bad)
        with patch.object(contract, "git", return_value="0"*40):
            with self.assertRaises(io.InvalidCertificate):
                contract.check_merged_base(HERE, lock)

    def test_actual_reviewed_dag_and_negative_mutations(self):
        register = io.load_strict_json(HERE/"SOURCE_REGISTER.json", 16*1024*1024)
        dag = register["module_dag"]
        self.assertEqual(len(contract.check_dag(dag)["required_modules"]), 16)
        for mutation in ("cycle", "optional", "missing", "minimal"):
            bad = deepcopy(dag)
            if mutation == "cycle":
                bad["modules"][0]["direct_round2_imports"].append(bad["modules"][0]["module"])
            elif mutation == "optional":
                bad["modules"][0]["direct_round2_imports"].append("Zeta23.OPICARound2.ClassicalTransfer")
            elif mutation == "missing":
                bad["modules"][0]["contract_ids"].pop()
            else:
                next(x for x in bad["umbrellas"] if x["kind"] == "MATHEMATICAL_MINIMAL")["imports"].append(
                    "Zeta23.OPICARound2.ProbeGram")
            with self.subTest(mutation=mutation), self.assertRaises(io.InvalidCertificate):
                contract.check_dag(bad)

    def test_upstream_symbols_follow_actual_round2_transitive_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp)
            for name,text in (("Zeta23.OPICARound2.Middle","import Zeta23.Native.Source\n"),
                              ("Zeta23.Native.Source","theorem native_symbol : True := by trivial\n"),
                              ("Zeta23.Native.Unreachable","theorem native_symbol : True := by trivial\n")):
                path=repo/(name.replace(".","/")+".lean")
                path.parent.mkdir(parents=True,exist_ok=True)
                path.write_bytes(text.encode("utf-8"))
            consumer="Zeta23.OPICARound2.Consumer"
            source=repo/"Zeta23/Native/Source.lean"
            row={"consumer_module":consumer,"module":"Zeta23.Native.Source","symbol":"native_symbol",
                 "path":"Zeta23/Native/Source.lean","sha256":contract.digest(source)}
            dag={"modules":{consumer:{"direct_round2_imports":["Zeta23.OPICARound2.Middle"],"upstream_project_imports":[]}}}
            contract.check_upstream_symbols(repo,{"upstream_symbols":[row]},dag)
            bad={**row,"module":"Zeta23.Native.Unreachable","path":"Zeta23/Native/Unreachable.lean",
                 "sha256":contract.digest(repo/"Zeta23/Native/Unreachable.lean")}
            with self.assertRaises(io.InvalidCertificate):
                contract.check_upstream_symbols(repo,{"upstream_symbols":[bad]},dag)
            with self.assertRaises(io.InvalidCertificate):
                contract.check_upstream_symbols(repo,{"upstream_symbols":[row]},
                    {"modules":{consumer:{"direct_round2_imports":[],"upstream_project_imports":[]}}})

    def test_facade_actual_scope_and_hidden_commands_are_checked(self):
        register=io.load_strict_json(HERE/"SOURCE_REGISTER.json",16*1024*1024)
        public=io.load_strict_json(HERE/"PUBLIC_ROOTS.json",16*1024*1024)
        dag=register["module_dag"]
        contract.check_facade_sources(contract.REPO,dag,public)
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp)
            paths=[row["path"] for row in dag["umbrellas"] if row["required"]]+["Zeta23/RHRC/OpicaRound2Bindings.lean"]
            for relative in paths:
                path=repo/relative;path.parent.mkdir(parents=True,exist_ok=True)
                path.write_bytes((contract.REPO/relative).read_bytes())
            minimal=next(row for row in dag["umbrellas"] if row["kind"]=="MATHEMATICAL_MINIMAL")
            (repo/minimal["path"]).write_bytes(("\n".join("import "+name for name in minimal["imports"])+"\n").encode("utf-8"))
            contract.check_facade_sources(repo,dag,public)
            mutations=[("Zeta23/OPICARound2.lean",b"import Zeta23.OPICARound2.All\n"),
                ("Zeta23/OPICARound2/All.lean",(repo/"Zeta23/OPICARound2/All.lean").read_bytes()+b"theorem hidden : True := by trivial\n"),
                ("Zeta23/RHRC/OpicaRound2Bindings.lean",(repo/"Zeta23/RHRC/OpicaRound2Bindings.lean").read_bytes()+b"#eval 1\n")]
            for relative,payload in mutations:
                path=repo/relative;original=path.read_bytes();path.write_bytes(payload)
                with self.subTest(path=relative),self.assertRaises(io.InvalidCertificate):contract.check_facade_sources(repo,dag,public)
                path.write_bytes(original)

    def test_comment_parser_does_not_hide_proof_escapes(self):
        self.assertEqual(contract.imports('/- import Fake /- nested -/ -/\nimport Real.Module -- comment\n'), ["Real.Module"])
        with self.assertRaises(io.InvalidCertificate):
            contract.imports("/- never closed")
        source = 'theorem good : True := by trivial\n/- sorry -/\n-- axiom\n'
        self.assertNotIn("sorry", contract._strip_comments_and_strings(source))
        self.assertIn("sorry", contract._strip_comments_and_strings("theorem bad : True := by sorry"))

    def test_registered_inputs_cannot_change_or_gain_unlisted_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            here = Path(tmp)
            (here/"paper").mkdir()
            source = here/"paper/input.json"
            source.write_text("{}", encoding="utf-8")
            register = {"inputs": [{"path": "paper/input.json",
                                    "sha256": hashlib.sha256(b"{}").hexdigest()}]}
            contract.check_registered_inputs(here, register)
            (here/"paper/extra.json").write_text("{}", encoding="utf-8")
            with self.assertRaises(io.InvalidCertificate):
                contract.check_registered_inputs(here, register)
            (here/"paper/extra.json").unlink()
            source.write_text('{"changed":true}', encoding="utf-8")
            with self.assertRaises(io.InvalidCertificate):
                contract.check_registered_inputs(here, register)

    def test_missing_metadata_is_failure_not_preflight_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            report = contract.preflight(Path(tmp), Path(tmp))
            self.assertEqual(report["status"], "FAIL_PREFLIGHT")
            self.assertFalse(report["full_core_accepted"])
            self.assertFalse(report["full_release_accepted"])

    def test_protected_bytes_are_bound_to_git_object_not_candidate_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/"input"
            path.write_bytes(b"original\n")
            length, blob, sha256 = contract.actual_blob_identity(path)
            self.assertEqual(blob, hashlib.sha1(b"blob 9\0original\n").hexdigest())
            self.assertEqual((length, sha256), (9, hashlib.sha256(b"original\n").hexdigest()))
            path.write_bytes(b"tampered\n")
            self.assertNotEqual(contract.actual_blob_identity(path)[1], blob)

    def test_public_contracts_and_crosswalk_bind_normative_records(self):
        register = io.load_strict_json(HERE/"SOURCE_REGISTER.json", 16*1024*1024)
        dag = contract.check_dag(register["module_dag"])
        public = io.load_strict_json(HERE/"PUBLIC_ROOTS.json", 8*1024*1024)
        crosswalk = io.load_strict_json(HERE/"PAPER_CROSSWALK.json", 16*1024*1024)
        contract.check_family_contracts(HERE, public, crosswalk, dag)
        for mutation in ("name", "hash", "required", "clause_binding"):
            bad, bad_crosswalk = deepcopy(public), deepcopy(crosswalk)
            if mutation == "name":
                bad["roots"][0]["proposed_public_name"] = "Zeta23.OPICARound2.fake"
            elif mutation == "hash":
                bad["roots"][0]["input_contract_sha256"] = "0"*64
            elif mutation == "required":
                bad["roots"][0]["required_for_full_core"] = False
            else:
                bad_crosswalk["family_bindings"][0]["input_record_sha256"] = "0"*64
            with self.subTest(mutation=mutation), self.assertRaises(io.InvalidCertificate):
                contract.check_family_contracts(HERE, bad, bad_crosswalk, dag)


class ClauseBindingTests(unittest.TestCase):
    def setUp(self):
        crosswalk = io.load_strict_json(HERE/"PAPER_CROSSWALK.json", 16*1024*1024)
        self.mapping = contract.control_mapping(HERE, crosswalk)

    def test_all_families_and_clauses_remain_unaccepted(self):
        result = controls.check_control_bindings(self.mapping)
        self.assertEqual((result["families"], result["required_families"], result["clauses"]), (46, 40, 143))
        self.assertTrue(result["all_acceptance_false"])
        with self.assertRaises(io.InvalidCertificate):
            controls.check_control_bindings(self.mapping, acceptance=True)

    def test_clause_count_family_demotion_and_unknown_control_fail(self):
        for mutation in ("family", "clause", "demote", "control", "evidence"):
            bad = deepcopy(self.mapping)
            if mutation == "family":
                bad["family_bindings"].pop()
            elif mutation == "clause":
                bad["family_bindings"][0]["components"].pop()
            elif mutation == "demote":
                bad["family_bindings"][0]["required_for_full_core"] = False
            elif mutation == "control":
                bad["family_bindings"][0]["components"][0]["controls"][0]["control_id"] = "UNKNOWN"
            else:
                bad["family_bindings"][0]["components"][0]["acceptance"] = True
            with self.subTest(mutation=mutation), self.assertRaises(io.InvalidCertificate):
                controls.check_control_bindings(bad)

    def test_reference_cannot_self_approve(self):
        link = self.mapping["family_bindings"][0]["components"][0]["controls"][0]
        link["resolved_theorem_or_replay_reference"] = {"claim": "FORGED"}
        with self.assertRaises(io.InvalidCertificate):
            controls.check_control_bindings(self.mapping)

    def test_control_evidence_requires_reparse_for_every_required_clause(self):
        for family in self.mapping["family_bindings"]:
            if not family["required_for_full_core"]:
                continue
            family["source_pinned_receipt"] = {"synthetic_protocol_test": True}
            for clause in family["components"]:
                clause["acceptance"] = True
                for link in clause["controls"]:
                    link["actual_evidence"] = [{"synthetic_protocol_test": True}]
                    link["resolved_theorem_or_replay_reference"] = "synthetic_protocol_test"
        with self.assertRaises(io.InvalidCertificate):
            controls.check_control_bindings(self.mapping, acceptance=True)
        with self.assertRaises(io.InvalidCertificate):
            controls.check_control_bindings(self.mapping, acceptance=True,
                                           evidence_validator=lambda family, clause, link: False)
        calls = []
        def synthetic_verifier(family, clause, link):
            calls.append((family["family_id"], clause and clause["clause_id"]))
            return True
        result = controls.check_control_bindings(self.mapping, acceptance=True,
                                                evidence_validator=synthetic_verifier)
        self.assertEqual(result["status"], "PASS_VERIFIED_CONTROL_EVIDENCE")
        self.assertGreater(len(calls), 143)
        self.mapping["family_bindings"][0]["components"][0]["controls"][0]["actual_evidence"] = []
        with self.assertRaises(io.InvalidCertificate):
            controls.check_control_bindings(self.mapping, acceptance=True,
                                           evidence_validator=synthetic_verifier)

    def test_duplicate_control_cannot_inflate_clause_coverage(self):
        clause = self.mapping["family_bindings"][0]["components"][0]
        clause["controls"].append(deepcopy(clause["controls"][0]))
        with self.assertRaises(io.InvalidCertificate):
            controls.check_control_bindings(self.mapping)

    def test_clause_scope_and_evidence_classes_cannot_be_weakened(self):
        for key in ("statement_or_scope", "clause_id", "accepted_evidence_classes"):
            bad = deepcopy(self.mapping)
            clause = bad["family_bindings"][0]["components"][0]
            if key == "accepted_evidence_classes":
                clause["controls"][0][key] = ["UNREVIEWED_SELF_ASSERTION"]
            else:
                clause[key] = "SUBSTITUTED_TRIVIAL_SCOPE"
            with self.subTest(key=key), self.assertRaises(io.InvalidCertificate):
                controls.check_control_bindings(bad)




class MinimalNativeDependencyTests(unittest.TestCase):
    def test_minimal_keeps_exact_classical_adapter_dependency(self):
        register = io.load_strict_json(HERE/'SOURCE_REGISTER.json', 16*1024*1024)
        dag = register['module_dag']
        result = contract.check_dag(dag)
        fixed = result['modules']['Zeta23.OPICARound2.FixedFilter']
        self.assertIn('Zeta23.OPICARound2.ClassicalAdapter', fixed['direct_round2_imports'])
        self.assertEqual(len(result['required_modules']), 16)
        bad = deepcopy(dag)
        target = next(row for row in bad['modules'] if row['module']=='Zeta23.OPICARound2.FixedFilter')
        target['direct_round2_imports'].remove('Zeta23.OPICARound2.ClassicalAdapter')
        with self.assertRaises(ValueError):
            contract.check_dag(bad)

if __name__ == "__main__":
    unittest.main()

