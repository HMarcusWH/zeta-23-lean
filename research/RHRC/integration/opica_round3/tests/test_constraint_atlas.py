"""Atlas protocol/crosswalk adversaries. Fake objects below are parser fixtures only."""
from __future__ import annotations
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("atlas_under_test", HERE / "constraint_atlas.py")
atlas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(atlas)
REPO = HERE.parents[3]


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data if isinstance(data, bytes) else (json.dumps(data, ensure_ascii=False) + "\n").encode())


def name(value):
    result = ["anonymous"]
    for part in value.split("."): result = ["str", result, part]
    return result


def query_fixture():
    return [{"declaration": "Zeta23.Fixture.constraint", "module": "Zeta23.Fixture", "source_path": "Zeta23/Fixture.lean",
             "memberships": [{"cohort": "UNIT_PROTOCOL_FIXTURE", "identity": "UNIT", "provenance": "NO_COMPILER_AUTHORITY"}]}]


def compiler_fixture():
    nodes = [["sort", ["succ", ["zero"]]], ["bvar", "0"], ["const", name("Inhabited"), [["zero"]]],
             ["app", "2", "1"], ["const", name("True"), []], ["forall", name("h"), "default", "4", "4"],
             ["forall", name("inst"), "instImplicit", "3", "5"], ["forall", name("alpha"), "implicit", "0", "6"]]
    binders = [{"position": 0, "name": "alpha", "binder_info": "implicit", "domain_text": "Type", "domain_is_prop": False,
                "typeclass_binder": False, "class_name": None},
               {"position": 1, "name": "inst", "binder_info": "instImplicit", "domain_text": "Inhabited alpha", "domain_is_prop": False,
                "typeclass_binder": True, "class_name": "Inhabited"},
               {"position": 2, "name": "h", "binder_info": "default", "domain_text": "True", "domain_is_prop": True,
                "typeclass_binder": False, "class_name": None}]
    return {"schema": "OPICA3_ATLAS_COMPILER_ROW_V1", "declaration": "Zeta23.Fixture.constraint", "module": "Zeta23.Fixture",
            "kind": "THEOREM", "universe_parameters": [], "type_text": "forall {alpha : Type} [Inhabited alpha], True -> True",
            "type_expression": {"format": "LEAN_EXPR_DAG_V1", "root": "7", "nodes": nodes}, "outer_telescope": binders,
            "conclusion_text": "True", "type_constants": ["Inhabited", "True"],
            "value_constants": ["Classical.choice", "Fixture.proofHelper", "True.intro"], "structure_constants": [],
            "axioms": ["Classical.choice"]}


def protocol(row): return "OPICA3_ATLAS\t" + json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n"


def fixture_repo(repo):
    write(repo / "Zeta23/Fixture.lean", b"-- UNIT PROTOCOL FIXTURE, NOT A PROOF\n")
    write(repo / atlas.EXPORTER, b"-- UNIT EXPORTER SOURCE FIXTURE\n")
    write(repo / atlas.OVERLAY, {"unit_fixture": True})
    write(repo / atlas.SCHEMA, (REPO / atlas.SCHEMA).read_bytes())
    write(repo / atlas.ATLAS, b"")
    return {"reviews": {}, "connections": [], "source_only_review": {"status": "UNREVIEWED"}}


class AtlasCrosswalkTests(unittest.TestCase):
    def test_current_required_cohorts_and_priority_backlog_are_complete(self):
        overlay = atlas.load_overlay(REPO)
        queries = atlas.query_inventory(REPO, overlay)
        counts = {}
        for row in queries:
            for member in row["memberships"]: counts[member["cohort"]] = counts.get(member["cohort"], 0) + 1
        self.assertEqual({key: counts[key] for key in ("OPICA_ORIGINAL76", "OPICA_FOLLOWUP100", "OPICA_ROUND2_40", "OPICA_ROUND3_5")},
                         {"OPICA_ORIGINAL76": 76, "OPICA_FOLLOWUP100": 100, "OPICA_ROUND2_40": 40, "OPICA_ROUND3_5": 5})
        self.assertEqual(counts["UCDP_HISTORICAL216"], 216)
        self.assertEqual(counts["UCDP_CONTACT185"], 185)
        self.assertEqual(counts["UCDP_PRIORITY_TRIPLE18"], 18)
        self.assertEqual(counts["ROUND3_INDEPENDENT_CONSUMERS5"], 5)
        self.assertEqual(len(queries), len({row["declaration"] for row in queries}))

    def test_declaration_deduplication_retains_additional_membership(self):
        overlay = atlas.load_overlay(REPO)
        before = atlas.query_inventory(REPO, overlay)
        row = next(row for row in before if any(m["cohort"] == "OPICA_ORIGINAL76" for m in row["memberships"]))
        trial = copy.deepcopy(overlay)
        trial["support_declarations"].append({"declaration": row["declaration"], "module": row["module"],
            "source": row["source_path"], "reason": "EXTRA_UNIT_TEST_MEMBERSHIP"})
        after = atlas.query_inventory(REPO, trial)
        self.assertEqual(len(after), len(before))
        updated = next(r for r in after if r["declaration"] == row["declaration"])
        self.assertEqual(len(updated["memberships"]), len(row["memberships"]) + 1)
        trial["support_declarations"][-1]["module"] = "Zeta23.Other"
        trial["support_declarations"][-1]["source"] = "Zeta23/Other.lean"
        with self.assertRaises(atlas.InvalidAtlas): atlas.query_inventory(REPO, trial)

    def test_historical_raw_json_csv_hashes_are_preserved(self):
        overlay = atlas.load_overlay(REPO)
        for row in overlay["reference_inputs"]:
            self.assertEqual(atlas.digest(row["raw_utf8"].encode()), row["sha256"])
            self.assertEqual(row["authority"], "HISTORICAL_RESEARCH_INPUT_NOT_CURRENT_PROOF")
        self.assertFalse(overlay["source_only_review"]["all185_contacts_semantically_reviewed"])
        self.assertIn("NOT_EXHAUSTIVE", overlay["source_only_review"]["status"])

    def test_historical_and_binding_census_mutations_refused(self):
        original = atlas.read_json
        def changed(path, *args, **kwargs):
            value = original(path, *args, **kwargs)
            if str(path).replace("\\", "/").endswith("/opica/PUBLIC_ROOTS.json"):
                value["primary_roots"].pop()
            return value
        with patch.object(atlas, "read_json", side_effect=changed):
            with self.assertRaises(atlas.InvalidAtlas): atlas.query_inventory(REPO)


class AtlasCompilerProtocolTests(unittest.TestCase):
    def test_whole_output_kernel_zero_does_not_remove_transformed_component(self):
        # Exact self-adjoint 2x2, rank-one source defect. This is a generic
        # countermodel, not the canonical zeta source or an arithmetic sign.
        T, O, w = ((-1, -1), (-1, 0)), ((0, 0), (0, 1)), (1, 1)
        defect = tuple(tuple(O[i][j] - T[i][j] for j in range(2)) for i in range(2))
        mul = lambda A, x: tuple(sum(A[i][j] * x[j] for j in range(2)) for i in range(2))
        transformed, source = mul(T, w), mul(defect, w)
        whole = tuple(a + b for a, b in zip(transformed, source))
        self.assertEqual(defect, ((1, 1), (1, 1)))
        self.assertEqual(whole, mul(O, w))
        self.assertEqual(whole[0], 0)  # Kernel(O) is the first coordinate.
        self.assertNotEqual(source[0], 0)
        self.assertEqual(sum(w[i] * transformed[i] for i in range(2)), -3)

    def test_actual_type_dag_telescope_and_constant_channels_positive(self):
        row = atlas.parse_output(protocol(compiler_fixture()), query_fixture())[0]
        self.assertEqual(len(row["outer_telescope"]), 3)
        self.assertTrue(row["outer_telescope"][1]["typeclass_binder"])
        self.assertFalse(row["outer_telescope"][1]["domain_is_prop"])
        self.assertTrue(row["outer_telescope"][2]["domain_is_prop"])
        self.assertNotIn("Fixture.proofHelper", row["type_constants"])
        wrapped = compiler_fixture()
        wrapped["type_expression"]["nodes"].append(["mdata", [], "7"])
        wrapped["type_expression"]["root"] = "8"
        self.assertEqual(len(atlas.parse_output(protocol(wrapped), query_fixture())[0]["outer_telescope"]), 3)

    def test_prop_typeclass_hypothesis_keeps_both_classification_flags(self):
        row = compiler_fixture()
        row["type_expression"]["nodes"][0] = ["sort", ["zero"]]
        row["type_expression"]["nodes"][2] = ["const", name("Fact"), []]
        row["outer_telescope"][0]["domain_text"] = "Prop"
        row["outer_telescope"][1]["domain_text"] = "Fact alpha"
        row["type_text"] = "forall {alpha : Prop} [Fact alpha], True -> True"
        row["type_constants"] = ["Fact", "True"]
        row["outer_telescope"][1].update(domain_is_prop=True, class_name="Fact")
        parsed = atlas.parse_output(protocol(row), query_fixture())[0]
        self.assertTrue(parsed["outer_telescope"][1]["domain_is_prop"])
        self.assertTrue(parsed["outer_telescope"][1]["typeclass_binder"])

    def test_unknown_duplicate_missing_unsafe_kind_and_axiom_refused(self):
        for mode in ("unknown", "origin", "axiom", "kind", "bool_position", "bool_prop", "classflag", "binder_count", "loose_bvar", "extra_field"):
            with self.subTest(mode=mode):
                row = compiler_fixture()
                if mode == "unknown": row["declaration"] = "Zeta23.other"
                elif mode == "origin": row["module"] = "Zeta23.Other"
                elif mode == "axiom": row["axioms"] = ["sorryAx"]
                elif mode == "kind": row["kind"] = "AXIOM"
                elif mode == "bool_position": row["outer_telescope"][0]["position"] = False
                elif mode == "bool_prop": row["outer_telescope"][0]["domain_is_prop"] = 0
                elif mode == "classflag": row["outer_telescope"][0]["typeclass_binder"] = True
                elif mode == "binder_count": row["outer_telescope"].pop()
                elif mode == "loose_bvar": row["type_expression"]["nodes"][1][1] = "999"
                else: row["assumed_RH"] = True
                with self.assertRaises(ValueError): atlas.parse_output(protocol(row), query_fixture())
        with self.assertRaises(ValueError): atlas.parse_output(protocol(compiler_fixture()) * 2, query_fixture())
        with self.assertRaises(ValueError): atlas.parse_output("", query_fixture())

    def test_strict_json_rejects_duplicate_float_and_nonfinite_protocol_fields(self):
        raw = protocol(compiler_fixture())
        for trial in (raw.replace('"kind":"THEOREM"', '"kind":"THEOREM","kind":"AXIOM"'),
                      raw.replace('"position":0', '"position":0.0'),
                      raw.replace('"position":0', '"position":NaN')):
            with self.assertRaises(ValueError): atlas.parse_output(trial, query_fixture())

    def test_hypotheses_are_telescope_props_not_proof_dependencies(self):
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            overlay = fixture_repo(repo)
            with patch.object(atlas, "reference", side_effect=lambda _, kind: {"roots": []} if kind == "ROOTS216_JSON" else {"contacts": []}):
                rows = atlas.atlas_records(repo, query_fixture(), [compiler_fixture()], overlay)
            self.assertEqual([r["name"] for r in rows[0]["theorem_inputs"]], ["alpha", "inst", "h"])
            self.assertEqual([r["name"] for r in rows[0]["proposition_hypotheses"]], ["h"])
            self.assertEqual([r["name"] for r in rows[0]["data_and_typeclass_parameters"]], ["alpha", "inst"])
            self.assertIn("Fixture.proofHelper", rows[0]["proof_only_dependencies"])
            self.assertEqual(rows[0]["semantic_review"]["status"], "UNREVIEWED")
            self.assertFalse(rows[0]["semantic_exhaustion"])
            _, cio = atlas.runtime()
            schema = atlas.read_json(repo / atlas.SCHEMA)
            for mutation in ("extra", "path", "bytes", "claim", "hypothesis"):
                trial = copy.deepcopy(rows[0])
                if mutation == "extra": trial["invented_assumption"] = "Fixture.proofHelper"
                elif mutation == "path": trial["source"]["path"] = "../escape.lean"
                elif mutation == "bytes": trial["source"]["bytes"] = False
                elif mutation == "claim": trial["RH"] = "PROVED"
                else: trial["theorem_inputs"][0]["assumed_from_proof"] = True
                with self.subTest(mutation=mutation), self.assertRaises(ValueError): cio.validate_schema(trial, schema)

    def test_canonical_atlas_is_deduplicated_and_not_order_sensitive_json(self):
        rows = [{"declaration": "Zeta23.a", "value": {"b": 1, "a": 2}}]
        self.assertEqual(atlas.serialize_atlas(rows), atlas.serialize_atlas([{"value": {"a": 2, "b": 1}, "declaration": "Zeta23.a"}]))
        for trial in ([], rows + rows, [{"declaration": "Zeta23.z"}, {"declaration": "Zeta23.a"}]):
            with self.assertRaises(atlas.InvalidAtlas): atlas.serialize_atlas(trial)

    def test_constructor_fields_are_not_silently_relabelled_theorem_assumptions(self):
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            overlay = fixture_repo(repo)
            fact = compiler_fixture(); fact["kind"] = "CONSTRUCTOR"
            with patch.object(atlas, "reference", side_effect=lambda _, kind: {"roots": []} if kind == "ROOTS216_JSON" else {"contacts": []}):
                row = atlas.atlas_records(repo, query_fixture(), [fact], overlay)[0]
            self.assertEqual(row["theorem_inputs"], [])
            self.assertEqual([r["name"] for r in row["non_theorem_prop_arguments"]], ["h"])
            self.assertEqual(row["proof_only_dependencies"], [])
            self.assertIn("Fixture.proofHelper", row["implementation_only_dependencies"])
            self.assertEqual(row["scientific_status"], "COMPILED_DECLARATION_NOT_THEOREM")

    def test_path_and_evidence_budget_refusals(self):
        for name in ("../escape", "./x", "/absolute", "a//b", "a\\b", "C:/drive"):
            with self.assertRaises(atlas.InvalidAtlas): atlas.safe_relative(name)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); write(root / "input.json", b"12345")
            with self.assertRaises(atlas.InvalidAtlas): atlas.file_at(root, "input.json", 4)
            with patch.object(Path, "is_symlink", return_value=True):
                with self.assertRaises(atlas.InvalidAtlas): atlas.file_at(root, "input.json")
            with patch.dict(os.environ, {"LEAN_PATH": "/foreign/compiled/objects"}):
                with self.assertRaises(atlas.InvalidAtlas): atlas.capture(REPO, root / "out", 1)

    def capture_fixture(self, base):
        repo, output = base / "repo", base / "downloaded-capture"
        overlay = fixture_repo(repo)
        compiler, _ = atlas.runtime()
        queries = query_fixture(); fact = compiler_fixture()
        source = [{"path": "Zeta23/Fixture.lean", "mode": "100644", "git_blob": "0" * 40,
                   "bytes": (repo / "Zeta23/Fixture.lean").stat().st_size, "sha256": atlas.sha(repo / "Zeta23/Fixture.lean")}]
        env = {"lean_toolchain": "fixture", "mathlib_commit": "c" * 40}
        packages = [{"name": "fixture", "commit": "d" * 40}]
        write(output / "AtlasQuery.lean", atlas.render_driver(queries))
        write(output / "AtlasQuery.olean", b"UNIT PARSER FIXTURE, NOT A LEAN OBJECT")
        write(output / "source-manifest.json", source)
        producer = "/original-ci/atlas"
        recipes = [["lake", "env", "lean", "--version"],
                   ["lake", "build", "Zeta23.Fixture", "Zeta23.RHRC.OpicaRound3AtlasExport"],
                   ["lake", "env", "lean", "-R", producer, "-o", producer + "/AtlasQuery.olean", producer + "/AtlasQuery.lean"]]
        commands = []
        for label, recipe in zip(("version", "build", "export"), recipes):
            text = ("Lean (version 4.33.0-rc2, commit d8b18978322de05a8f3dba51ef03cf5461676c17)\n" if label == "version"
                    else protocol(fact) if label == "export" else "UNIT BUILD LOG\n")
            write(output / (label + ".stdout.log"), text.encode()); write(output / (label + ".stderr.log"), b"")
            commands.append({"argv": recipe, "returncode": 0, "working_tree_sha": "b" * 40,
                "stdout_sha256": atlas.sha(output / (label + ".stdout.log")), "stderr_sha256": atlas.sha(output / (label + ".stderr.log"))})
        receipt = {"schema": "OPICA3_ATLAS_CAPTURE_V1", "status": "PASS_SOURCE_BOUND_ATLAS_EXPORT",
            "checked_commit": "a" * 40, "checked_tree": "b" * 40, "source_manifest_sha256": compiler.compiler_canonical_sha256(source),
            "environment": env, "pinned_packages": packages, "build_mode": "WARM_NATIVE_CURRENT_ENVIRONMENT_EXPORT_NOT_COLD_PROOF_RECEIPT",
            "producer_root": producer, "commands": commands, "query_sha256": atlas.sha(output / "AtlasQuery.lean"),
            "exporter_sha256": atlas.sha(repo / atlas.EXPORTER), "overlay_sha256": atlas.sha(repo / atlas.OVERLAY),
            "schema_sha256": atlas.sha(repo / atlas.SCHEMA), "records": 1, "object_sha256": atlas.sha(output / "AtlasQuery.olean"),
            "parsed_protocol_sha256": compiler.compiler_canonical_sha256([fact]), **atlas.CAPS}
        write(output / "receipt.json", receipt)
        return repo, output, overlay, compiler, source, env, packages, queries

    def reparse_capture_fixture(self, fixture):
        repo, output, overlay, compiler, source, env, packages, queries = fixture
        with patch.object(atlas, "REPO", repo), patch.object(atlas, "load_overlay", return_value=overlay), \
             patch.object(atlas, "query_inventory", return_value=queries), \
             patch.object(atlas, "git", side_effect=lambda _, *args: "a" * 40 if args[-1] == "HEAD" else "b" * 40), \
             patch.object(atlas, "reference", side_effect=lambda _, kind: {"roots": []} if kind == "ROOTS216_JSON" else {"contacts": []}), \
             patch.object(compiler, "source_manifest", return_value=source), \
             patch.object(compiler, "validate_environment", return_value=env), \
             patch.object(compiler, "validate_packages", return_value=packages), \
             patch.dict(os.environ, {"REQUESTED_HEAD": "a" * 40}):
            return atlas.verify_atlas_capture(repo, output)

    def test_source_bound_capture_reparse_preserves_original_paths_on_relocation(self):
        with tempfile.TemporaryDirectory() as temporary:
            rows, report = self.reparse_capture_fixture(self.capture_fixture(Path(temporary)))
            self.assertEqual(report["status"], "PASS_REPARSED_CURRENT_ATLAS_CAPTURE")
            self.assertEqual(len(rows), 1)
            self.assertFalse(report["fresh_compiler_replay"])
            self.assertFalse(report["full_release_accepted"])

    def test_changed_capture_head_logs_object_recipe_and_booleans_refused(self):
        for mode in ("head", "object", "raw_log", "argv", "boolean_exit", "cold", "extra_file", "source_manifest"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                fixture = self.capture_fixture(Path(temporary)); repo, output = fixture[:2]
                receipt = atlas.read_json(output / "receipt.json")
                if mode == "head": receipt["checked_commit"] = "0" * 40
                elif mode == "object": write(output / "AtlasQuery.olean", b"REPLACED OBJECT")
                elif mode == "raw_log": write(output / "export.stdout.log", b"REPLACED RAW PROTOCOL")
                elif mode == "argv": receipt["commands"][2]["argv"][-1] = "/somewhere/Other.lean"
                elif mode == "boolean_exit": receipt["commands"][0]["returncode"] = False
                elif mode == "cold": receipt["build_mode"] = "COLD_FULL_PROOF"
                elif mode == "extra_file": write(output / "unlisted.json", {})
                else: write(output / "source-manifest.json", [])
                write(output / "receipt.json", receipt)
                with self.assertRaises(ValueError): self.reparse_capture_fixture(fixture)


if __name__ == "__main__": unittest.main()
