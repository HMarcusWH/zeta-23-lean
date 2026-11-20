import copy
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from research.RHRC.integration.opica_round6.constraint_graph import HISTORICAL, audit_group, audit_input, build, check_axioms, check_historical, check_rhkg, encoding, explain


def record(key, status, **extras):
    return dict(id=key, status=status, sources=["proof.lean"], declarations=[], depends_on=[],
                statement="finite graph test", **extras)


class ConstraintGraphTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "proof.lean").write_text(
            "namespace Zeta23.Demo\n/-- theorem fake : True := trivial -/\ntheorem verified : True := trivial\nend Zeta23.Demo\n",
            encoding="utf-8")
        self.rows = [record("formal", "PROVED"), record("unpaid", "OPEN"), record("alternative", "OPEN"),
                     record("context", "OPEN"), record("method", "DERIVED"), record("result", "OPEN")]
        self.rows[0]["declarations"] = ["Zeta23.Demo.verified"]
        self.rows[4].update(depends_on=["formal", "unpaid"], alternatives=["alternative"], context=["context"])
        self.rows[5]["depends_on"] = ["method"]
        self.catalog = dict(schema="OPICA_ROUND6_CONSTRAINTS_V1", RH="OPEN", Step4="OPEN", constraints=self.rows)

    def test_frontier_and_canonical_join(self):
        graph = build(self.catalog, self.root)
        self.assertEqual(graph["input_branch_coverage"]["result"],
                         {"open_on_joint_edges_only": ["unpaid"], "open_on_any_input_branch": ["alternative", "unpaid"],
                          "open_in_every_catalog_route": ["alternative", "unpaid"]})
        self.assertIn("context", graph["open_entries"])
        anchor = graph["source_only_declaration_anchors"]["Zeta23.Demo.verified"]
        self.assertEqual(anchor["line"], 3)
        (self.root / "repository_files.jsonl").write_text('{"id":"rh:file:proof.lean"}\n', encoding="utf-8")
        row = dict(id=anchor["rhkg_source_id"], path="proof.lean", module="proof", line=3, command_kind="THEOREM")
        declarations = self.root / "lean_source_declarations.jsonl"
        declarations.write_text(json.dumps(row)+"\n", encoding="utf-8")
        check_rhkg(graph, self.root)
        row["line"] += 1
        declarations.write_text(json.dumps(row)+"\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "named-source"):
            check_rhkg(graph, self.root)
        self.assertEqual(encoding(graph), encoding(build(copy.deepcopy(self.catalog), self.root)))

    def test_shared_open_input_survives_alternatives(self):
        self.rows[4].update(depends_on=["unpaid"], alternatives=[])
        other = record("other", "DERIVED")
        other["depends_on"] = ["unpaid", "alternative"]
        self.rows.append(other)
        self.rows[5].update(depends_on=[], alternatives=["method", "other"])
        view = build(self.catalog, self.root)["input_branch_coverage"]["result"]
        self.assertEqual(view["open_in_every_catalog_route"], ["unpaid"])
        self.assertEqual(view["open_on_joint_edges_only"], [])
        self.assertEqual(view["open_on_any_input_branch"], ["alternative", "unpaid"])
        routes = explain(build(self.catalog, self.root), "result")["shortest_open_routes"]
        self.assertNotIn("context", routes)
        self.assertEqual([edge["kind"] for edge in routes["unpaid"]], ["JOINT_INPUT", "ALTERNATIVE_INPUT"])

    def test_rejected_catalog_changes(self):
        for key, field, value in [(0, "declarations", []), (0, "declarations", ["Zeta23.Demo.fake"]),
                                  (1, "sources", ["../outside"]), (1, "id", "formal"),
                                  (2, "depends_on", ["result"]), (3, "context", ["missing"]),
                                  (4, "alternatives", ["unpaid"]), (5, "status", "RH_PROVED")]:
            with self.subTest(key=key, field=field):
                c = copy.deepcopy(self.catalog)
                c["constraints"][key][field] = value
                with self.assertRaises(ValueError):
                    build(c, self.root)

    def test_compiler_audit(self):
        graph = build(self.catalog, self.root)
        good = "'Zeta23.Demo.verified' depends on axioms: [propext,\n Classical.choice]"
        self.assertEqual(check_axioms(graph, good)["Zeta23.Demo.verified"], ["Classical.choice", "propext"])
        for bad in [good+good, "", good.replace("propext","sorryAx")]:
            with self.assertRaises(ValueError):
                check_axioms(graph, bad)

    def test_historical_disposition_is_context_only(self):
        self.rows[3].update(status="SOURCE_RECORD", source_disposition="REFUTED_CONTROL",
                            closing_relevance="NONE", parameter_order=["epsilon", "horizon"])
        graph = build(self.catalog, self.root)
        self.assertEqual(graph["nodes"]["context"]["source_disposition"], "REFUTED_CONTROL")
        for field in ("depends_on", "alternatives"):
            self.rows[5][field] = ["context"]
            with self.assertRaisesRegex(ValueError, "historical"):
                build(self.catalog, self.root)
            self.rows[5][field] = []

    def test_historical_fidelity(self):
        old = {"constraints": [{"id": "CR01", "name": "Evidence", "statement": "Finite.",
                                "native_validity": "CERTIFIED", "closing_relevance": "SUPPORT",
                                "parameter_order": "cut first"}]}
        row = {"status": "SOURCE_RECORD", "source_disposition": "CERTIFIED", "closing_relevance": "SUPPORT",
               "parameter_order": "cut first", "statement": "Evidence. Finite.", "source_files": ["rh:file:" + HISTORICAL]}
        g = {"nodes": {"CR01": row}}
        check_historical(g, old)
        with self.assertRaisesRegex(ValueError, "coverage"):
            check_historical({"nodes": {}}, old)
        row["parameter_order"] = "cut last"
        with self.assertRaisesRegex(ValueError, "differs"):
            check_historical(g, old)

    def test_opposed_product_preserves_both_open_inputs(self):
        package = Path(__file__).resolve().parent
        catalog = json.loads((package / "CONSTRAINTS.json").read_bytes())
        graph = build(catalog, package.parents[3])
        nodes = graph["nodes"]
        route = "P303_OPPOSED_PRODUCT_ROUTE"
        upper = "P303_OPPOSED_PRODUCT_UPPER"
        validation = "PAPER_ROUTE_VALIDATION"
        self.assertEqual(set(explain(graph, route)["open_in_every_catalog_route"]),
                         {upper, validation})
        self.assertEqual(set(explain(graph, "SURVIVOR_ROUTE")["open_in_every_catalog_route"]),
                         {"ACTUAL_UPPER", validation})
        self.assertEqual(nodes[upper]["depends_on"] + nodes[upper]["alternatives"], [])
        self.assertIn("P303_PREDICTOR_REMAINDER", nodes[upper]["context"])
        for target in ("STEP4", "RH", route, upper, validation):
            self.assertEqual(nodes[target]["status"], "OPEN")
        steps = explain(graph, "STEP4")["shortest_open_routes"][upper]
        self.assertEqual([(step["from"], step["kind"], step["to"]) for step in steps],
                         [(upper, "JOINT_INPUT", route), (route, "ALTERNATIVE_INPUT", "STEP4")])
        algebra = nodes["P303_DEFICIT_ALGEBRA"]
        module = "Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct."
        self.assertEqual(algebra["status"], "PROVED")
        self.assertEqual(set(algebra["declarations"]), {module + name for name in
                         ("quadrant_remainder", "weighted_absolute_remainder", "forced_coefficient")})
        self.assertEqual(nodes["P303_DEFICIT_PRODUCT"]["status"], "DERIVED")
        self.assertIn("P303_DEFICIT_ALGEBRA", nodes["P303_DEFICIT_PRODUCT"]["depends_on"])

    def test_stale_finite_replay_cannot_export(self):
        fixtures = Path(__file__).resolve().parent / "evidence" / "step4-parity-deficit-2026-11-20"
        for name in ("receipt.py", "check_divisor_halves.py"):
            shutil.copyfile(fixtures / name, self.root / name)
        (self.root / "DIVISOR_HALVES_EXACT.json").write_bytes(b'{}\n')
        output = self.root / "export.json"
        result = subprocess.run(
            [sys.executable, "-O", "-B", str(self.root / "check_divisor_halves.py"),
             "--output", str(output)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Finite replay differs", result.stderr)
        self.assertFalse(output.exists())

    def test_nested_cut_frontier_and_prior_graph(self):
        package = Path(__file__).resolve().parent
        graph = build(json.loads((package / "CONSTRAINTS.json").read_bytes()), package.parents[3])
        nodes = graph["nodes"]
        route = "N20_NESTED_ROUTE"
        upper = "N20_JOINT_ARITHMETIC_UPPER"
        formal = "PAPER_ROUTE_VALIDATION"
        self.assertEqual(explain(graph, route)["open_in_every_catalog_route"], [upper, formal])
        self.assertEqual(nodes[upper]["depends_on"] + nodes[upper]["alternatives"], [])
        self.assertIn("N20_LOCAL_PRIME_GRAPH_CUT", nodes[route]["depends_on"])
        self.assertIn("N20_RAW_SPARSE_SECTOR", nodes["N20_LOCAL_PRIME_GRAPH_CUT"]["depends_on"])
        self.assertIn("N20_LOCAL_PRIME_GRAPH_CUT", nodes[upper]["context"])
        self.assertNotIn("N20_PAID_PRIME_GRAPHS", nodes["N20_LOCAL_PRIME_GRAPH_CUT"]["depends_on"])
        self.assertNotIn("N20_PAID_PRIME_GRAPHS", nodes["N20_SHIFTED_RETIREMENT"]["depends_on"])
        for name in (route, upper, formal, "STEP4", "RH"):
            self.assertEqual(nodes[name]["status"], "OPEN")
        for edge in graph["edges"]:
            if edge["from"].startswith("N20_") and nodes[edge["from"]]["status"] in {"SOURCE_RECORD", "EXPERIMENTAL_SIGNAL"}:
                self.assertEqual(edge["kind"], "CONTEXT_ONLY")

        # a6a001fd issued the original 190 entries, 168 edges, and 56 declaration anchors.
        previous = {k: copy.deepcopy(v) for k, v in nodes.items() if not k.startswith("N20_")}
        previous["STEP4"]["alternatives"].remove(route)
        edges = [e for e in graph["edges"] if e["from"] in previous and e["to"] in previous]
        anchors = graph["source_only_declaration_anchors"]
        old_anchors = {name: anchors[name] for node in previous.values() for name in node["declarations"]}
        self.assertEqual((len(previous), len(edges), len(old_anchors)), (190, 168, 56))
        old = {"nodes": previous, "edges": edges, "anchors": old_anchors}
        self.assertEqual(sha256(encoding(old)).hexdigest(),
                         "acec50d94e3b1ca7dd8a2172103d348c1f05ccc78522989ebb47cceee26a3b71")

        fresh = set(anchors) - set(old_anchors)
        formal_rows = ("N20_FINITE_CELL_BRACKET", "N20_FINITE_SELECTOR_COST",
                       "N20_FINITE_POLARITY_COST", "N20_FINITE_STOPPING")
        self.assertEqual(fresh, {name for k in formal_rows for name in nodes[k]["declarations"]})
        self.assertEqual(len(fresh), 23)
        self.assertTrue(all(nodes[k]["status"] == "PROVED" for k in formal_rows))
        self.assertTrue(all(nodes[k]["status"] == "DERIVED" for k in
                            ("N20_DETECTOR_PATH", "N20_TOTAL_CUT_DETECTOR", "N20_LOCAL_PRIME_GRAPH_CUT")))

    def test_concrete_geometry_readback_keeps_finite_sets_symbolic(self):
        package = Path(__file__).resolve().parent
        graph = build(json.loads((package / "CONSTRAINTS.json").read_bytes()), package.parents[3])
        prefix = "Zeta23.OPICARound6.PrimeFactorPaths."
        witness = prefix + "NativeGeometry.mersenne_whole_base"
        attr = "attribute [local irreducible] " + prefix + "NativeCells.terminalLabels " + prefix + "NativeCells.wholeCoarseKeys"
        for group in ("all", "round6", "prior-parity", "other-history"):
            program = audit_input(graph, group)
            selected = audit_group(graph, group)
            self.assertEqual(program.count("#print axioms "), len(selected))
            self.assertEqual(program.count("#check "), len(selected))
            self.assertEqual(program.count("env.getModuleIdxFor?"), len(selected))
            if group in ("all", "round6"):
                self.assertIn(witness, selected)
                self.assertEqual(program.count(attr), 1)
                self.assertLess(program.index(attr), program.index("#check " + witness))
            else:
                self.assertNotIn(witness, selected)
                self.assertNotIn(attr, program)

    def test_stale_nested_replay_cannot_export(self):
        fixtures = Path(__file__).resolve().parent / "evidence" / "step4-nested-cuts-2026-11-20"
        for name in ("finite_replay.py", "check_divisor_spacing.py"):
            shutil.copyfile(fixtures / name, self.root / name)
        (self.root / "DIVISOR_SPACING_CHECK.json").write_bytes(b"{}\n")
        output = self.root / "export.json"
        result = subprocess.run(
            [sys.executable, "-B", "-O", str(self.root / "check_divisor_spacing.py"),
             "--output", str(output)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Finite replay differs", result.stderr)
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
