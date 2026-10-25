from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import random
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC / "graph"))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


shards = load("registered_shards_tests", RHRC / "integration/registered_dependency_shards.py")
extract = load("registered_extract_tests", RHRC / "tools/lean_dependency_extract.py")
build = load("registered_build_tests", RHRC / "graph/build.py")
query = load("registered_query_tests", RHRC / "tools/query_dependencies.py")


def fixture_rows(count=80):
    names = [f"Zeta23.Synthetic.d{i:04d}" for i in range(count)]
    rows = [{"schema_version": shards.ROW_SCHEMA, "declaration": name,
        "module": "Zeta23.Synthetic", "repository_scope": "LOCAL",
        "graph_role": "LOCAL_DEPENDENCY", "declaration_kind": "THEOREM",
        "private_or_internal": bool(index % 2), "dependencies": [
            {"constant": target, "used_in_type": bool(bits & 1),
             "used_in_value": bool(bits & 2), "used_in_structure": bool(bits & 4)}
            for bits, target in enumerate(names[:7], 1)]}
        for index, name in enumerate(names)]
    random.Random(294).shuffle(rows)
    return rows


def canonical(rows):
    return "".join(shards.render_row(row) for row in sorted(rows, key=lambda r: r["declaration"])).encode()


class RegisteredDependencyStorageTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        self.rows = fixture_rows()
        self.rendered = shards.write_rows(self.rows, self.repo)

    def index(self):
        return json.loads((self.repo / shards.INDEX_PATH).read_bytes())

    def write_index(self, index):
        (self.repo / shards.INDEX_PATH).write_text(json.dumps(index), encoding="utf-8")

    def rebind_shard(self, path, data):
        (self.repo / path).write_bytes(data)
        index = self.index()
        meta = next(row for row in index["shards"] if row["path"] == path)
        meta.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest(), declaration_count=data.count(b"\n"))
        self.write_index(index)

    def assert_rejected(self):
        with self.assertRaises((ValueError, OSError)):
            shards.load_rows(self.repo)

    def test_fixed16_paths_and_original_index_are_explicit(self):
        self.assertEqual(len(shards.SHARD_PATHS), 16)
        self.assertEqual(len(set(shards.SHARD_PATHS)), 16)
        self.assertEqual(shards.INDEX_PATH, "research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl")
        self.assertLess(len(self.rendered[shards.INDEX_PATH]), 10000)
        for path in shards.SHARD_PATHS:
            self.assertIn(path, build.ALL_DECLARED_GENERATED_PRODUCTS)
            self.assertEqual(build.GENERATED_PRODUCT_PRODUCER[path], "research/RHRC/tools/lean_dependency_extract.py")

    def test_lossless_global_merge_preserves_every_field_and_flag(self):
        loaded = shards.load_rows(self.repo)
        self.assertEqual(loaded, sorted(self.rows, key=lambda r: r["declaration"]))
        self.assertEqual(canonical(loaded), extract.render_receipt(loaded))
        self.assertEqual(shards.logical_sha256(self.repo), hashlib.sha256(canonical(self.rows)).hexdigest())
        self.assertEqual(self.index()["logical_bytes"], len(canonical(self.rows)))
        self.assertEqual({tuple(dep[key] for key in ("used_in_type", "used_in_value", "used_in_structure"))
            for row in loaded for dep in row["dependencies"]},
            {(bool(n & 1), bool(n & 2), bool(n & 4)) for n in range(1, 8)})

    def test_render_is_deterministic_under_input_permutation(self):
        self.assertEqual(self.rendered, shards.render_storage(list(reversed(self.rows))))
        self.assertEqual(shards.shard_file_errors(self.repo), [])
        shards.check_storage(self.rendered, self.repo)

    def test_empty_storage_still_contains_all16_shards(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp); rendered = shards.write_rows([], repo)
            self.assertEqual(len(rendered), 17)
            self.assertTrue(all(rendered[path] == b"" for path in shards.SHARD_PATHS))
            self.assertEqual(shards.load_rows(repo), [])
            self.assertEqual(shards.logical_sha256(repo), hashlib.sha256(b"").hexdigest())

    def test_legacy_and_indexed_data_and_consumer_apis_are_identical(self):
        with tempfile.TemporaryDirectory() as tmp:
            legacy = Path(tmp); target = legacy / shards.INDEX_PATH
            target.parent.mkdir(parents=True); target.write_bytes(canonical(self.rows))
            self.assertEqual(shards.load_rows(legacy), shards.load_rows(self.repo))
            self.assertEqual(shards.logical_sha256(legacy), shards.logical_sha256(self.repo))
            with patch.object(build, "REPO", legacy):
                old = build.load_compiler_dependency_receipt()
            with patch.object(build, "REPO", self.repo):
                self.assertEqual(build.load_compiler_dependency_receipt(), old)
            with patch.object(query, "ROOT", self.repo / "research/RHRC"):
                self.assertEqual(query.load_compiler_receipt(), old)

    def test_single_legacy_row_and_unicode_declarations(self):
        row = fixture_rows(7)[0]; row["declaration"] = "Zeta23.Συνάρτηση.σ"
        data = canonical([row])
        self.assertEqual(shards.load_from_reader(lambda _: data), [row])
        self.assertEqual(shards.shard_key(row["declaration"]), hashlib.sha256(row["declaration"].encode()).hexdigest()[0])

    def test_legacy_duplicate_and_unsorted_declarations_reject(self):
        ordered = sorted(self.rows, key=lambda r: r["declaration"])
        for rows in [ordered + [ordered[-1]], list(reversed(ordered))]:
            data = "".join(shards.render_row(row) for row in rows).encode()
            with self.subTest(case=rows[-1]["declaration"]), self.assertRaises(ValueError):
                shards.load_from_reader(lambda _: data)

    def test_missing_and_extra_shards_reject(self):
        missing = self.repo / shards.SHARD_PATHS[0]; saved = missing.read_bytes(); missing.unlink()
        self.assert_rejected(); missing.write_bytes(saved)
        extra = self.repo / shards.SHARD_DIR / "unexpected.jsonl"; extra.write_bytes(b"")
        self.assert_rejected()
        with self.assertRaises(ValueError):
            shards.write_rows(self.rows, self.repo)

    def test_shard_tampering_is_rejected_before_json_is_trusted(self):
        path = next(path for path in shards.SHARD_PATHS if self.rendered[path])
        (self.repo / path).write_bytes(self.rendered[path].replace(b"THEOREM", b"ALTERED", 1))
        self.assert_rejected()

    def test_forged_hash_byte_and_row_counts_reject(self):
        original = self.index()
        for field, value in [("sha256", "0" * 64), ("bytes", 0), ("declaration_count", 999), ("bytes", True)]:
            index = json.loads(json.dumps(original)); index["shards"][0][field] = value
            self.write_index(index)
            with self.subTest(field=field): self.assert_rejected()

    def test_wrong_index_paths_duplicates_and_order_reject(self):
        original = self.index()
        for change in [lambda x: x["shards"].reverse(),
                       lambda x: x["shards"].__setitem__(1, x["shards"][0]),
                       lambda x: x["shards"][0].update(path="../escape.jsonl")]:
            index = json.loads(json.dumps(original)); change(index); self.write_index(index)
            self.assert_rejected()

    def test_rebound_wrong_shard_membership_rejects(self):
        first, second = [path for path in shards.SHARD_PATHS if self.rendered[path]][:2]
        self.rebind_shard(first, self.rendered[second]); self.rebind_shard(second, self.rendered[first])
        self.assert_rejected()

    def test_rebound_unsorted_and_duplicate_rows_reject(self):
        path = next(path for path in shards.SHARD_PATHS if self.rendered[path].count(b"\n") > 1)
        lines = self.rendered[path].splitlines(keepends=True)
        for data in [b"".join(reversed(lines)), b"".join(lines + [lines[-1]])]:
            self.rebind_shard(path, data); self.assert_rejected()

    def test_rebound_noncanonical_shard_serialization_rejects(self):
        path = next(path for path in shards.SHARD_PATHS if self.rendered[path])
        rows = [json.loads(line) for line in self.rendered[path].splitlines()]
        self.rebind_shard(path, ("\n".join(json.dumps(row) for row in rows) + "\n").encode())
        self.assert_rejected()

    def test_logical_digest_bytes_and_total_count_cannot_be_forged(self):
        original = self.index()
        for field, value in [("logical_sha256", "0" * 64), ("logical_bytes", 1), ("declaration_count", 1)]:
            index = json.loads(json.dumps(original)); index[field] = value; self.write_index(index)
            with self.subTest(field=field): self.assert_rejected()

    def test_malformed_or_unknown_index_never_falls_back_to_legacy(self):
        original = self.index()
        for data in [b'{"schema":"BROKEN"}\n', b'{"schema":',
                     json.dumps({**original, "schema": "UNKNOWN_VERSION"}).encode(),
                     json.dumps(original).encode() + b"\n" + canonical(self.rows)]:
            (self.repo / shards.INDEX_PATH).write_bytes(data); self.assert_rejected()

    def test_duplicate_json_keys_are_rejected_in_index_legacy_and_shards(self):
        data = json.dumps(self.index()).encode().replace(b'{', b'{"schema":"FORGED",', 1)
        (self.repo / shards.INDEX_PATH).write_bytes(data); self.assert_rejected()
        row = sorted(self.rows, key=lambda r: r["declaration"])[0]
        legacy = canonical([row]).replace(b'{', b'{"declaration":"FORGED",', 1)
        with self.assertRaises(ValueError): shards.load_from_reader(lambda _: legacy)
        for path, payload in self.rendered.items(): (self.repo / path).write_bytes(payload)
        path = next(path for path in shards.SHARD_PATHS if self.rendered[path])
        self.rebind_shard(path, self.rendered[path].replace(b'{', b'{"declaration":"FORGED",', 1))
        self.assert_rejected()

    def test_channel_flags_and_schema_cannot_be_changed_by_storage(self):
        row = fixture_rows(7)[0]
        for mutate in [lambda x: x.update(schema_version="0.3"),
                       lambda x: x["dependencies"][0].update(used_in_type=1),
                       lambda x: x["dependencies"][0].update(used_in_type=False, used_in_value=False, used_in_structure=False)]:
            changed = json.loads(json.dumps(row)); mutate(changed)
            with self.assertRaises(ValueError): shards.render_storage([changed])

    def test_immutable_reader_verifies_same_index_and_shard_bytes(self):
        self.assertEqual(shards.load_from_reader(self.rendered.__getitem__), shards.load_rows(self.repo))
        tampered = dict(self.rendered); tampered[shards.SHARD_PATHS[0]] += b"\n"
        with self.assertRaises(ValueError): shards.load_from_reader(tampered.__getitem__)

    def test_fresh_compiler_check_rejects_even_self_consistent_changed_storage(self):
        changed = json.loads(json.dumps(self.rows)); changed[0]["private_or_internal"] = not changed[0]["private_or_internal"]
        shards.write_rows(changed, self.repo)
        self.assertEqual(shards.load_rows(self.repo), sorted(changed, key=lambda r: r["declaration"]))
        with self.assertRaises(ValueError): shards.check_storage(self.rendered, self.repo)

    def test_original_wire_parser_and_render_api_preserve_all3_channels(self):
        roots = [{"id": "claim:test", "theorem": "Zeta23.Test.root"}]
        wire = "RHKG_DEP_DECL\tZeta23.Test.root\tZeta23.Test\tTHEOREM\t0\n"
        wire += "RHKG_DEP_CHANNEL\tZeta23.Test.root\tTYPE\tZeta23.Test.root\n"
        wire += "RHKG_DEP_CHANNEL\tZeta23.Test.root\tVALUE\tZeta23.Test.root\n"
        wire += "RHKG_DEP_CHANNEL\tZeta23.Test.root\tSTRUCTURE\tZeta23.Test.root\n"
        rows = extract.parse_output(wire, roots)
        self.assertEqual(rows[0]["dependencies"], [{"constant": "Zeta23.Test.root",
            "used_in_type": True, "used_in_value": True, "used_in_structure": True}])
        rendered = shards.render_storage(rows)
        self.assertEqual(canonical(shards.load_from_reader(rendered.__getitem__)), extract.render_receipt(rows))
        with tempfile.TemporaryDirectory() as tmp, patch.object(extract, "REPO", Path(tmp)), \
             patch.object(extract, "load_roots", return_value=roots), patch.object(extract, "run_lean", return_value=wire):
            for argument in ["--write", "--check"]:
                with patch.object(sys, "argv", ["lean_dependency_extract.py", argument]), contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(extract.main(), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
