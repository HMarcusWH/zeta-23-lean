from __future__ import annotations

import hashlib
import importlib.util
import json
import random
import sys
import tempfile
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
# graph/build.py imports its sibling helper modules by name.
sys.path.insert(0, str(RHRC / "graph"))


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


shards = _load("rhrc_source_only_shards_test", RHRC / "integration" / "source_only_shards.py")
build = _load("rhrc_graph_build_for_shard_test", RHRC / "graph" / "build.py")


def synthetic_rows(count: int) -> list[dict]:
    rows = [
        {
            "declaration": f"Zeta23.Synthetic.decl{i:04d}",
            "dependencies": [{"constant": f"Dep{i % 5}", "used_in_type": True}],
            "graph_role": "LOCAL_DEPENDENCY",
        }
        for i in range(count)
    ]
    random.Random(285).shuffle(rows)
    return rows


def single_stream(rows: list[dict]) -> bytes:
    return "".join(
        shards.render_row(row) for row in sorted(rows, key=lambda r: r["declaration"])
    ).encode("utf-8")


def write_layout(repo: Path, rendered: dict[str, bytes]) -> None:
    for path, data in rendered.items():
        target = repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)


class SourceOnlyShardLayoutTests(unittest.TestCase):
    def test_shard_paths_are_fixed_and_declared_by_graph_build(self):
        self.assertEqual(len(shards.SHARD_PATHS), 16)
        self.assertEqual(len(set(shards.SHARD_PATHS)), 16)
        for path in shards.SHARD_PATHS:
            self.assertTrue(path.startswith(shards.SHARD_DIR + "/"))
            self.assertIn(path, build.DECLARED_INTEGRATION_GENERATED_PRODUCTS)
            self.assertEqual(
                build.GENERATED_PRODUCT_PRODUCER[path],
                "research/RHRC/integration/source_only_dependency_extract.py",
            )
        self.assertNotIn(shards.LEGACY_PATH, build.ALL_DECLARED_GENERATED_PRODUCTS)

    def test_merged_shards_reproduce_single_stream_and_digest(self):
        rows = synthetic_rows(400)
        rendered = shards.render_shards(rows)
        self.assertEqual(list(rendered), shards.SHARD_PATHS)
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            write_layout(repo, rendered)
            self.assertEqual(shards.shard_file_errors(repo), [])
            loaded = shards.load_rows(repo)
            self.assertEqual(loaded, sorted(rows, key=lambda r: r["declaration"]))
            self.assertEqual(
                shards.logical_sha256(repo), hashlib.sha256(single_stream(rows)).hexdigest()
            )

    def test_every_row_lands_in_its_key_shard(self):
        rendered = shards.render_shards(synthetic_rows(200))
        for key, path in zip(shards.SHARD_KEYS, shards.SHARD_PATHS):
            for line in rendered[path].decode("utf-8").splitlines():
                self.assertEqual(shards.shard_key(json.loads(line)["declaration"]), key)

    def test_layout_errors_are_reported(self):
        rendered = shards.render_shards(synthetic_rows(50))
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            write_layout(repo, rendered)
            (repo / shards.LEGACY_PATH).write_text("{}\n", encoding="utf-8")
            (repo / shards.SHARD_DIR / "stray.jsonl").write_text("", encoding="utf-8")
            (repo / shards.SHARD_PATHS[3]).unlink()
            errors = " ".join(shards.shard_file_errors(repo))
            self.assertIn("legacy monolithic receipt", errors)
            self.assertIn("stray.jsonl", errors)
            self.assertIn(shards.SHARD_PATHS[3], errors)
            with self.assertRaises(SystemExit):
                shards.load_rows(repo)

    def test_misplaced_or_unsorted_rows_are_rejected(self):
        rows = synthetic_rows(60)
        rendered = shards.render_shards(rows)
        nonempty = [path for path in shards.SHARD_PATHS if rendered[path].count(b"\n") >= 2]
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            swapped = dict(rendered)
            lines = swapped[nonempty[0]].splitlines(keepends=True)
            swapped[nonempty[0]] = b"".join(reversed(lines))
            write_layout(repo, swapped)
            with self.assertRaises(SystemExit):
                shards.load_rows(repo)
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            moved = dict(rendered)
            first, second = nonempty[0], nonempty[1]
            moved[second] = moved[first].splitlines(keepends=True)[0] + moved[second]
            write_layout(repo, moved)
            with self.assertRaises(SystemExit):
                shards.load_rows(repo)


if __name__ == "__main__":
    unittest.main()
