from __future__ import annotations

import random
import sys
import unittest
from pathlib import Path

GRAPH = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(GRAPH))

import build  # noqa: E402
import validate  # noqa: E402


def synthetic_relations(count: int) -> list[dict]:
    rows = [
        build.relation("USES_CONSTANT", f"rh:decl:A{i}", f"rh:decl:B{i % 7}", "LEAN_ENV_EXACT")
        for i in range(count)
    ]
    random.Random(285).shuffle(rows)
    return rows


class RelationShardLayoutTests(unittest.TestCase):
    def test_shard_paths_are_fixed_declared_and_built_by_graph_build(self):
        self.assertEqual(len(build.RELATION_SHARD_PATHS), 16)
        self.assertEqual(build.RELATION_SHARD_PATHS, sorted(build.RELATION_SHARD_PATHS))
        self.assertEqual(len(set(build.RELATION_SHARD_PATHS)), 16)
        for path in build.RELATION_SHARD_PATHS:
            self.assertTrue(path.startswith(build.RELATION_SHARD_DIR + "/relations-"))
            self.assertIn(path, build.DECLARED_GENERATED_PRODUCTS)
            self.assertEqual(
                build.GENERATED_PRODUCT_PRODUCER[path], "research/RHRC/graph/build.py"
            )
        self.assertNotIn(build.LEGACY_RELATIONS_PATH, build.ALL_DECLARED_GENERATED_PRODUCTS)

    def test_concatenated_shards_equal_single_sorted_stream(self):
        rows = synthetic_relations(500)
        shards = build.render_relation_shards(rows)
        self.assertEqual(list(shards), build.RELATION_SHARD_PATHS)
        self.assertEqual(b"".join(shards.values()), build._jsonl(rows))

    def test_every_shard_is_emitted_even_when_empty(self):
        shards = build.render_relation_shards(synthetic_relations(3))
        self.assertEqual(list(shards), build.RELATION_SHARD_PATHS)
        self.assertIn(b"", shards.values())

    def test_rows_land_in_the_shard_named_by_their_id(self):
        shards = build.render_relation_shards(synthetic_relations(200))
        parsed = [
            (path, validate.parse_jsonl(data.decode("utf-8"), path)) for path, data in shards.items()
        ]
        self.assertEqual(validate.relation_shard_row_errors(parsed), [])

    def test_malformed_relation_ids_are_rejected(self):
        good = build.relation("CONTAINS", "rh:a", "rh:b", "GIT_EXACT")["id"]
        self.assertEqual(build.relation_shard_key(good), good[len("rh:rel:")])
        for bad in ("rh:rel:", "rh:rel:" + "A" * 64, "rh:rel:" + "0" * 63, "rh:node:" + "0" * 64):
            with self.assertRaises(RuntimeError):
                build.relation_shard_key(bad)

    def test_row_check_rejects_misplaced_and_unordered_rows(self):
        rows = synthetic_relations(64)
        by_key: dict[str, list[dict]] = {key: [] for key in build.RELATION_SHARD_KEYS}
        for row in sorted(rows, key=lambda r: r["id"]):
            by_key[build.relation_shard_key(row["id"])].append(row)
        nonempty = next(key for key in build.RELATION_SHARD_KEYS if len(by_key[key]) >= 2)
        other = next(key for key in build.RELATION_SHARD_KEYS if key != nonempty)

        misplaced = {key: list(value) for key, value in by_key.items()}
        misplaced[other] = misplaced[other] + [misplaced[nonempty][0]]
        shards = [(path, misplaced[key]) for key, path in zip(build.RELATION_SHARD_KEYS, build.RELATION_SHARD_PATHS)]
        self.assertTrue(
            any("does not belong to shard" in e for e in validate.relation_shard_row_errors(shards))
        )

        unordered = {key: list(value) for key, value in by_key.items()}
        unordered[nonempty] = list(reversed(unordered[nonempty]))
        shards = [(path, unordered[key]) for key, path in zip(build.RELATION_SHARD_KEYS, build.RELATION_SHARD_PATHS)]
        self.assertTrue(
            any("not strictly increasing" in e for e in validate.relation_shard_row_errors(shards))
        )


if __name__ == "__main__":
    unittest.main()
