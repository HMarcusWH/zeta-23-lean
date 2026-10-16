"""Source-only RHKG file input and closure-integrity controls.

These are synthetic fail-closed regressions, not compiler theorem authority.
The full fresh inventory is checked separately by the guarded Lean generator.
"""
from __future__ import annotations

import json
import re
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import source_only_dependency_extract as export


def roots(n: int) -> list[dict]:
    return [
        {
            "resolved_full_name": f"Zeta23.CCM.Mock.t{i:04d}",
            "module": f"Zeta23.CCM.Mock.Module{i % 7}",
            "compiler_kind": "THEOREM",
            "source_declaration_id": f"synthetic:{i:04d}",
        }
        for i in range(n)
    ]


def record(name: str, module: str, kind="THEOREM", private="0") -> str:
    return "\t".join(["RHKG_DEP_DECL", name, module, kind, private])


def channel(source: str, kind: str, *targets: str) -> str:
    return "\t".join(["RHKG_DEP_CHANNEL", source, kind, *targets])


def complete_protocol(rows: list[dict]) -> str:
    declarations = [
        record(row["resolved_full_name"], row["module"])
        for row in rows
    ]
    channels = [
        channel(row["resolved_full_name"], kind)
        for row in rows for kind in ("TYPE", "VALUE", "STRUCTURE")
    ]
    return "\n".join(declarations + channels)


class FileBackedRootTransportTests(unittest.TestCase):
    def test_canonical_file_preserves_complete_inventory(self):
        for n in (1, 64, 65, 1360, 2766):
            with self.subTest(root_count=n):
                original = roots(n)
                payload = export.render_root_file(original)
                self.assertTrue(payload.endswith("\n"))
                self.assertEqual(payload.count("\n"), n)
                self.assertEqual(
                    payload.splitlines(),
                    [r["resolved_full_name"] + "\t" + r["module"]
                     for r in original],
                )
                self.assertEqual(len(set(payload.splitlines())), n)

    def test_driver_uses_single_small_file_backed_entrypoint(self):
        root_rows = roots(2766)
        path = Path("/tmp/source-only-test-Ω.tsv")
        driver = export.render_driver(path, root_rows)
        self.assertEqual(driver.count("run_cmd do"), 1)
        self.assertEqual(driver.count("Zeta23.RHRC.exportDependenciesFile"), 1)
        self.assertNotIn("roots := roots ++ #[", driver)
        self.assertNotIn("exportDependencies #[", driver)
        self.assertNotIn(root_rows[0]["resolved_full_name"], driver)
        self.assertEqual(driver.count("import Zeta23.RHRC.DeclarationDependencyExport"), 1)
        self.assertEqual(driver.count("import Zeta23.CCM.Mock.Module0\n"), 1)
        self.assertIn(json.dumps(str(path), ensure_ascii=False), driver)
        self.assertLess(len(driver.splitlines()), 20)

    def test_invalid_root_inventory_fails_closed(self):
        with self.assertRaisesRegex(SystemExit, "empty"):
            export.render_root_file([])
        dup = roots(2)
        dup[1]["resolved_full_name"] = dup[0]["resolved_full_name"]
        with self.assertRaisesRegex(SystemExit, "duplicate exact Lean"):
            export.render_root_file(dup)
        dup_id = roots(2)
        dup_id[1]["source_declaration_id"] = dup_id[0]["source_declaration_id"]
        with self.assertRaisesRegex(SystemExit, "duplicate source candidate"):
            export.render_root_file(dup_id)
        missing = roots(1)
        missing[0]["module"] = None
        with self.assertRaisesRegex(SystemExit, "missing"):
            export.render_root_file(missing)
        for field in ("resolved_full_name", "module", "source_declaration_id"):
            for injected in ("\n", "\r", "\t", "\x00"):
                with self.subTest(field=field, injected=repr(injected)):
                    tampered = roots(1)
                    tampered[0][field] += injected
                    with self.assertRaisesRegex(SystemExit, "control character"):
                        export.render_root_file(tampered)
        wrong_kind = roots(1)
        wrong_kind[0]["compiler_kind"] = "DEFINITION"
        with self.assertRaisesRegex(SystemExit, "non-theorem"):
            export.render_root_file(wrong_kind)
        wrong_module = roots(1)
        wrong_module[0]["module"] = "Mathlib.Other"
        with self.assertRaisesRegex(SystemExit, "audited source scope"):
            export.render_root_file(wrong_module)
        unsorted = list(reversed(roots(3)))
        with self.assertRaisesRegex(SystemExit, "canonical compiler-name ordering"):
            export.render_root_file(unsorted)


class CompilerProtocolIntegrityTests(unittest.TestCase):
    def test_every_root_and_channel_roundtrips(self):
        original = roots(12)
        out = export.parse_output(complete_protocol(original), original)
        self.assertEqual(len(out), len(original))
        self.assertEqual(
            {r["declaration"] for r in out},
            {r["resolved_full_name"] for r in original},
        )
        self.assertEqual(
            {r["source_candidate_id"] for r in out},
            {r["source_declaration_id"] for r in original},
        )
        self.assertTrue(all(r["graph_role"] == "SOURCE_ONLY_ROOT" for r in out))

    def test_local_dependencies_and_external_boundary(self):
        original = roots(1)
        root = original[0]["resolved_full_name"]
        helper = "Zeta23.CCM.Mock.helper"
        external = "Mathlib.Util.external"
        source = "\n".join([
            record(root, original[0]["module"]),
            record(helper, "Zeta23.CCM.Mock.Module0", "DEFINITION", "1"),
            record(external, "Mathlib.Util", "DEFINITION", "0"),
            channel(root, "TYPE", helper),
            channel(root, "VALUE", helper, external),
            channel(root, "STRUCTURE"),
            channel(helper, "TYPE"),
            channel(helper, "VALUE"),
            channel(helper, "STRUCTURE"),
        ])
        out = {
            r["declaration"]: r
            for r in export.parse_output(source, original)
        }
        self.assertEqual(out[root]["graph_role"], "SOURCE_ONLY_ROOT")
        self.assertEqual(out[helper]["graph_role"], "LOCAL_DEPENDENCY")
        self.assertEqual(out[external]["graph_role"], "EXTERNAL_BOUNDARY")
        deps = {d["constant"]: d for d in out[root]["dependencies"]}
        self.assertTrue(deps[helper]["used_in_type"])
        self.assertTrue(deps[helper]["used_in_value"])
        self.assertFalse(deps[helper]["used_in_structure"])
        self.assertTrue(deps[external]["used_in_value"])

    def test_missing_root_and_channel_rejected(self):
        original = roots(1)
        root = original[0]["resolved_full_name"]
        with self.assertRaisesRegex(SystemExit, "omitted"):
            export.parse_output("", original)
        full = complete_protocol(original)
        for kind in ("TYPE", "VALUE", "STRUCTURE"):
            with self.subTest(missing=kind):
                dropped = full.replace(channel(root, kind) + "\n", "")
                # The final STRUCTURE row has no trailing newline.
                if kind == "STRUCTURE":
                    dropped = dropped.replace(channel(root, kind), "")
                with self.assertRaisesRegex(SystemExit, "incomplete compiler dependency channels"):
                    export.parse_output(dropped, original)

    def test_forged_metadata_duplicate_channels_and_dangling_target(self):
        original = roots(1)
        root = original[0]["resolved_full_name"]
        full = complete_protocol(original)
        for altered in (
            full.replace(original[0]["module"], "Zeta23.CCM.Forged"),
            full.replace("\tTHEOREM\t0", "\tDEFINITION\t0"),
            full.replace("\tTHEOREM\t0", "\tTHEOREM\t1"),
        ):
            with self.assertRaisesRegex(SystemExit, "wrong module, kind or visibility"):
                export.parse_output(altered, original)
        with self.assertRaisesRegex(SystemExit, "duplicate dependency channel"):
            export.parse_output(full + "\n" + channel(root, "TYPE"), original)
        with self.assertRaisesRegex(SystemExit, "target lacks declaration"):
            export.parse_output(
                full.replace(channel(root, "TYPE"),
                             channel(root, "TYPE", "Zeta23.CCM.Unknown")),
                original,
            )
        with self.assertRaisesRegex(SystemExit, "inconsistent duplicate"):
            export.parse_output(
                full + "\n" + record(root, "Zeta23.CCM.Other"),
                original,
            )


if __name__ == "__main__":
    unittest.main()
