"""Fail-closed classification regression for the PR292 historical-review inputs.

Historical compiler logs, detached Lean check snippets, and frozen input archives
are evidence/fixtures, not promoted Lean theorem roots. This test does not run
the historical files and never grants mathematical authority.
"""
from __future__ import annotations

import re
import sys
import unittest
from collections import Counter
from pathlib import Path

GRAPH = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(GRAPH))

import build  # noqa: E402


# The five additions classify exactly 160 formerly unknown files in the
# inspected PR292 source tree. Future explicitly tracked files may increase
# these counts, but previously classified files must never change class/zone.
RULE_SPECS = {
    "post290_review_git_attributes": ("BUILD_CONFIGURATION", "AUDIT_ONLY", 2),
    "post290_review_compiler_receipts": ("RESEARCH_RECEIPT", "AUDIT_ONLY", 146),
    "post290_archived_lean_review_fixtures": ("RESEARCH_FIXTURE", "AUDIT_ONLY", 7),
    "post290_source_packet_archives": ("RESEARCH_FIXTURE", "RESEARCH_ONLY", 4),
    "post290_k3_checkpoint_script": ("RESEARCH_EXECUTABLE", "RESEARCH_ONLY", 1),
}

HISTORICAL_LEAN_ROOT = (
    "research/RHRC/integration/post290/"
    "review_execution_2026-10-14/local_components/"
)
KNOWN_EXAMPLES = {
    "research/RHRC/integration/post290/review_2026-10-14/.gitattributes":
        "post290_review_git_attributes",
    "research/RHRC/integration/post290/review_execution_2026-10-14/.gitattributes":
        "post290_review_git_attributes",
    "research/RHRC/integration/post290/review_2026-10-14/"
    "compiler_logs/Zeta23/CCM/CanonicalDeepThresholdGap.log":
        "post290_review_compiler_receipts",
    HISTORICAL_LEAN_ROOT + "bounds/BoundsTypedCheck.lean":
        "post290_archived_lean_review_fixtures",
    "research/RHRC/integration/post290/spec/inputs/"
    "ABC_Step4_Research_Package_2026-10-13(1).zip":
        "post290_source_packet_archives",
    "research/RHRC/routes/R003_ccm_bridge/post290/k3_checkpoint_upload.cjs":
        "post290_k3_checkpoint_script",
}


class Post292HistoricalFileClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.contract = build.load_classification_contract()
        cls.tracked = build.tracked_files()
        cls.original_contract = {
            **cls.contract,
            "rules": [
                rule for rule in cls.contract["rules"]
                if rule["id"] not in RULE_SPECS
            ],
        }

    def test_rule_identifiers_schema_and_narrow_precedence(self) -> None:
        rules = self.contract["rules"]
        ids = [rule["id"] for rule in rules]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual(set(ids[:5]), set(RULE_SPECS))
        self.assertEqual(self.contract["unknown_class"], "UNKNOWN_FILE_CLASS")
        self.assertEqual(self.contract["unknown_trust_zone"], "UNKNOWN")
        for rule in rules:
            re.compile(rule["pattern"])
            self.assertIn(rule["file_class"], self.contract["classes"])
            self.assertIn(rule["trust_zone"], self.contract["trust_zones"])
        for rid, (file_class, trust_zone, _) in RULE_SPECS.items():
            matches = [r for r in rules if r["id"] == rid]
            self.assertEqual(len(matches), 1)
            self.assertEqual(
                (matches[0]["file_class"], matches[0]["trust_zone"]),
                (file_class, trust_zone),
            )

    def test_full_tracked_census_preserves_existing_assignments(self) -> None:
        self.assertEqual(len(self.tracked), len(set(self.tracked)))
        self.assertGreaterEqual(len(self.tracked), 2310)
        baseline_unknown = []
        still_unknown = []
        previous_classification_changed = []
        newly_classified = Counter()
        for path in self.tracked:
            old = build.classify(path, self.original_contract)
            new = build.classify(path, self.contract)
            if new[0] == self.contract["unknown_class"]:
                still_unknown.append(path)
            if old[0] != self.contract["unknown_class"]:
                if old != new:
                    previous_classification_changed.append((path, old, new))
            else:
                baseline_unknown.append(path)
                self.assertIn(new[2], RULE_SPECS, path)
                expected_class, expected_zone, _ = RULE_SPECS[new[2]]
                self.assertEqual((new[0], new[1]), (expected_class, expected_zone))
                newly_classified[new[2]] += 1

        self.assertEqual(still_unknown, [])
        self.assertEqual(previous_classification_changed, [])
        self.assertGreaterEqual(len(baseline_unknown), 160)
        self.assertEqual(set(newly_classified), set(RULE_SPECS))
        for rid, (_, _, minimum_count) in RULE_SPECS.items():
            self.assertGreaterEqual(newly_classified[rid], minimum_count)

    def test_frozen_receipts_and_input_examples_are_not_authority(self) -> None:
        tracked_set = set(self.tracked)
        for path, expected_id in KNOWN_EXAMPLES.items():
            self.assertIn(path, tracked_set)
            actual_class, trust_zone, actual_id = build.classify(
                path, self.contract
            )
            self.assertEqual(actual_id, expected_id)
            file_class, expected_zone, _ = RULE_SPECS[expected_id]
            self.assertEqual((actual_class, trust_zone), (file_class, expected_zone))
            self.assertNotIn(actual_class, {"LEAN_SOURCE", "LEAN_ROOT"})

    def test_detached_lean_snippets_not_added_to_compiler_roots(self) -> None:
        review_leans = [
            path for path in self.tracked
            if path.startswith(HISTORICAL_LEAN_ROOT) and path.endswith(".lean")
        ]
        self.assertGreaterEqual(len(review_leans), 7)
        for path in review_leans:
            file_class, trust, rid = build.classify(path, self.contract)
            self.assertEqual(
                (file_class, trust, rid),
                ("RESEARCH_FIXTURE", "AUDIT_ONLY",
                 "post290_archived_lean_review_fixtures"),
            )
        # build_records() discovers active Lean modules exclusively through
        # files typed LEAN_SOURCE / LEAN_ROOT; detached review snippets must
        # never enter that module census or gain theorem/axiom authority.
        active_lean_files = {
            path for path in self.tracked
            if build.classify(path, self.contract)[0]
            in {"LEAN_SOURCE", "LEAN_ROOT"}
        }
        self.assertTrue(set(review_leans).isdisjoint(active_lean_files))
        self.assertEqual(
            build.classify("Zeta23/CCM/CanonicalDeepThresholdGap.lean",
                           self.contract)[:2],
            ("LEAN_SOURCE", "RH_FORMAL_CORE"),
        )

    def test_unknown_extension_still_fails_closed(self) -> None:
        for path in (
            "research/RHRC/integration/post290/review_2026-10-14/new.unknown",
            HISTORICAL_LEAN_ROOT + "bounds/new.unknown",
            "research/RHRC/integration/post290/spec/inputs/new.unknown",
        ):
            self.assertEqual(
                build.classify(path, self.contract),
                ("UNKNOWN_FILE_CLASS", "UNKNOWN", "no_matching_rule"),
            )


if __name__ == "__main__":
    unittest.main()
