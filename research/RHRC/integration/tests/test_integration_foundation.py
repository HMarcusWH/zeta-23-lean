from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path

INTEGRATION = Path(__file__).resolve().parents[1]
RHRC = INTEGRATION.parent
sys.path.insert(0, str(INTEGRATION))

from source_candidates import classify_visibility, select_rh_core_theorem_sources, summarize


class IntegrationFoundationTests(unittest.TestCase):
    def test_selector_is_exactly_rh_core_theorem_and_lemma(self):
        rows = [
            {"id": "a", "module": "M", "line": 2, "declared_name": "t", "trust_zone": "RH_FORMAL_CORE", "command_kind": "THEOREM"},
            {"id": "b", "module": "M", "line": 1, "declared_name": "l", "trust_zone": "RH_FORMAL_CORE", "command_kind": "LEMMA"},
            {"id": "c", "module": "M", "line": 3, "declared_name": "d", "trust_zone": "RH_FORMAL_CORE", "command_kind": "DEF"},
            {"id": "d", "module": "M", "line": 4, "declared_name": "x", "trust_zone": "AUXILIARY_FORMALIZATION", "command_kind": "THEOREM"},
        ]
        self.assertEqual([row["id"] for row in select_rh_core_theorem_sources(rows)], ["b", "a"])

    def test_visibility_classification_is_fail_closed(self):
        closure = {
            "Root.t": {"graph_role": "REGISTERED_CLAIM_ROOT", "registered_claim_id": "C1"},
            "Dep.t": {"graph_role": "LOCAL_DEPENDENCY"},
        }
        visible, claim = classify_visibility(
            {"resolution_status": "RESOLVED_UNIQUE", "resolved_full_name": "Root.t"},
            closure,
        )
        self.assertEqual((visible, claim), ("ALREADY_REGISTERED_ROOT", "C1"))
        visible, claim = classify_visibility(
            {"resolution_status": "RESOLVED_UNIQUE", "resolved_full_name": "Fresh.t"},
            closure,
        )
        self.assertEqual((visible, claim), ("SOURCE_ONLY_PUBLIC_THEOREM", None))
        visible, _ = classify_visibility(
            {"resolution_status": "AMBIGUOUS_COMPILER_MATCH", "resolved_full_name": None},
            closure,
        )
        self.assertEqual(visible, "AMBIGUOUS_SOURCE_IDENTITY")

    def test_summary_cannot_promote(self):
        s = summarize([
            {"visibility_class": "SOURCE_ONLY_PUBLIC_THEOREM", "resolution_status": "RESOLVED_UNIQUE"},
            {"visibility_class": "ALREADY_REGISTERED_ROOT", "resolution_status": "RESOLVED_UNIQUE"},
        ])
        self.assertEqual(s["source_only_public_theorem_count"], 1)
        self.assertEqual(s["terminal_claim"], "RH_OPEN")
        self.assertFalse(s["theorem_promotion"])

    def test_authority_anchors_are_separate(self):
        state = json.loads((INTEGRATION / "INTEGRATION_STATE.json").read_text())
        self.assertEqual(state["theorem_authority"]["pr"], 262)
        self.assertEqual(state["frozen_control_authority"]["pr"], 117)
        self.assertEqual(state["repository_graph_authority"]["pr"], 263)
        self.assertFalse(state["theorem_promotion"])


if __name__ == "__main__":
    unittest.main()
