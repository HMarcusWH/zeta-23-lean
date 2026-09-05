import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.retro.revival import RevivalRecord, require_revival_records


class RevivalTests(unittest.TestCase):
    def test_dead_route_requires_explicit_revival(self):
        with self.assertRaises(RuntimeError):
            require_revival_records(("DR-010",), ())

    def test_changed_premise_record_can_cover_route(self):
        record = RevivalRecord(
            dead_route_id="DR-010",
            proposed_route_id="EXACT_ANALYTIC_GENERATOR",
            original_blocker="fitted small commutator had collapsing spectral gaps",
            changed_premise="new route uses an analytically specified generator and a separate absolute gap theorem",
            evidence_for_change=("theorem-X", "theorem-Y"),
        )
        require_revival_records(("DR-010",), (record,))


if __name__ == "__main__":
    unittest.main()
