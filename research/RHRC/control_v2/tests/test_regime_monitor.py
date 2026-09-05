import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.regime_monitor import ResearchRegime, RouteHistoryRecord, assess_regime


class RegimeMonitorTests(unittest.TestCase):
    def rec(self, action, evaluator="e", benchmark=None, complexity=1, outcome="OPEN"):
        return RouteHistoryRecord(action, evaluator, benchmark, complexity, outcome)

    def test_no_history_is_read_only(self):
        result = assess_regime(())
        self.assertEqual(result.regime, ResearchRegime.NO_HISTORY)
        self.assertFalse(result.authorization)

    def test_abab_churn_is_detected(self):
        history = tuple(self.rec(x, evaluator=str(i)) for i, x in enumerate(["A", "B", "A", "B"]))
        result = assess_regime(history)
        self.assertEqual(result.regime, ResearchRegime.OSCILLATION)
        self.assertFalse(result.authorization)

    def test_complexity_ratchet_is_detected(self):
        history = tuple(self.rec(f"A{i}", evaluator=f"e{i}", complexity=i) for i in range(1, 6))
        result = assess_regime(history)
        self.assertEqual(result.regime, ResearchRegime.CAPABILITY_RATCHET)


if __name__ == "__main__":
    unittest.main()
