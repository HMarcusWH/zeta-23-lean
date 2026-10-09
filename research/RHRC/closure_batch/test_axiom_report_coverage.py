"""Guard the exact contact-calculus declaration inventory from silent omission."""
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from axiom_audit import EXPECTED_REPORTS, missing_expected_reports


class AxiomReportCoverageTests(unittest.TestCase):
    def test_all_expected_prints_exist_in_source(self):
        for filename, expected in EXPECTED_REPORTS.items():
            with self.subTest(filename=filename):
                source = Path(filename).read_text(encoding="utf-8")
                actual = set(re.findall(r"(?m)^\\s*#print axioms\\s+(\\S+)", source))
                self.assertTrue(expected <= actual, sorted(expected - actual))

    def test_a_missing_target_is_detected(self):
        for filename, expected in EXPECTED_REPORTS.items():
            target = sorted(expected)[0]
            with self.subTest(filename=filename):
                self.assertEqual(
                    [target],
                    missing_expected_reports(filename, expected - {target}),
                )
                self.assertEqual([], missing_expected_reports(filename, expected))


if __name__ == "__main__":
    unittest.main()
