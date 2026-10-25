"""Reject stale receipts, source drift and mathematical-authority promotion."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('followup_replay', HERE / 'replay_controls.py')
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)


class RegressionReplayTests(unittest.TestCase):
    def test_original_round2_schema_retained(self):
        replay.validate_numeric_scope('round2', {
            'status': 'PASS_NUMERICAL_CONSISTENCY_NOT_INTERVAL_CERTIFIED',
            'infinite_theorem_certification': False, 'new_Lean_roots': 0,
            'independent_review': False})

    def test_round2_proof_promotion_rejected(self):
        with self.assertRaises(ValueError):
            replay.validate_numeric_scope('round2', {
                'status': 'PASS_NUMERICAL_CONSISTENCY_NOT_INTERVAL_CERTIFIED',
                'infinite_theorem_certification': True, 'new_Lean_roots': 0,
                'independent_review': False})

    def test_interval_promotion_rejected(self):
        with self.assertRaises(ValueError):
            replay.validate_numeric_scope('final', {
                'status': 'PASS_NUMERICAL_CONSISTENCY_ONLY', 'interval_certified': True})

    def test_empty_numeric_receipt_rejected(self):
        for suite in ('round2', 'final', 'copoisson'):
            with self.subTest(suite=suite), self.assertRaises(ValueError):
                replay.validate_numeric_scope(suite, {})

    def test_boolean_control_count_rejected(self):
        with self.assertRaises(ValueError):
            replay.exact_count({'total_checks': True})

    def test_missing_control_count_rejected(self):
        with self.assertRaises(ValueError):
            replay.exact_count({})

    def test_changed_frozen_checker_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / 'checker.py'
            source.write_text('pass\n')
            with self.assertRaises(ValueError):
                replay.verify_source(source, '0' * 64)

    def test_successful_no_output_process_cannot_reuse_stale_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, receipt, log = root / 'checker.py', root / 'receipt.json', root / 'stdout.log'
            source.write_text('pass\n')
            receipt.write_text(json.dumps({'total_checks': 39920}))
            with self.assertRaises(RuntimeError):
                replay.run_checker(source, receipt, 'normal', log)
            self.assertFalse(receipt.exists())

    def test_script_cannot_change_while_executing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, receipt = root / 'checker.py', root / 'receipt.json'
            source.write_text('from pathlib import Path\nimport sys\n'
                              'Path(sys.argv[2]).write_text("{}")\n'
                              'Path(__file__).write_text("pass\\n")\n')
            with self.assertRaises(ValueError):
                replay.run_checker(source, receipt, 'normal', root / 'stdout.log')


if __name__ == '__main__':
    unittest.main()
