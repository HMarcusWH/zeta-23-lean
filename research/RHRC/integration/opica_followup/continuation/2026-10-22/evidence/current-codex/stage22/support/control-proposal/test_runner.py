"""Protocol tests use historical real logs; they are not Stage22 Lean receipts."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
WORK = HERE.parent
spec = importlib.util.spec_from_file_location('stage22_control_runner', HERE / 'run_controls.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
PLAN = json.loads((HERE / 'CONTROL_PLAN.json').read_bytes())


def historical_log(row):
    if row['origin']['kind'] == 'EXACT_STAGE21_BYTES':
        return WORK / 'opica-stage21/clean-controls' / (row['name'] + '.log')
    if row['origin']['kind'] == 'EXACT_SEALED_CANONICAL_MUTATION':
        return WORK / 'audit-release' / (row['name'] + '.log')
    if row['origin']['kind'] == 'SEALED_SQUARE_EXAMPLE_SPLIT_IMPORT_ONLY':
        return WORK / 'audit-square-physical/final-square-negative-contracts.log'
    if row['origin']['kind'] == 'SEALED_COMPACT_COMPATIBILITY_IMPORT_ONLY':
        return WORK / 'audit-tempered-lattice/SEALED_TEMPERED_LATTICE_2026-10-24/negative1.log'
    if row['origin']['kind'] == 'SEALED_CT13_IMPORT_ONLY':
        return WORK / 'audit-ct13' / (row['name'] + '.log')
    if row['origin']['kind'] == 'SEALED_CC_COMMON_TV_IMPORT_ONLY':
        return WORK / 'audit-independent-expected-types/compact-negative-no-common-budget.log'
    raise ValueError('unrecognized historical provenance')


class ControlProtocol(unittest.TestCase):
    def test_inventory_and_exact21_source_preservation(self):
        self.assertEqual(len(PLAN['controls']), 31)
        self.assertEqual(sum(row['expected'] == 'PASS' for row in PLAN['controls']), 4)
        preserved = [row for row in PLAN['controls'] if row['origin']['kind'] == 'EXACT_STAGE21_BYTES']
        self.assertEqual(len(preserved), 21)
        for row in PLAN['controls']:
            path = HERE / 'sources' / row['file']
            self.assertEqual(runner.sha(path), row['source_sha256'])
            if row in preserved:
                self.assertEqual(path.read_bytes(), Path(row['origin']['path']).read_bytes())

    def test_historical_logs_classify_at_their_own_original_states(self):
        for row in PLAN['controls']:
            with self.subTest(name=row['name']):
                log = historical_log(row).read_text(encoding='utf-8')
                source = (HERE / 'sources' / row['file']).read_text(encoding='utf-8')
                result = runner.classify(row, source, log, 0 if row['expected'] == 'PASS' else 1)
                self.assertTrue(result['passed'], result['failure_reasons'])

    def test_unknown_identifier_is_not_a_negative_success(self):
        row = {'expected': 'REJECTED', 'required_diagnostic_regex': ['TargetPremise']}
        for error in ["error(lean.unknownIdentifier): Unknown identifier `TargetPremise`",
                      'error: unknown module TargetPremise', 'error: invalid import TargetPremise',
                      "error: object file 'TargetPremise.olean' does not exist"]:
            with self.subTest(error=error):
                self.assertFalse(runner.classify(row, '', error, 1)['passed'])

    def test_unrelated_type_error_or_unrejected_file_fails(self):
        row = {'expected': 'REJECTED', 'required_diagnostic_regex': ['RequiredDomain']}
        self.assertFalse(runner.classify(row, '', 'error: type mismatch for another term', 1)['passed'])
        self.assertFalse(runner.classify(row, '', 'error: RequiredDomain mismatch', 0)['passed'])
        self.assertFalse(runner.classify(row, '', 'RequiredDomain', 1)['passed'])

    def test_error_lean_invalid_field_is_real_omitted_premise_diagnostic(self):
        row = next(row for row in PLAN['controls'] if row['name'] == 'NegativeBudgetIndependenceFinal')
        log = historical_log(row).read_text(encoding='utf-8')
        self.assertIn('error(lean.invalidField)', log)
        self.assertTrue(runner.classify(row, '', log, 1)['passed'])

    def test_both_lean_error_formats_supported(self):
        row = {'expected': 'REJECTED', 'required_diagnostic_regex': ['RequiredDomain']}
        for diagnostic in ['error: RequiredDomain mismatch',
                           'error(lean.synthInstanceFailed): RequiredDomain missing']:
            self.assertTrue(runner.classify(row, '', diagnostic, 1)['passed'])

    def test_positive_exact_fully_qualified_axiom_coverage(self):
        row = {'expected': 'PASS'}
        source = '#print axioms Expected.actual\n'
        log = "'Expected.actual' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertTrue(runner.classify(row, source, log, 0)['passed'])
        self.assertFalse(runner.classify(row, source, log.replace('Expected.actual', 'Other.actual'), 0)['passed'])
        self.assertFalse(runner.classify(row, source.replace('Expected.actual', 'actual'), log, 0)['passed'])
        self.assertFalse(runner.classify(row, source, log, 1)['passed'])
        self.assertTrue(runner.classify(row, source, "'Expected.actual' does not depend on any axioms", 0)['passed'])

    def test_nonstandard_axioms_and_duplicate_prints_fail(self):
        row = {'expected': 'PASS'}
        source = '#print axioms Expected.actual\n'
        for axiom in ['sorryAx', 'Unapproved.claim']:
            self.assertFalse(runner.classify(row, source, "'Expected.actual' depends on axioms: [" + axiom + ']', 0)['passed'])
        log = "'Expected.actual' depends on axioms: [propext]\n" * 2
        self.assertFalse(runner.classify(row, source, log, 0)['passed'])

    def test_error_recovery_in_negative_confers_no_authority(self):
        row = next(row for row in PLAN['controls'] if row['name'] == 'NegativeCanonicalRecoveryWrongCost')
        result = runner.classify(row, '', historical_log(row).read_text(encoding='utf-8'), 1)
        self.assertTrue(result['passed'])
        self.assertTrue(result['error_recovery_sorryAx_in_rejected_output'])
        self.assertFalse(result['formal_authority_from_failed_declarations'])
        log = historical_log(row).read_text(encoding='utf-8').replace('sorryAx', 'Unapproved.claim')
        self.assertFalse(runner.classify(row, '', log, 1)['passed'])

    def test_diagnostic_requirements_cannot_be_omitted(self):
        row = {'expected': 'REJECTED', 'required_diagnostic_regex': []}
        self.assertFalse(runner.classify(row, '', 'error: type mismatch', 1)['passed'])

    def test_resource_failure_does_not_establish_contract_rejection(self):
        row = {'expected': 'REJECTED', 'required_diagnostic_regex': ['RequiredDomain']}
        for failure in ['error: RequiredDomain: maximum number of heartbeats (800000) has been reached',
                        'error: RequiredDomain: (deterministic) timeout',
                        'error: RequiredDomain: out of memory']:
            self.assertFalse(runner.classify(row, '', failure, 1)['passed'])

    def test_pin_checks_fail_closed_for_head_tree_and_dirty_status(self):
        for state in [['wrong', PLAN['checked_tree'], ''],
                      [PLAN['checked_commit'], 'wrong', ''],
                      [PLAN['checked_commit'], PLAN['checked_tree'], ' M file.lean']]:
            with patch.object(runner, 'git', side_effect=state):
                with self.assertRaises(ValueError):
                    runner.check_pin(Path('.'), PLAN)
        with patch.object(runner, 'git', side_effect=[PLAN['checked_commit'], PLAN['checked_tree'], '']):
            runner.check_pin(Path('.'), PLAN)

    def test_shared_cache_guard_detects_writes_and_new_objects(self):
        with TemporaryDirectory(dir=HERE) as temp:
            repo = Path(temp)
            cache = repo / '.lake/build/lib/lean'
            cache.mkdir(parents=True)
            path = cache / 'Existing.olean'
            path.write_bytes(b'old object')
            before = runner.cache_snapshot(repo)
            self.assertEqual(before, runner.cache_snapshot(repo))
            path.write_bytes(b'changed object with a different size')
            self.assertNotEqual(before, runner.cache_snapshot(repo))
            before = runner.cache_snapshot(repo)
            (cache / 'Unexpected.olean').write_bytes(b'new object')
            self.assertNotEqual(before, runner.cache_snapshot(repo))


if __name__ == '__main__':
    unittest.main(verbosity=2)
