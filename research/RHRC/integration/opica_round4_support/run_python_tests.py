"""Run the exact authored test inventory; no success from an empty/skipped suite."""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
import unittest

BASE = Path(__file__).resolve().parent

def flatten(suite: unittest.TestSuite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from flatten(item)
        else:
            yield item

def run(expected: Path) -> int:
    expected_ids = json.loads(expected.read_text(encoding='utf-8'))
    if type(expected_ids) is not list or not expected_ids or \
            len(expected_ids) != len(set(expected_ids)) or \
            any(type(t) is not str or not t for t in expected_ids):
        raise ValueError('invalid expected test inventory')
    loader = unittest.TestLoader()
    suite = loader.discover(str(BASE/'tests'), pattern='test_*.py', top_level_dir=str(BASE/'tests'))
    actual = sorted(test.id() for test in flatten(suite))
    if sorted(expected_ids) != actual:
        print(json.dumps({'status':'FAIL','reason':'TEST_INVENTORY_MISMATCH',
                          'expected': sorted(expected_ids), 'actual': actual}),file=sys.stderr)
        return 2
    runner=unittest.TextTestRunner(verbosity=2,stream=sys.stderr,failfast=False)
    result=runner.run(suite)
    success = result.wasSuccessful() and result.testsRun == len(expected_ids) and \
              not result.skipped and not result.expectedFailures and not result.unexpectedSuccesses
    report={'status':'PASS' if success else 'FAIL', 'expected':len(expected_ids),
            'executed':result.testsRun, 'failures':len(result.failures),
            'errors':len(result.errors), 'skips':len(result.skipped),
            'expected_failures':len(result.expectedFailures),
            'unexpected_successes':len(result.unexpectedSuccesses),
            'optimized':not __debug__, 'test_ids':actual}
    print(json.dumps(report,sort_keys=True))
    return 0 if success else 1

def main() -> int:
    parser=argparse.ArgumentParser()
    parser.add_argument('--expected',type=Path,default=BASE/'EXPECTED_TEST_IDS.json')
    args=parser.parse_args()
    return run(args.expected)
if __name__=='__main__':
    raise SystemExit(main())
