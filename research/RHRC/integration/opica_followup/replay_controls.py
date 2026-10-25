"""Replay byte-frozen paper controls outside the checkout, without proof promotion."""
from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
EXACT = [
    ('p0', HERE.parent / 'opica/check_exact.py', 5112,
     '42a1b29e979a415647b2ad477df4aa8e00b46f1afa52c1748748af4c79aa6985'),
    ('round1', HERE / 'checks/frozen_round1_check_round1.py', 18862,
     '2348097d4b2918fb06fd0a92e34a79e27bcbc3baaf9cef3a4d60a1eddb8450a8'),
    ('round2', HERE / 'checks/frozen_round2_check_round2.py', 14672,
     '86452973526f9711b0c027e7609bf986a6d1bc9eaec82134d9eeeb9893e32c29'),
    ('final', HERE / 'checks/check_final_exact.py', 1274,
     '87b2c328252dff666f2f414cf3fb09bf46abd95d64d241dbce223a2707448225'),
]
NUMERIC = [
    ('copoisson', HERE / 'checks/replay_copoisson_numeric.py',
     '298de5d144cdc18adcd0173843460d43be4611187228cb276dc03095704a5859'),
    ('round2', HERE / 'checks/frozen_round2_check_round2_numeric.py',
     '87be185b244b86633edd183eb88008d7c72ff31fb0ed83abc3fd36ec45453626'),
    ('final', HERE / 'checks/check_final_numeric.py',
     'ee00bdfcd7d8f3d4bbf552f2fc54ff363ad672c4514de67f8cebfd6926b1e08d'),
]


def verify_source(path: Path, expected: str) -> None:
    if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError('frozen checker drift: ' + str(path))


def exact_count(receipt: dict) -> int:
    value = receipt.get('total_checks', receipt.get('assertions'))
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError('missing integer scientific check count')
    return value


def run_checker(script: Path, output: Path, mode: str, log: Path, *, fixed_output=False) -> dict:
    before = hashlib.sha256(script.read_bytes()).hexdigest()
    if output.is_symlink():
        raise ValueError('receipt target is a symlink')
    if output.exists():
        output.unlink()
    command = [sys.executable] + (['-O'] if mode == 'optimized' else []) + [str(script)]
    if not fixed_output:
        command += ['--output', str(output)]
    process = subprocess.run(command, cwd=REPO, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=1200)
    log.write_bytes(process.stdout)
    if process.returncode != 0 or not output.is_file():
        raise RuntimeError('checker failed: ' + script.name + '; log: ' + str(log))
    if hashlib.sha256(script.read_bytes()).hexdigest() != before:
        raise ValueError('checker source changed during execution')
    result = json.loads(output.read_text(encoding='utf-8'))
    observed = result.get('script_sha256', result.get('checker_sha256'))
    if observed != before:
        raise ValueError('checker receipt is not bound to the executed script')
    return {'script': str(script), 'command': command, 'exit_code': process.returncode,
            'executed_script_sha256': before,
            'receipt_sha256': hashlib.sha256(output.read_bytes()).hexdigest(), 'result': result}


def validate_numeric_scope(suite: str, result: dict) -> None:
    if suite == 'round2':
        valid = (result.get('status') == 'PASS_NUMERICAL_CONSISTENCY_NOT_INTERVAL_CERTIFIED'
                 and result.get('infinite_theorem_certification') is False
                 and result.get('new_Lean_roots') == 0
                 and result.get('independent_review') is False)
    else:
        valid = (result.get('status') == 'PASS_NUMERICAL_CONSISTENCY_ONLY'
                 and result.get('interval_certified') is False)
    if not valid:
        raise ValueError('numeric receipt must retain its original noninterval-certified scope')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--modes', choices=['normal', 'optimized'], nargs='+', required=True)
    parser.add_argument('--include-numerical', action='store_true')
    parser.add_argument('--allow-development-runtime', action='store_true',
                        help='record an explicit non-release replay on another Python version')
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    output_dir = args.output_dir.resolve()
    if output_dir.is_relative_to(REPO.resolve()):
        parser.error('receipts must be outside the repository')
    if len(args.modes) != len(set(args.modes)):
        parser.error('duplicate Python modes')
    versions = {name: importlib.metadata.version(name) for name in ['sympy', 'mpmath']}
    if versions != {'sympy': '1.14.0', 'mpmath': '1.3.0'}:
        parser.error('frozen package versions required')
    runtime_matches = sys.version_info[:2] == (3, 13)
    if not runtime_matches and not args.allow_development_runtime:
        parser.error('Python 3.13 required; use the explicit development flag for a non-release replay')
    for _, path, _, expected in EXACT:
        verify_source(path, expected)
    for _, path, expected in NUMERIC:
        verify_source(path, expected)
    output_dir.mkdir(parents=True, exist_ok=True)
    exact_rows, numeric_rows = [], []
    for mode in args.modes:
        total = 0
        for label, path, count, expected in EXACT:
            receipt = output_dir / (label + '-' + mode + '.json')
            row = run_checker(path, receipt, mode, receipt.with_suffix('.log'))
            if exact_count(row['result']) != count:
                raise ValueError('frozen control count drift: ' + label)
            row.update(suite=label, mode=mode, expected_checks=count, checker_sha256=expected)
            exact_rows.append(row)
            total += count
            print(json.dumps({'suite': label, 'mode': mode, 'checks': count}), flush=True)
        if total != 39920:
            raise ValueError('full frozen exact inventory not replayed')
    if args.include_numerical:
        for label, path, expected in NUMERIC:
            receipt = output_dir / ('numeric-' + label + '.json')
            if label == 'copoisson':
                # This unchanged script writes to ../receipts relative to itself.
                # It must run in a temporary package, never the tracked package.
                with tempfile.TemporaryDirectory(prefix='opica-copoisson-', dir=output_dir) as tmp:
                    package = Path(tmp)
                    if not package.resolve().is_relative_to(output_dir):
                        raise ValueError('temporary package escaped receipt directory')
                    (package / 'checks').mkdir()
                    (package / 'receipts').mkdir()
                    copy = package / 'checks' / path.name
                    shutil.copyfile(path, copy)
                    produced = package / 'receipts/copoisson_numeric.json'
                    row = run_checker(copy, produced, 'normal', receipt.with_suffix('.log'), fixed_output=True)
                    shutil.copyfile(produced, receipt)
                    row['script'] = str(path)
            else:
                row = run_checker(path, receipt, 'normal', receipt.with_suffix('.log'))
            validate_numeric_scope(label, row['result'])
            row.update(suite=label, checker_sha256=expected)
            numeric_rows.append(row)
            print(json.dumps({'numerical_suite': label, 'status': 'CONSISTENCY_ONLY'}), flush=True)
        cases = sum(len(r['result']['cases']) if isinstance(r['result']['cases'], list)
                    else r['result']['cases'] for r in numeric_rows)
        if cases != 33:
            raise ValueError('expected exactly 33 separate numerical cases')
    report = {'schema': 'OPICA_FOLLOWUP_REGRESSION_REPLAY_V1',
              'status': 'PASS_FROZEN_REGRESSION_ONLY', 'python': platform.python_version(),
              'packages': versions, 'python313_runtime': runtime_matches,
              'release_runtime_accepted': False,
              'runtime_note': 'A platform-independent artifact hash lock and acceptance run remain required.',
              'exact': exact_rows, 'numerical': numeric_rows, 'interval_certified': False,
              'Lean_proof_authority': False, 'RH': 'OPEN', 'Step4': 'OPEN'}
    (output_dir / 'summary.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
