#!/usr/bin/env python3
"""Replay the recorded repository commands on a user-provided checkout.

This writes new logs only under --output. It does not overwrite the frozen audit.
A Git checkout/index is needed by the repository's census tools. Existing Lean
and Arb dependencies are not installed automatically. Numerical checks can be
expensive; --batch primary is the default.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    ap.add_argument('--batch', choices=['primary', 'expanded', 'both'], default='primary')
    ap.add_argument('--timeout', type=float, default=120.0)
    ns = ap.parse_args()
    repo = ns.repo.resolve()
    if not (repo / 'lean-toolchain').is_file():
        ap.error('--repo is not the zeta-23-lean repository root')
    frozen = Path(__file__).resolve().parents[1] / 'results'
    out = ns.output.resolve()
    if out == frozen or frozen in out.parents:
        ap.error('--output must not overwrite the frozen audit results')
    out.mkdir(parents=True, exist_ok=True)
    names = (['test_results.json'] if ns.batch == 'primary' else
             ['extra_test_results.json'] if ns.batch == 'expanded' else
             ['test_results.json', 'extra_test_results.json'])
    tasks = [x for name in names for x in json.loads((frozen / name).read_text())]
    env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1',
               MKL_NUM_THREADS='1', PYTHONHASHSEED='0')
    results = []
    for task in tasks:
        command = [sys.executable, *task['command'][1:]]
        log = out / (task['name'] + '.log')
        start = time.monotonic()
        rc = None
        try:
            with log.open('w') as fp:
                fp.write('$ ' + ' '.join(command) + '\n')
                fp.flush()
                process = subprocess.run(command, cwd=repo, env=env,
                    stdout=fp, stderr=subprocess.STDOUT, timeout=ns.timeout)
                rc = process.returncode
            status = 'PASS' if rc == 0 else 'FAIL'
        except subprocess.TimeoutExpired:
            status = 'TIMEOUT'
        text = log.read_text(errors='replace')
        if rc not in (None, 0) and ('No module named \'flint\'' in text or
                                  'No module named "flint"' in text):
            status = 'ENVIRONMENT_BLOCKED'
        results.append({'name': task['name'], 'command': command,
                        'returncode': rc, 'disposition': status,
                        'elapsed_seconds': round(time.monotonic() - start, 3),
                        'log': str(log)})
        (out / 'replay_results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(task['name'], status, flush=True)
    return 0 if all(x['disposition'] == 'PASS' for x in results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
