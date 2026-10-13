#!/usr/bin/env python3
"""Fail-closed adversarial RHKG freshness controls; leaves checkout byte-identical."""
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BUILD=[sys.executable,str(ROOT/'research/RHRC/graph/build.py'),'--check']

def run():
    return subprocess.run(BUILD,cwd=ROOT,text=True,stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT,check=False,timeout=300)

def corrupt_and_reject(path: Path, suffix: bytes, target: str):
    before=path.read_bytes()
    try:
        path.write_bytes(before+suffix)
        trial=run()
        if trial.returncode==0 or 'stale generated output' not in trial.stdout or target not in trial.stdout:
            raise AssertionError('stale RHKG input was not rejected: '+target+' '+trial.stdout[-2200:])
    finally:
        path.write_bytes(before)
    if path.read_bytes()!=before:
        raise AssertionError('restoration failed: '+str(path))

first=run()
assert first.returncode==0,first.stdout[-3000:]
corrupt_and_reject(ROOT/'research/RHRC/graph/generated/lean_modules.jsonl',
                   b'\n', 'lean_modules.jsonl')
corrupt_and_reject(ROOT/'Zeta23/CCM.lean',
                   b'\n-- rhkg source-blob mutation control\n','repository_files.jsonl')
final=run()
assert final.returncode==0,final.stdout[-3000:]
print('RHKG COMMITTED-STATE MUTATIONS: PASS (2 rejections; initial/final clean)')
