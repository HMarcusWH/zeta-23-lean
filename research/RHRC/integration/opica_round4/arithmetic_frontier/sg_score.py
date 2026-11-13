"""Mechanical scoring of the frozen (SG) predictions against a generated record.

EXPERIMENTAL SIGNAL bookkeeping only. A miss is an operational prediction failure,
not a mathematical falsification of (SG); a hit proves nothing about all L.
RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import sys
from pathlib import Path

SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_SG_OUTCOMES_V1'


def sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def value(quantity: str, row: dict) -> float:
    if quantity == 'norm_l / K^2':
        return row['norm_l'] / row['K'] ** 2
    if quantity == '-sg_lower_bound':
        return -row['sg_lower_bound']
    return row[quantity]


def score_prediction(p: dict, parity: str, row: dict) -> bool:
    """Closed intervals, except P6 whose lower endpoint is open (strictly positive)."""
    if p['quantity'] == 'identity residuals':
        return all(row[key] < bound for key, bound in p['bounds'].items())
    lo, hi = p[parity]
    x = value(p['quantity'], row)
    if p['id'] == 'P6':
        return lo < x <= hi
    return lo <= x <= hi


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--predictions', type=Path, required=True)
    ap.add_argument('--record', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args(argv)
    pred = json.loads(args.predictions.read_bytes())
    rec = json.loads(args.record.read_bytes())
    rows = {s['parity']: s for s in rec['states'] if s['L'] == str(pred['state']['L'])}
    scores = {}
    for p in pred['predictions']:
        scores[p['id']] = {}
        for parity in pred['state']['parities']:
            row = rows[parity]
            entry = {'hit': score_prediction(p, parity, row)}
            if p['quantity'] != 'identity residuals':
                entry.update(value=value(p['quantity'], row), interval=p[parity])
            else:
                entry.update(values={k: row[k] for k in p['bounds']})
            scores[p['id']][parity] = entry
    hits = sum(v['hit'] for s in scores.values() for v in s.values())
    total = sum(len(s) for s in scores.values())
    out = {'schema': SCHEMA, 'RH': 'OPEN', 'Step4': 'OPEN',
           'authority': 'MECHANICAL_SCORE_OF_FROZEN_OPERATIONAL_PREDICTIONS',
           'predictions_file': args.predictions.name, 'predictions_sha256': sha256(args.predictions),
           'predictions_frozen_utc': pred['frozen_utc'], 'record_file': args.record.name, 'record_sha256': sha256(args.record),
           'results_recorded_utc': datetime.datetime.fromtimestamp(args.record.stat().st_mtime, datetime.timezone.utc)
                                   .strftime('%Y-%m-%dT%H:%M:%SZ'),
           'scorer_sha256': sha256(Path(__file__)), 'scores': scores, 'hits': hits, 'total': total,
           'reading': 'A miss is an operational prediction failure, not a falsification of (SG). Hits prove nothing about all L.'}
    args.output.write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'hits': hits, 'total': total,
                      'misses': [(k, par) for k, s in scores.items() for par, v in s.items() if not v['hit']]}))
    return 0


if __name__ == '__main__':
    sys.exit(main())
