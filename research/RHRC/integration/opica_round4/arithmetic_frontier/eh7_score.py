"""Mechanical scoring of the frozen E-H7 predictions P9-P13 (no numerics; reads the run records).

The predictions and their acceptance rules are frozen in
evidence/increment3b/E-H7_PREDICTIONS.json together with the sha256 of every
tool. This scorer first checks those hashes against the current files and the
hashes recorded inside each run record, then applies each acceptance rule
literally. A failed prediction is recorded as failed.

Scoring derivation for P13 ("native checkpoint 1/5 CERTIFIED"): the frozen
tool emits no separate native-form certificate. The checkpoint is scored
CERTIFIED exactly when SCHUR_FULL_INVERSE_ACTION is CERTIFIED and A >= aI is
CERTIFIED: this is the hypothesis set of the Lean consumer
blockEnergy_nonneg_of_inverse_residual_certificate, whose conclusion is
nonnegativity of the shifted pencil F + eps G, i.e. the checkpoint inequality
Q_p >= -eps ||x||^2. The derivation is recorded in the output. RH and Step 4
remain OPEN.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PRED = HERE / 'evidence' / 'increment3b' / 'E-H7_PREDICTIONS.json'


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def score(records: dict) -> dict:
    pred = json.loads(PRED.read_bytes())
    files = {'basis_ed1_summary': HERE / 'evidence' / 'increment3b' / 'SUMMARY.json'}
    hash_checks = {f: (sha(files.get(f, HERE / f)) == h) for f, h in pred['rule_hashes'].items()}
    rec_checks = {}
    for par, r in records.items():
        rec_checks[par] = {'tool': r['tool_sha256'] == pred['rule_hashes'].get('ed1_response.py'),
                           'engine': r['engine_sha256'] == pred['rule_hashes'].get('native_slice.py'),
                           'kernel': r['kernel_sha256'] == pred['rule_hashes'].get('certificates.py'),
                           'state': (r['L'], r['K'], r['tolerance'], r['split']) == ('7', 2401, '1/5', 1200)}
    out = []
    # P9
    vals = {p: r['INVERSE_RESIDUAL_LADDER']['smallest_successful_tested_degree'] for p, r in records.items()}
    out.append({'id': 'P9', 'observed': vals, 'outcome': 'CONFIRMED' if all(v == 32 for v in vals.values()) else 'FAILED'})
    # P10
    tails = {p: [(x['degree'], x['status']) for x in r['GEOMETRIC_TAIL_LADDER']['rows']] for p, r in records.items()}
    ok = all(st == 'FALSIFIED_BOUND' for rows in tails.values() for _, st in rows)
    out.append({'id': 'P10', 'observed': tails, 'outcome': 'CONFIRMED' if ok else 'FAILED'})
    # P11
    counts = {p: r['RESPONSE_BANDS']['near_band']['count'] for p, r in records.items()}
    out.append({'id': 'P11', 'observed': counts, 'outcome': 'CONFIRMED' if all(200 <= c <= 500 for c in counts.values()) else 'FAILED'})
    # P12
    nb = {p: (r['RESPONSE_BANDS']['near_band']['trace_coupling_mass'], r['RESPONSE_BANDS']['near_band']['response_trace'])
          for p, r in records.items()}
    ok = all(c <= 1e-4 and rr <= 1e-3 for c, rr in nb.values())
    out.append({'id': 'P12', 'observed': {p: {'coupling_trace': c, 'response_trace': rr} for p, (c, rr) in nb.items()},
                'outcome': 'CONFIRMED' if ok else 'FAILED', 'authority_of_observed': 'EXPERIMENTAL_SIGNAL_FLOATING_SPECTRAL_PROJECTORS'})
    # P13
    obs, ok = {}, True
    for p, r in records.items():
        chk = 'CERTIFIED' if (r['SCHUR_FULL_INVERSE_ACTION']['status'] == 'CERTIFIED' and r['A_ge_aI'] == 'CERTIFIED') else 'NOT_CERTIFIED'
        sg = r['SCALAR_GAP']['status']
        charge = r['RESPONSE_BANDS']['near_band']['scalar_gap_worst_charge']
        obs[p] = {'native_checkpoint_via_consumer': chk, 'schur_full': r['SCHUR_FULL_INVERSE_ACTION']['status'],
                  'A_ge_aI': r['A_ge_aI'], 'scalar_gap': sg, 'worst_charge': charge}
        ok = ok and chk == 'CERTIFIED' and r['SCHUR_FULL_INVERSE_ACTION']['status'] == 'CERTIFIED' and sg == 'FALSIFIED_BOUND' and charge >= 80
    out.append({'id': 'P13', 'observed': obs, 'outcome': 'CONFIRMED' if ok else 'FAILED',
                'scoring_derivation': 'native checkpoint := SCHUR_FULL_INVERSE_ACTION CERTIFIED and A >= aI CERTIFIED (hypotheses of blockEnergy_nonneg_of_inverse_residual_certificate)'})
    return {'schema': 'OPICA4_ARITHMETIC_FRONTIER_EH7_OUTCOMES_V1', 'RH': 'OPEN', 'Step4': 'OPEN', 'experiment': 'E-H7',
            'predictions_sha256': sha(PRED), 'scorer_sha256': sha(Path(__file__)),
            'rule_hash_checks_current_files': hash_checks, 'record_hash_checks': rec_checks,
            'rules_intact': all(hash_checks.values()) and all(all(v.values()) for v in rec_checks.values()),
            'outcomes': out, 'confirmed': [o['id'] for o in out if o['outcome'] == 'CONFIRMED'],
            'failed': [o['id'] for o in out if o['outcome'] == 'FAILED'],
            'scope': 'Finite research outcome at L = 7, tolerance 1/5; a confirmed law is not an asymptotic theorem; RH and Step 4 OPEN'}


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--even', type=Path, required=True)
    p.add_argument('--odd', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args(argv)
    recs = {'even': json.loads(a.even.read_bytes()), 'odd': json.loads(a.odd.read_bytes())}
    res = score(recs)
    a.out.write_text(json.dumps(res, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'rules_intact': res['rules_intact'], 'confirmed': res['confirmed'], 'failed': res['failed']}))
    return 0


if __name__ == '__main__':
    sys.exit(main())
