#!/usr/bin/env python3
"""Post-#287 source/claim firewall for single WP0–WP7 integration PR.

An honest green means that the ledger remains coherent with its declared
research scope. It does not establish RH, full K3 positivity, or any
unproved formal declaration.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
LEDGER=Path(__file__).resolve().with_name('OPEN_OBLIGATIONS.json')
ALLOWED={'IMPLEMENTED_PENDING_FULL_HARVEST','PROVED_PENDING_CI','PARTIAL_PENDING_CI','GATE_PENDING_CI',
         'INTERVAL_EVIDENCE_PENDING_REPLAY','GATE_UNRESOLVED',
         'EXPERIMENTAL_SIGNAL_PENDING_REPLAY','PENDING_CI',
         'PROVED','INTERVAL_EVIDENCE','EXPERIMENTAL_SIGNAL','UNRESOLVED'}
PROTECTED={'C_RH','R001_PRIME_UPPER','R002_WINDOWED_VISIBILITY',
           'R003_COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES',
           'M14_BRANCH_EXCLUSION','M32_CANONICAL_GRONWALL_COEFFICIENT',
           'M76_ARITHMETIC_COMPOSITION','OBS060O_STATIONARY_SATURATION_EXCLUSION'}

def main():
    d=json.loads(LEDGER.read_text())
    assert d['terminal_claim']=='RH_OPEN'
    assert d['requirements']['D2'].startswith('FULL_K3')
    assert set(d['protected_open'])==PROTECTED
    assert len(d['packages'])==8
    assert [x['id'] for x in d['packages']]==[f'WP{i}' for i in range(8)]
    for row in d['packages']:
        assert row['status'] in ALLOWED, (row['id'],row['status'])
        if 'path' in row:
            f=ROOT/row['path']
            assert f.is_file(),f
            if f.suffix=='.lean':
                body=f.read_text()
                assert not re.search(r'(?m)^\s*(sorry|admit|axiom)\b',body),f
                assert '#print axioms' in body,f
        if row['id']=='WP4':
            assert not row['status'].startswith('PROVED'),row
            assert row['alternate'].startswith('only predeclared fourth-order')
        if row['id']=='WP5':
            assert 'not actual zeta' in row['open_detail']
    # WP7: Every newly advertised source must really exist on this head.
    # This is a source/integration gate ONLY; it never upgrades a numerical
    # observation or a conditional theorem into RH proof authority.
    for path in d.get('implementation_source_files', []):
        source=ROOT/path
        assert source.is_file(), ('missing implementation source', path)
        if source.suffix=='.lean':
            code=source.read_text()
            assert '#print axioms' in code, path
            assert not re.search(r'(?m)^\s*(sorry|admit|axiom)\b',code), path
    wp4=next(row for row in d['packages'] if row['id']=='WP4')
    if wp4['status'] in ('GATE_UNRESOLVED', 'GATE_PENDING_CI'):
        for key in ('fallback','jet_validator','k2_odd','full_cover',
                    'cover_checker','assembler','lean_record'):
            assert (ROOT/wp4[key]).is_file(), ('missing required WP4 method',key)
        assert 'K3 positivity remains OPEN' in wp4['open_detail'], (
            'source/certificate status must not promote a failed gate'
        )
    assert d['merge_policy'].startswith('USER_APPROVAL_REQUIRED')
    print(json.dumps({'status':'PASS','claim_status':'RH_OPEN',
                      'work_packages':8,'protected_open':len(PROTECTED),
                      'scientific_gate':'ledger consistency only'}))

if __name__=='__main__':
    main()
