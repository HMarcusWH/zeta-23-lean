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

def validate_wp5_model_scope(row: dict) -> None:
    """A positive modified-prime crossing is not a zeta counterexample."""
    assert row["model_scope"] == "NON_ZETA_MODIFIED_PRIME"
    assert row["model_is_actual_zeta"] is False
    assert row["rh_counterexample_claim"] is False


EXPECTED_D2='FULL_K3_BOTH_PARITIES_CONTINUOUS_[1/512,log16]'
CAMPAIGN='31512dbb698dd59b90cfa32549f0e9273a5163f9'
REMAINING={'Q9_even':7,'Q13_even':7,'Q14_even':11,'Q15_even':10}

def validate_d2_deferral(d: dict) -> None:
    """Differentiate user-authorized merge scope from unproved D2 mathematics."""
    assert d['terminal_claim']=='RH_OPEN'
    assert d['requirements']['D2']==EXPECTED_D2
    s=d['merge_scope']
    assert s['kind']=='REPAIR_ONLY_D2_DEFERRED'
    assert s['authorized_date']=='2026-10-13'
    assert s['authorized_by']=='user_in_conversation'
    assert s['original_D2_required'] is True
    assert s['D2_full_status']=='OPEN_DEFERRED_NEXT_PR'
    assert s['merge_without_D2_full'] is True
    assert s['requires_user_approval'] is True
    assert s['next_pr_target'].startswith('K3_CONTINUOUS')
    a=s['original_campaign']
    assert a['source_commit']==CAMPAIGN
    assert a['run_id']==38332529352
    assert (a['total_layers'],a['complete_layers'],a['unresolved_layers'],a['unresolved_intervals'])==(30,26,4,35)
    assert a['unresolved_by_layer']==REMAINING
    assert d['merge_policy'].startswith('USER_APPROVAL_REQUIRED')
    assert 'RH_OPEN' in d['merge_policy']

def validate_wp4_gate(d: dict) -> None:
    """Never allow the partial K3 evidence to masquerade as the frozen-gate or global theorem."""
    wp4=next(x for x in d['packages'] if x['id']=='WP4')
    assert wp4['status']=='GATE_UNRESOLVED'
    assert wp4['formal_status']=='PROVED_CONDITIONAL'
    assert wp4['numerical_status']=='PARTIAL_SOURCE_PINNED'
    assert wp4['frozen_second_gate']=='PASS_18_OF_18'
    assert wp4['full_window_status']=='UNRESOLVED'
    assert wp4['source_campaign_run_id']==38332529352
    assert wp4['source_campaign_commit']==CAMPAIGN
    assert (wp4['total_layers'],wp4['complete_layers'])==(30,26)
    assert wp4['remaining_layer_intervals']==REMAINING
    assert sum(wp4['remaining_layer_intervals'].values())==35
    assert wp4['next_pr_obligation']=='D2_FULL_K3_EVEN_SECTOR_35_SUBINTERVALS'
    assert 'K3 positivity remains OPEN' in wp4['open_detail']
    assert 'hWindows' in wp4['open_detail']
    assert wp4['alternate'].startswith('only predeclared fourth-order')
    for key in ('path','fallback','jet_validator','k2_odd','full_cover',
                'cover_checker','assembler','lean_record'):
        assert (ROOT/wp4[key]).is_file(),('missing required WP4 method',key)
    assert (ROOT/'research/RHRC/integration/post287/PR290_SCOPE_OVERRIDE_AND_HANDOFF.md').is_file()

def main():
    d=json.loads(LEDGER.read_text())
    validate_d2_deferral(d)
    validate_wp4_gate(d)
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
            validate_wp5_model_scope(row)
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
