#!/usr/bin/env python3
"""Check exact inventory preservation, not theorem correctness."""
from pathlib import Path
import json
k=Path(__file__).resolve().parents[1];orig=json.loads((k/'workspace/research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json').read_text())['roots'];l=json.loads((k/'state/ROOT_LEDGER_100.json').read_text());rows=l['roots']
if len(orig)!=100 or len(rows)!=100 or len({r['full_name'] for r in rows})!=100:raise ValueError('Root identities/count changed')
if l['acceptance_units']!=28 or l['current_aggregate_accepted']:raise ValueError('Scope/status changed')
if [r['contract'] for r in rows]!=orig:raise ValueError('Original quantified contracts changed')
for r in rows:
 if r['gates']['full_release_acceptance']!='OPEN':raise ValueError('Improper promotion')
 for p in r['evidence']:
  if not (k/p).is_file():raise ValueError('Missing evidence reference '+p)
print(json.dumps({'status':'PASS_STRUCTURAL_ONLY','original_roots':100,'acceptance_units':28,'status_counts':l['status_counts'],'full_release_accepted':False},indent=2))
