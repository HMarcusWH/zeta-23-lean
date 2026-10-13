"""Reject completion unless every mandatory producer and D2 gate has receipts.

This is an integrity check, not a mathematical proof. Exact compiler receipts
and independent mathematical review are both required by the original contract.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

def release_gaps(manifest, formal, d2, jobs):
    gaps = []
    if manifest.get('claim_cap') != 'RH_OPEN':
        gaps.append('claim firewall changed')
    bindings = {r['theorem']:r for r in formal.get('declarations', [])}
    tree = formal.get('source_tree')
    if not tree or len(tree) != 40:
        gaps.append('exact compiler-tested tree missing')
    for module in manifest['new_lean_modules']:
        if not module.get('mandatory_core'):
            continue
        for name in module['proposed_exports']:
            receipt = bindings.get(name)
            if not receipt:
                gaps.append('missing producer: ' + name)
            elif (receipt.get('authority') != 'PROVED' or receipt.get('source_tree') != tree
                  or not receipt.get('normalized_type') or
                  hashlib.sha256(receipt.get('normalized_type','').encode()).hexdigest() != receipt.get('normalized_type_sha256')
                  or not receipt.get('axiom_audit_pass')):
                gaps.append('unverified or stale producer: ' + name)
        if module.get('status') != 'COMPLETE_VERIFIED':
            gaps.append('unfulfilled module acceptance: ' + module['id'])
    required_d2 = ('complete_layers','unresolved_tiles','unrun_tiles','missing_artifacts','unverified_tiles','nonfinite_enclosures')
    if (d2.get('status') != 'D2_COMPLETE' or d2.get('complete_layers') != 30
        or not d2.get('independent_nonpartial_verified') or not d2.get('both_parities')
        or not d2.get('physical_seams_verified') or any(k not in d2 for k in required_d2)
        or any(d2.get(k,1) != 0 for k in required_d2[1:])):
        gaps.append('D2 continuous full-domain gate incomplete')
    for job in jobs:
        if job.get('required') and (job.get('head_tree') != tree or job.get('status') != 'completed'
            or job.get('conclusion') != 'success' or not job.get('scientific_acceptance')):
            gaps.append('required job unestablished: ' + job['name'])
    if not jobs:
        gaps.append('workflow harvest missing')
    if not formal.get('independent_assumption_review_pass'):
        gaps.append('independent producer assumption review missing')
    return gaps

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--formal', type=Path, required=True)
    p.add_argument('--d2', type=Path, required=True)
    p.add_argument('--harvest', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    read = lambda path: json.loads(path.read_text())
    gaps = release_gaps(read(args.manifest),read(args.formal),read(args.d2),read(args.harvest).get('jobs',[]))
    result = {'execution_status':'SUCCESS', 'integrity_status':'PASS' if not gaps else 'RELEASE_REJECTED',
              'scientific_disposition':'CORE_OUTPUT_COMPLETE_RH_OPEN' if not gaps else 'PARTIAL_OUTPUT_RH_OPEN',
              'claim_cap':'RH_OPEN', 'unfulfilled_requirements':gaps}
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'scientific_disposition':result['scientific_disposition'],'unfulfilled_requirements':len(gaps)}))
    raise SystemExit(0 if not gaps else 2)
