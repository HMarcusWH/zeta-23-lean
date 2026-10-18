"""Read-only replay of the existing canonical validator on captured D2 results.

This validates result records, not their numerical inequalities. It dispatches
no search and cannot replace the required fresh 768-bit independent checker.
Raw plan and result ZIPs remain external inputs authenticated by their hashes.
"""
from pathlib import Path
import argparse, hashlib, json, sys, zipfile

REPO = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO / 'research/RHRC/routes/R003_ccm_bridge/post290'))
import k3_continue_unrun460 as C


def need(condition, message):
    if not condition:
        raise ValueError(message)


def validate(ledger_path, plan_zip, cache):
    ledger = json.loads(ledger_path.read_text())
    with zipfile.ZipFile(plan_zip) as archive:
        plan_bytes = archive.read('plan.json')
    plan_hash = hashlib.sha256(plan_bytes).hexdigest()
    need(plan_hash == '433107bbfe412625223fe1f08da36ca7d837bd82e7a536fc50a2d447886cf6ef',
         'Wrong frozen single-use plan')
    need(ledger['plan_sha256'] == plan_hash and ledger['child_count'] == 460,
         'Wrong ledger plan or child count')
    plan = json.loads(plan_bytes)
    need(plan['resources'] == C.RESOURCE and plan['max_concurrency'] == 8,
         'Frozen resource limits changed')
    need(plan['budget_policy'] == 'ONE_EXECUTION_PER_CHILD_NO_RERUN_NO_RETRY',
         'Frozen no-retry policy changed')
    need(len(ledger['rows']) == 460 and
         [row['index'] for row in ledger['rows']] == list(range(460)),
         'Missing, reordered or duplicate child index')
    count = 0
    for row in ledger['rows']:
        spec = plan['jobs'][row['index']]
        need(spec['job']['id'] == row['child_id'], 'Ledger child identity changed')
        if row['scientific_disposition'] not in {'PASS', 'UNRESOLVED'}:
            continue
        path = cache / (str(row['artifact_id']) + '.zip')
        need(hashlib.sha256(path.read_bytes()).hexdigest() == row['artifact_digest'].split(':')[-1],
             'Result ZIP digest mismatch')
        with zipfile.ZipFile(path) as archive:
            need(archive.testzip() is None, 'Result ZIP CRC failure')
            payload = archive.read('result.json')
        need(hashlib.sha256(payload).hexdigest() == row['result_sha256'],
             'Result member digest mismatch')
        result = C.validate_result(json.loads(payload), spec['job'], plan_hash)
        need(not result['certified_negative_stop'], 'Certified negative requires investigation')
        need(result['status'] == row['scientific_disposition'], 'Ledger disposition mismatch')
        need(len(result['accepted']) == row['accepted_leaves'] and
             len(result['unresolved']) == row['unresolved_pieces'], 'Ledger piece count mismatch')
        count += 1
    need(count == sum(ledger['scientific_counts'].get(name, 0) for name in ['PASS', 'UNRESOLVED']),
         'Incomplete captured result replay')
    return {'scope':'EXISTING_CANONICAL_RESULT_VALIDATOR_REPLAY_ONLY',
        'validated_completed_children':count, 'plan_sha256':plan_hash,
        'ledger_sha256':hashlib.sha256(ledger_path.read_bytes()).hexdigest(),
        'existing_validator_sha256':hashlib.sha256(Path(C.__file__).read_bytes()).hexdigest(),
        'fresh_768_bit_independent_checker':'NOT_RUN_BY_THIS_PROGRAM',
        'D2':'OPEN','RH':'OPEN'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger', type=Path, required=True)
    parser.add_argument('--plan-zip', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = validate(args.ledger, args.plan_zip, args.cache)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
