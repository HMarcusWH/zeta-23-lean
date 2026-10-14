"""Harvest all workflow pages and attempts for an exact head; never promote skips."""
from __future__ import annotations
import argparse
import json
import os
import urllib.request
from pathlib import Path

REPOSITORY = 'HMarcusWH/zeta-23-lean'
ROLES = {
    ('RHRC post290 source and output proof components', 'lean-components'): 'FORMAL_VALIDITY_GATE',
    ('RHRC post290 source and output proof components', 'exact-controls'): 'REGRESSION_GATE',
    ('RHRC post290 source and output proof components', 'native-observations'): 'RESEARCH_PRODUCING_CHECK',
    ('RHRC post290 D2 SECOND continuation (manual)', 'd2-second-continuation'): 'RESEARCH_PRODUCING_CHECK',
    ('RHRC post290 K3 independent no-search shards','freeze-checker-shards'):'REGRESSION_GATE',
    ('RHRC post290 K3 independent no-search shards','independent-leaf-shards'):'RESEARCH_PRODUCING_CHECK',
    ('RHRC post290 K3 independent no-search shards','assemble-nonpartial'):'RESEARCH_PRODUCING_CHECK',
    ('RHRC materialize derived state for review','materialize'):'FORMAL_VALIDITY_GATE',
    ('RHRC approved SECOND460 resource continuation','freeze'):'REGRESSION_GATE',
    ('RHRC approved SECOND460 resource continuation','search-wave1'):'RESEARCH_PRODUCING_CHECK',
    ('RHRC approved SECOND460 resource continuation','search-wave2'):'RESEARCH_PRODUCING_CHECK',
    ('RHRC approved SECOND460 resource continuation','assemble-search'):'RESEARCH_PRODUCING_CHECK',
    ('RHRC approved SECOND460 resource continuation','final-nonpartial'):'RESEARCH_PRODUCING_CHECK',
}


def classify_job(workflow, job):
    if workflow == 'RHRC approved SECOND460 resource continuation':
        if job.startswith('independent-check-batches ('):
            if job.endswith('/ freeze-batch'):
                return 'REGRESSION_GATE'
            if '/ check-leaves (' in job:
                return 'RESEARCH_PRODUCING_CHECK'
    return ROLES.get((workflow, job.split(' (')[0]), 'REQUIRES_SOURCE_REVIEW')

def get(url):
    headers = {'Accept': 'application/vnd.github+json', 'User-Agent': 'RH-post290-harvest'}
    if os.environ.get('GH_TOKEN'):
        headers['Authorization'] = 'Bearer ' + os.environ['GH_TOKEN']
    with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=60) as r:
        return json.load(r)

def pages(url, key):
    result, page = [], 1
    while True:
        data = get(url + ('&' if '?' in url else '?') + f'per_page=100&page={page}')
        rows = data[key]
        result.extend(rows)
        if len(rows) < 100:
            return result
        page += 1

def inventory(head):
    root = 'https://api.github.com/repos/' + REPOSITORY
    runs = pages(root + '/actions/runs?head_sha=' + head, 'workflow_runs')
    for run in runs:
        if run['head_sha'] != head:
            raise ValueError('wrong workflow head returned')
        run['attempt_inventory'] = []
        for attempt in range(1, run['run_attempt'] + 1):
            jobs = pages(root + f"/actions/runs/{run['id']}/attempts/{attempt}/jobs", 'jobs')
            run['attempt_inventory'].append({'attempt': attempt, 'jobs': jobs})
    return {'head': head, 'runs': runs}

def harvest(snapshot):
    head, records = snapshot['head'], []
    for run in snapshot['runs']:
        if run['head_sha'] != head:
            raise ValueError('snapshot includes a different head')
        for attempt in run['attempt_inventory']:
            for job in attempt['jobs']:
                latest = attempt['attempt'] == run['run_attempt']
                role = classify_job(run['name'], job['name'])
                conclusion = job.get('conclusion')
                disposition = {
                    'skipped': 'NOT_EXECUTED', 'cancelled': 'CANCELLED_UNESTABLISHED',
                    'timed_out': 'UNRESOLVED_RESOURCE_LIMIT', 'failure': 'GATE_FAILED',
                }.get(conclusion, 'RUNNING_OR_QUEUED' if conclusion is None else 'READ_JOB_OUTPUT_REQUIRED')
                records.append({'run_id': run['id'], 'workflow': run['name'], 'job_id': job['id'],
                    'job': job['name'], 'name':job['name'], 'attempt': attempt['attempt'], 'latest_attempt': latest,
                    'classification': role, 'status': job['status'], 'conclusion': conclusion,
                    'scientific_disposition': disposition, 'url': job['html_url'],
                    'head': head, 'head_tree':run.get('head_commit',{}).get('tree_id'),
                    'runner_checked_head':None, 'runner_checked_tree':None, 'checkout_identity_review':None,
                    'required':role!='REQUIRES_SOURCE_REVIEW',
                    'scientific_acceptance':False,
                    'output_reviewed':False,
                    'acceptance_note':'Raw job status is not reviewed mathematical output; separate source-bound receipt required.',
                    'steps': job.get('steps', []), 'formal_authority_created_by_status': False})
    return {'head': head, 'repository': REPOSITORY, 'claim_cap': 'RH_OPEN', 'jobs': records,
            'all_latest_jobs_completed': bool(records) and all(r['status'] == 'completed' for r in records if r['latest_attempt']),
            'scope': 'Exact API dispositions and all attempts; success requires separate log/source review.'}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--head')
    p.add_argument('--snapshot', type=Path)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    if bool(args.head) == bool(args.snapshot):
        p.error('provide exactly one of --head and --snapshot')
    snapshot = json.loads(args.snapshot.read_text()) if args.snapshot else inventory(args.head)
    result = harvest(snapshot)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'head':result['head'],'job_attempts':len(result['jobs']),
                      'all_latest_jobs_completed':result['all_latest_jobs_completed']}))
