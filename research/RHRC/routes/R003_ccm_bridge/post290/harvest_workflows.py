"""Harvest all workflow pages and attempts for an exact head; never promote skips."""
from __future__ import annotations
import argparse
import json
import os
import urllib.request
from pathlib import Path

REPOSITORY = 'HMarcusWH/zeta-23-lean'
APPROVED_D2_RUN_ID = 38569316691
APPROVED_D2_HEAD = 'a55fbeeed6500bffe2ccac3960258ca5c590c7ee'
APPROVED_D2_WORKFLOW = 'RHRC approved SECOND460 resource continuation'
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


# Classification is only a research/CI JOB ROLE, never acceptance or theorem authority.
# Actual per-job logs and artifacts still require separate external review.
KNOWN_WORKFLOW_DEFAULTS = {
    # Source-reviewed deterministic compiler/derived-state validation. A skip
    # remains NOT_EXECUTED; the classification grants no scientific acceptance.
    'PR292 guarded one-shot RHKG generated-state refresh':'FORMAL_VALIDITY_GATE',
    'RHRC post287 bounded signed-ray probe':'RESEARCH_PRODUCING_CHECK',
    'RHRC post-214 kernel dual geometry':'REGRESSION_GATE',
    'RHRC post-194 parity trajectory sharp enclosure':'RESEARCH_PRODUCING_CHECK',
    'Permansson v0.1.6 formal verification':'FORMAL_VALIDITY_GATE',
    'RHRC post-198 Q14 parity source mechanism':'RESEARCH_PRODUCING_CHECK',
    'RHRC post-190 canonical realizability audit':'REGRESSION_GATE',
    'RHRC post287 focused Step3 checks':'REGRESSION_GATE',
    'RHRC post-222 bi-regular zero-shift scalar':'RESEARCH_PRODUCING_CHECK',
    'RHRC post-192 parity trajectory rigidity':'RESEARCH_PRODUCING_CHECK',
    'RHRC post-196 Q14 residual cell replay':'REGRESSION_GATE',
    'RHRC post-202 Q14 composite parity gap':'RESEARCH_PRODUCING_CHECK',
    'RHRC post-200 Q14 discrepancy mechanism':'RESEARCH_PRODUCING_CHECK',
    'RHRC parallel closure campaign':'REGRESSION_GATE',
    'RHRC post268 complete audit replay':'REGRESSION_GATE',
    'RHRC post-282 contact calculus':'REGRESSION_GATE',
    'RHRC post287 WP2 and WP4 interval research':'RESEARCH_PRODUCING_CHECK',
    'RHRC post-284 source inertia campaign':'RESEARCH_PRODUCING_CHECK',
    'RHRC research and Lean checks':'REGRESSION_GATE',
    'PR292 complete-output release candidate (manual)':'FORMAL_VALIDITY_GATE',
}

RELEASE_WORKFLOW='PR292 complete-output release candidate (manual)'
# A prerequisite snapshot cannot contain its own intake/release jobs.
# The post-release every-job inventory MUST include these administrative runs.
ADMIN_EVIDENCE_WORKFLOWS = {
    RELEASE_WORKFLOW,
    'PR292 independent 44-field review artifact intake (manual)',
    'PR292 prerequisite workflow scientific harvest intake (manual)',
}



def classify_job(workflow, job):
    if workflow == 'RHRC approved SECOND460 resource continuation':
        if job.startswith('independent-check-batches ('):
            if job.endswith('/ freeze-batch'):
                return 'REGRESSION_GATE'
            if '/ check-leaves (' in job:
                return 'RESEARCH_PRODUCING_CHECK'
    base=job.split(' (')[0]
    exact=ROLES.get((workflow,base))
    if exact:
        return exact
    if workflow in ('RHRC parallel closure campaign','RHRC post-282 contact calculus',
                    'RHRC post287 focused Step3 checks',
                    'RHRC post-284 source inertia campaign','RHRC research and Lean checks'):
        if base.startswith('lean') or base in ('r003-normalization-audit',):
            return 'FORMAL_VALIDITY_GATE'
        if 'research' in base or 'arb-' in base or 'modified-prime' in base:
            return 'RESEARCH_PRODUCING_CHECK'
    return KNOWN_WORKFLOW_DEFAULTS.get(workflow,'REQUIRES_SOURCE_REVIEW')

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

def inventory(head, approved_d2_run_id=None,
              phase='PRE_RELEASE_PREREQUISITES'):
    if phase not in ('PRE_RELEASE_PREREQUISITES','POST_RELEASE_EVERY_JOB'):
        raise ValueError('unrecognized workflow-harvest phase')
    root = 'https://api.github.com/repos/' + REPOSITORY
    runs = pages(root + '/actions/runs?head_sha=' + head, 'workflow_runs')
    excluded_administrative_runs = []
    if phase == 'PRE_RELEASE_PREREQUISITES':
        excluded_administrative_runs = [
            {'run_id': run['id'], 'workflow':run['name'], 'status':run['status'],
             'conclusion':run.get('conclusion'), 'head':run['head_sha'],
             'exclusion_reason':'ADMINISTRATIVE_INTAKE_NOT_PREREQUISITE'}
            for run in runs if run['name'] in ADMIN_EVIDENCE_WORKFLOWS
        ]
        runs = [run for run in runs if run['name'] not in ADMIN_EVIDENCE_WORKFLOWS]
    if approved_d2_run_id is not None:
        if type(approved_d2_run_id) is not int or approved_d2_run_id != APPROVED_D2_RUN_ID:
            raise ValueError('unapproved external numerical workflow ID')
        external = get(root + '/actions/runs/' + str(approved_d2_run_id))
        if (external.get('id') != APPROVED_D2_RUN_ID or
            external.get('head_sha') != APPROVED_D2_HEAD or
            external.get('name') != APPROVED_D2_WORKFLOW or
            external.get('run_attempt') != 1):
            raise ValueError('external D2 run does not match frozen approval')
        runs.append(external)
    for run in runs:
        if run['head_sha'] != head and not (run.get('id') == approved_d2_run_id
                                            and run['head_sha'] == APPROVED_D2_HEAD):
            raise ValueError('wrong workflow head returned')
        run['attempt_inventory'] = []
        for attempt in range(1, run['run_attempt'] + 1):
            jobs = pages(root + f"/actions/runs/{run['id']}/attempts/{attempt}/jobs", 'jobs')
            run['attempt_inventory'].append({'attempt': attempt, 'jobs': jobs})
    return {'head': head, 'runs': runs,
            'review_phase':phase, 'excluded_administrative_runs':excluded_administrative_runs,
            'external_d2_run_id': approved_d2_run_id}


def effective_jobs(records):
    """Validate ALL historical attempts; return one newest row per logical job.

    Identity includes the GitHub run ID. Separate workflow runs are never
    silently substituted for each other, and matrix/display-name collisions
    within one attempt fail closed.
    """
    if not isinstance(records, list) or not records:
        raise ValueError("missing workflow attempt inventory")
    latest = {}
    seen_jobs = set()
    for row in records:
        if not isinstance(row, dict):
            raise ValueError("invalid workflow attempt row")
        run_id, job_id, attempt = row.get("run_id"), row.get("job_id"), row.get("attempt")
        workflow, name = row.get("workflow"), row.get("name")
        if (type(run_id) is not int or run_id <= 0 or
            type(job_id) is not int or job_id <= 0 or
            type(attempt) is not int or attempt <= 0 or
            not isinstance(workflow, str) or not workflow or
            not isinstance(name, str) or not name):
            raise ValueError("invalid workflow attempt identity")
        if type(row.get("latest_attempt")) is not bool:
            raise ValueError("missing/non-Boolean latest_attempt")
        logical = (run_id, workflow, name)
        slot = (logical, attempt)
        if slot in seen_jobs:
            raise ValueError("duplicate logical job within one attempt")
        seen_jobs.add(slot)
        latest[logical] = max(latest.get(logical, 0), attempt)
    effective = []
    for row in records:
        logical = (row["run_id"], row["workflow"], row["name"])
        current = row["attempt"] == latest[logical]
        if row["latest_attempt"] is not current:
            raise ValueError("conflicting effective job attempt flags")
        if current:
            effective.append(row)
    return effective


def harvest(snapshot, phase='PRE_RELEASE_PREREQUISITES'):
    if phase not in ('PRE_RELEASE_PREREQUISITES','POST_RELEASE_EVERY_JOB'):
        raise ValueError('unknown release harvest phase')
    if snapshot.get('review_phase',phase) != phase:
        raise ValueError('review phase disagrees with live snapshot')
    excluded = snapshot.get('excluded_administrative_runs', [])
    if (not isinstance(excluded,list) or
        any(r.get('workflow') not in ADMIN_EVIDENCE_WORKFLOWS or
            r.get('exclusion_reason')!='ADMINISTRATIVE_INTAKE_NOT_PREREQUISITE'
            for r in excluded)):
        raise ValueError('unreviewed or fabricated excluded workflow')
    if phase == 'PRE_RELEASE_PREREQUISITES':
        if any(run.get('name') in ADMIN_EVIDENCE_WORKFLOWS
               for run in snapshot['runs']):
            raise ValueError('administrative job cannot approve its own prerequisite harvest')
    elif excluded:
        raise ValueError('post-release every-job harvest cannot exclude administrative runs')
    head, records = snapshot['head'], []
    external_id = snapshot.get('external_d2_run_id')
    if external_id not in (None, APPROVED_D2_RUN_ID):
        raise ValueError('snapshot uses a non-approved cross-head run')
    for run in snapshot['runs']:
        external = run.get('id') == external_id and run.get('head_sha') == APPROVED_D2_HEAD
        if run['head_sha'] != head and not external:
            raise ValueError('snapshot includes a different head')
        if external and (run.get('name') != APPROVED_D2_WORKFLOW or
                         run.get('run_attempt') != 1):
            raise ValueError('external D2 identity/attempt mismatch')
        for attempt in run['attempt_inventory']:
            for job in attempt['jobs']:
                if ('run_id' in job and
                    (type(job['run_id']) is not int or job['run_id'] != run['id'])):
                    raise ValueError('job run_id disagrees with enclosing run')
                if ('run_attempt' in job and
                    (type(job['run_attempt']) is not int or job['run_attempt'] != attempt['attempt'])):
                    raise ValueError('job run_attempt disagrees with enclosing attempt')
                latest = attempt['attempt'] == run['run_attempt']
                role = classify_job(run['name'], job['name'])
                conclusion = job.get('conclusion')
                disposition = {
                    'skipped': 'NOT_EXECUTED', 'cancelled': 'CANCELLED_UNESTABLISHED',
                    'timed_out': 'UNRESOLVED_RESOURCE_LIMIT', 'failure': 'GATE_FAILED',
                }.get(conclusion, 'RUNNING_OR_QUEUED' if conclusion is None else 'READ_JOB_OUTPUT_REQUIRED')
                mandatory = ((not external and
                              (run['name'], job['name']) in {
                                  ('RHRC post290 source and output proof components', 'lean-components'),
                                  ('RHRC post290 source and output proof components', 'exact-controls'),
                                  ('RHRC post290 source and output proof components', 'native-observations')})
                             or (external and job['name'] == 'final-nonpartial'))
                records.append({'run_id': run['id'], 'workflow': run['name'], 'job_id': job['id'],
                    'job': job['name'], 'name':job['name'], 'attempt': attempt['attempt'], 'latest_attempt': latest,
                    'classification': role, 'status': job['status'], 'conclusion': conclusion,
                    'scientific_disposition': disposition, 'url': job['html_url'],
                    'head': run['head_sha'], 'head_tree':run.get('head_commit',{}).get('tree_id'),
                    'evidence_scope': 'APPROVED_EXTERNAL_D2' if external else 'EXACT_PROOF_HEAD',
                    'runner_checked_head':None, 'runner_checked_tree':None, 'checkout_identity_review':None,
                    'required':mandatory,
                    'scientific_acceptance':False,
                    'output_reviewed':False,
                    'acceptance_note':'Raw job status is not reviewed mathematical output; separate source-bound receipt required.',
                    'steps': job.get('steps', []), 'formal_authority_created_by_status': False})
    # Recompute effective flags from each logical job's last *observed*
    # attempt: partial reruns may not repeat already-successful jobs.
    by_logical = {}
    for row in records:
        logical = (row["run_id"], row["workflow"], row["name"])
        by_logical[logical] = max(by_logical.get(logical, 0), row["attempt"])
    for row in records:
        logical = (row["run_id"], row["workflow"], row["name"])
        row["latest_attempt"] = row["attempt"] == by_logical[logical]
    effective_jobs(records)
    return {'head': head, 'repository': REPOSITORY, 'claim_cap': 'RH_OPEN',
            'review_phase':phase, 'includes_release_run':any(r['workflow']==RELEASE_WORKFLOW for r in records),
            'excluded_administrative_runs':excluded,
            'jobs': records,
            'all_latest_jobs_completed': bool(records) and all(r['status'] == 'completed' for r in records if r['latest_attempt']),
            'scope': 'Exact API dispositions and all attempts; success requires separate log/source review.'}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--head')
    p.add_argument('--snapshot', type=Path)
    p.add_argument('--approved-d2-run-id', type=int, default=None,
                   help='Read only the single approved D2 run; never dispatch or retry.')
    p.add_argument('--review-phase', choices=['PRE_RELEASE_PREREQUISITES','POST_RELEASE_EVERY_JOB'],
                   default='PRE_RELEASE_PREREQUISITES')
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    if bool(args.head) == bool(args.snapshot):
        p.error('provide exactly one of --head and --snapshot')
    if args.snapshot and args.approved_d2_run_id is not None:
        p.error('external D2 selection must come from the frozen snapshot in snapshot mode')
    snapshot = (json.loads(args.snapshot.read_text()) if args.snapshot else
                inventory(args.head, args.approved_d2_run_id, args.review_phase))
    result = harvest(snapshot, args.review_phase)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'head':result['head'],'job_attempts':len(result['jobs']),
                      'all_latest_jobs_completed':result['all_latest_jobs_completed']}))
