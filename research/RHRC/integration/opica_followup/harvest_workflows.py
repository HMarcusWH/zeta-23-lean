"""Harvest exact GitHub execution scopes without promoting scientific outcomes.

``harvest`` is an offline validator; ``collect`` accepts an injected JSON reader.
The CLI uses only public GitHub GET endpoints. A collection is not mathematical
review: exact command/receipt/disposition reviews are supplied separately.
"""
from __future__ import annotations

import argparse
import base64
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import re
from urllib.parse import urlencode, urlsplit
from urllib.request import Request, urlopen

SCHEMA = 'OPICA_FOLLOWUP_WORKFLOW_HARVEST_V1'
SHA = re.compile(r'[0-9a-f]{40}\Z')
HASH = re.compile(r'[0-9a-f]{64}\Z')
WORKFLOW = '.github/workflows/rhrc_opica_followup.yml'
CLASSES = {'FORMAL_VALIDITY_GATE', 'FORMAL_VALIDITY_GATE_STATIC',
           'REGRESSION_GATE', 'RESEARCH_PRODUCING_CHECK', 'COMPLETENESS_GATE'}
STATUSES = {'queued', 'in_progress', 'completed', 'waiting', 'pending', 'requested'}
CHILD_JOBS = {
    'followup-contract': 'FORMAL_VALIDITY_GATE_STATIC',
    'followup-regression': 'REGRESSION_GATE',
    **{'followup-formal (' + lane + ')': 'FORMAL_VALIDITY_GATE'
       for lane in ('local', 'arithmetic', 'heat', 'spectral')},
    'followup-aggregate': 'FORMAL_VALIDITY_GATE',
    'followup-generated': 'REGRESSION_GATE',
    'followup-research-delta': 'RESEARCH_PRODUCING_CHECK',
    'followup-summary': 'COMPLETENESS_GATE',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, minimum=0):
    return type(value) is int and value >= minimum


def sha(value):
    return isinstance(value, str) and SHA.fullmatch(value) is not None


def complete_pages(pages, field):
    """Reject changing totals, duplicates, and first-page-only inventories."""
    require(isinstance(pages, list) and bool(pages), 'missing pages: ' + field)
    counts = [p.get('total_count') for p in pages]
    require(all(integer(n) for n in counts) and len(set(counts)) == 1,
            'unstable or invalid provider total: ' + field)
    require(all(isinstance(p.get(field), list) for p in pages),
            'missing provider collection: ' + field)
    items = [item for page in pages for item in page[field]]
    require(len(items) == counts[0], 'incomplete or excess pages: ' + field)
    ids = [item.get('id') for item in items]
    require(all(integer(i, 1) for i in ids) and len(ids) == len(set(ids)),
            'duplicate or invalid provider identity: ' + field)
    return items


def fetch_pages(fetch_json, url, field):
    pages, seen = [], 0
    for page in range(1, 10001):
        separator = '&' if '?' in url else '?'
        payload = fetch_json(url + separator + urlencode({'per_page': 100, 'page': page}))
        require(isinstance(payload, dict) and integer(payload.get('total_count')),
                'invalid paginated response: ' + field)
        require(isinstance(payload.get(field), list), 'invalid collection: ' + field)
        if pages:
            require(payload['total_count'] == pages[0]['total_count'],
                    'provider total changed during collection: ' + field)
        pages.append(payload)
        seen += len(payload[field])
        require(seen <= payload['total_count'], 'excess provider records: ' + field)
        if seen == payload['total_count']:
            complete_pages(pages, field)
            return pages
        require(bool(payload[field]), 'empty page before provider total: ' + field)
    raise ValueError('pagination limit reached: ' + field)


def _collections(data, key, field):
    collections = data.get(key + '_collections')
    if collections is None:
        collections = [{'head_sha': data['head_sha'], 'pages': data[key + '_pages']}]
    rows, source_ids = [], set()
    for collection in collections:
        source = collection['head_sha']
        require(source not in source_ids, 'duplicate source collection: ' + key)
        source_ids.add(source)
        items = complete_pages(collection['pages'], field)
        require(all(item.get('head_sha') == source for item in items),
                'provider source/query mismatch: ' + key)
        rows.extend(items)
    require(source_ids == set(data.get('collected_shas', [data['head_sha']])),
            'missing source collection: ' + key)
    require(len({row['id'] for row in rows}) == len(rows), 'duplicate cross-source ' + key)
    return rows


def default_policy(runs, head_sha):
    events = {r['event'] for r in runs if r['path'].split('@', 1)[0] == WORKFLOW
              and r['head_sha'] == head_sha} or {'pull_request'}
    return [{'workflow': WORKFLOW, 'event': event, 'head_sha': head_sha,
             'name': name, 'required': True, 'classification': kind}
            for event in sorted(events) for name, kind in CHILD_JOBS.items()]


def _policy_for(job, policies):
    matches = [p for p in policies if p['workflow'] == job['workflow']
               and p['event'] == job['event'] and p['name'] == job['name']
               and p.get('head_sha', job['head_sha']) == job['head_sha']]
    require(len(matches) <= 1, 'ambiguous job policy: ' + job['name'])
    return matches[0] if matches else None


def classify_job(job, policies):
    policy = _policy_for(job, policies)
    if policy:
        return policy['classification']
    if job['workflow'] == WORKFLOW and job['name'] in CHILD_JOBS:
        return CHILD_JOBS[job['name']]
    return 'UNCLASSIFIED'


def compare_fixture(review, previous_jobs):
    fixture, digest = review.get('fixture_id'), review.get('fixture_sha256')
    if not fixture or not isinstance(digest, str) or not HASH.fullmatch(digest):
        return {'status': 'NOT_COMPARABLE', 'reason': 'exact fixture identity absent'}
    matches = [j for j in previous_jobs if j.get('review', {}).get('fixture_id') == fixture
               and j['review'].get('fixture_sha256') == digest]
    if not matches:
        return {'status': 'NOT_COMPARABLE', 'reason': 'no prior identical fixture'}
    prior = [j['review']['mathematical_disposition'] for j in matches]
    return {'status': 'UNCHANGED' if all(p == review['mathematical_disposition'] for p in prior)
            else 'CHANGED', 'previous_job_ids': [j['id'] for j in matches]}


def _validate_review(review, job, data, classification):
    require(isinstance(review, dict), 'invalid job review')
    for key in ('run_id', 'attempt', 'head_sha', 'event'):
        require(review.get(key) == job[key], 'mixed-source review identity: ' + key)
    checked, tree = review.get('checked_sha'), review.get('checked_tree')
    require(sha(checked) and sha(tree) and data['commit_trees'].get(checked) == tree,
            'unresolved reviewed checkout/tree')
    require(checked in data.get('collected_shas', [data['head_sha']]), 'foreign reviewed checkout')
    if checked != job['head_sha']:
        parents = data.get('commit_parents', {}).get(checked, [])
        require(len(parents) == 2 and job['head_sha'] in parents,
                'stale reviewed synthetic merge')
    require(review.get('classification') in CLASSES, 'unclassified reviewed job')
    if classification != 'UNCLASSIFIED':
        require(review['classification'] == classification, 'review classification drift')
    require(isinstance(review.get('commands'), list) and bool(review['commands']),
            'review lacks actual command records')
    for command in review['commands']:
        require(isinstance(command, dict) and isinstance(command.get('command'), str)
                and bool(command['command'].strip()) and type(command.get('exit_code')) is int,
                'invalid reviewed command/exit record')
    require('mathematical_disposition' in review and review['mathematical_disposition']
            not in (None, '', {}, []), 'scientific output not reviewed')
    for artifact in review.get('artifacts', []):
        require(artifact.get('checked_tree') == tree and artifact.get('checked_sha') == checked,
                'mixed-source artifacts')
        require(isinstance(artifact.get('sha256'), str) and HASH.fullmatch(artifact['sha256']),
                'invalid reviewed artifact digest')
    return deepcopy(review)


def harvest(data, previous=None):
    """Validate a complete snapshot; return failures as data, never as green.

    Provider-integrity errors raise ValueError. Only unsuccessful *required*
    effective jobs/checks block execution. Optional skips, cancellations, pending
    jobs and every historical failure remain in the report verbatim.
    """
    data = deepcopy(data)
    for field in ('head_sha', 'head_tree'):
        require(sha(data.get(field)), 'invalid source identity: ' + field)
    trees = data.get('commit_trees', {})
    require(trees.get(data['head_sha']) == data['head_tree'], 'foreign head tree')
    require(all(sha(k) and sha(v) for k, v in trees.items()), 'invalid commit tree map')
    allowed = set(data.get('collected_shas', [data['head_sha']]))
    require(data['head_sha'] in allowed and allowed <= set(trees), 'unresolved source scopes')
    checked = data.get('checked_sha', data['head_sha'])
    require(checked in allowed and data.get('checked_tree', trees[checked]) == trees[checked],
            'checked source/tree mismatch')
    for source in allowed - {data['head_sha']}:
        parents = data.get('commit_parents', {}).get(source, [])
        require(len(parents) == 2 and len(set(parents)) == 2
                and all(sha(parent) for parent in parents) and data['head_sha'] in parents,
                'stale synthetic merge source')
    runs = _collections(data, 'run', 'workflow_runs')
    checks = _collections(data, 'check', 'check_runs')
    run_by_id = {r['id']: r for r in runs}
    policy = data.get('job_policies', data.get('expected_jobs'))
    if policy is None:
        policy = default_policy(runs, data['head_sha'])
    require(isinstance(policy, list) and bool(policy), 'required job policy absent')
    for p in policy:
        require(isinstance(p.get('workflow'), str) and isinstance(p.get('event'), str)
                and isinstance(p.get('name'), str) and type(p.get('required')) is bool,
                'policy must give exact workflow/event/name and required Boolean')
        require(p.get('classification') in CLASSES, 'invalid policy classification')
        require('head_sha' not in p or sha(p['head_sha']), 'invalid policy head')
    require(any(p['required'] for p in policy), 'vacuous required policy')
    # An extension contract may describe inherited jobs, but cannot demote a
    # prescribed child proof lane. These names are the specification's roles,
    # not a permanent assertion about how many attached jobs succeeded.
    child_scopes = {(r['event'], r['head_sha']) for r in runs
                    if r['path'].split('@', 1)[0] == WORKFLOW}
    for event, source in child_scopes:
        for name, kind in CHILD_JOBS.items():
            row = {'workflow': WORKFLOW, 'event': event, 'head_sha': source, 'name': name}
            existing = _policy_for(row, policy)
            if existing is None:
                policy.append({**row, 'required': True, 'classification': kind})
            else:
                require(existing['required'] and existing['classification'] == kind,
                        'required child lane demoted or reclassified')
    latest, attempt_jobs, run_numbers = {}, {}, set()
    for run in runs:
        require(run.get('head_sha') in allowed, 'foreign run head')
        require(integer(run.get('run_attempt'), 1) and integer(run.get('run_number'), 1),
                'invalid run attempt/number')
        path = run.get('path', '').split('@', 1)[0]
        require(path.startswith('.github/workflows/') and '..' not in path.split('/'),
                'invalid workflow path')
        require(isinstance(run.get('event'), str) and bool(run['event']), 'missing run event')
        require(run.get('status') in STATUSES, 'invalid run status')
        scope = (path, run['event'], run['head_sha'])
        prior = latest.get(scope)
        require((*scope, run['run_number']) not in run_numbers,
                'conflicting workflow run number')
        run_numbers.add((*scope, run['run_number']))
        if prior is None or run['run_number'] > prior['run_number']:
            latest[scope] = run
    for record in data.get('job_pages', []):
        run_id, attempt = record['run_id'], record['attempt']
        require(run_id in run_by_id and integer(attempt, 1)
                and attempt <= run_by_id[run_id]['run_attempt'], 'foreign job attempt')
        require((run_id, attempt) not in attempt_jobs, 'duplicate job attempt collection')
        jobs = complete_pages(record['pages'], 'jobs')
        require(len({j.get('name') for j in jobs}) == len(jobs), 'duplicate job name in attempt')
        for job in jobs:
            run = run_by_id[run_id]
            require(job.get('run_id') == run_id and job.get('run_attempt') == attempt,
                    'job run/attempt mismatch')
            require(job.get('head_sha') == run['head_sha'], 'job head mismatch')
            require(job.get('event', run['event']) == run['event'], 'job event mismatch')
            require(isinstance(job.get('name'), str) and bool(job['name']), 'invalid job name')
            require(job.get('status') in STATUSES, 'invalid job status')
            if job.get('status') == 'completed':
                require(isinstance(job.get('conclusion'), str) and bool(job['conclusion']),
                        'completed job has no conclusion')
        attempt_jobs[(run_id, attempt)] = jobs
    all_jobs, effective, used_reviews, job_ids = [], {}, set(), set()
    previous_jobs = (previous or {}).get('effective_jobs', [])
    for run in runs:
        scope = (run['path'].split('@', 1)[0], run['event'], run['head_sha'])
        for attempt in range(1, run['run_attempt'] + 1):
            require((run['id'], attempt) in attempt_jobs, 'missing historical job attempt')
            for raw in attempt_jobs[(run['id'], attempt)]:
                require(raw['id'] not in job_ids, 'job identity reused across attempts')
                job_ids.add(raw['id'])
                job = {**raw, 'workflow': scope[0], 'event': scope[1],
                       'head_sha': scope[2], 'attempt': attempt, 'conclusion': raw.get('conclusion')}
                p = _policy_for(job, policy)
                job['required'] = bool(p and p['required'])
                job['classification'] = classify_job(job, policy)
                key = str(run['id']) + ':' + str(attempt) + ':' + str(job['id'])
                review = data.get('job_reviews', {}).get(key)
                job['review_status'] = 'UNREVIEWED'
                if job['conclusion'] == 'skipped':
                    job['conditional_disposition'] = data.get('conditional_skips', {}).get(key)
                if review is not None:
                    used_reviews.add(key)
                    job['review'] = _validate_review(review, job, data, job['classification'])
                    job['classification'] = review['classification']
                    job['review_status'] = 'RECORDED_NOT_INDEPENDENT_APPROVAL'
                    job['fixture_comparison'] = compare_fixture(review, previous_jobs)
                all_jobs.append(job)
                if latest[scope]['id'] == run['id']:
                    effective[(*scope, job['name'])] = job
    require(used_reviews == set(data.get('job_reviews', {})), 'review refers to an absent job attempt')
    blockers = []
    for scope, run in latest.items():
        required_scope = any(p['required'] and p['workflow'] == scope[0]
                             and p['event'] == scope[1]
                             and p.get('head_sha', scope[2]) == scope[2] for p in policy)
        if required_scope and (run['status'] != 'completed' or run.get('conclusion') != 'success'):
            blockers.append({'reason': 'REQUIRED_WORKFLOW_NOT_SUCCESSFUL', 'run_id': run['id'],
                             'status': run['status'], 'conclusion': run.get('conclusion')})
    for p in policy:
        if not p['required']:
            continue
        matches = [j for j in effective.values() if _policy_for(j, [p])]
        if not matches:
            blockers.append({'reason': 'MISSING_REQUIRED_JOB', 'policy': p})
        for j in matches:
            if j['status'] != 'completed' or j['conclusion'] != 'success':
                blockers.append({'reason': 'REQUIRED_JOB_NOT_SUCCESSFUL', 'job_id': j['id'],
                                 'status': j['status'], 'conclusion': j['conclusion']})
            review = j.get('review')
            if review and review['checked_tree'] != data.get('checked_tree', data['head_tree']):
                blockers.append({'reason': 'REQUIRED_JOB_FOREIGN_CHECKED_TREE', 'job_id': j['id']})
            if review and any(c['exit_code'] != 0 for c in review['commands']):
                blockers.append({'reason': 'NONZERO_REQUIRED_COMMAND', 'job_id': j['id']})
    latest_checks = {}
    for check in checks:
        require(check.get('head_sha') in allowed, 'foreign attached check')
        require(integer(check.get('app', {}).get('id'), 1)
                and isinstance(check.get('name'), str) and bool(check['name']),
                'invalid attached check app/name')
        require(check.get('status') in STATUSES, 'invalid attached check status')
        if check['status'] == 'completed':
            require(isinstance(check.get('conclusion'), str) and bool(check['conclusion']),
                    'completed attached check has no conclusion')
        key = (check.get('app', {}).get('id'), check.get('name'), check['head_sha'])
        prior = latest_checks.get(key)
        # A freshly queued check can lack started_at. Its newer provider ID
        # must supersede an older successful check, even without a start time.
        if prior is None or check['id'] > prior['id']:
            latest_checks[key] = check
    for p in data.get('required_checks', []):
        matches = [c for c in latest_checks.values() if c.get('name') == p['name']
                   and c.get('app', {}).get('id') == p['app_id'] and c['head_sha'] == p['head_sha']]
        if not matches or any(c.get('status') != 'completed' or c.get('conclusion') != 'success' for c in matches):
            blockers.append({'reason': 'REQUIRED_ATTACHED_CHECK_NOT_SUCCESSFUL', 'policy': p})
    artifacts, artifact_runs, artifact_ids = [], set(), set()
    for record in data.get('artifact_pages', []):
        require(record['run_id'] in run_by_id, 'foreign artifact run')
        require(record['run_id'] not in artifact_runs, 'duplicate artifact collection')
        artifact_runs.add(record['run_id'])
        for artifact in complete_pages(record['pages'], 'artifacts'):
            require(artifact['id'] not in artifact_ids, 'artifact identity reused across runs')
            artifact_ids.add(artifact['id'])
            require(artifact.get('workflow_run', {}).get('id') == record['run_id'],
                    'artifact run mismatch')
            require(artifact.get('workflow_run', {}).get('head_sha')
                    == run_by_id[record['run_id']]['head_sha'], 'artifact head mismatch')
            artifacts.append({'run_id': record['run_id'], **artifact})
    require(artifact_runs == set(run_by_id), 'missing artifact pagination')
    provider_artifacts = {a['id']: a for a in artifacts}
    for j in all_jobs:
        for a in j.get('review', {}).get('artifacts', []):
            provider = provider_artifacts.get(a.get('id'))
            require(provider and provider['run_id'] == j['run_id'], 'reviewed artifact belongs to another run')
            digest = provider.get('digest')
            require(digest is None or digest == 'sha256:' + a['sha256'], 'reviewed artifact/provider digest mismatch')
            a['provider_digest_matches'] = digest is not None
    source_keys = set()
    for source in data.get('workflow_sources', []):
        key = (source['path'], source['source_sha'])
        require(key not in source_keys, 'duplicate workflow source')
        source_keys.add(key)
        require(source['source_sha'] in allowed and source.get('source_tree') == trees[source['source_sha']],
                'foreign workflow source tree')
        raw = source['content'].encode('utf-8')
        require(source.get('sha256') == hashlib.sha256(raw).hexdigest(), 'workflow source digest mismatch')
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(source.get('git_blob') == blob, 'workflow source blob mismatch')
    expected_sources = {(r['path'].split('@', 1)[0], r['head_sha']) for r in runs}
    require(source_keys <= expected_sources, 'unexpected workflow source')
    sources_complete = source_keys == expected_sources
    jobs = list(effective.values())
    review_complete = bool(jobs) and sources_complete and all(j['status'] == 'completed' and j['classification'] != 'UNCLASSIFIED'
                          and (j['review_status'] != 'UNREVIEWED'
                               or (j['conclusion'] == 'skipped' and j.get('conditional_disposition')))
                          for j in jobs)
    return {'schema': SCHEMA, 'status': 'BLOCKED' if blockers else 'PASS',
            'execution_status': 'BLOCKED' if blockers else 'PASS',
            'review_status': 'RECORDED_NOT_INDEPENDENT_APPROVAL' if review_complete else 'INCOMPLETE',
            'head_sha': data['head_sha'], 'head_tree': data['head_tree'],
            'checked_sha': checked, 'checked_tree': trees[checked],
            'commit_trees': trees, 'collected_shas': sorted(allowed), 'blockers': blockers,
            'job_policies': policy, 'effective_jobs': jobs, 'all_job_attempts': all_jobs,
            'all_workflow_runs': runs, 'all_check_runs': checks,
            'effective_checks': list(latest_checks.values()), 'artifacts': artifacts,
            'workflow_sources': data.get('workflow_sources', []),
            'workflow_source_inventory': 'COMPLETE' if sources_complete else 'INCOMPLETE',
            'independent_review_approved': False, 'theorem_promotion': False,
            'RH': 'OPEN', 'Step4': 'OPEN',
            'authority': 'Execution inventory and explicit reviews; scientific dispositions retain their own scope.'}


def collect(fetch_json, repository, head_sha, checked_sha=None):
    require(re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository), 'invalid repository')
    require(sha(head_sha) and (checked_sha is None or sha(checked_sha)), 'exact 40-hex head required')
    root = 'https://api.github.com/repos/' + repository
    sources = list(dict.fromkeys([head_sha] + ([checked_sha] if checked_sha else [])))
    data = {'repository': repository, 'head_sha': head_sha, 'checked_sha': checked_sha or head_sha,
            'collected_shas': sources,
            'commit_trees': {}, 'commit_parents': {}, 'run_collections': [],
            'check_collections': [], 'job_pages': [], 'artifact_pages': [], 'workflow_sources': []}
    for source in sources:
        commit = fetch_json(root + '/git/commits/' + source)
        require(commit.get('sha') == source and sha(commit.get('tree', {}).get('sha')), 'foreign Git commit response')
        data['commit_trees'][source] = commit['tree']['sha']
        data['commit_parents'][source] = [p['sha'] for p in commit['parents']]
        data['run_collections'].append({'head_sha': source, 'pages': fetch_pages(
            fetch_json, root + '/actions/runs?' + urlencode({'head_sha': source}), 'workflow_runs')})
        data['check_collections'].append({'head_sha': source, 'pages': fetch_pages(
            fetch_json, root + '/commits/' + source + '/check-runs?filter=all', 'check_runs')})
    data['head_tree'] = data['commit_trees'][head_sha]
    data['checked_tree'] = data['commit_trees'][checked_sha or head_sha]
    runs = _collections(data, 'run', 'workflow_runs')
    frozen_sources = set()
    for run in runs:
        for attempt in range(1, run['run_attempt'] + 1):
            url = root + '/actions/runs/' + str(run['id']) + '/attempts/' + str(attempt) + '/jobs'
            data['job_pages'].append({'run_id': run['id'], 'attempt': attempt,
                                     'pages': fetch_pages(fetch_json, url, 'jobs')})
        data['artifact_pages'].append({'run_id': run['id'], 'pages': fetch_pages(
            fetch_json, root + '/actions/runs/' + str(run['id']) + '/artifacts', 'artifacts')})
        path, ref = run['path'].split('@', 1)[0], run['head_sha']
        if (path, ref) not in frozen_sources:
            require(path.startswith('.github/workflows/') and '..' not in path.split('/'), 'invalid workflow source path')
            content = fetch_json(root + '/contents/' + path + '?' + urlencode({'ref': ref}))
            require(content.get('encoding') == 'base64' and content.get('path') == path,
                    'invalid frozen workflow response')
            raw = base64.b64decode(content['content'])
            blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            require(blob == content.get('sha'), 'workflow blob content mismatch')
            data['workflow_sources'].append({'path': path, 'source_sha': ref,
                'source_tree': data['commit_trees'][ref], 'git_blob': content['sha'],
                'sha256': hashlib.sha256(raw).hexdigest(), 'content': raw.decode('utf-8')})
            frozen_sources.add((path, ref))
    # A rerun or new workflow created during collection invalidates the snapshot;
    # no earlier favorable attempt is silently presented as the latest one.
    for collection in data['run_collections']:
        fresh = fetch_pages(fetch_json, root + '/actions/runs?' + urlencode(
            {'head_sha': collection['head_sha']}), 'workflow_runs')
        keys = ('id', 'head_sha', 'event', 'path', 'run_number', 'run_attempt', 'status', 'conclusion')
        identity = lambda pages: sorted(tuple(r.get(k) for k in keys)
                                       for r in complete_pages(pages, 'workflow_runs'))
        require(identity(fresh) == identity(collection['pages']), 'workflow inventory changed during collection')
    for collection in data['check_collections']:
        fresh = fetch_pages(fetch_json, root + '/commits/' + collection['head_sha']
                            + '/check-runs?filter=all', 'check_runs')
        keys = ('id', 'head_sha', 'name', 'status', 'conclusion', 'started_at')
        identity = lambda pages: sorted(tuple(c.get(k) for k in keys)
                                       for c in complete_pages(pages, 'check_runs'))
        require(identity(fresh) == identity(collection['pages']), 'attached checks changed during collection')
    return data


def public_github_json(url):
    require(urlsplit(url).scheme == 'https' and urlsplit(url).netloc == 'api.github.com',
            'only GitHub API GET URLs are allowed')
    headers = {'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28',
               'User-Agent': 'opica-followup-workflow-harvest'}
    token = os.environ.get('GITHUB_TOKEN') or os.environ.get('GH_TOKEN')
    if token:
        headers['Authorization'] = 'Bearer ' + token
    with urlopen(Request(url, headers=headers, method='GET'), timeout=30) as response:
        return json.load(response)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo')
    parser.add_argument('--head')
    parser.add_argument('--checked-sha')
    parser.add_argument('--input', type=Path, help='offline raw collection JSON')
    parser.add_argument('--contract', type=Path, help='job_policies and optional required_checks')
    parser.add_argument('--reviews', type=Path, help='exact run:attempt:job review mapping')
    parser.add_argument('--previous', type=Path, help='previous harvest for exact-fixture comparison')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    read = lambda p: json.loads(p.read_text(encoding='utf-8'))
    if args.input:
        data = read(args.input)
        require(args.head is None or args.head == data['head_sha'], 'input belongs to a different requested head')
        require(args.repo is None or args.repo == data.get('repository'), 'input belongs to a different repository')
    else:
        require(args.repo and args.head, '--repo and --head are required for collection')
        data = collect(public_github_json, args.repo, args.head, args.checked_sha)
    if args.contract:
        contract = read(args.contract)
        data['job_policies'] = contract['job_policies']
        data['required_checks'] = contract.get('required_checks', [])
    if args.reviews:
        data['job_reviews'] = read(args.reviews)
    result = harvest(data, read(args.previous) if args.previous else None)
    # Raw pages remain available for independent pagination/attempt auditing.
    result['raw_collection'] = data
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'execution_status': result['execution_status'],
                      'review_status': result['review_status'], 'RH': 'OPEN',
                      'required_blockers': len(result['blockers'])}))
    return 1 if result['blockers'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
