"""Resolve complete GitHub run/check/job pages without dropping failed attempts."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SHA = re.compile(r'[0-9a-f]{40}\Z')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def complete_pages(pages, field):
    require(bool(pages), 'missing paginated '+field)
    counts = {page.get('total_count') for page in pages}
    require(len(counts) == 1 and type(next(iter(counts))) is int, 'unstable/missing provider total: '+field)
    items = [item for page in pages for item in page[field]]
    require(len(items) == next(iter(counts)), 'incomplete or duplicated pages: '+field)
    ids = [item['id'] for item in items]
    require(len(ids) == len(set(ids)), 'duplicate provider identity: '+field)
    return items


def harvest(data):
    for key in ('head_sha','head_tree','checked_sha','checked_tree'):
        require(isinstance(data.get(key),str) and SHA.fullmatch(data[key]), 'invalid source identity: '+key)
    trees = data['commit_trees']
    require(trees.get(data['head_sha']) == data['head_tree'], 'foreign PR head tree')
    require(trees.get(data['checked_sha']) == data['checked_tree'], 'foreign checked tree')
    if data['checked_sha'] != data['head_sha']:
        require(data['head_sha'] in data.get('checked_parents',[]), 'stale synthetic merge: current head is not a parent')
    runs = complete_pages(data['run_pages'],'workflow_runs')
    checks = complete_pages(data['check_pages'],'check_runs')
    require(bool(checks),'attached check inventory empty')
    run_by_id = {run['id']:run for run in runs}
    allowed_shas = {data['head_sha'],data['checked_sha']}
    for record in runs + checks:
        require(record['head_sha'] in allowed_shas, 'foreign run/check head')
        require(record['head_sha'] in trees, 'unresolved run/check tree')
    jobs_by_attempt = {}
    for collection in data['job_pages']:
        key = (collection['run_id'],collection['attempt'])
        require(key not in jobs_by_attempt, 'duplicate run/attempt job collection')
        require(key[0] in run_by_id, 'job collection has unknown run')
        require(1 <= key[1] <= run_by_id[key[0]]['run_attempt'], 'foreign attempt')
        jobs = complete_pages(collection['pages'],'jobs')
        require(len({job['name'] for job in jobs}) == len(jobs), 'duplicate job name in one attempt')
        for job in jobs:
            require(job['run_id'] == key[0] and job.get('run_attempt',key[1]) == key[1], 'job run identity mismatch')
            require(job.get('head_sha',run_by_id[key[0]]['head_sha']) == run_by_id[key[0]]['head_sha'], 'job head mismatch')
            require(job.get('event',run_by_id[key[0]]['event']) == run_by_id[key[0]]['event'], 'job event mismatch')
        jobs_by_attempt[key] = jobs
    effective, history = {}, []
    latest_runs = {}
    for run in runs:
        path = run['path'].split('@',1)[0]
        scope = (path,run['event'],run['head_sha'])
        prior = latest_runs.get(scope)
        if prior is None or run['run_number'] > prior['run_number']:
            latest_runs[scope] = run
        elif run['run_number'] == prior['run_number']:
            raise ValueError('conflicting run_number identity')
        for attempt in range(1,run['run_attempt']+1):
            require((run['id'],attempt) in jobs_by_attempt, 'missing historical attempt')
            for job in jobs_by_attempt[(run['id'],attempt)]:
                history.append({'workflow':path,'run_id':run['id'],'attempt':attempt,
                    'event':run['event'],'head_sha':run['head_sha'],**job})
    for scope,run in latest_runs.items():
        require(run['status'] == 'completed', 'workflow still running or queued')
        require(run['conclusion'] == 'success', 'workflow cancelled/skipped/failed/unresolved')
        for attempt in range(1,run['run_attempt']+1):
            for job in jobs_by_attempt[(run['id'],attempt)]:
                effective[(*scope,job['name'])] = {'workflow':scope[0], 'run_id':run['id'],
                    'attempt':attempt,'event':scope[1],'head_sha':scope[2],**job}
    skips = data.get('reviewed_skips',{})
    for key,job in effective.items():
        require(job['status'] == 'completed', 'required job running/queued: '+job['name'])
        if job['conclusion'] == 'skipped':
            identity = f"{job['run_id']}:{job['attempt']}:{job['id']}"
            require(bool(skips.get(identity)), 'skipped job lacks exact reviewed disposition')
            require(job['workflow'] != '.github/workflows/rhrc_opica.yml', 'required OPICA job skipped')
            job['disposition'] = 'EXPLICIT_REVIEWED_SKIP'
            job['review_disposition'] = skips[identity]
        else:
            require(job['conclusion'] == 'success', 'effective job unsuccessful: '+job['name'])
            job['disposition'] = 'SUCCESS'
    expected = data['expected_jobs']
    require(bool(expected), 'expected job inventory absent')
    for item in expected:
        matches = [job for job in effective.values() if job['workflow'] == item['workflow'] and job['name'] == item['name']
            and ('event' not in item or job['event'] == item['event'])
            and ('head_sha' not in item or job['head_sha'] == item['head_sha'])]
        require(bool(matches), 'required workflow/job absent: '+item['workflow']+'/'+item['name'])
    required_new = {'opica-contract','opica-formal','opica-regression','opica-dependency-delta','opica-component-summary'}
    actual_new = {job['name'] for job in effective.values() if job['workflow'] == '.github/workflows/rhrc_opica.yml'}
    require(required_new <= actual_new, 'incomplete OPICA component jobs')
    # Every attached check is retained. An older failed attempt is superseded
    # only by the exact same app/name/head identity, never by a favorable status.
    latest_checks = {}
    for check in checks:
        scope = (check['app']['id'],check['name'],check['head_sha'])
        prior = latest_checks.get(scope)
        if prior is None or (check['started_at'],check['id']) > (prior['started_at'],prior['id']):
            latest_checks[scope] = check
    for check in latest_checks.values():
        require(check['status'] == 'completed', 'attached effective check running: '+check['name'])
        if check['conclusion'] == 'skipped':
            require(check['name'] not in required_new and
                bool(data.get('reviewed_check_skips',{}).get(str(check['id']))),
                'attached skipped check lacks exact reviewed disposition: '+check['name'])
        else:
            require(check['conclusion'] == 'success', 'attached effective check not green: '+check['name'])
    return {'schema':'OPICA_WORKFLOW_HARVEST_V1','status':'PASS',
        'head_sha':data['head_sha'],'head_tree':data['head_tree'],
        'checked_sha':data['checked_sha'],'checked_tree':data['checked_tree'],
        'effective_jobs':list(effective.values()),'all_job_attempts':history,
        'all_workflow_runs':runs,'all_check_runs':checks,
        'effective_check_ids':[c['id'] for c in latest_checks.values()],
        'authority':'GitHub execution dispositions and explicit source identities; no mathematical review approval.',
        'independent_review_approved':False,'RH':'OPEN','Step4':'OPEN'}


def validate_source_identity(repo, data, requested_head):
    """Bind provider-page claims to Git objects at the requested checkout."""
    def git(*parts):
        return subprocess.check_output(['git',*parts],cwd=repo,text=True).strip()
    expected = git('rev-parse','--verify',requested_head+'^{commit}')
    require(data['head_sha'] == expected, 'harvest belongs to a foreign requested head')
    for sha, field in [(data['head_sha'],'head_tree'),(data['checked_sha'],'checked_tree')]:
        require(git('rev-parse','--verify',sha+'^{tree}') == data[field],
            'harvest tree differs from actual Git source: '+field)
    if data['checked_sha'] != expected:
        parents = git('rev-list','--parents','-n','1',data['checked_sha']).split()[1:]
        require(len(parents)==2,'harvest synthetic merge must have exactly two actual parents')
        require(expected in parents and parents == data.get('checked_parents'),
            'harvest synthetic-merge parent claims differ from Git objects')
    return expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--requested-head',default='HEAD')
    args = parser.parse_args()
    require(not args.output.resolve().is_relative_to(REPO.resolve()),'harvest artifacts must be external')
    data = json.loads(args.input.read_text(encoding='utf-8'))
    result = harvest(data)
    result['requested_head'] = validate_source_identity(REPO,data,args.requested_head)
    result['source_identity_verified_by'] = 'LOCAL_GIT_OBJECTS'
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('Complete workflow harvest: '+str(args.output))


if __name__ == '__main__':
    main()
