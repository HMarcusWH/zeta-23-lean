"""Capture source identity before child edits. Source capture is not release acceptance."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PINNED_HEAD = '553b4263b58d9fec178320de251ff299a0bd702a'
ACCEPTED_PARENT = 'd53dd70d38b0762af130b1d19b795af259f505f5'
PINNED_TREE = '12691099f1a155a8bfa3ad4f6689146175b233b2'


def git(*args: str) -> bytes:
    return subprocess.run(['git', '-C', str(REPO), *args], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


def capture(expected_head: str, expected_tree: str) -> dict:
    if expected_head not in {PINNED_HEAD, ACCEPTED_PARENT} or expected_tree != PINNED_TREE:
        raise ValueError('unreviewed parent pin; a versioned amendment is required')
    if git('rev-parse', expected_head + '^{tree}').decode().strip() != expected_tree:
        raise ValueError('parent commit/tree mismatch')
    if git('rev-parse', 'HEAD').decode().strip() != expected_head:
        raise ValueError('source capture requires the exact parent HEAD')
    # Untracked child work is excluded from this frozen parent inventory. Every
    # tracked parent's working bytes must still match its committed blob.
    if git('diff', '--name-only', 'HEAD', '--'):
        raise ValueError('tracked parent edits already present')
    rows = []
    for entry in git('ls-tree', '-r', '-z', expected_head).split(b'\0'):
        if not entry:
            continue
        meta, raw_path = entry.split(b'\t', 1)
        mode, kind, oid = meta.decode().split()
        path = raw_path.decode('utf-8')
        if kind != 'blob' or mode not in {'100644', '100755'}:
            raise ValueError('unsupported parent tree entry: ' + path)
        target = REPO / path
        if target.is_symlink() or not target.resolve().is_relative_to(REPO.resolve()):
            raise ValueError('parent path escapes checkout: ' + path)
        content = target.read_bytes()
        # Git blob identity checks exact bytes; no line-ending conversion.
        actual_blob = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
        if actual_blob != oid:
            raise ValueError('working bytes differ from parent blob: ' + path)
        rows.append({'path': path, 'mode': mode, 'git_blob': oid,
                     'bytes': len(content), 'sha256': hashlib.sha256(content).hexdigest()})
    def read(relative):
        return json.loads((REPO / relative).read_text(encoding='utf-8'))
    claims = read('research/RHRC/CLAIM_REGISTRY.json')
    bindings = read('research/RHRC/REGISTERED_THEOREM_BINDINGS.json')
    open_ids = ['C_RH', 'R001_PRIME_UPPER', 'R002_WINDOWED_VISIBILITY',
                'R003_COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES']
    return {'schema': 'OPICA_FOLLOWUP_PROTECTED_PARENT_V1', 'parent_head': expected_head,
            'original_pr_head': PINNED_HEAD, 'parent_tree': expected_tree,
            'phase': 'SOURCE_CAPTURE_ONLY', 'compiler_validated_here': False,
            'review_status': 'INDEPENDENT_REVIEW_NOT_ESTABLISHED',
            'files': rows, 'claim_registry': claims, 'theorem_bindings': bindings,
            'file_classes': read('research/RHRC/graph/FILE_CLASSES.json'),
            'semantic_closure': read('research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json'),
            'open_claim_ids': open_ids, 'RH': 'OPEN', 'Step4': 'OPEN'}


"""Proposal functions to embed in the planned capture_parent.py, not a new authority."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import textwrap
import zipfile
from urllib.request import Request, urlopen

PARENT_READER_SHA256 = 'c4918486016d25b16caa1013666a22979f8ebe86e41369cbf616a8a2b9512ddc'
PROTECTED_PARENT_SHA256 = 'c62aad1d5dba23e0413f084a4deb9ecdaeb655e803fe809cd603c8efc7bc1779'
PARENT_FOLDER = 'research/RHRC/integration/opica/'
CHILD_FOLDER = 'research/RHRC/integration/opica_followup/'
REPOSITORY = 'HMarcusWH/zeta-23-lean'
ACCEPTED_PARENT = 'd53dd70d38b0762af130b1d19b795af259f505f5'
PINNED_HEAD = '553b4263b58d9fec178320de251ff299a0bd702a'
PINNED_TREE = '12691099f1a155a8bfa3ad4f6689146175b233b2'
EXACT_SOURCE_READER_SHA256 = '0b393f7d1b177a1c497917aa0aaade1355b0512338bc3a143991b4550fae5e44'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate JSON key: '+key)
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=pairs,
        parse_constant=lambda value: (_ for _ in ()).throw(ValueError('nonfinite JSON number')))


def file_sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def regular_artifact(path, folder=None):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'regular evidence artifact required: '+str(path))
    for ancestor in [path, *path.parents]:
        require(not ancestor.is_symlink() and not getattr(ancestor, 'is_junction', lambda:False)(),
            'evidence symlink/junction is forbidden: '+str(path))
    if folder is not None:
        require(path.resolve().is_relative_to(Path(folder).resolve()), 'evidence artifact escaped folder')
    return path


def evidence_relative_name(name):
    require(isinstance(name,str) and bool(name) and not name.startswith('/')
        and ':' not in name and '\\' not in name
        and all(part not in {'','.','..'} for part in name.split('/')),
        'unsafe workflow artifact relative path')
    return name


def git_bytes(repo, *parts):
    return subprocess.check_output(['git','-C',str(repo),*parts])


def load_evidence_tool(repo, relative, name, expected_sha256=None):
    path = regular_artifact(Path(repo)/relative, repo)
    if expected_sha256 is not None:
        require(file_sha256(path)==expected_sha256, 'immutable evidence reader changed')
    sys.path.insert(0,str(Path(repo)/'research/RHRC/routes/R003_ccm_bridge/post290'))
    spec = importlib.util.spec_from_file_location(name,path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def verify_p0_evidence(repo, receipt_path, expected_head, expected_tree):
    """Reparse all three original logs and full P0 records at the actual Git pin."""
    repo = Path(repo)
    require(re.fullmatch('[0-9a-f]{40}',expected_head) and
        re.fullmatch('[0-9a-f]{40}',expected_tree), 'exact P0 head/tree required')
    require(git_bytes(repo,'rev-parse',expected_head+'^{tree}').decode().strip()==expected_tree,
        'P0 checked commit/tree is not the actual Git object')
    reader = load_evidence_tool(repo,PARENT_FOLDER+'build_receipt.py',
        'opica_immutable_parent_reader_for_acceptance',PARENT_READER_SHA256)
    read_at = lambda name: unique_json(git_bytes(repo,'show',expected_head+':'+PARENT_FOLDER+name))
    manifest, public, workflow = map(read_at, ['BUILD_MANIFEST.json','PUBLIC_ROOTS.json','WORKFLOW_CONTRACT.json'])
    roots = reader.with_reviewed_root_types(public['primary_roots'],workflow['reviewed_root_type_sha256'])
    receipt_path = regular_artifact(receipt_path)
    receipt = unique_json(receipt_path.read_bytes())
    reader.validate_compiler_receipt(receipt,manifest,roots)
    parents = git_bytes(repo,'rev-list','--parents','-n','1',expected_head).decode().split()[1:]
    reader.validate_checkout_identity(receipt,expected_head,expected_tree,parents)
    logs = []
    for command in receipt['commands']:
        name = command['log']
        require(name in {'lean-version.log','build.log','bindings.log'}, 'unknown original P0 log')
        path = regular_artifact(receipt_path.parent/name,receipt_path.parent)
        require(file_sha256(path)==command['log_sha256'], 'P0 compiler log hash differs: '+name)
        logs.append({'log':name,'bytes':path.stat().st_size,'sha256':file_sha256(path),
            'argv':command['argv'],'exit_code':command['exit_code']})
    require((receipt_path.parent/'lean-version.log').read_text(encoding='utf-8').strip()==receipt['lean'],
        'P0 version log and compiler receipt disagree')
    parsed = reader.parse_compiler_output((receipt_path.parent/'bindings.log').read_text(encoding='utf-8'),roots)
    require(all(receipt.get(key)==value for key,value in parsed.items()), 'P0 log reparse differs from supplied receipt')
    expected_sources = {row['path'] for row in manifest['create']+manifest['modify']}
    require(set(receipt['sources'])==expected_sources, 'P0 exact source inventory incomplete')
    for path in expected_sources:
        data = git_bytes(repo,'show',expected_head+':'+path)
        require(receipt['sources'][path]==hashlib.sha256(data).hexdigest(), 'P0 source differs from checked Git object: '+path)
    return receipt, {'checked_commit':expected_head,'checked_tree':expected_tree,
        'receipt_sha256':file_sha256(receipt_path),'parent_reader_sha256':PARENT_READER_SHA256,
        'primary_root_count':len(roots),'public_declarations':len(receipt['declarations']),
        'source_count':len(expected_sources),'logs':logs,'input_reparsed':True,
        'fresh_compilation_performed_by_this_reader':False}


def workflow_provider_identity(raw, harvester):
    """Provider scope fields; review text never supplies a missing execution."""
    def ordered(rows, keys):
        return sorted(([row.get(key) for key in keys] for row in rows),key=repr)
    runs = harvester._collections(raw,'run','workflow_runs')
    checks = harvester._collections(raw,'check','check_runs')
    jobs = []
    for record in raw.get('job_pages',[]):
        for job in harvester.complete_pages(record['pages'],'jobs'):
            jobs.append({**job,'_attempt':record['attempt']})
    artifacts = []
    for record in raw.get('artifact_pages',[]):
        for artifact in harvester.complete_pages(record['pages'],'artifacts'):
            artifacts.append({**artifact,'_run_id':record['run_id']})
    return {'repository':raw.get('repository'),'head_sha':raw['head_sha'],
        'checked_sha':raw.get('checked_sha',raw['head_sha']),
        'commit_trees':raw['commit_trees'],'commit_parents':raw.get('commit_parents',{}),
        'collected_shas':sorted(raw.get('collected_shas',[raw['head_sha']])),
        'runs':ordered(runs,['id','path','head_sha','event','run_number','run_attempt','status','conclusion']),
        'jobs':ordered(jobs,['id','run_id','_attempt','name','head_sha','status','conclusion','steps']),
        'checks':ordered(checks,['id','head_sha','name','app','status','conclusion']),
        'artifacts':ordered(artifacts,['id','_run_id','name','size_in_bytes','digest','expired','workflow_run']),
        'workflow_sources':sorted(raw.get('workflow_sources',[]),key=lambda row:(row['path'],row['source_sha']))}


def public_github_bytes(url):
    require(url.startswith('https://api.github.com/repos/'+REPOSITORY+'/actions/'),
        'only exact repository GitHub action artifact GET is allowed')
    headers={'Accept':'application/vnd.github+json','User-Agent':'opica-followup-acceptance'}
    import os
    token=os.environ.get('GITHUB_TOKEN') or os.environ.get('GH_TOKEN')
    request=Request(url,headers=headers,method='GET')
    if token:request.add_unredirected_header('Authorization','Bearer '+token)
    with urlopen(request,timeout=60) as response:
        return response.read()


def workflow_archive_members(path):
    """Reparse actual archive bytes without extracting or following any entry."""
    rows=[];names=set()
    with zipfile.ZipFile(path) as archive:
        require(archive.testzip() is None, 'workflow archive CRC failure')
        for member in archive.infolist():
            name=member.filename
            require(name and not name.startswith('/') and '\\' not in name and ':' not in name
                and all(part not in {'','..','.'} for part in name.rstrip('/').split('/')),
                'unsafe workflow archive member')
            require(name.casefold() not in names, 'duplicate or case-aliased workflow archive member')
            names.add(name.casefold())
            require((member.external_attr>>16)&0o170000 != 0o120000, 'workflow archive symlink member')
            if member.is_dir():continue
            data=archive.read(member)
            require(len(data)==member.file_size, 'truncated workflow archive member')
            rows.append({'path':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
    return sorted(rows,key=lambda row:row['path'])


def static_yaml_scalar(value):
    value=value.strip()
    require(value and '${{' not in value and not value.startswith(('!','&','*','[','{')),
        'unsupported dynamic workflow scalar')
    if value.startswith('"'):
        result=unique_json(value)
        require(isinstance(result,str),'static workflow scalar must be a string')
        return result
    if value.startswith("'"):
        require(value.endswith("'"),'unterminated workflow scalar')
        return value[1:-1].replace("''", "'")
    return value.split(' #',1)[0].strip()


def named_job_step_run_body(source, job_name, step_name):
    """Conservative static GitHub job/step binding, not a general YAML parser.

    Unsupported dynamic or ambiguous names fail closed. The two historical
    stdout-unavailable proof jobs use static names and ordinary run blocks.
    """
    lines=source.splitlines()
    require('\t' not in source,'workflow indentation tabs are unsupported')
    roots=[i for i,line in enumerate(lines) if re.fullmatch(r'jobs:\s*(?:#.*)?',line)]
    require(len(roots)==1,'unique workflow jobs block required')
    job_starts=[(i,re.fullmatch(r'  ([A-Za-z_][A-Za-z_0-9-]*):\s*(?:#.*)?',line))
        for i,line in enumerate(lines) if i>roots[0]]
    job_starts=[(i,match.group(1)) for i,match in job_starts if match]
    candidates=[]
    for index,(start,identity) in enumerate(job_starts):
        end=job_starts[index+1][0] if index+1<len(job_starts) else len(lines)
        names=[static_yaml_scalar(line.strip()[5:]) for line in lines[start+1:end]
            if re.match(r'^    name:\s*',line)]
        require(len(names)<=1,'ambiguous workflow job display name')
        if (names[0] if names else identity)==job_name:candidates.append((start,end))
    require(len(candidates)==1,'actual selected static workflow job is missing or ambiguous')
    start,end=candidates[0]
    markers=[i for i in range(start+1,end) if re.fullmatch(r'    steps:\s*(?:#.*)?',lines[i])]
    require(len(markers)==1,'selected workflow job steps block required')
    starts=[i for i in range(markers[0]+1,end) if re.match(r'^      -\s+',lines[i])]
    selected=[]
    for index,step_start in enumerate(starts):
        step_end=starts[index+1] if index+1<len(starts) else end
        names=[]
        for i in range(step_start,step_end):
            text=lines[i][8:] if i==step_start else lines[i].strip()
            if (i==step_start or re.match(r'^        name:',lines[i])) and text.startswith('name:'):
                names.append(static_yaml_scalar(text[5:]))
        require(len(names)<=1,'ambiguous workflow step name')
        if names and names[0]==step_name:selected.append((step_start,step_end))
    require(len(selected)==1,'actual named step does not uniquely occur in selected workflow job')
    step_start,step_end=selected[0]
    headers=[]
    for i in range(step_start,step_end):
        text=lines[i][8:] if i==step_start else lines[i].strip()
        if (i==step_start or re.match(r'^        run:',lines[i])) and text.startswith('run:'):
            headers.append((i,text[4:].strip()))
    require(len(headers)==1,'selected actual step has no unique shell run body')
    header,indicator=headers[0]
    if indicator in {'|','|-','|+'}:
        first=header+1;last=first
        while last<step_end and (not lines[last].strip() or len(lines[last])-len(lines[last].lstrip())>8):last+=1
        while first<last and not lines[first].strip():first+=1
        while last>first and not lines[last-1].strip():last-=1
        require(first<last,'actual step run body is empty')
        return [first+1,last],textwrap.dedent('\n'.join(lines[first:last])).strip()
    require(not indicator.startswith(('>','|')),'unsupported workflow run scalar')
    return [header+1,header+1],static_yaml_scalar(indicator)


def source_and_provider_command_evidence(job, sources):
    """Retain honest CI-step exit provenance when a full stdout fetch failed.

    This does not infer a scientific JSON outcome or individual Lean declaration
    from a successful process. The supplied nonauthor review names that limited
    disposition, and any required scientific outputs remain separate artifacts.
    """
    review=job['review']
    limitation=review.get('stdout_disposition')
    require(isinstance(limitation,dict) and limitation.get('available') is False
        and isinstance(limitation.get('reason'),str) and bool(limitation['reason'].strip()),
        'unavailable stdout must have an explicit reviewed limitation')
    matches=[source for source in sources if source['path']==job['workflow']
        and source['source_sha']==job['head_sha']]
    require(len(matches)==1, 'exact workflow source for command evidence is missing')
    source=matches[0];lines=source['content'].splitlines();rows=[]
    steps={step['number']:step for step in job.get('steps',[])}
    require(len(steps)==len(job.get('steps',[])), 'duplicate actual provider step number')
    for command in review['commands']:
        require(command.get('exit_code_provenance')=='CI_STEP_CONCLUSION'
            and command.get('workflow_sha256')==source['sha256'], 'command lacks honest source/CI-step provenance')
        step=steps.get(command.get('provider_step_number'))
        require(step is not None and step.get('name')==command.get('provider_step_name')
            and step.get('status')=='completed' and step.get('conclusion')=='success'
            and command['exit_code']==0, 'actual named CI step does not establish the reviewed command success')
        span=command.get('source_lines')
        require(isinstance(span,list) and len(span)==2 and all(type(value) is int for value in span)
            and 1<=span[0]<=span[1]<=len(lines), 'exact command source line span required')
        actual_span,literal=named_job_step_run_body(source['content'],job['name'],step['name'])
        require(span==actual_span and literal==command['command'],
            'reviewed command source span is not the entire run body of the actual selected job/step')
        rows.append({'command':command['command'],'exit_code':0,'exit_code_provenance':'CI_STEP_CONCLUSION',
            'provider_step_number':step['number'],'provider_step_name':step['name'],
            'workflow_sha256':source['sha256'],'source_lines':span})
    return {'kind':'EXACT_WORKFLOW_COMMAND_AND_FRESH_PROVIDER_STEP','job_id':job['id'],
        'commands':rows,'stdout_disposition':limitation,'full_stdout_claimed':False}


def previous_harvest_input(previous, harvester):
    if previous is None:return None,None
    if isinstance(previous,(str,Path)):
        path=regular_artifact(previous);data=path.read_bytes();document=unique_json(data)
    else:
        data=json.dumps(previous,sort_keys=True,separators=(',',':')).encode()
        document=unique_json(data)
    require(document.get('schema')=='OPICA_FOLLOWUP_WORKFLOW_HARVEST_V1'
        and isinstance(document.get('raw_collection'),dict), 'previous complete raw harvest input required')
    require(document['raw_collection'].get('repository')==REPOSITORY, 'foreign previous workflow repository')
    parsed=harvester.harvest(document['raw_collection'])
    for key in ['head_sha','head_tree','checked_sha','checked_tree']:
        require(document.get(key)==parsed[key],'previous harvest source identity differs from raw input')
    def without_older_comparison(rows):
        return [{key:value for key,value in row.items() if key!='fixture_comparison'} for row in rows]
    for key in ['effective_jobs','all_job_attempts']:
        require(without_older_comparison(document.get(key,[]))==without_older_comparison(parsed[key]),
            'previous reviewed job/output differs from its raw source-bound records')
    return document,hashlib.sha256(data).hexdigest()


def verify_workflow_evidence(repo, report_path, *, expected_head, expected_tree,
        allow_parent_same_tree=False, fetch_json=None, fetch_bytes=None, artifact_folder=None,
        refresh_output_bytes=False, previous_harvest=None):
    """Fresh collection plus exact supplied nonauthor output review; no status-only intake."""
    repo=Path(repo); report_path=regular_artifact(report_path)
    document=unique_json(report_path.read_bytes())
    require(document.get('schema')=='OPICA_FOLLOWUP_WORKFLOW_HARVEST_V1'
        and isinstance(document.get('raw_collection'),dict), 'complete raw paginated harvest required')
    raw=document['raw_collection']
    require(raw.get('repository')==REPOSITORY, 'foreign workflow repository')
    harvester=load_evidence_tool(repo,CHILD_FOLDER+'harvest_workflows.py','opica_fresh_acceptance_harvester')
    previous,previous_sha256=previous_harvest_input(previous_harvest,harvester)
    calculated=harvester.harvest(raw,previous)
    require(calculated['execution_status']=='PASS' and not calculated['blockers'], 'required workflow execution is incomplete')
    require(calculated['review_status']=='RECORDED_NOT_INDEPENDENT_APPROVAL'
        and calculated['workflow_source_inventory']=='COMPLETE', 'complete exact-output job review is missing')
    for key in ['head_sha','head_tree','checked_sha','checked_tree','effective_jobs','all_job_attempts',
                'all_workflow_runs','all_check_runs','artifacts','workflow_sources']:
        require(document.get(key)==calculated[key], 'serialized harvest differs from raw revalidation: '+key)
    additional=set(raw.get('collected_shas',[raw['head_sha']]))-{raw['head_sha']}
    require(len(additional)<=1, 'unsupported workflow collection source multiplicity')
    extra=next(iter(additional),raw['head_sha'])
    fresh=harvester.collect(fetch_json or harvester.public_github_json,REPOSITORY,raw['head_sha'],extra)
    # The second collection argument chooses an additional actual provider
    # scope; a report may designate its head as the reviewed checked source.
    selected=raw.get('checked_sha',raw['head_sha'])
    require(selected in fresh['commit_trees'], 'reviewed checked source was not freshly collected')
    fresh['checked_sha']=selected
    fresh['checked_tree']=fresh['commit_trees'][selected]
    require(workflow_provider_identity(fresh,harvester)==workflow_provider_identity(raw,harvester),
        'fresh GitHub workflow scope/attempt/source/artifact differs from reviewed input')
    if calculated['checked_sha']==expected_head:
        require(calculated['checked_tree']==expected_tree, 'workflow and compiler checked trees disagree')
        bridge={'kind':'EXACT_CHECKED_COMMIT','checked_commit':expected_head,'checked_tree':expected_tree}
    else:
        require(allow_parent_same_tree and expected_head==ACCEPTED_PARENT and expected_tree==PINNED_TREE
            and calculated['head_sha']==PINNED_HEAD and calculated['head_tree']==expected_tree
            and calculated['checked_tree']==expected_tree, 'workflow head does not match exact compiler source')
        parents=git_bytes(repo,'rev-list','--parents','-n','1',expected_head).decode().split()[1:]
        require(len(parents)==2 and PINNED_HEAD in parents, 'accepted parent does not contain original tested head')
        require(git_bytes(repo,'rev-parse',PINNED_HEAD+'^{tree}').decode().strip()==expected_tree,
            'historical tested head tree differs from accepted parent')
        bridge={'kind':'ORIGINAL_PARENT_SAME_TREE_MERGE_WITH_LOCAL_EXACT_P0_REPLAY',
            'accepted_commit':expected_head,'accepted_tree':expected_tree,'accepted_parents':parents,
            'historical_head':calculated['head_sha'],'historical_checked_commit':calculated['checked_sha'],
            'historical_checked_tree':calculated['checked_tree'],'merge_sha_ci_run_invented':False}
    for source in calculated['workflow_sources']:
        # All historical source trees equal the accepted tree; the source bytes
        # are independently tied to Git objects, not only to provider JSON.
        tree=fresh['commit_trees'][source['source_sha']]
        reference=expected_head if tree==expected_tree else source['source_sha']
        actual=git_bytes(repo,'show',reference+':'+source['path'])
        require(actual==source['content'].encode(), 'reviewed workflow source differs from actual Git bytes')
    folder=Path(artifact_folder) if artifact_folder is not None else report_path.parent
    fetch_bytes=fetch_bytes or public_github_bytes
    evidence=[]
    for job in calculated['all_job_attempts']:
        if job['status']!='completed' or job['conclusion']=='skipped':
            continue
        review=job.get('review')
        require(isinstance(review,dict), 'completed historical attempt lacks actual output review')
        log_binding=review.get('job_log')
        if log_binding is not None:
            require(isinstance(log_binding,dict) and set(log_binding)=={'file','bytes','sha256'},
                'actual reviewed job log binding required')
            name=evidence_relative_name(log_binding['file'])
            path=regular_artifact(folder/name,folder)
            require(path.stat().st_size==log_binding['bytes'] and file_sha256(path)==log_binding['sha256'],
                'reviewed job log bytes differ')
            if refresh_output_bytes:
                remote=fetch_bytes('https://api.github.com/repos/'+REPOSITORY+'/actions/jobs/'+str(job['id'])+'/logs')
                require(remote==path.read_bytes(), 'actual GitHub job log differs from supplied reviewed output')
            evidence.append({'kind':'JOB_LOG','job_id':job['id'],**log_binding,
                'fresh_blob_download_compared':refresh_output_bytes,
                'scope':'SUPPLIED_NONAUTHOR_OUTPUT_REVIEW_BOUND_TO_FRESH_PROVIDER_JOB_SOURCE'})
        else:
            evidence.append(source_and_provider_command_evidence(job,calculated['workflow_sources']))
            require(job['classification'] in {'FORMAL_VALIDITY_GATE','FORMAL_VALIDITY_GATE_STATIC','COMPLETENESS_GATE'}
                or bool(review.get('artifacts')), 'missing scientific outputs cannot be replaced by process success')
        for artifact in review.get('artifacts',[]):
            name=evidence_relative_name(artifact.get('file'))
            path=regular_artifact(folder/name,folder)
            require(file_sha256(path)==artifact['sha256'], 'reviewed workflow artifact hash differs')
            provider=next(row for row in calculated['artifacts'] if row['id']==artifact['id'])
            official=provider.get('digest')
            downloaded=refresh_output_bytes or official is None
            if downloaded:
                remote=fetch_bytes('https://api.github.com/repos/'+REPOSITORY+'/actions/artifacts/'+str(artifact['id'])+'/zip')
                require(remote==path.read_bytes(), 'actual GitHub artifact differs from reviewed archive')
            else:
                require(official=='sha256:'+artifact['sha256'],'fresh official artifact digest differs from actual archive')
            evidence.append({'kind':'WORKFLOW_ARCHIVE','artifact_id':artifact['id'],'file':name,
                'bytes':path.stat().st_size,'sha256':artifact['sha256'],
                'fresh_official_digest':official,'fresh_blob_download_compared':downloaded,
                'members':workflow_archive_members(path)})
    return {'schema':'OPICA_REVALIDATED_WORKFLOW_OUTPUT_INPUT_V1','report_sha256':file_sha256(report_path),
        'previous_harvest_sha256':previous_sha256,
        'raw_collection_sha256':hashlib.sha256(json.dumps(raw,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'fresh_provider_scope_verified':True,'source_bridge':bridge,'external_evidence':evidence,
        'output_review_provenance':document.get('review_provenance'),
        'independent_review_approved_by_validator':False,'human_review':'NOT_ESTABLISHED',
        'required_job_count':sum(job.get('required',False) for job in calculated['effective_jobs']),
        'all_attempt_job_count':len(calculated['all_job_attempts']),'new_theorem_authority':False,
        'RH':'OPEN','Step4':'OPEN'}


def acceptance_from_evidence(repo, expected_head, expected_tree, formal_receipt, workflow_harvest,
        *, fetch_json=None, fetch_bytes=None, artifact_folder=None, previous_harvest=None):
    """Actual accepted-parent intake, including historical scope provenance."""
    repo=Path(repo)
    require(expected_head==ACCEPTED_PARENT and expected_tree==PINNED_TREE,
        'only the existing reviewed accepted-parent amendment is authorized')
    protected_path=regular_artifact(repo/CHILD_FOLDER/'PROTECTED_STATE.json',repo)
    require(file_sha256(protected_path)==PROTECTED_PARENT_SHA256, 'frozen protected parent baseline changed')
    protected=unique_json(protected_path.read_bytes())
    require(protected['parent_head']==expected_head and protected['parent_tree']==expected_tree,
        'protected parent identity differs')
    source_reader=load_evidence_tool(repo,CHILD_FOLDER+'exact_extension.py',
        'opica_exact_source_reader_for_acceptance',EXACT_SOURCE_READER_SHA256)
    actual_tree,actual_files,_=source_reader.capture_commit(repo,expected_head)
    require(actual_tree==expected_tree and actual_files==protected['files'],
        'protected parent complete immutable Git inventory differs')
    _,compiler=verify_p0_evidence(repo,formal_receipt,expected_head,expected_tree)
    workflows=verify_workflow_evidence(repo,workflow_harvest,expected_head=expected_head,
        expected_tree=expected_tree,allow_parent_same_tree=True,fetch_json=fetch_json,
        fetch_bytes=fetch_bytes,artifact_folder=artifact_folder,previous_harvest=previous_harvest)
    result=dict(protected)
    result.update({'phase':'ACCEPTANCE_INPUTS_REVALIDATED','compiler_validated_here':True,
        'compiler_validation_scope':'SUPPLIED_ACTUAL_EXACT_P0_LOGS_REPARSED_NOT_A_NEW_COMPILER_RUN',
        'review_status':'SUPPLIED_NONAUTHOR_OUTPUT_REVIEW_REVALIDATED_NOT_AUTO_APPROVED',
        'accepted_parent_compiler_evidence':compiler,'accepted_parent_workflow_evidence':workflows,
        'release_acceptance':False,'full_child_release_accepted':False,'RH':'OPEN','Step4':'OPEN'})
    return result


def main() -> int:
    global REPO
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent-pr', type=int, required=True)
    parser.add_argument('--expected-head', required=True)
    parser.add_argument('--expected-tree', required=True)
    parser.add_argument('--phase', choices=['source', 'acceptance'], required=True)
    parser.add_argument('--formal-receipt', type=Path)
    parser.add_argument('--workflow-harvest', type=Path)
    parser.add_argument('--workflow-artifacts', type=Path)
    parser.add_argument('--previous-workflow-harvest', type=Path)
    parser.add_argument('--repo', type=Path, default=REPO)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    REPO = args.repo.resolve()
    if args.parent_pr != 293:
        parser.error('only parent PR293 is authorized')
    if args.output.resolve().is_relative_to(REPO):
        parser.error('execution receipts must be outside the repository')
    if args.output.is_symlink() or any(parent.is_symlink() or getattr(parent,'is_junction',lambda:False)()
        for parent in args.output.parents):
        parser.error('receipt output may not follow a symlink or junction')
    exit_code = 0
    try:
        if args.phase == 'acceptance':
            require(args.formal_receipt is not None and args.workflow_harvest is not None,
                'acceptance requires actual P0 compiler artifacts and the complete reviewed workflow harvest')
            report = acceptance_from_evidence(REPO,args.expected_head,args.expected_tree,
                args.formal_receipt,args.workflow_harvest,artifact_folder=args.workflow_artifacts,
                previous_harvest=args.previous_workflow_harvest)
        else:
            report = capture(args.expected_head,args.expected_tree)
    except (KeyError,TypeError,ValueError,OSError,RuntimeError,subprocess.SubprocessError,zipfile.BadZipFile) as exc:
        if args.phase != 'acceptance':
            raise
        report = {'schema':'OPICA_FOLLOWUP_PARENT_ACCEPTANCE_REJECTION_V1',
            'phase':'ACCEPTANCE_REJECTED','parent_head':args.expected_head,'parent_tree':args.expected_tree,
            'errors':[str(exc)],'compiler_validated_here':False,'release_acceptance':False,
            'full_child_release_accepted':False,'RH':'OPEN','Step4':'OPEN'}
        exit_code = 1
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status':report['phase'],'parent_head':report['parent_head'],
        'parent_tree':report['parent_tree'],'tracked_files':len(report.get('files',[])),
        'release_acceptance':False,'errors':report.get('errors',[])}))
    return exit_code


if __name__ == '__main__':
    raise SystemExit(main())
