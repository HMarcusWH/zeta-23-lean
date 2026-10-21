"""Build and inspect complete OPICA compiler exports at the current clean checkout."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO/'research/RHRC/routes/R003_ccm_bridge/post290'))
from lean_expr_dag import validate_expression

ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SHA40 = re.compile(r'[0-9a-f]{40}\Z')
SHA256 = re.compile(r'[0-9a-f]{64}\Z')
MATHEMATICAL_MODULES = frozenset(item['module'] for item in
    json.loads((HERE/'BUILD_MANIFEST.json').read_text(encoding='utf-8'))['modules']
    if item['trust_zone'] in {'AUXILIARY_FORMALIZATION', 'RH_FORMAL_CORE'}
    and (item['module'] == 'Zeta23.OPICA' or item['module'].startswith('Zeta23.OPICA.')))


def require(condition, description):
    if not condition:
        raise ValueError(description)


def write_compiler_log(path, captured_stdout):
    """Store exactly the UTF-8 bytes bound by the command's artifact digest."""
    payload = captured_stdout.encode('utf-8')
    path.write_bytes(payload)
    return hashlib.sha256(payload).hexdigest()


def validate_dependency_closure(declarations, metadata, dependencies):
    """Check the complete project traversal, including private helper nodes.

    Every project constant reached by the exporter is expanded in all three
    channels. External constants are boundary nodes. Checking only public root
    channels would accept a log truncated just before a helper's expansion.
    """
    public = {item['name']: item for item in declarations}
    require(len(public) == len(declarations), 'duplicate public declaration')
    nodes = {item['name']: item for item in metadata}
    require(len(nodes) == len(metadata), 'duplicate dependency declaration')
    kinds = {'AXIOM','DEFINITION','THEOREM','OPAQUE','QUOTIENT','INDUCTIVE','CONSTRUCTOR','RECURSOR'}
    for item in metadata:
        require(item['kind'] in kinds and type(item['internal']) is bool,
            'invalid dependency declaration metadata')
    def project(item):
        return item['module'] == 'Zeta23' or item['module'].startswith('Zeta23.')
    for name, item in public.items():
        require(name in nodes, 'missing public dependency metadata: '+name)
        require(nodes[name]['module'] == item['module'] and nodes[name]['kind'] == item['kind']
            and not nodes[name]['internal'], 'public dependency metadata mismatch: '+name)
    channels = {}
    for item in dependencies:
        source, channel, targets = item['source'], item['channel'], item['targets']
        require(source in nodes, 'unknown dependency source')
        require(project(nodes[source]), 'external dependency boundary was expanded: '+source)
        require(channel in {'TYPE','VALUE','STRUCTURE'}, 'unknown dependency channel')
        require((source,channel) not in channels, 'duplicate dependency channel')
        require(len(targets) == len(set(targets)) and all(targets), 'invalid dependency targets')
        require(all(target in nodes for target in targets), 'unknown dependency target')
        channels[source,channel] = targets
    for name, item in nodes.items():
        if project(item):
            require(all((name,c) in channels for c in ('TYPE','VALUE','STRUCTURE')),
                'incomplete project dependency channels: type/value/structure provenance: '+name)
    reached, pending = set(), list(public)
    while pending:
        source = pending.pop()
        if source in reached:
            continue
        reached.add(source)
        if project(nodes[source]):
            for channel in ('TYPE','VALUE','STRUCTURE'):
                pending.extend(channels[source,channel])
    require(reached == set(nodes), 'unreachable dependency metadata outside public-root closure')


def validate_compiler_records(receipt, expected_roots=()):
    """Revalidate serialized evidence without trusting its stored type hashes."""
    records = receipt['declarations']
    require(isinstance(records,list) and bool(records), 'empty or malformed public declaration inventory')
    declarations = {}
    kinds = {'DEFINITION','THEOREM','OPAQUE','QUOTIENT','INDUCTIVE','CONSTRUCTOR','RECURSOR'}
    for record in records:
        require(isinstance(record,dict) and {'name','module','kind','axioms','type_expression',
            'type_sha256','type_metrics'}<=set(record), 'missing public declaration evidence fields')
        name,module,kind = record['name'],record['module'],record['kind']
        require(isinstance(name,str) and name not in declarations, 'invalid or duplicate public declaration')
        require(module in MATHEMATICAL_MODULES, 'foreign defining module')
        require(kind in kinds, 'unadmitted public declaration kind')
        require(name.startswith('Zeta23.OPICA.') or (kind=='THEOREM' and name.endswith('.congr_simp')),
            'foreign declaration namespace')
        axioms = record['axioms']
        require(isinstance(axioms,list) and all(isinstance(ax,str) for ax in axioms)
            and len(axioms)==len(set(axioms)) and set(axioms)<=ALLOWED_AXIOMS,
            'unadmitted mathematical axiom: '+name)
        require(isinstance(record['type_expression'],dict), 'missing or malformed full type DAG: '+name)
        encoded = json.dumps(record['type_expression'],ensure_ascii=False,separators=(',',':'))
        metrics = validate_expression(encoded)
        digest = hashlib.sha256(encoded.encode('utf-8')).hexdigest()
        require(record['type_sha256']==digest, 'full type DAG digest mismatch: '+name)
        require(record['type_metrics']==metrics, 'full type DAG metrics mismatch: '+name)
        declarations[name] = record
    for root in expected_roots:
        require(root['full_name'].startswith('Zeta23.OPICA.'), 'foreign primary root namespace')
        require(root['module'] in MATHEMATICAL_MODULES, 'foreign primary defining module')
        record = declarations.get(root['full_name'])
        require(record is not None and record['module']==root['module'] and record['kind']==root['kind'],
            'missing or wrong source-bound primary declaration: '+root['full_name'])
        require(isinstance(record.get('full_type'),str) and bool(record['full_type'].strip()),
            'missing human-readable root type')
        if 'expected_type_sha256' in root:
            require(record['type_sha256']==root['expected_type_sha256'], 'reviewed expected type changed: '+root['full_name'])
    constructors = receipt.get('constructors')
    require(isinstance(constructors,dict), 'missing or malformed constructor inventory')
    require(set(constructors)=={name for name,record in declarations.items() if record['kind']=='CONSTRUCTOR'},
        'constructor inventory differs from public constructor declarations')
    validate_dependency_closure(records,receipt['dependency_declarations'],receipt['dependencies'])
    channels = {(item['source'],item['channel']):item['targets'] for item in receipt['dependencies']}
    for node in receipt['dependency_declarations']:
        if node['module'] in MATHEMATICAL_MODULES and not node['internal']:
            require(node['name'] in declarations, 'public mathematical dependency escaped enumeration: '+node['name'])
    for name,record in constructors.items():
        family = record['family']
        require(family in declarations and declarations[family]['kind']=='INDUCTIVE', 'constructor family mismatch')
        require(isinstance(record['type_expression'],dict), 'malformed constructor full type')
        validate_expression(json.dumps(record['type_expression'],ensure_ascii=False,separators=(',',':')))
        require(record['type_expression']==declarations[name]['type_expression'], 'constructor full type mismatch')
        require(channels[name,'STRUCTURE']==[family], 'constructor structural family mismatch')
        require(name in channels[family,'STRUCTURE'], 'constructor missing from inductive structural family')


def validate_compiler_receipt(receipt, manifest, expected_roots):
    """Validate the complete generated receipt before release or delta use."""
    require(receipt.get('schema')=='OPICA_COMPILER_RECEIPT_V1' and receipt.get('status')=='COMPILER_VERIFIED',
        'complete compiler receipt required')
    require(bool(expected_roots) and all(isinstance(root.get('expected_type_sha256'),str)
        and SHA256.fullmatch(root['expected_type_sha256']) for root in expected_roots),
        'complete reviewed primary type digests required')
    for field in ('checked_commit','checked_tree','requested_head'):
        require(isinstance(receipt.get(field),str) and SHA40.fullmatch(receipt[field]),
            'invalid compiler checkout identity: '+field)
    expected_kind = 'PR_HEAD' if receipt['requested_head']==receipt['checked_commit'] else 'SYNTHETIC_MERGE'
    require(receipt.get('checkout_kind')==expected_kind, 'compiler checkout kind disagrees with requested head')
    require(receipt.get('requested_base')==manifest['base_commit'] and
        receipt.get('mathlib_commit')==manifest['mathlib_commit'], 'compiler source pin mismatch')
    require(isinstance(receipt.get('lean'),str) and 'version 4.33.0-rc2,' in receipt['lean'],
        'wrong compiler runtime pin')
    expected = [(['lake','env','lean','--version'],'lean-version.log'),
        (['lake','build',*manifest['no_root_api_pollution']['required_build_targets']],'build.log'),
        (['lake','env','lean','Zeta23/RHRC/OpicaBindings.lean'],'bindings.log')]
    commands = receipt.get('commands')
    require(isinstance(commands,list) and len(commands)==len(expected), 'wrong compiler command inventory')
    for command,(argv,log) in zip(commands,expected):
        require(command.get('argv')==argv and command.get('log')==log and
            type(command.get('exit_code')) is int and command['exit_code']==0,
            'compiler command identity or successful exit mismatch: '+log)
        require(isinstance(command.get('log_sha256'),str) and SHA256.fullmatch(command['log_sha256']),
            'invalid compiler log digest: '+log)
        if 'seconds' in command:
            seconds = command['seconds']
            require(type(seconds) in (int,float) and seconds>=0 and math.isfinite(seconds),
                'invalid compiler command timing: '+log)
    validate_compiler_records(receipt,expected_roots)


def validate_checkout_identity(receipt, checked_commit, checked_tree, parents):
    require(receipt.get('checked_commit')==checked_commit and receipt.get('checked_tree')==checked_tree,
        'stale formal receipt head/tree')
    requested = receipt.get('requested_head')
    require(isinstance(requested,str) and SHA40.fullmatch(requested), 'invalid compiler requested head')
    require(requested==checked_commit or requested in parents, 'foreign compiler requested head')
    require(requested==checked_commit or len(parents)==2, 'synthetic merge must have exactly two actual parents')
    expected_kind = 'PR_HEAD' if requested==checked_commit else 'SYNTHETIC_MERGE'
    require(receipt.get('checkout_kind')==expected_kind, 'compiler checkout kind disagrees with requested head')


def with_reviewed_root_types(roots, reviewed):
    names = {root['full_name'] for root in roots}
    require(isinstance(reviewed,dict) and set(reviewed)==names and len(names)==len(roots),
        'reviewed root type inventory incomplete or inconsistent')
    for digest in reviewed.values():
        require(isinstance(digest,str) and SHA256.fullmatch(digest), 'invalid reviewed type digest')
    return [{**root,'expected_type_sha256':reviewed[root['full_name']]} for root in roots]


def mapped_registered_dependencies(rootnames, bindings, dependencies):
    """Map transitive TYPE/VALUE/STRUCTURE compiler uses to registered IDs.

    Callers must first validate the complete compiler traversal and its metadata.
    This records compiler-use provenance, including uses through unregistered
    helpers. It asserts neither logical equivalence nor proof of an antecedent.
    Unrelated bindings and each root's own registered identity are excluded.
    """
    roots = list(rootnames)
    require(len(roots) == len(set(roots)) and all(isinstance(name,str) and name for name in roots),
        'invalid or duplicate mapped dependency root')
    identities = [item['id'] for item in bindings]
    require(len(identities) == len(set(identities)), 'duplicate registered binding identity')
    by_name = {}
    for item in bindings:
        require(isinstance(item['theorem'],str) and item['theorem'] and isinstance(item['id'],str) and item['id'],
            'invalid registered theorem binding')
        by_name.setdefault(item['theorem'],set()).add(item['id'])
    channels, adjacency = {}, {}
    for item in dependencies:
        source, channel, targets = item['source'],item['channel'],item['targets']
        require(channel in {'TYPE','VALUE','STRUCTURE'}, 'unknown mapped dependency channel')
        require((source,channel) not in channels, 'duplicate mapped dependency channel')
        require(len(targets) == len(set(targets)) and all(isinstance(target,str) and target for target in targets),
            'invalid mapped dependency targets')
        channels[source,channel] = targets
        adjacency.setdefault(source,set()).update(targets)
    for source in adjacency:
        require(all((source,c) in channels for c in ('TYPE','VALUE','STRUCTURE')),
            'incomplete mapped dependency provenance: '+source)
    result = {}
    for root in roots:
        require(root in by_name, 'mapped root has no registered binding: '+root)
        require(root in adjacency, 'mapped root has no complete compiler expansion: '+root)
        reached, pending, mapped = {root}, list(adjacency[root]), set()
        while pending:
            name = pending.pop()
            if name in reached:
                continue
            reached.add(name)
            if name in by_name:
                require(name in adjacency, 'reachable registered root lacks compiler expansion: '+name)
                mapped.update(by_name[name])
            pending.extend(adjacency.get(name,()))
        result[root] = sorted(mapped - by_name[root])
    return result


def parse_compiler_output(text, expected_roots):
    declarations, constructors, candidates, channels, dependency_declarations = {}, {}, {}, {}, {}
    count, complete = None, None
    for root in expected_roots:
        require(root['full_name'].startswith('Zeta23.OPICA.'), 'foreign primary root namespace')
        require(root['module'] in MATHEMATICAL_MODULES, 'foreign primary defining module')
    for line in text.splitlines():
        require(complete is None or not line.strip(), 'output after the terminating completeness record')
        if line.startswith('OPICA_DECL\t'):
            parts = line.split('\t')
            require(len(parts) == 6, 'malformed OPICA declaration')
            _, name, module, kind, expression, axioms_raw = parts
            require(name not in declarations, 'duplicate OPICA declaration: '+name)
            require(module in MATHEMATICAL_MODULES, 'foreign defining module')
            # Lean caches constructor congruence lemmas in the current defining
            # module under the original constructor namespace. Enumerate these
            # public helpers with the same type, axiom and dependency audits;
            # the exception never applies to primary root identities.
            generated_congruence = kind == 'THEOREM' and name.endswith('.congr_simp')
            require(name.startswith('Zeta23.OPICA.') or generated_congruence,
                'foreign declaration namespace')
            metrics = validate_expression(expression)
            axioms = axioms_raw.split(',') if axioms_raw else []
            require(len(axioms) == len(set(axioms)), 'duplicate axiom')
            require(set(axioms) <= ALLOWED_AXIOMS, 'unadmitted mathematical axiom: '+name)
            require(kind != 'AXIOM', 'new project axiom: '+name)
            declarations[name] = {'name':name, 'module':module, 'kind':kind,
                'type_expression':json.loads(expression), 'type_metrics':metrics,
                'type_sha256':hashlib.sha256(expression.encode()).hexdigest(), 'axioms':axioms}
        elif line.startswith('OPICA_CONSTRUCTOR\t'):
            parts = line.split('\t')
            require(len(parts) == 4, 'malformed constructor')
            _, family, name, expression = parts
            require(name not in constructors, 'duplicate constructor: '+name)
            validate_expression(expression)
            constructors[name] = {'family':family, 'type_expression':json.loads(expression)}
        elif line.startswith('OPICA_PUBLIC_COUNT\t'):
            require(count is None, 'duplicate public count')
            parts = line.split('\t')
            require(len(parts) == 2 and parts[1].isdigit(), 'malformed public count')
            count = int(parts[1])
        elif line.startswith('OPICA_COMPLETE\t'):
            parts = line.split('\t')
            require(len(parts) == 2 and parts[1].isdigit(), 'malformed terminating completeness record')
            complete = int(parts[1])
        elif line.startswith('RHRC_CANDIDATE_RESULT\t'):
            parts = line.split('\t')
            require(len(parts) == 10, 'malformed exact candidate resolution')
            _, identity, status, number, name, module, kind, private, pretty_type, _ = parts
            require(identity not in candidates, 'duplicate root candidate')
            require(status == 'RESOLVED_UNIQUE' and number == '1' and private == '0',
                    'unresolved/private/ambiguous root: '+identity)
            candidates[identity] = {'name':name, 'module':module, 'kind':kind, 'full_type':pretty_type}
        elif line.startswith('RHKG_DEP_DECL\t'):
            parts = line.split('\t')
            require(len(parts) == 5, 'malformed dependency declaration')
            _, name, module, kind, internal = parts
            require(internal in {'0','1'}, 'invalid dependency privacy flag')
            record = (module, kind, internal)
            require(name not in dependency_declarations, 'duplicate dependency declaration')
            dependency_declarations[name] = record
        elif line.startswith('RHKG_DEP_CHANNEL\t'):
            _, name, channel, *targets = line.split('\t')
            require(channel in {'TYPE','VALUE','STRUCTURE'}, 'unknown dependency channel')
            key = (name, channel)
            require(key not in channels, 'duplicate dependency channel')
            require(len(targets) == len(set(targets)) and all(targets), 'invalid dependency targets')
            channels[key] = targets
        elif line.startswith(('OPICA_', 'RHKG_DEP_', 'RHRC_CANDIDATE_RESULT')):
            raise ValueError('unknown or malformed compiler protocol record')
    require(count is not None and count == len(declarations) and count > 0, 'incomplete public enumeration')
    require(complete == count, 'missing or inconsistent terminating completeness record')
    expected_ids = {root['id'] for root in expected_roots}
    require(set(candidates) == expected_ids, 'missing or extra primary root resolutions')
    for root in expected_roots:
        name = root['full_name']
        require(name in declarations, 'missing root type/axiom export: '+name)
        record = declarations[name]
        candidate = candidates[root['id']]
        require(record['module'] == root['module'] and record['kind'] == root['kind'], 'root module/kind mismatch')
        require(candidate['name'] == name and candidate['module'] == root['module'] and candidate['kind'] == root['kind'],
                'root source resolution mismatch')
        require(bool(candidate['full_type']), 'missing human-readable root type')
        record['full_type'] = candidate['full_type']
        if 'expected_type_sha256' in root:
            require(record['type_sha256'] == root['expected_type_sha256'], 'reviewed expected type changed: '+name)
    result = {'declarations':list(declarations.values()), 'constructors':constructors,
        'dependency_declarations':[{'name':name,'module':module,'kind':kind,'internal':internal == '1'}
            for name,(module,kind,internal) in sorted(dependency_declarations.items())],
        'dependencies':[{'source':source,'channel':channel,'targets':targets}
            for (source,channel),targets in sorted(channels.items())]}
    validate_compiler_records(result,expected_roots)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    destination = parser.add_mutually_exclusive_group(required=True)
    destination.add_argument('--output-dir', type=Path)
    destination.add_argument('--output', type=Path)
    parser.add_argument('--manifest', type=Path, default=HERE/'BUILD_MANIFEST.json')
    parser.add_argument('--roots', type=Path, default=HERE/'PUBLIC_ROOTS.json')
    parser.add_argument('--compiler-log', type=Path)
    parser.add_argument('--requested-head', default='HEAD')
    parser.add_argument('--requested-base', default='97926d6a949fed7af0429a373b47abc772012834')
    args = parser.parse_args()
    target = args.output.resolve() if args.output else args.output_dir.resolve()/'compiler-receipt.json'
    output = args.output_dir.resolve() if args.output_dir else target.parent/(target.stem+'-logs')
    require(not target.is_relative_to(REPO.resolve()), 'compiler receipt must be external')
    require(not output.is_relative_to(REPO.resolve()), 'execution artifacts must be external')
    output.mkdir(parents=True, exist_ok=True)
    require(args.manifest.resolve() == (HERE/'BUILD_MANIFEST.json').resolve(), 'foreign manifest path')
    require(args.roots.resolve() == (HERE/'PUBLIC_ROOTS.json').resolve(), 'foreign roots path')
    manifest = json.loads((HERE/'BUILD_MANIFEST.json').read_text(encoding='utf-8'))
    def git(*parts):
        return subprocess.check_output(['git',*parts],cwd=REPO,text=True).strip()
    head, tree = git('rev-parse','HEAD'), git('rev-parse','HEAD^{tree}')
    require(not git('status','--porcelain'), 'compiler receipt requires a clean committed checkout')
    require(git('rev-parse',args.requested_base) == manifest['base_commit'], 'base precondition changed')
    requested_head = git('rev-parse',args.requested_head)
    parents = git('rev-list','--parents','-n','1',head).split()[1:]
    checkout_kind = 'PR_HEAD' if requested_head==head else 'SYNTHETIC_MERGE'
    validate_checkout_identity({'checked_commit':head,'checked_tree':tree,
        'requested_head':requested_head,'checkout_kind':checkout_kind},head,tree,parents)
    commands = []
    def run(command, log_name):
        started = time.monotonic()
        result = subprocess.run(command,cwd=REPO,text=True,encoding='utf-8',
            stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log_sha256 = write_compiler_log(output/log_name,result.stdout)
        commands.append({'argv':command,'exit_code':result.returncode,'seconds':time.monotonic()-started,
            'log':log_name,'log_sha256':log_sha256})
        require(result.returncode == 0, 'compiler command failed; see '+str(output/log_name))
        return result.stdout
    version = run(['lake','env','lean','--version'],'lean-version.log')
    require('version 4.33.0-rc2,' in version, 'wrong Lean runtime')
    lake_manifest = json.loads((REPO/'lake-manifest.json').read_text(encoding='utf-8'))
    require(next(p['rev'] for p in lake_manifest['packages'] if p['name']=='mathlib') == manifest['mathlib_commit'],
        'wrong Mathlib pin')
    mathlib = str(REPO/'.lake/packages/mathlib')
    require(git('-C',mathlib,'rev-parse','HEAD') == manifest['mathlib_commit'], 'wrong Mathlib source checkout')
    require(not git('-C',mathlib,'diff','--name-only','HEAD'), 'modified Mathlib tracked sources')
    run(['lake','build',*manifest['no_root_api_pollution']['required_build_targets']],'build.log')
    stdout = run(['lake','env','lean','Zeta23/RHRC/OpicaBindings.lean'],'bindings.log')
    roots = json.loads((HERE/'PUBLIC_ROOTS.json').read_text(encoding='utf-8'))['primary_roots']
    reviewed = json.loads((HERE/'WORKFLOW_CONTRACT.json').read_text(encoding='utf-8')).get('reviewed_root_type_sha256', {})
    roots = with_reviewed_root_types(roots,reviewed)
    receipt = parse_compiler_output(stdout,roots)
    if args.compiler_log:
        supplied = parse_compiler_output(args.compiler_log.read_text(encoding='utf-8'),roots)
        require(supplied == receipt, 'supplied compiler log differs from fresh current-checkout export')
    source_paths = [item['path'] for item in manifest['create']] + [item['path'] for item in manifest['modify']]
    receipt.update({'schema':'OPICA_COMPILER_RECEIPT_V1','checked_commit':head,'checked_tree':tree,
        'requested_head':requested_head,'requested_base':manifest['base_commit'],
        'checkout_kind':checkout_kind,
        'commands':commands,'python':platform.python_version(),'lean':version.strip(),
        'runner':{'os':platform.system(),'release':platform.release(),
            'architecture':platform.machine(),'github_runner_os':os.environ.get('RUNNER_OS'),
            'github_runner_arch':os.environ.get('RUNNER_ARCH'),
            'image_os':os.environ.get('ImageOS'),'image_version':os.environ.get('ImageVersion')},
        'mathlib_commit':manifest['mathlib_commit'],
        'sources':{p:hashlib.sha256((REPO/p).read_bytes()).hexdigest() for p in source_paths},
        'status':'COMPILER_VERIFIED','semantic_review':'REQUIRES_EXACT_TYPE_AND_PAPER_CLAUSE_REVIEW',
        'independent_review_approved':False,'RH':'OPEN','Step4':'OPEN'})
    require(git('rev-parse','HEAD') == head and not git('status','--porcelain'), 'checkout changed during build')
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print('Complete compiler receipt: '+str(target))


if __name__ == '__main__':
    main()
