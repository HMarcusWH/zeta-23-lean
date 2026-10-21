"""Structural compiler-use delta. Shared dependencies never imply equivalence."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0,str(HERE))
from build_receipt import validate_checkout_identity, validate_compiler_receipt, validate_dependency_closure, with_reviewed_root_types


def require(condition, message):
    if not condition:
        raise ValueError(message)


def baseline_edges(rows):
    result = set()
    sources = set()
    for row in rows:
        source = row['declaration']
        require(source not in sources,'duplicate baseline declaration')
        sources.add(source)
        for dependency in row['dependencies']:
            for field,channel in [('used_in_type','TYPE'),('used_in_value','VALUE'),('used_in_structure','STRUCTURE')]:
                if dependency[field]:
                    result.add((source,dependency['constant'],channel))
    return result,sources


def delta(old_rows,receipt,roots):
    require(receipt.get('schema') == 'OPICA_COMPILER_RECEIPT_V1' and receipt.get('status') == 'COMPILER_VERIFIED',
        'complete compiler receipt required')
    for field in ('checked_commit','checked_tree'):
        require(re.fullmatch(r'[0-9a-f]{40}',receipt[field]) is not None,'invalid checked source identity')
    names = [d['name'] for d in receipt['declarations']]
    require(len(names) == len(set(names)),'duplicate public declaration')
    declared = {d['name']:d for d in receipt['declarations']}
    for root in roots:
        item = declared.get(root['full_name'])
        require(item is not None and item['kind'] == 'THEOREM' and item['module'] == root['module'],
            'missing or wrong source-bound primary root')
    validate_dependency_closure(receipt['declarations'],receipt['dependency_declarations'],receipt['dependencies'])
    old,old_sources = baseline_edges(old_rows)
    new,seen,visited_sources = set(),set(),set()
    for record in receipt['dependencies']:
        source,channel = record['source'],record['channel']
        require(channel in {'TYPE','VALUE','STRUCTURE'},'unknown dependency provenance')
        require((source,channel) not in seen,'duplicate compiler channel')
        seen.add((source,channel))
        visited_sources.add(source)
        targets = record['targets']
        require(len(targets) == len(set(targets)),'duplicate dependency target')
        new.update((source,target,channel) for target in targets)
    for source in visited_sources:
        require(all((source,c) in seen for c in ('TYPE','VALUE','STRUCTURE')),'incomplete type/value/structure provenance')
    # A new-root traversal does not revisit every old registered root. An edge
    # outside that traversal has not been removed from the mathematical source.
    revisited_old = {edge for edge in old if edge[0] in visited_sources}
    observed_old = {edge for edge in new if edge[0] in old_sources}
    require(revisited_old == observed_old,'unchanged baseline declaration dependency drift')
    added = sorted(new-old)
    shared = sorted({target for _,target,_ in old} & {target for _,target,_ in new})
    coverage = {}
    for root in roots:
        coverage.setdefault(root['paper_id'],[]).append(root['full_name'])
    return {'schema':'OPICA_DEPENDENCY_DELTA_V1','status':'PASS',
        'checked_commit':receipt['checked_commit'],'checked_tree':receipt['checked_tree'],
        'primary_root_count':len(roots),'public_declaration_count':len(names),
        'added_compiler_use_count':len(added),
        'added_compiler_uses':[{'source':s,'target':t,'channel':c} for s,t,c in added],
        'revisited_baseline_source_count':len(old_sources & visited_sources),
        'baseline_sources_not_revisited':sorted(old_sources-visited_sources),
        'shared_dependency_count':len(shared),'shared_dependencies':shared,
        'paper_root_presence':coverage,
        'logical_equivalence_inferred':False,'semantic_clause_coverage_inferred':False,
        'native_premises_proved_by_dependency_sharing':False,
        'authority':'Compiler use and root-presence structure only; inspect theorem types and paper clauses separately.',
        'RH':'OPEN','Step4':'OPEN'}


def validate_source_identity(repo, receipt, manifest):
    def git(*parts):
        return subprocess.check_output(['git',*parts],cwd=repo,text=True).strip()
    require(receipt.get('checked_commit') == git('rev-parse','HEAD') and
        receipt.get('checked_tree') == git('rev-parse','HEAD^{tree}'), 'stale formal receipt head/tree')
    parents = [] if receipt.get('requested_head')==receipt['checked_commit'] else git(
        'rev-list','--parents','-n','1',receipt['checked_commit']).split()[1:]
    validate_checkout_identity(receipt,receipt['checked_commit'],receipt['checked_tree'],parents)
    require(receipt.get('requested_base') == manifest['base_commit'] and
        receipt.get('mathlib_commit') == manifest['mathlib_commit'], 'foreign formal receipt source pins')
    paths = {item['path'] for item in manifest['create'] + manifest['modify']}
    sources = receipt.get('sources',{})
    require(set(sources) == paths, 'formal receipt source inventory mismatch')
    for path in paths:
        require((repo/path).is_file() and sources[path] == hashlib.sha256((repo/path).read_bytes()).hexdigest(),
            'formal receipt source identity mismatch: '+path)


def validate_receipt_for_delta(repo, receipt, manifest, roots, reviewed=None):
    validate_source_identity(repo,receipt,manifest)
    if reviewed is None:
        reviewed = json.loads((HERE/'WORKFLOW_CONTRACT.json').read_text(encoding='utf-8')).get('reviewed_root_type_sha256',{})
    validate_compiler_receipt(receipt,manifest,with_reviewed_root_types(roots,reviewed))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal-receipt',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    require(not args.output.resolve().is_relative_to(REPO.resolve()),'research artifacts must be external')
    manifest = json.loads((HERE/'BUILD_MANIFEST.json').read_text(encoding='utf-8'))
    baseline_path = 'research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl'
    baseline_bytes = subprocess.check_output(['git','show',manifest['base_commit']+':'+baseline_path],cwd=REPO)
    old = [json.loads(line) for line in baseline_bytes.decode('utf-8').splitlines() if line]
    receipt = json.loads(args.formal_receipt.read_text(encoding='utf-8'))
    roots = json.loads((HERE/'PUBLIC_ROOTS.json').read_text(encoding='utf-8'))['primary_roots']
    validate_receipt_for_delta(REPO,receipt,manifest,roots)
    result = delta(old,receipt,roots)
    result['baseline_receipt_sha256'] = hashlib.sha256(baseline_bytes).hexdigest()
    result['baseline_commit'] = manifest['base_commit']
    result['opica_receipt_sha256'] = hashlib.sha256(args.formal_receipt.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('Structural dependency delta: '+str(args.output))


if __name__ == '__main__':
    main()
