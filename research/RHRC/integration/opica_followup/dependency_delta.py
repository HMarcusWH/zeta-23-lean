"""Source-bound compiler use and type-binder delta; never mathematical equivalence.

Full CLI use requires the real all100 receipt and both the accepted-parent and
current-child P0 compiler receipts/logs. It does not fabricate missing parent
acceptance or independent review. Pure comparison functions also support
adversarial protocol tests; synthetic test records are not compiler authority.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
CHANNELS = ('TYPE', 'VALUE', 'STRUCTURE')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_builders(repo):
    path = Path(repo) / 'research/RHRC/integration/opica_followup/build_receipt.py'
    spec = importlib.util.spec_from_file_location('_opica_delta_child_receipt', path)
    child = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(child)
    return child, child.load_parent_builder(Path(repo))


def dependency_channels(export):
    """Require all three unique compiler channels for every expanded source."""
    result = {}
    for row in export['dependencies']:
        key = row['source'], row['channel']
        require(row['channel'] in CHANNELS and key not in result,
                'unknown or duplicate dependency channel')
        targets = row['targets']
        require(isinstance(targets, list) and all(isinstance(t, str) and t for t in targets)
                and len(targets) == len(set(targets)), 'invalid dependency targets')
        result[key] = tuple(sorted(targets))
    for source, _ in result:
        require(all((source, c) in result for c in CHANNELS),
                'incomplete dependency channels: ' + source)
    return result


def compare_parent_exports(baseline, current, parent_builder):
    """Compare revalidated full types, axioms and complete use graphs exactly.

    This reports compiler equality only. Source/log/checkout identity and scope
    must additionally be validated by the CLI before using the report.
    """
    parent_builder.validate_compiler_records(baseline)
    parent_builder.validate_compiler_records(current)
    old = {r['name']: r for r in baseline['declarations']}
    new = {r['name']: r for r in current['declarations']}
    require(set(old) == set(new), 'parent public declaration inventory changed')
    require(baseline['constructors'] == current['constructors'], 'parent constructor inventory changed')
    for name, row in old.items():
        require(row['module'] == new[name]['module'] and row['kind'] == new[name]['kind'],
                'parent declaration origin or kind changed: ' + name)
        require(row['type_expression'] == new[name]['type_expression']
                and row['type_sha256'] == new[name]['type_sha256'],
                'parent full type or premise changed: ' + name)
        require(sorted(row['axioms']) == sorted(new[name]['axioms']),
                'parent axiom set changed: ' + name)
    old_channels, new_channels = dependency_channels(baseline), dependency_channels(current)
    require(old_channels == new_channels, 'parent TYPE/VALUE/STRUCTURE dependency graph changed')
    old_nodes = {r['name']: r for r in baseline['dependency_declarations']}
    new_nodes = {r['name']: r for r in current['dependency_declarations']}
    require(old_nodes == new_nodes, 'parent dependency origins/kinds/private nodes changed')
    require(not any(r['module'] == 'Zeta23.OPICAFollowup' or
                    r['module'].startswith('Zeta23.OPICAFollowup.') for r in new_nodes.values()),
            'parent mathematical compiler closure acquired a child dependency')
    return {'status': 'EXACT_PARENT_COMPILER_TYPES_AXIOMS_AND_DEPENDENCIES_EQUAL',
            'public_declarations': len(old), 'constructors': len(baseline['constructors']),
            'dependency_nodes': len(old_nodes), 'dependency_channels': len(old_channels),
            'changed_parent_types': [], 'changed_parent_axioms': [], 'changed_parent_dependencies': []}


def type_binder_inventory(expression, validate_expression):
    """List actual leading binders without calling every parameter a premise."""
    encoded = json.dumps(expression, ensure_ascii=False, separators=(',', ':'))
    validate_expression(encoded)
    dag = expression
    nodes = dag['nodes']; index = int(dag['root']); rows = []
    while True:
        node = nodes[index]
        if node[0] == 'mdata':
            index = int(node[2]); continue
        if node[0] != 'forall':
            break
        rows.append({'position': len(rows), 'name': node[1], 'binder_info': node[2],
                     'domain_dag_node': node[3],
                     'domain_node_sha256': hashlib.sha256(json.dumps(nodes[int(node[3])],
                         ensure_ascii=False, separators=(',', ':')).encode()).hexdigest(),
                     'classification': 'EXPORTED_BINDER_NOT_AUTOMATICALLY_A_LOGICAL_PREMISE'})
        index = int(node[4])
    return rows


def child_use_report(export, roots, bindings, child_builder, parent_builder, *, modules):
    """Validate complete compiler records and map registered uses, not implication."""
    child_builder.validate_compiler_records(export, roots, mathematical_modules=modules)
    channels = dependency_channels(export)
    require(len(roots) == 100 and len({r['full_name'] for r in roots}) == 100,
            'exact original100 roots required for child delta')
    require(len(bindings) == 294 and len({r['id'] for r in bindings}) == 294,
            'exact parent194 plus child100 bindings required')
    by_id = {r['id']: r for r in bindings}
    for root in roots:
        require(root['id'] in by_id and by_id[root['id']]['theorem'] == root['full_name']
                and by_id[root['id']]['source'] == root['path'],
                'registered child identity/source differs from frozen root: ' + root['full_name'])
    declarations = {r['name']: r for r in export['declarations']}
    mapped = parent_builder.mapped_registered_dependencies(
        [r['full_name'] for r in roots], bindings, export['dependencies'])
    result = []
    for root in roots:
        record = declarations[root['full_name']]
        result.append({'full_name': root['full_name'], 'id': root['id'],
            'full_type_sha256': record['type_sha256'], 'axioms': record['axioms'],
            'frozen_required_premises': root.get('required_premises', ''),
            'frozen_statement_contract': root['statement_contract'],
            'leading_type_binders': type_binder_inventory(record['type_expression'], child_builder.validate_expression),
            'direct_compiler_channels': {c: list(channels[root['full_name'], c]) for c in CHANNELS},
            'transitive_registered_use_ids': mapped[root['full_name']],
            'logical_strength_or_equivalence': 'NOT_INFERRED_FROM_COMPILER_USES'})
    return result


def verify_parent_artifacts(data, artifacts, parent, manifest, roots):
    parent.validate_compiler_receipt(data, manifest, roots)
    artifacts = Path(artifacts).resolve()
    for row in data['commands']:
        relative = row['log']
        require(relative in {'lean-version.log', 'build.log', 'bindings.log'}, 'unexpected parent artifact')
        path = artifacts / relative
        require(path.is_file() and not path.is_symlink() and path.resolve().parent == artifacts,
                'missing or escaped parent artifact')
        require(hashlib.sha256(path.read_bytes()).hexdigest() == row['log_sha256'],
                'parent compiler log hash differs: ' + relative)
    parsed = parent.parse_compiler_output((artifacts / 'bindings.log').read_text(encoding='utf-8'), roots)
    require(all(data.get(key) == value for key, value in parsed.items()),
            'parent compiler wire export differs from receipt')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent-intake', type=Path, required=True)
    parser.add_argument('--formal-receipt', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repo', type=Path, default=REPO)
    parser.add_argument('--parent-formal-receipt', type=Path)
    parser.add_argument('--current-parent-formal-receipt', type=Path)
    parser.add_argument('--parent-artifacts', type=Path)
    parser.add_argument('--current-parent-artifacts', type=Path)
    parser.add_argument('--formal-artifacts', type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve(); output = args.output.resolve()
    require(not output.is_relative_to(repo), 'delta output must be external')
    child, parent = load_builders(repo)
    contract = child.full_contract(repo)
    intake = child.unique_json(args.parent_intake.read_bytes())
    protected = child.unique_json((repo / 'research/RHRC/integration/opica_followup/PROTECTED_STATE.json').read_bytes())
    require(intake.get('schema') == 'OPICA_FOLLOWUP_PROTECTED_PARENT_V1'
            and intake.get('parent_head') == protected['parent_head']
            and intake.get('parent_tree') == protected['parent_tree'], 'exact protected parent intake required')
    for key in ('files', 'claim_registry', 'theorem_bindings', 'file_classes', 'semantic_closure', 'open_claim_ids'):
        require(intake.get(key) == protected[key], 'parent intake differs from protected baseline: ' + key)
    require(args.parent_formal_receipt is not None and args.current_parent_formal_receipt is not None,
            'both accepted-parent and current-child P0 compiler receipts are required; source capture alone has no type/premise evidence')
    formal = child.unique_json(args.formal_receipt.read_bytes())
    child.validate_full_receipt_structure(formal, repo, args.formal_artifacts or args.formal_receipt.parent)
    baseline = child.unique_json(args.parent_formal_receipt.read_bytes())
    current = child.unique_json(args.current_parent_formal_receipt.read_bytes())
    parent_folder = repo / 'research/RHRC/integration/opica'
    manifest = child.unique_json((parent_folder / 'BUILD_MANIFEST.json').read_bytes())
    roots = child.unique_json((parent_folder / 'PUBLIC_ROOTS.json').read_bytes())['primary_roots']
    workflow = child.unique_json((parent_folder / 'WORKFLOW_CONTRACT.json').read_bytes())
    roots = parent.with_reviewed_root_types(roots, workflow['reviewed_root_type_sha256'])
    verify_parent_artifacts(baseline, args.parent_artifacts or args.parent_formal_receipt.parent, parent, manifest, roots)
    verify_parent_artifacts(current, args.current_parent_artifacts or args.current_parent_formal_receipt.parent, parent, manifest, roots)
    require(baseline['checked_commit'] == protected['parent_head'] and baseline['checked_tree'] == protected['parent_tree'],
            'baseline compiler receipt is not the exact accepted parent')
    require(current['checked_commit'] == formal['checked_commit'] and current['checked_tree'] == formal['checked_tree'],
            'current P0 and child compiler receipts mix source trees')
    expected_source_paths = {r['path'] for r in manifest['create'] + manifest['modify']}
    require(set(baseline['sources']) == expected_source_paths and set(current['sources']) == expected_source_paths,
            'parent source hash inventory incomplete')
    for path in sorted(expected_source_paths):
        original = subprocess.check_output(['git', '-C', str(repo), 'show', protected['parent_head'] + ':' + path])
        require(baseline['sources'][path] == hashlib.sha256(original).hexdigest(), 'baseline parent source hash differs: ' + path)
        require(current['sources'][path] == hashlib.sha256(child.safe_source(repo, path).read_bytes()).hexdigest(),
                'current parent source hash differs: ' + path)
    old = compare_parent_exports(baseline, current, parent)
    bindings = child.unique_json((repo / 'research/RHRC/REGISTERED_THEOREM_BINDINGS.json').read_bytes())['bindings']
    report = {'schema': 'OPICA_FOLLOWUP_DEPENDENCY_DELTA_V1',
        'status': 'SOURCE_BOUND_COMPILER_DELTA_VERIFIED_NOT_RELEASE_ACCEPTANCE',
        'checked_commit': formal['checked_commit'], 'checked_tree': formal['checked_tree'],
        'parent_checked_commit': baseline['checked_commit'], 'parent_checked_tree': baseline['checked_tree'],
        'parent_preservation': old,
        'original100_child_uses': child_use_report(formal, contract['roots'], bindings, child, parent, modules=contract['export_modules']),
        'input_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in
            [args.parent_intake, args.formal_receipt, args.parent_formal_receipt, args.current_parent_formal_receipt]},
        'logical_equivalence_from_shared_edges': False,
        'fresh_replay_or_parent_acceptance_established_here': False,
        'independent_semantic_review': 'NOT_CREATED_BY_THIS_REPORT',
        'release_ready': False, 'full_release_accepted': False, 'RH': 'OPEN', 'Step4': 'OPEN'}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(report['status'])
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
