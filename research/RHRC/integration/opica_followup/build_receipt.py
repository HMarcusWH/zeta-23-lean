"""Compiler receipt for the implemented subset; full release remains closed.

The type-DAG and TYPE/VALUE/STRUCTURE closure algorithms are copied from the
immutable parent build_receipt.py at the accepted PR293 tree. Their child's
namespace, modules and wire-record prefix are separate from P0.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO / 'research/RHRC/routes/R003_ccm_bridge/post290'))
from lean_expr_dag import validate_expression
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SHA40 = re.compile(r'[0-9a-f]{40}\Z')
SHA256 = re.compile(r'[0-9a-f]{64}\Z')
MATHEMATICAL_MODULES = frozenset(['Zeta23.OPICAFollowup.BalancedCoefficients', 'Zeta23.OPICAFollowup.Counterexamples', 'Zeta23.OPICAFollowup.ForwardLocalization', 'Zeta23.OPICAFollowup.JointObservation', 'Zeta23.OPICAFollowup.NativeExplicitFormula', 'Zeta23.OPICAFollowup.NativeFilters', 'Zeta23.OPICAFollowup.NativeSourceFamily', 'Zeta23.OPICAFollowup.NativeSourceTransforms', 'Zeta23.OPICAFollowup.NativeTransformationWords', 'Zeta23.OPICAFollowup.NormFirstTransfer', 'Zeta23.OPICAFollowup.RobustLaurent', 'Zeta23.OPICAFollowup.SourceVerticalBounds', 'Zeta23.OPICAFollowup.UniformSourceBounds', 'Zeta23.OPICAFollowup.ZetaLeftLineBounds'])

IMPLEMENTED_ROOT_NAMES = frozenset(['Zeta23.OPICAFollowup.approx_compatibility_left_null', 'Zeta23.OPICAFollowup.balanced_coeff_divisor_bound', 'Zeta23.OPICAFollowup.coupled_gram_collision_control', 'Zeta23.OPICAFollowup.energy_allocation_bound', 'Zeta23.OPICAFollowup.energy_allocation_rate_lower', 'Zeta23.OPICAFollowup.forced_positive_gram_nonreal_control', 'Zeta23.OPICAFollowup.forwardKernel_double_exp_decay', 'Zeta23.OPICAFollowup.forwardKernel_left_contour_budget', 'Zeta23.OPICAFollowup.forwardKernel_physical_laplace', 'Zeta23.OPICAFollowup.history_recovery_cost_control', 'Zeta23.OPICAFollowup.joint_recovery_iff', 'Zeta23.OPICAFollowup.joint_recovery_noise_bound', 'Zeta23.OPICAFollowup.joint_recovery_optimal_norm', 'Zeta23.OPICAFollowup.laurent_coefficient_error_bound', 'Zeta23.OPICAFollowup.laurent_observation_survives', 'Zeta23.OPICAFollowup.nativeGenerator_transform', 'Zeta23.OPICAFollowup.nativeGenerator_unit_or_completion', 'Zeta23.OPICAFollowup.nativePrimeField_visiblePole', 'Zeta23.OPICAFollowup.nativeWord_contour_consumer', 'Zeta23.OPICAFollowup.nativeWord_corrected_transform', 'Zeta23.OPICAFollowup.nativeWord_factor_costs', 'Zeta23.OPICAFollowup.nativeWord_first_nonzero_derivative', 'Zeta23.OPICAFollowup.nativeWord_order_and_leading', 'Zeta23.OPICAFollowup.native_binomial_inverse_identity', 'Zeta23.OPICAFollowup.native_field_theta_envelope', 'Zeta23.OPICAFollowup.native_source_explicit_formula', 'Zeta23.OPICAFollowup.native_zero_count_summability', 'Zeta23.OPICAFollowup.native_zero_sup_bounds', 'Zeta23.OPICAFollowup.norm_first_log_comparison', 'Zeta23.OPICAFollowup.norm_first_rate_transfer', 'Zeta23.OPICAFollowup.norm_first_strictly_weaker_control', 'Zeta23.OPICAFollowup.recovery_subexp_budget', 'Zeta23.OPICAFollowup.sourceFamily_laplace_identity', 'Zeta23.OPICAFollowup.sourceFamily_support_smooth_moments', 'Zeta23.OPICAFollowup.sourceFamily_zero_eq_original', 'Zeta23.OPICAFollowup.source_order_uniform_norms', 'Zeta23.OPICAFollowup.source_product_vertical_bound', 'Zeta23.OPICAFollowup.zeta_left_line_uniform_bound'])


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
    equations = receipt.get('generated_equations', {})
    require(isinstance(equations,dict) and all(isinstance(name,str) and isinstance(origin,str)
        for name,origin in equations.items()), 'malformed generated equation provenance')
    declarations = {}
    kinds = {'DEFINITION','THEOREM','OPAQUE','QUOTIENT','INDUCTIVE','CONSTRUCTOR','RECURSOR'}
    for record in records:
        require(isinstance(record,dict) and {'name','module','kind','axioms','type_expression',
            'type_sha256','type_metrics'}<=set(record), 'missing public declaration evidence fields')
        name,module,kind = record['name'],record['module'],record['kind']
        require(isinstance(name,str) and name not in declarations, 'invalid or duplicate public declaration')
        require(module in MATHEMATICAL_MODULES, 'foreign defining module')
        require(kind in kinds, 'unadmitted public declaration kind')
        require(name.startswith('Zeta23.OPICAFollowup.') or
            (kind=='THEOREM' and (name.endswith('.congr_simp') or name in equations)),
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
        require(root['full_name'].startswith('Zeta23.OPICAFollowup.'), 'foreign primary root namespace')
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
    validate_generated_equations(equations,declarations,channels,
        {row['name']:(row['module'],row['kind'],'1' if row['internal'] else '0')
            for row in receipt['dependency_declarations']})
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


def validate_generated_equations(equations, declarations, channels, dependency_declarations):
    """Reserved equation names are audited helpers, never additional roots."""
    for name, origin in equations.items():
        require(name in declarations and declarations[name]['kind'] == 'THEOREM',
                'generated equation lacks public theorem audit')
        require(re.fullmatch(re.escape(origin) + r'\.(?:eq_[0-9]+|eq_def|eq_unfold)', name) is not None,
                'generated equation has noncanonical reserved name')
        require(origin in channels.get((name, 'TYPE'), []),
                'generated equation type does not reference its original definition')
        require(origin in dependency_declarations and dependency_declarations[origin][1] == 'DEFINITION',
                'generated equation origin is not an audited definition')


def parse_compiler_output(text, expected_roots):
    declarations, constructors, candidates, channels, dependency_declarations = {}, {}, {}, {}, {}
    generated_equations = {}
    count, complete = None, None
    for root in expected_roots:
        require(root['full_name'].startswith('Zeta23.OPICAFollowup.'), 'foreign primary root namespace')
        require(root['module'] in MATHEMATICAL_MODULES, 'foreign primary defining module')
    for line in text.splitlines():
        require(complete is None or not line.strip(), 'output after the terminating completeness record')
        if line.startswith('OPICA_FOLLOWUP_DECL\t'):
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
            generated_equation = kind == 'THEOREM' and name in generated_equations
            require(name.startswith('Zeta23.OPICAFollowup.') or generated_congruence or generated_equation,
                'foreign declaration namespace')
            metrics = validate_expression(expression)
            axioms = axioms_raw.split(',') if axioms_raw else []
            require(len(axioms) == len(set(axioms)), 'duplicate axiom')
            require(set(axioms) <= ALLOWED_AXIOMS, 'unadmitted mathematical axiom: '+name)
            require(kind != 'AXIOM', 'new project axiom: '+name)
            declarations[name] = {'name':name, 'module':module, 'kind':kind,
                'type_expression':json.loads(expression), 'type_metrics':metrics,
                'type_sha256':hashlib.sha256(expression.encode()).hexdigest(), 'axioms':axioms}
        elif line.startswith('OPICA_FOLLOWUP_GENERATED_EQUATION\t'):
            parts = line.split('\t')
            require(len(parts) == 3 and all(parts[1:]), 'malformed generated equation provenance')
            _, name, origin = parts
            require(name not in generated_equations, 'duplicate generated equation provenance')
            generated_equations[name] = origin
        elif line.startswith('OPICA_FOLLOWUP_CONSTRUCTOR\t'):
            parts = line.split('\t')
            require(len(parts) == 4, 'malformed constructor')
            _, family, name, expression = parts
            require(name not in constructors, 'duplicate constructor: '+name)
            validate_expression(expression)
            constructors[name] = {'family':family, 'type_expression':json.loads(expression)}
        elif line.startswith('OPICA_FOLLOWUP_PUBLIC_COUNT\t'):
            require(count is None, 'duplicate public count')
            parts = line.split('\t')
            require(len(parts) == 2 and parts[1].isdigit(), 'malformed public count')
            count = int(parts[1])
        elif line.startswith('OPICA_FOLLOWUP_COMPLETE\t'):
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
        elif line.startswith(('OPICA_FOLLOWUP_', 'RHKG_DEP_', 'RHRC_CANDIDATE_RESULT')):
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
    validate_generated_equations(generated_equations, declarations, channels, dependency_declarations)
    result = {'declarations':list(declarations.values()), 'constructors':constructors,
        'generated_equations':generated_equations,
        'dependency_declarations':[{'name':name,'module':module,'kind':kind,'internal':internal == '1'}
            for name,(module,kind,internal) in sorted(dependency_declarations.items())],
        'dependencies':[{'source':source,'channel':channel,'targets':targets}
            for (source,channel),targets in sorted(channels.items())]}
    validate_compiler_records(result,expected_roots)
    return result

def git(*parts):
    return subprocess.run(['git', '-C', str(REPO), *parts], check=True,
                          stdout=subprocess.PIPE).stdout.decode('utf-8').strip()


def source_manifest():
    paths = git('ls-files', '-z', '--cached', '--others', '--exclude-standard').split('\0')
    result = []
    for name in sorted(set(filter(None, paths))):
        path = REPO / name
        require(path.is_file() and not path.is_symlink()
                and path.resolve().is_relative_to(REPO.resolve()), 'source path missing/escaped: ' + name)
        content = path.read_bytes()
        result.append({'path': name, 'bytes': len(content),
                       'sha256': hashlib.sha256(content).hexdigest()})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--requested-head', required=True)
    parser.add_argument('--requested-base', required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--preparation-only', action='store_true')
    args = parser.parse_args()
    if not args.preparation_only:
        parser.error('full release is closed: this compiler audit covers only the implemented subset')
    require(SHA40.fullmatch(args.requested_head) is not None, 'exact requested head required')
    require(args.requested_head == git('rev-parse', 'HEAD'), 'requested head differs from checkout')
    require(args.requested_base == 'd53dd70d38b0762af130b1d19b795af259f505f5',
            'unreviewed accepted parent')
    require(git('merge-base', args.requested_head, args.requested_base) == args.requested_base,
            'checkout does not descend from accepted parent')
    output = args.output_dir.resolve()
    require(not output.is_relative_to(REPO.resolve()), 'compiler artifacts must be outside checkout')
    output.mkdir(parents=True, exist_ok=True)
    root_bytes = (HERE / 'PUBLIC_ROOTS.json').read_bytes()
    require(hashlib.sha256(root_bytes).hexdigest() ==
            '2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41',
            'frozen public root inventory changed')
    public = json.loads(root_bytes)['roots']
    roots = [row for row in public if row['full_name'] in IMPLEMENTED_ROOT_NAMES]
    require(len(roots) == 38 and len({r['id'] for r in roots}) == 38,
            'exact thirty-eight-root implemented subset required')
    before = source_manifest()
    records = []
    environment = os.environ.copy()
    environment['LEAN_NUM_THREADS'] = '2'
    for label, command in [
        ('version', [args.lake, 'env', 'lean', '--version']),
        ('build', [args.lake, 'build', 'Zeta23.OPICAFollowup.Validation']),
        # Compile the exporter once, emitting both its checked object and full
        # protocol. Building it first would repeat the same expensive traversal.
        ('export', [args.lake, 'env', 'lean', 'Zeta23/RHRC/OpicaFollowupBindings.lean',
                    '-o', str(output / 'OpicaFollowupBindings.olean')])]:
        process = subprocess.run(command, cwd=REPO, env=environment, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, timeout=3600)
        log = output / (label + '.log')
        log.write_bytes(process.stdout)
        records.append({'command': command, 'exit_code': process.returncode,
                        'log': log.name, 'stdout_sha256': hashlib.sha256(process.stdout).hexdigest()})
        require(process.returncode == 0, 'compiler command failed: ' + label)
        if label == 'version':
            require('version 4.33.0-rc2,' in process.stdout.decode('utf-8'),
                    'wrong Lean compiler version')
        if label == 'export':
            parsed = parse_compiler_output(process.stdout.decode('utf-8'), roots)
    require(before == source_manifest(), 'source inputs changed during compiler commands')
    require(args.requested_head == git('rev-parse', 'HEAD'), 'checkout head changed during audit')
    missing = [r['full_name'] for r in public if r not in roots]
    report = {'schema': 'OPICA_FOLLOWUP_SUBSET_COMPILER_RECEIPT_V1',
              'status': 'PASS_SOURCE_BOUND_SUBSET_ONLY', 'release_ready': False,
              'requested_head': args.requested_head, 'checked_commit': git('rev-parse', 'HEAD'),
              'checked_tree': git('rev-parse', 'HEAD^{tree}'),
              'requested_base': args.requested_base,
              'working_tree_dirty': bool(git('status', '--porcelain')),
              'source_manifest': before,
              'source_manifest_sha256': hashlib.sha256(json.dumps(before, sort_keys=True).encode()).hexdigest(),
              'commands': records, 'implemented_primary_roots': [r['full_name'] for r in roots],
              'compiled_export_sha256': hashlib.sha256(
                  (output / 'OpicaFollowupBindings.olean').read_bytes()).hexdigest(),
              'missing_primary_roots': missing, 'full_primary_count': len(public),
              'type_review': 'Explicit expected-type consumers compiled; agent review is not independent human review',
              'independent_human_review': 'NOT_ESTABLISHED', 'RH': 'OPEN', 'Step4': 'OPEN', **parsed}
    (output / 'compiler-receipt.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': report['status'], 'primary_roots': len(roots),
                      'remaining': len(missing), 'public_declarations': len(parsed['declarations']),
                      'constructors': len(parsed['constructors']),
                      'dependency_nodes': len(parsed['dependency_declarations']), 'release_ready': False}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
