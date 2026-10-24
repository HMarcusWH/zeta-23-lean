"""Separate source-bound subset and full100 compiler receipts.

The type-DAG and TYPE/VALUE/STRUCTURE closure algorithms are copied from the
immutable parent build_receipt.py at the accepted PR293 tree. Their child's
namespace, modules and wire-record prefix are separate from P0.

Full mode additionally needs a separately sealed full semantic review and a
cold project clone. Compiler success alone never accepts the full release.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO / 'research/RHRC/routes/R003_ccm_bridge/post290'))
from lean_expr_dag import validate_expression
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SHA40 = re.compile(r'[0-9a-f]{40}\Z')
SHA256 = re.compile(r'[0-9a-f]{64}\Z')
MATHEMATICAL_MODULES = frozenset(['Zeta23.OPICAFollowup.BalancedCoefficients', 'Zeta23.OPICAFollowup.Counterexamples', 'Zeta23.OPICAFollowup.ForwardLocalization', 'Zeta23.OPICAFollowup.JointObservation', 'Zeta23.OPICAFollowup.NativeExplicitFormula', 'Zeta23.OPICAFollowup.NativeFilters', 'Zeta23.OPICAFollowup.NativeSourceFamily', 'Zeta23.OPICAFollowup.NativeSourceTransforms', 'Zeta23.OPICAFollowup.NativeTransformationWords', 'Zeta23.OPICAFollowup.NormFirstTransfer', 'Zeta23.OPICAFollowup.RobustLaurent', 'Zeta23.OPICAFollowup.SourceVerticalBounds', 'Zeta23.OPICAFollowup.UniformSourceBounds', 'Zeta23.OPICAFollowup.ZetaLeftLineBounds'])

IMPLEMENTED_ROOT_NAMES = frozenset(['Zeta23.OPICAFollowup.approx_compatibility_left_null', 'Zeta23.OPICAFollowup.balanced_coeff_divisor_bound', 'Zeta23.OPICAFollowup.coupled_gram_collision_control', 'Zeta23.OPICAFollowup.energy_allocation_bound', 'Zeta23.OPICAFollowup.energy_allocation_rate_lower', 'Zeta23.OPICAFollowup.forced_positive_gram_nonreal_control', 'Zeta23.OPICAFollowup.forwardKernel_double_exp_decay', 'Zeta23.OPICAFollowup.forwardKernel_left_contour_budget', 'Zeta23.OPICAFollowup.forwardKernel_physical_laplace', 'Zeta23.OPICAFollowup.history_recovery_cost_control', 'Zeta23.OPICAFollowup.joint_recovery_iff', 'Zeta23.OPICAFollowup.joint_recovery_noise_bound', 'Zeta23.OPICAFollowup.joint_recovery_optimal_norm', 'Zeta23.OPICAFollowup.laurent_coefficient_error_bound', 'Zeta23.OPICAFollowup.laurent_observation_survives', 'Zeta23.OPICAFollowup.nativeGenerator_transform', 'Zeta23.OPICAFollowup.nativeGenerator_unit_or_completion', 'Zeta23.OPICAFollowup.nativePrimeField_visiblePole', 'Zeta23.OPICAFollowup.nativeWord_contour_consumer', 'Zeta23.OPICAFollowup.nativeWord_corrected_transform', 'Zeta23.OPICAFollowup.nativeWord_factor_costs', 'Zeta23.OPICAFollowup.nativeWord_first_nonzero_derivative', 'Zeta23.OPICAFollowup.nativeWord_order_and_leading', 'Zeta23.OPICAFollowup.native_binomial_inverse_identity', 'Zeta23.OPICAFollowup.native_field_theta_envelope', 'Zeta23.OPICAFollowup.native_source_explicit_formula', 'Zeta23.OPICAFollowup.native_zero_count_summability', 'Zeta23.OPICAFollowup.native_zero_sup_bounds', 'Zeta23.OPICAFollowup.norm_first_log_comparison', 'Zeta23.OPICAFollowup.norm_first_rate_transfer', 'Zeta23.OPICAFollowup.norm_first_strictly_weaker_control', 'Zeta23.OPICAFollowup.recovery_subexp_budget', 'Zeta23.OPICAFollowup.sourceFamily_laplace_identity', 'Zeta23.OPICAFollowup.sourceFamily_support_smooth_moments', 'Zeta23.OPICAFollowup.sourceFamily_zero_eq_original', 'Zeta23.OPICAFollowup.source_order_uniform_norms', 'Zeta23.OPICAFollowup.source_product_vertical_bound', 'Zeta23.OPICAFollowup.zeta_left_line_uniform_bound'])


# The continuation adds three original primary roots and supporting declarations
# in four already planned modules. Support alone never increases the root count.
MATHEMATICAL_MODULES = MATHEMATICAL_MODULES | frozenset({
    'Zeta23.OPICAFollowup.LogSlackBalance',
    'Zeta23.OPICAFollowup.MaskedNativeRate',
    'Zeta23.OPICAFollowup.AuxiliaryCompletions',
    'Zeta23.OPICAFollowup.ComplexLocalMeasures',
})
IMPLEMENTED_ROOT_NAMES = IMPLEMENTED_ROOT_NAMES | frozenset({
    'Zeta23.OPICAFollowup.log_slack_native_decomposition',
    'Zeta23.OPICAFollowup.log_slack_typeI_error',
    'Zeta23.OPICAFollowup.fixed_two_factor_preparation',
})


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


def validate_compiler_records(receipt, expected_roots=(), *, mathematical_modules=None):
    """Revalidate serialized evidence without trusting its stored type hashes."""
    modules = MATHEMATICAL_MODULES if mathematical_modules is None else frozenset(mathematical_modules)
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
        require(module in modules, 'foreign defining module')
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
        require(root['module'] in modules, 'foreign primary defining module')
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
        if node['module'] in modules and not node['internal']:
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


def parse_compiler_output(text, expected_roots, *, mathematical_modules=None):
    modules = MATHEMATICAL_MODULES if mathematical_modules is None else frozenset(mathematical_modules)
    declarations, constructors, candidates, channels, dependency_declarations = {}, {}, {}, {}, {}
    generated_equations = {}
    count, complete = None, None
    for root in expected_roots:
        require(root['full_name'].startswith('Zeta23.OPICAFollowup.'), 'foreign primary root namespace')
        require(root['module'] in modules, 'foreign primary defining module')
    for line in text.splitlines():
        require(complete is None or not line.strip(), 'output after the terminating completeness record')
        if line.startswith('OPICA_FOLLOWUP_DECL\t'):
            parts = line.split('\t')
            require(len(parts) == 6, 'malformed OPICA declaration')
            _, name, module, kind, expression, axioms_raw = parts
            require(name not in declarations, 'duplicate OPICA declaration: '+name)
            require(module in modules, 'foreign defining module')
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
            require(complete is None, 'duplicate terminating completeness record')
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
    validate_compiler_records(result,expected_roots,mathematical_modules=modules)
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


FULL_RECEIPT_SCHEMA = 'OPICA_FOLLOWUP_FULL_COMPILER_RECEIPT_V1'
FULL_REVIEW_SCHEMA = 'OPICA_FOLLOWUP_FULL_REVIEW_V1'
# No all100 semantic/type review has been accepted. This is intentionally unset;
# filling it requires an independent review, never copying a producer's digest.
FULL_REVIEW_SHA256 = None
FULL_TEMPLATE_SHA256 = '41b5dc78dd06d51336cec5ccfa3581da41952674a3bbcfdee8728fb55c6defd0'
ACCEPTED_PARENT = 'd53dd70d38b0762af130b1d19b795af259f505f5'
ACCEPTED_PARENT_TREE = '12691099f1a155a8bfa3ad4f6689146175b233b2'
COMPILER_COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
PARENT_BUILDER_SHA256 = 'c4918486016d25b16caa1013666a22979f8ebe86e41369cbf616a8a2b9512ddc'
PARENT_PROJECTION_VALIDATOR_SHA256 = '3b3ca7cb137d3b6cc239730afd960659c9c5e09492acdd4b8f76b59cb3ade079'
FROZEN_FULL_INPUTS = {
    'BUILD_SPEC.md': 'cacab08834aeb9badd578d90828be99cff33c7a617c609e75bb878eb5fa3b29c',
    'BUILD_MANIFEST.json': 'c99ec7acbfe996455525b31088a7d04addd20653787e12098e4e51a4a7ce296e',
    'PUBLIC_ROOTS.json': '2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41',
    'PAPER_CROSSWALK.json': '9e1252631f26fb81f4a5c60ac714e483c076be5c9858e25056e3835933ce6451',
    'PARENT_EXTENSION.json': '2b88b5497861679e6b1f686af6c8b5b7dbe5a5887841be43d862ba9836187ac3',
    'PROTECTED_STATE.json': 'c62aad1d5dba23e0413f084a4deb9ecdaeb655e803fe809cd603c8efc7bc1779',
}
VALIDATION_MODULE = 'Zeta23.OPICAFollowup.Validation'
VALIDATION_PATH = 'Zeta23/OPICAFollowup/Validation.lean'


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':')).encode('utf-8')


def object_sha256(value):
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def unique_json(payload):
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate JSON key: '+key)
            result[key] = value
        return result
    def bad_constant(value):
        raise ValueError('nonfinite JSON value: '+value)
    return json.loads(payload, object_pairs_hook=object_pairs,parse_constant=bad_constant)


def safe_source(repo, relative):
    require(isinstance(relative, str) and relative and '\\' not in relative and ':' not in relative
        and all(part not in {'', '.', '..'} for part in relative.split('/'))
        and not any(ord(char)<32 or ord(char)==127 for char in relative), 'unsafe source path')
    repo = Path(repo).absolute()
    path = repo/relative
    require(not any(p.is_symlink() for p in [path, *path.parents] if p.is_relative_to(repo)),
        'symlink in source path: '+relative)
    require(path.is_file() and path.resolve()==repo.resolve()/relative,
        'missing, escaped or aliased source: '+relative)
    return path


def full_contract(repo):
    """Read all frozen scope inputs; no mutable workflow table can redefine them."""
    documents = {}
    for name, digest in FROZEN_FULL_INPUTS.items():
        data = safe_source(repo, 'research/RHRC/integration/opica_followup/'+name).read_bytes()
        require(hashlib.sha256(data).hexdigest()==digest, 'frozen full scope changed: '+name)
        documents[name] = unique_json(data) if name.endswith('.json') else data.decode('utf-8')
    manifest = documents['BUILD_MANIFEST.json']
    roots = documents['PUBLIC_ROOTS.json']['roots']
    units = documents['PAPER_CROSSWALK.json']['scope_units']
    require(len(roots)==100 and len({r['id'] for r in roots})==100
        and len({r['full_name'] for r in roots})==100, 'exact original100 roots required')
    require(len(units)==28 and len({u['paper_id'] for u in units})==28,
        'exact original28 acceptance units required')
    require(len(manifest['modules'])==43, 'exact full module inventory required')
    modules = [r['module'] for r in manifest['modules'] if r['trust_zone']!='AUDIT_ONLY']
    require(len(modules)==41 and len(set(modules))==41, 'full mathematical module inventory differs')
    return {'manifest':manifest, 'roots':roots, 'units':units,
        'mathematical_modules':sorted(modules), 'export_modules':sorted([*modules, VALIDATION_MODULE]),
        'input_sha256':dict(FROZEN_FULL_INPUTS)}


def reviewed_full_contract(repo, contract):
    """Consume a separately sealed semantic review, never infer it from a receipt.

    The seal is deliberately absent in the partial checkout. Test-only seals do
    not establish mathematics. Names/source presence cannot establish adequacy.
    """
    require(isinstance(FULL_REVIEW_SHA256, str) and SHA256.fullmatch(FULL_REVIEW_SHA256),
        'independent full100 review seal is not established')
    register = unique_json(safe_source(repo,
        'research/RHRC/integration/opica_followup/SOURCE_REGISTER.json').read_bytes())
    review = register.get('full_receipt_review')
    require(isinstance(review, dict) and object_sha256(review)==FULL_REVIEW_SHA256,
        'full review differs from independent hardcoded seal')
    required = {'schema':FULL_REVIEW_SCHEMA,
        'status':'INDEPENDENT_EXPECTED_TYPES_AND_PHYSICAL_DOMAINS_REVIEWED',
        'scope':'FULL_100_ORIGINAL_ROOTS', 'primary_roots':100, 'acceptance_units':28,
        'frozen_input_sha256':contract['input_sha256'], 'RH':'OPEN', 'Step4':'OPEN',
        'independent_closing_inequalities':'OPEN'}
    for key, value in required.items():
        require(type(review.get(key)) is type(value) and review[key]==value,
            'full semantic review scope/status differs: '+key)
    if 'exact_source_extension_policy' in register:
        exact_policy = register['exact_source_extension_policy']
        require(isinstance(exact_policy,dict) and
            exact_policy.get('schema')=='OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V2' and
            review.get('exact_source_extension_policy_sha256')==object_sha256(exact_policy),
            'full semantic review omitted or changed the exact source policy')
    amendment = register.get('implementation_dependency_amendment')
    require(isinstance(amendment,dict) and isinstance(amendment.get('id'),str)
        and amendment.get('status')=='IMPLEMENTATION_ONLY_NO_MATHEMATICAL_SCOPE_CHANGE'
        and review.get('implementation_dependency_amendment_sha256')==object_sha256(amendment),
        'independently sealed implementation-origin amendment absent or changed')
    registry_review = register.get('accepted_registry_extension')
    require(isinstance(registry_review,dict)
        and review.get('accepted_registry_extension_sha256')==object_sha256(registry_review),
        'independently sealed full registered-object review absent or changed')
    workflow = unique_json(safe_source(repo,
        'research/RHRC/integration/opica_followup/WORKFLOW_CONTRACT.json').read_bytes())
    type_table = workflow.get('implemented_root_type_sha256')
    require(isinstance(type_table,dict) and review.get('registered_type_table_sha256')==object_sha256(type_table),
        'registered full type table differs from independent semantic seal')
    planned_paths = {r['path'] for r in contract['manifest']['modules']
        if r['module'] in contract['export_modules']}
    hashes = review.get('source_sha256')
    require(isinstance(hashes,dict) and set(hashes)==planned_paths,
        'complete reviewed mathematical/consumer source inventory required')
    for path, expected in hashes.items():
        require(isinstance(expected,str) and SHA256.fullmatch(expected)
            and hashlib.sha256(safe_source(repo,path).read_bytes()).hexdigest()==expected,
            'reviewed source bytes changed: '+path)
    rows = review.get('roots')
    require(isinstance(rows,list) and len(rows)==100 and all(isinstance(r,dict) for r in rows)
        and [r.get('full_name') for r in rows]==[r['full_name'] for r in contract['roots']],
        'full reviewed root identity/order differs')
    consumers = review.get('consumers')
    require(isinstance(consumers,list) and all(isinstance(c,dict) for c in consumers),
        'reviewed independent consumer inventory required')
    by_consumer = {}
    for consumer in consumers:
        name = consumer.get('name')
        require(isinstance(name,str) and re.fullmatch(r'Zeta23\.OPICAFollowup\.Validation\.[A-Za-z_][A-Za-z0-9_]*',name)
            and name not in by_consumer, 'invalid or duplicate independent consumer')
        require(consumer.get('module')==VALIDATION_MODULE and consumer.get('path')==VALIDATION_PATH
            and consumer.get('review_status')=='INDEPENDENT_EXPLICIT_TYPE_AND_DOMAIN_REVIEWED',
            'consumer source or independent review differs: '+name)
        require(isinstance(consumer.get('type_sha256'),str) and SHA256.fullmatch(consumer['type_sha256']),
            'reviewed consumer full type digest absent: '+name)
        by_consumer[name] = consumer
    expected_roots, used_consumers = [], set()
    for frozen, row in zip(contract['roots'],rows):
        name = frozen['full_name']
        require(row.get('frozen_contract_sha256')==object_sha256(frozen),
            'review omitted or changed a frozen mathematical clause: '+name)
        require(isinstance(row.get('type_sha256'),str) and SHA256.fullmatch(row['type_sha256']),
            'reviewed full root type absent: '+name)
        expected = VALIDATION_MODULE+'.'+frozen['expected_type_consumer']
        require(row.get('expected_type_consumer')==expected and expected in by_consumer,
            'independently stated expected consumer absent: '+name)
        physical = row.get('physical_or_domain_consumers')
        require(isinstance(physical,list) and bool(physical)
            and all(isinstance(c,str) and c in by_consumer for c in physical)
            and len(physical)==len(set(physical)), 'actual physical/domain consumers absent: '+name)
        require(row.get('review_status')=='FULL_FROZEN_CLAUSES_AND_ACTUAL_DOMAINS_REVIEWED'
            and isinstance(row.get('domain_review'),str) and bool(row['domain_review'].strip()),
            'actual construction/domain review absent: '+name)
        used_consumers.update([expected,*physical])
        expected_roots.append({**frozen,'expected_type_sha256':row['type_sha256']})
    require(type_table=={row['full_name']:row['type_sha256'] for row in rows},
        'registered type table must cover exactly all100 reviewed types')
    definition_specs = [(module['module'],'Zeta23.OPICAFollowup.'+name)
        for module in contract['manifest']['modules'] if module['module'] in contract['mathematical_modules']
        for name in module.get('required_definitions',[])]
    definitions = review.get('required_definitions')
    require(isinstance(definitions,list) and all(isinstance(row,dict) for row in definitions)
        and [(row.get('original_module'),row.get('full_name')) for row in definitions]==definition_specs,
        'exact canonical required-definition review inventory required')
    for row in definitions:
        require(row.get('actual_module') in contract['mathematical_modules']
            and row.get('kind') in {'DEFINITION','INDUCTIVE','OPAQUE'}
            and isinstance(row.get('type_sha256'),str) and SHA256.fullmatch(row['type_sha256'])
            and row.get('review_status')=='CANONICAL_DEFINITION_SEMANTICS_AND_ORIGIN_REVIEWED'
            and isinstance(row.get('reason'),str) and bool(row['reason'].strip()),
            'canonical declaration kind/type/semantic-origin review absent: '+row['full_name'])
        relocated = row['original_module']!=row['actual_module']
        require(row.get('relocation_amendment_id')==(amendment['id'] if relocated else None),
            'module-origin relocation lacks separately sealed amendment authority: '+row['full_name'])
    require(set(by_consumer)==used_consumers, 'unused or omitted consumer review rows')
    unit_rows = review.get('units')
    require(isinstance(unit_rows,list) and len(unit_rows)==28 and all(isinstance(u,dict) for u in unit_rows)
        and [u.get('paper_id') for u in unit_rows]==[u['paper_id'] for u in contract['units']],
        'full28 reviewed acceptance-unit inventory differs')
    by_root = {r['full_name']:r for r in rows}
    for frozen, row in zip(contract['units'],unit_rows):
        require(row.get('frozen_contract_sha256')==object_sha256(frozen)
            and row.get('review_status')=='ALL_CLAUSES_AND_PHYSICAL_DOMAINS_REVIEWED',
            'acceptance unit lost a frozen clause: '+frozen['paper_id'])
        required_names = set()
        for root_name in frozen['required_roots']:
            entry = by_root[root_name]
            required_names.update([entry['expected_type_consumer'],*entry['physical_or_domain_consumers']])
        listed = row.get('consumers')
        require(isinstance(listed,list) and all(isinstance(n,str) and n in by_consumer for n in listed)
            and len(listed)==len(set(listed)) and required_names<=set(listed),
            'acceptance unit consumer coverage incomplete: '+frozen['paper_id'])
    consumer_queries = [{'id':'OPICA_FULL_CONSUMER_'+hashlib.sha256(n.encode()).hexdigest(),
        'full_name':n,'module':VALIDATION_MODULE,'kind':'THEOREM',
        'expected_type_sha256':by_consumer[n]['type_sha256']} for n in sorted(by_consumer)]
    return {'review':review, 'roots':expected_roots, 'consumer_queries':consumer_queries,
        'required_definitions':definitions,
        'queries':[*expected_roots,*consumer_queries], 'review_sha256':FULL_REVIEW_SHA256}


def render_full_exporter(repo, contract, reviewed):
    """Instantiate only sealed exporter data arrays, never user-provided Lean code."""
    template = safe_source(repo,'Zeta23/RHRC/OpicaFollowupBindings.lean').read_bytes()
    require(hashlib.sha256(template).hexdigest()==FULL_TEMPLATE_SHA256,
        'full exporter template changed without independent seal review')
    text = template.decode('utf-8')
    queries = []
    for query in reviewed['queries']:
        values = [query['id'],query['module'],query['full_name'],query['kind']]
        require(all(isinstance(v,str) and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',v) for v in values),
            'invalid code-free full exporter query')
        queries.append('    ({ sourceId := '+json.dumps(values[0])+', moduleName := '+json.dumps(values[1])+
            ', shortName := '+json.dumps(values[2])+', sourceKind := '+json.dumps(values[3])+' } : SourceCandidateQuery)')
    query_block = '  let queries : Array SourceCandidateQuery := #[\n'+',\n'.join(queries)+']\n  resolveSourceCandidates queries'
    text, count = re.subn(r'  let queries : Array SourceCandidateQuery := #\[.*?\n  resolveSourceCandidates queries',
        lambda _:query_block,text,flags=re.S)
    require(count==1, 'sealed exporter query boundary differs')
    module_block = '  let mathematicalModules : Array String := #[\n'+',\n'.join(
        '    '+json.dumps(n) for n in contract['export_modules'])+']\n  let mut names'
    text, count = re.subn(r'  let mathematicalModules : Array String := #\[.*?\n  let mut names',
        lambda _:module_block,text,flags=re.S)
    require(count==1, 'sealed exporter module boundary differs')
    imports = '\n'.join('import '+n for n in contract['export_modules'])+'\n'
    return (imports+text).encode('utf-8')


def full_source_manifest(repo):
    """Verify all clean tracked working bytes against the actual immutable tree."""
    repo = Path(repo)
    def run(*args):
        return subprocess.check_output(['git','-C',str(repo),*args],env=full_git_environment())
    require(not run('status','--porcelain'), 'full compiler evidence requires a clean committed checkout')
    records = []
    for entry in run('ls-tree','-r','-z','HEAD').split(b'\0'):
        if not entry:
            continue
        metadata,name = entry.split(b'\t',1)
        mode,kind,oid = metadata.decode('ascii').split()
        name = name.decode('utf-8')
        require(kind=='blob' and mode in {'100644','100755'}, 'unsupported tracked source mode')
        payload = safe_source(repo,name).read_bytes()
        require(hashlib.sha1(b'blob '+str(len(payload)).encode()+b'\0'+payload).hexdigest()==oid,
            'working bytes differ from immutable tree: '+name)
        records.append({'path':name,'mode':mode,'git_blob':oid,'bytes':len(payload),
            'sha256':hashlib.sha256(payload).hexdigest()})
    return sorted(records,key=lambda r:r['path'])


def full_git_environment():
    environment = os.environ.copy()
    environment['GIT_NO_LAZY_FETCH'] = '1'
    return environment


def load_parent_builder(repo):
    """Use a unique module identity: parent and child have identical filenames."""
    path = safe_source(repo, 'research/RHRC/integration/opica/build_receipt.py')
    require(hashlib.sha256(path.read_bytes()).hexdigest()==PARENT_BUILDER_SHA256,
        'immutable parent compiler reader changed')
    spec = importlib.util.spec_from_file_location('opica_parent_receipt_for_full_child', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def full_checkout_identity(repo, requested_head, requested_base):
    def git_at(*args):
        return subprocess.check_output(['git','-C',str(repo),*args],env=full_git_environment()).decode().strip()
    require(isinstance(requested_head,str) and SHA40.fullmatch(requested_head), 'exact requested head required')
    require(requested_base==ACCEPTED_PARENT, 'unreviewed parent base')
    checked = git_at('rev-parse','HEAD')
    tree = git_at('rev-parse','HEAD^{tree}')
    parents = git_at('show','-s','--format=%P','HEAD').split()
    require(checked==requested_head or (len(parents)==2 and requested_head in parents
        and requested_base in parents), 'requested head is not this head or its exact synthetic merge')
    require(git_at('rev-parse',requested_base+'^{tree}')==ACCEPTED_PARENT_TREE,
        'accepted parent tree differs')
    require(git_at('merge-base',checked,requested_base)==requested_base,
        'checked tree does not descend from accepted parent')
    return {'requested_head':requested_head,'requested_base':requested_base,
        'checked_commit':checked,'checked_tree':tree,
        'checkout_kind':'PR_HEAD' if checked==requested_head else 'SYNTHETIC_MERGE'}


def verify_mathlib_checkout(repo, contract):
    package = Path(repo)/'.lake/packages/mathlib'
    require((package/'.git').exists(), 'actual mathlib Git checkout required for full evidence')
    top = subprocess.check_output(['git','-C',str(package),'rev-parse','--show-toplevel'],env=full_git_environment()).decode().strip()
    require(Path(top).resolve()==package.resolve(), 'mathlib pin resolved to an enclosing checkout')
    actual = subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],env=full_git_environment()).decode().strip()
    expected = contract['manifest']['mathlib_commit']
    require(actual==expected, 'actual mathlib checkout differs from frozen pin')
    require(not subprocess.check_output(['git','-C',str(package),'status','--porcelain'],env=full_git_environment()),
        'mathlib checkout has uncommitted changes')
    return actual


def full_import_graph(repo, contract):
    """Check the planned facade closure, independently of importing every query."""
    modules = {row['module']:row for row in contract['manifest']['modules']}
    edges = {}
    for module in contract['mathematical_modules']:
        text = safe_source(repo,modules[module]['path']).read_text(encoding='utf-8')
        imports = lean_header_imports(text)
        require(not any(name in {'Zeta23.OPICAFollowup.Validation','Zeta23.RHRC.OpicaFollowupBindings'}
            for name in imports), 'audit-only import in mathematical module: '+module)
        edges[module] = sorted(set(imports)&set(contract['mathematical_modules']))
    seen, pending = set(), ['Zeta23.OPICAFollowup']
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(edges[name])
    require(seen==set(contract['mathematical_modules']), 'full facade does not reach every mathematical module')
    return edges


def lean_header_imports(text):
    """Conservative header parser: comments never manufacture facade edges."""
    clean, position, depth = [], 0, 0
    while position<len(text):
        pair = text[position:position+2]
        if not depth and text[position]=='"':
            clean.append('"')
            position += 1
            while position<len(text):
                char = text[position]
                clean.append(char)
                position += 1
                if char=='\\' and position<len(text):
                    clean.append(text[position])
                    position += 1
                elif char=='"':
                    break
        elif pair=='/-':
            depth += 1
            clean.append(' ')
            position += 2
        elif depth:
            if pair=='-/':
                depth -= 1
                position += 2
            else:
                clean.append('\n' if text[position]=='\n' else ' ')
                position += 1
        elif pair=='--':
            end = text.find('\n',position)
            position = len(text) if end<0 else end
        else:
            clean.append(text[position])
            position += 1
    require(depth==0, 'unterminated Lean comment')
    imports = []
    for line in ''.join(clean).splitlines():
        line = line.strip()
        if not line or line=='prelude':
            continue
        if not line.startswith('import '):
            break
        match = re.fullmatch(r'import\s+([A-Za-z_][A-Za-z0-9_.]*)',line)
        require(match is not None, 'full audit requires unambiguous one-module import headers')
        imports.append(match[1])
    return imports


def pinned_package_cache(repo):
    """Share dependency packages only; project build objects are never shared."""
    manifest = unique_json(safe_source(repo,'lake-manifest.json').read_bytes())
    require(manifest.get('packagesDir')=='.lake/packages', 'unreviewed dependency cache location')
    packages = manifest.get('packages')
    require(isinstance(packages,list) and bool(packages), 'pinned dependency package inventory required')
    records, names = [], set()
    for row in packages:
        name = row.get('name')
        require(isinstance(name,str) and re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*',name)
            and name not in names and row.get('type')=='git' and row.get('subDir') is None
            and isinstance(row.get('rev'),str) and SHA40.fullmatch(row['rev']),
            'unsupported or duplicate dependency package pin')
        names.add(name)
        package = Path(repo)/'.lake/packages'/name
        require((package/'.git').exists(), 'pinned package lacks its own Git checkout: '+name)
        def git_package(*args):
            return subprocess.check_output(['git','-C',str(package),*args],env=full_git_environment()).decode().strip()
        require(Path(git_package('rev-parse','--show-toplevel')).resolve()==package.resolve(),
            'dependency Git identity escaped package: '+name)
        require(git_package('rev-parse','HEAD')==row['rev'] and not git_package('status','--porcelain'),
            'dependency package pin or clean source differs: '+name)
        records.append({'name':name,'commit':row['rev'],'tree':git_package('rev-parse','HEAD^{tree}')})
    return sorted(records,key=lambda row:row['name'])


def cold_compiler_checkout(repo, workspace_parent, identity, sources):
    """Create an independent project build without deleting shared caches.

    Only manifest-pinned dependency packages may share cached objects. Symlink
    creation failures (including Windows privilege failures) fail closed.
    """
    packages = pinned_package_cache(repo)
    workspace = Path(tempfile.mkdtemp(prefix='opica-full-compiler-',dir=workspace_parent))/'repo'
    subprocess.run(['git','-c','core.autocrlf=false','clone','--shared','--no-checkout',
        '--no-hardlinks','--',str(Path(repo).resolve()),str(workspace)],check=True,
        stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=full_git_environment())
    subprocess.run(['git','-C',str(workspace),'-c','core.autocrlf=false','checkout','--detach',
        identity['checked_commit']],check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=full_git_environment())
    clone_identity = full_checkout_identity(workspace,identity['requested_head'],identity['requested_base'])
    require(clone_identity==identity and full_source_manifest(workspace)==sources,
        'cold compiler clone differs from exact checked source/head/tree')
    require(not (workspace/'.lake/build').exists(), 'cold compiler project cache is not empty')
    (workspace/'.lake').mkdir(exist_ok=True)
    (workspace/'.lake/packages').symlink_to((Path(repo)/'.lake/packages').resolve(),target_is_directory=True)
    require((workspace/'.lake/packages').resolve()==(Path(repo)/'.lake/packages').resolve(),
        'cold compiler shared an unexpected dependency cache')
    facts = {'mode':'COLD_LOCAL_GIT_CLONE_SHARED_PINNED_PACKAGES_V1',
        'checked_commit':identity['checked_commit'],'checked_tree':identity['checked_tree'],
        'source_manifest_sha256':object_sha256(sources),'cold_project_build_initially_absent':True,
        'shared_cache_scope':'MANIFEST_PINNED_DEPENDENCY_PACKAGES_ONLY',
        'inherited_lean_path_removed':True,'artifact_cache_disabled':True,'package_pins':packages}
    return workspace,facts


def expected_isolation(identity, sources, packages):
    return {'mode':'COLD_LOCAL_GIT_CLONE_SHARED_PINNED_PACKAGES_V1',
        'checked_commit':identity['checked_commit'],'checked_tree':identity['checked_tree'],
        'source_manifest_sha256':object_sha256(sources),'cold_project_build_initially_absent':True,
        'shared_cache_scope':'MANIFEST_PINNED_DEPENDENCY_PACKAGES_ONLY',
        'inherited_lean_path_removed':True,'artifact_cache_disabled':True,'package_pins':packages}


def full_registered_dependencies(repo, contract, parsed):
    """Bind registered IDs to actual compiler uses, including private helpers."""
    parent = load_parent_builder(repo)
    bindings = unique_json(safe_source(repo,'research/RHRC/REGISTERED_THEOREM_BINDINGS.json').read_bytes())['bindings']
    require(len(bindings)==294 and len({r['id'] for r in bindings})==294,
        'exact parent plus100 registered bindings required')
    by_id = {r['id']:r for r in bindings}
    for root in contract['roots']:
        require(root['id'] in by_id and by_id[root['id']]['theorem']==root['full_name'],
            'registered child identity differs from frozen root')
    return parent.mapped_registered_dependencies([r['full_name'] for r in contract['roots']],
        bindings,parsed['dependencies'])


def validate_consumer_provenance(parsed, reviewed):
    """Actual compiler use is necessary, but does not replace semantic review."""
    adjacency = {}
    for row in parsed['dependencies']:
        adjacency.setdefault(row['source'],set()).update(row['targets'])
    def reaches(consumer,root):
        seen, pending = set(), [consumer]
        while pending:
            name = pending.pop()
            if name==root:
                return True
            if name not in seen:
                seen.add(name)
                pending.extend(adjacency.get(name,()))
        return False
    for row in reviewed['review']['roots']:
        for name in [row['expected_type_consumer'],*row['physical_or_domain_consumers']]:
            require(reaches(name,row['full_name']),
                'independent consumer has no compiler-use path to assigned root: '+name)
    return True


def validate_required_definitions(parsed, reviewed):
    """Canonical interfaces cannot disappear behind100 proved primary names."""
    declarations = {row['name']:row for row in parsed['declarations']}
    for row in reviewed['required_definitions']:
        actual = declarations.get(row['full_name'])
        require(actual is not None and actual['module']==row['actual_module']
            and actual['kind']==row['kind'] and actual['type_sha256']==row['type_sha256'],
            'canonical public definition missing or its reviewed origin/kind/type differs: '+row['full_name'])
    return reviewed['required_definitions']


def full_registry_projection(repo, contract, mapped):
    """Preserve every parent object and reject metadata-only child promotion."""
    path = safe_source(repo,'research/RHRC/integration/opica/validate_contract.py')
    require(hashlib.sha256(path.read_bytes()).hexdigest()==PARENT_PROJECTION_VALIDATOR_SHA256,
        'parent projection implementation changed without independent review')
    spec = importlib.util.spec_from_file_location('opica_parent_contract_for_full_child',path)
    parent = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = parent
    spec.loader.exec_module(parent)
    # The parent wrapper verifies immutable baseline bytes and exact original
    # projection restrictions. It never substitutes for the compiler replay.
    context = parent._source_bound_followup_context(Path(repo))
    policy_binding = parent.exact_extension_binding(Path(repo))
    require(context is not None, 'source-bound full parent projection required')
    claims = unique_json(safe_source(repo,'research/RHRC/CLAIM_REGISTRY.json').read_bytes())['claims']
    require(len(claims)==298 and len({r['id'] for r in claims})==298,
        'exact parent plus100 registered claims required')
    by_id = {r['id']:r for r in claims}
    for root in contract['roots']:
        require(by_id[root['id']].get('dependencies')==mapped[root['full_name']],
            'registered claim edges differ from actual complete compiler uses: '+root['id'])
    return {'status':'EXACT_SOURCE_BOUND_PARENT_PROJECTION_AND_COMPILER_DEPENDENCIES_VERIFIED',
        'claim_count':298,'binding_count':294,'mapped_registered_dependencies_sha256':object_sha256(mapped),
        'exact_source_extension_policy':policy_binding}


def full_commands(contract):
    return [(['lake','env','lean','--version'],'lean-version.log'),
        (['lake','build',*contract['manifest']['required_final_build_targets'],
            'Zeta23.RHRC.OpicaTypeExprExport'],'build.log'),
        (['lake','env','lean','-R','@EXTERNAL_FULL_ROOT@','@EXTERNAL_FULL_EXPORTER@','-o','@EXTERNAL_FULL_OLEAN@'],'bindings.log')]



def instantiate_full_command(argv, output, lake):
    """Keep an external exporter inside its explicit Lean module root.

    The source checkout remains the subprocess cwd and import environment. The
    external root governs only the generated exporter's module/output identity.
    No source, parser, axiom, type, dependency or cold-isolation gate is changed.
    """
    require(isinstance(argv,list) and bool(argv) and argv[0]=='lake',
        'full compiler command must start with lake')
    output = Path(output).absolute()
    replacements = {'@EXTERNAL_FULL_ROOT@':str(output),
        '@EXTERNAL_FULL_EXPORTER@':str(output/'FullOpicaFollowupExport.lean'),
        '@EXTERNAL_FULL_OLEAN@':str(output/'FullOpicaFollowupExport.olean')}
    require(all(isinstance(token,str) and (not token.startswith('@') or token in replacements)
        for token in argv), 'unknown full compiler placeholder')
    return [str(lake) if i==0 else replacements.get(token,token)
        for i,token in enumerate(argv)]


def external_artifact(folder, name):
    require(isinstance(name,str) and re.fullmatch(r'[A-Za-z][A-Za-z0-9_.-]*',name),
        'invalid external artifact name')
    folder = Path(folder).absolute()
    path = folder/name
    require(path.is_file() and not path.is_symlink() and path.resolve()==folder.resolve()/name,
        'missing, symlinked or escaped compiler artifact: '+name)
    return path


def validate_full_receipt_structure(receipt, repo, artifacts):
    """Structural/source validation only; acceptance additionally requires fresh replay.

    A matching JSON object and log can be fabricated together. This function is
    deliberately never a release authority without verify_full_receipt_replay.
    """
    contract = full_contract(repo)
    reviewed = reviewed_full_contract(repo,contract)
    require(receipt.get('schema')==FULL_RECEIPT_SCHEMA
        and receipt.get('status')=='COMPILER_VERIFIED_FULL_100', 'full100 compiler schema/status required')
    flags = {'original_primary_count':100,'acceptance_units':28,'working_tree_dirty':False,
        'release_ready':False,'full_release_accepted':False,'RH':'OPEN','Step4':'OPEN',
        'independent_closing_inequalities':'OPEN','independent_human_review':'NOT_ESTABLISHED'}
    for key,value in flags.items():
        require(type(receipt.get(key)) is type(value) and receipt[key]==value,
            'full compiler scope or claim firewall differs: '+key)
    identity = full_checkout_identity(repo,receipt.get('requested_head'),receipt.get('requested_base'))
    require(all(receipt.get(k)==v for k,v in identity.items()), 'stale compiler head/tree identity')
    sources = full_source_manifest(repo)
    require(receipt.get('source_manifest')==sources
        and receipt.get('source_manifest_sha256')==object_sha256(sources), 'source census differs from clean tree')
    require(canonical_bytes(receipt.get('compiler_isolation'))==canonical_bytes(
        expected_isolation(identity,sources,pinned_package_cache(repo))),
        'full compiler must use a cold isolated source-built project checkout')
    require(receipt.get('frozen_input_sha256')==contract['input_sha256']
        and receipt.get('full_review_sha256')==reviewed['review_sha256'], 'full scope/review binding differs')
    require(receipt.get('original_primary_roots')==[r['full_name'] for r in contract['roots']]
        and receipt.get('consumer_queries')==reviewed['consumer_queries']
        and receipt.get('query_inventory_sha256')==object_sha256(reviewed['queries'])
        and receipt.get('export_modules')==contract['export_modules'], 'root/consumer/module inventory differs')
    driver = render_full_exporter(repo,contract,reviewed)
    require(receipt.get('exporter_template_sha256')==FULL_TEMPLATE_SHA256
        and receipt.get('exporter_driver_sha256')==hashlib.sha256(driver).hexdigest()
        and external_artifact(artifacts,'FullOpicaFollowupExport.lean').read_bytes()==driver,
        'full deterministic compiler driver differs')
    require(receipt.get('mathlib_commit')==verify_mathlib_checkout(repo,contract), 'mathlib receipt pin differs')
    require(receipt.get('import_graph')==full_import_graph(repo,contract), 'facade import closure differs')
    commands = receipt.get('commands')
    expected_commands = full_commands(contract)
    require(isinstance(commands,list) and len(commands)==len(expected_commands), 'full command inventory differs')
    for row,(argv,log) in zip(commands,expected_commands):
        require(row.get('argv')==argv and row.get('log')==log
            and type(row.get('exit_code')) is int and row['exit_code']==0, 'full command failed or substituted: '+log)
        require(type(row.get('seconds')) in {int,float} and math.isfinite(row['seconds'])
            and row['seconds']>=0, 'invalid command duration')
        payload = external_artifact(artifacts,log).read_bytes()
        require(row.get('log_sha256')==hashlib.sha256(payload).hexdigest(), 'compiler log digest differs: '+log)
    version = external_artifact(artifacts,'lean-version.log').read_text(encoding='utf-8')
    require(receipt.get('lean')==version.strip() and 'version 4.33.0-rc2,' in version
        and COMPILER_COMMIT in version, 'actual pinned compiler version/commit required')
    require(receipt.get('compiled_export_sha256')==hashlib.sha256(
        external_artifact(artifacts,'FullOpicaFollowupExport.olean').read_bytes()).hexdigest(),
        'compiled exporter object digest differs')
    parsed = parse_compiler_output(external_artifact(artifacts,'bindings.log').read_text(encoding='utf-8'),
        reviewed['queries'],mathematical_modules=contract['export_modules'])
    validate_consumer_provenance(parsed,reviewed)
    require(receipt.get('required_definition_inventory')==validate_required_definitions(parsed,reviewed),
        'canonical required-definition receipt inventory differs')
    require(all(receipt.get(key)==value for key,value in parsed.items()), 'compiler wire records differ from receipt')
    mapped = full_registered_dependencies(repo,contract,parsed)
    require(receipt.get('mapped_registered_dependencies')==mapped,
        'registered dependency provenance differs from complete compiler traversal')
    require(receipt.get('registry_projection')==full_registry_projection(repo,contract,mapped),
        'full registered projection differs')
    return {'status':'FULL_COMPILER_STRUCTURE_AND_SOURCE_VERIFIED_REPLAY_STILL_REQUIRED',
        'source_manifest_sha256':object_sha256(sources),'full_review_sha256':reviewed['review_sha256']}


def produce_full_receipt(repo, output, requested_head, requested_base, lake='lake'):
    """Future full producer. Absent reviewed100 types fail before any compiler call."""
    repo, output = Path(repo).resolve(), Path(output).absolute()
    require(not output.resolve().is_relative_to(repo), 'full compiler artifacts must be outside checkout')
    contract = full_contract(repo)
    reviewed = reviewed_full_contract(repo,contract)
    identity = full_checkout_identity(repo,requested_head,requested_base)
    before = full_source_manifest(repo)
    mathlib = verify_mathlib_checkout(repo,contract)
    graph = full_import_graph(repo,contract)
    driver = render_full_exporter(repo,contract,reviewed)
    output.mkdir(parents=True,exist_ok=True)
    require(not any(output.iterdir()), 'full compiler output directory must be fresh and empty')
    workspace,isolation = cold_compiler_checkout(repo,output.parent,identity,before)
    (output/'FullOpicaFollowupExport.lean').write_bytes(driver)
    environment = os.environ.copy()
    environment['LEAN_NUM_THREADS'] = '1'
    for key in ('LEAN_PATH','LEAN_SRC_PATH'):
        environment.pop(key,None)
    environment['LAKE_ARTIFACT_CACHE'] = 'false'
    commands = []
    for argv,log in full_commands(contract):
        actual = instantiate_full_command(argv,output,lake)
        started = time.monotonic()
        process = subprocess.run(actual,cwd=workspace,env=environment,stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,timeout=7200)
        (output/log).write_bytes(process.stdout)
        commands.append({'argv':argv,'log':log,'exit_code':process.returncode,
            'seconds':time.monotonic()-started,'log_sha256':hashlib.sha256(process.stdout).hexdigest()})
        require(process.returncode==0, 'full compiler command failed: '+log)
    require(before==full_source_manifest(repo), 'source bytes changed during full compiler run')
    require(before==full_source_manifest(workspace), 'cold compiler clone source changed during build')
    require(pinned_package_cache(repo)==isolation['package_pins'], 'dependency sources changed during compiler run')
    require(identity==full_checkout_identity(repo,requested_head,requested_base), 'head/tree changed during compiler run')
    parsed = parse_compiler_output((output/'bindings.log').read_text(encoding='utf-8'),
        reviewed['queries'],mathematical_modules=contract['export_modules'])
    validate_consumer_provenance(parsed,reviewed)
    definition_inventory = validate_required_definitions(parsed,reviewed)
    mapped = full_registered_dependencies(repo,contract,parsed)
    result = {'schema':FULL_RECEIPT_SCHEMA,'status':'COMPILER_VERIFIED_FULL_100',**identity,
        'original_primary_count':100,'acceptance_units':28,'working_tree_dirty':False,
        'release_ready':False,'full_release_accepted':False,'RH':'OPEN','Step4':'OPEN',
        'independent_closing_inequalities':'OPEN','independent_human_review':'NOT_ESTABLISHED',
        'source_manifest':before,'source_manifest_sha256':object_sha256(before),
        'compiler_isolation':isolation,
        'frozen_input_sha256':contract['input_sha256'],'full_review_sha256':reviewed['review_sha256'],
        'original_primary_roots':[r['full_name'] for r in contract['roots']],
        'consumer_queries':reviewed['consumer_queries'],'query_inventory_sha256':object_sha256(reviewed['queries']),
        'required_definition_inventory':definition_inventory,
        'export_modules':contract['export_modules'],'exporter_template_sha256':FULL_TEMPLATE_SHA256,
        'exporter_driver_sha256':hashlib.sha256(driver).hexdigest(),'import_graph':graph,
        'mathlib_commit':mathlib,'lean':(output/'lean-version.log').read_text(encoding='utf-8').strip(),
        'commands':commands,'compiled_export_sha256':hashlib.sha256(
            (output/'FullOpicaFollowupExport.olean').read_bytes()).hexdigest(),
        'mapped_registered_dependencies':mapped,'registry_projection':full_registry_projection(repo,contract,mapped),**parsed}
    validate_full_receipt_structure(result,repo,output)
    (output/'compiler-receipt.json').write_bytes(json.dumps(result,indent=2).encode('utf-8')+b'\n')
    return result


def verify_full_receipt_replay(receipt, repo, artifacts, replay_output, lake='lake'):
    """Only this function links a supplied full receipt to newly executed Lean."""
    validate_full_receipt_structure(receipt,repo,artifacts)
    fresh = produce_full_receipt(repo,replay_output,receipt['requested_head'],receipt['requested_base'],lake)
    # Build/version output and elapsed times may vary with cache state. All
    # mathematical exports, source identities and query authority must agree.
    keys = ('declarations','constructors','generated_equations','dependency_declarations','dependencies',
        'source_manifest','compiler_isolation','checked_commit','checked_tree','requested_head','requested_base','checkout_kind',
        'full_review_sha256','query_inventory_sha256','consumer_queries','export_modules','original_primary_roots',
        'exporter_template_sha256','exporter_driver_sha256','mathlib_commit','mapped_registered_dependencies',
        'registry_projection','import_graph')
    keys = (*keys,'required_definition_inventory')
    require(all(receipt.get(k)==fresh.get(k) for k in keys), 'fresh full compiler replay differs from supplied receipt')
    return {'status':'FRESH_COMPILER_REPLAY_VERIFIED_FULL_100','original_primary_count':100,
        'acceptance_units':28,'receipt_sha256':object_sha256(receipt),'fresh_receipt_sha256':object_sha256(fresh),
        'checked_commit':fresh['checked_commit'],'checked_tree':fresh['checked_tree'],
        'release_ready':False,'RH':'OPEN','Step4':'OPEN'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--requested-head', required=True)
    parser.add_argument('--requested-base', required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--preparation-only', action='store_true')
    args = parser.parse_args()
    if not args.preparation_only:
        report = produce_full_receipt(REPO,args.output_dir,args.requested_head,args.requested_base,args.lake)
        print(json.dumps({'status':report['status'],'primary_roots':100,'acceptance_units':28,
            'release_ready':False,'RH':'OPEN','Step4':'OPEN'}))
        return 0
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
    require(len(roots) == 41 and len({r['id'] for r in roots}) == 41,
            'exact forty-one-root implemented subset required')
    before = source_manifest()
    records = []
    environment = os.environ.copy()
    environment['LEAN_NUM_THREADS'] = '2'
    for label, command in [
        ('version', [args.lake, 'env', 'lean', '--version']),
        # Each project import of the exporter needs its own built object.
        ('build', [args.lake, 'build',
                   'Zeta23.OPICAFollowup.Validation',
                   'Zeta23.RHRC.OpicaTypeExprExport',
                   'Zeta23.RHRC.SourceCandidateResolution']),
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
