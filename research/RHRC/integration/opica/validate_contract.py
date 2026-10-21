"""Fail-closed OPICA source contract checks. Static checks are not Lean proofs."""
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
sys.path.insert(0, str(REPO / 'research/RHRC/tools'))
from lean_imports import import_modules, strip_lean_comments

OPICA_CLASS_RULES = [
    {'id':'opica_validation_audit','pattern':r'^Zeta23/OPICA/Validation\.lean$',
        'file_class':'LEAN_SOURCE','trust_zone':'AUDIT_ONLY'},
    {'id':'opica_native_adapters','pattern':r'^Zeta23/OPICA/(?:NativeJetAdapter|NativeArithmeticAdapter)\.lean$',
        'file_class':'LEAN_SOURCE','trust_zone':'AUXILIARY_FORMALIZATION'},
    {'id':'opica_math','pattern':r'^Zeta23/OPICA(?:/.*)?\.lean$',
        'file_class':'LEAN_SOURCE','trust_zone':'AUXILIARY_FORMALIZATION'},
]

# The frozen source-candidate producer supports only CCM/ExceptionalZero core
# modules. These two new files retain their exact source-bound native semantic
# roles and full OPICA proof audit, while their file classifications remain
# outside that legacy candidate population. No historical role is changed.
OPICA_CLASSIFICATION_OVERRIDES = [
    {'path':'Zeta23/OPICA/NativeJetAdapter.lean',
        'specified_trust_zone':'RH_FORMAL_CORE',
        'implementation_trust_zone':'AUXILIARY_FORMALIZATION'},
    {'path':'Zeta23/OPICA/NativeArithmeticAdapter.lean',
        'specified_trust_zone':'RH_FORMAL_CORE',
        'implementation_trust_zone':'AUXILIARY_FORMALIZATION'},
]

# Original user-supplied input identities, independent of the editable source
# register. Updating a descriptor alongside a changed paper cannot re-freeze it.
FROZEN_PAPER_SHA256 = {
    'paper/OPICA_Paper_Construction_v1_0_2026-10-21.md':
        '6c6d43857636d635c6da018b38046b19cdff4bee780840ac67ae81d32bec1777',
    'paper/OPICA_Lean_Implementation_Contract_2026-10-21.md':
        'ea8c59913b2733b4758b2d7cbdbc698d88dd5570d3d24f057a117ae12398a21a',
    'paper/OPICA_Theorem_and_Audit_Ledger_2026-10-21.json':
        'ff8a163e47208996b0a4ef70197414461f956aee45c470c42b56b9386178c08f',
}
FROZEN_SPECIFICATION_SHA256 = {
    'BUILD_SPEC.md':'97fbb13f569257a25843d8bce971be0586b4a155fad468e6573d2a257a4aeb44',
    'BUILD_MANIFEST.json':'7314261622be27a1fd678e1cf37bdc14a224717e73d5929b666d067b6bdab4dc',
    'PUBLIC_ROOTS.json':'fc14faa899e504089546d0235676c3539d81197d0ff235437f434cf1e336582d',
    'PAPER_CROSSWALK.json':'82bcbfaeb54e84b58298a0309bac97eb4d4d3f76e163bf35d9442ee85ded8218',
    'PROTECTED_STATE.json':'0f6a28e2f9ebd14b95f0201e22918d29af6c81ec4dd3f044a85a8413239bb7c7',
}


def read_json(path: Path):
    return json.loads(path.read_text(encoding='utf-8'))


def frozen_source_errors(register):
    errors = []
    for field, expected in [('paper_inputs',FROZEN_PAPER_SHA256),
        ('specification_sources',FROZEN_SPECIFICATION_SHA256)]:
        descriptors = register.get(field)
        if not isinstance(descriptors,list) or any(not isinstance(item,dict) for item in descriptors):
            errors.append('original frozen source descriptor inventory invalid: '+field)
            continue
        paths = [item.get('path') for item in descriptors]
        if len(paths) != len(expected) or len(set(paths)) != len(paths) or set(paths) != set(expected):
            errors.append('original frozen source descriptor inventory changed: '+field)
        for item in descriptors:
            path = item.get('path')
            if path not in expected or item.get('sha256') != expected[path]:
                errors.append('original frozen source descriptor identity changed: '+str(path))
    return errors


def metadata_errors(manifest, public, crosswalk):
    errors = []
    roots = public['primary_roots']
    for field in ('id', 'full_name'):
        if len({r[field] for r in roots}) != len(roots):
            errors.append('duplicate root ' + field)
    if roots != manifest['required_theorem_roots']:
        errors.append('manifest/public root inventory mismatch')
    families = set(manifest['scope']['required_paper_ids'])
    if len(roots) != 76 or len(families) != 25:
        errors.append('full scope requires 76 primary roots and 25 paper families')
    statements = crosswalk['statements']
    if {s['paper_id'] for s in statements} != families or len(statements) != 25:
        errors.append('missing or duplicate paper family')
    for statement in statements:
        expected = {r['full_name'] for r in roots if r['paper_id'] == statement['paper_id']}
        if set(statement['required_roots']) != expected:
            errors.append('paper subclause root mismatch: ' + statement['paper_id'])
        if not statement.get('coverage_rule'):
            errors.append('missing semantic coverage rule: ' + statement['paper_id'])
    if len(crosswalk['corrections']) != 38:
        errors.append('38 historical corrections must be retained')
    created = [x['path'] for x in manifest['create']]
    modified = [x['path'] for x in manifest['modify']]
    if len(created) != 50 or len(created) != len(set(created)):
        errors.append('new file inventory is not the exact 50 unique paths')
    if len(modified) != 9 or len(modified) != len(set(modified)):
        errors.append('authoritative edit inventory is not the exact nine unique paths')
    if set(created) & set(modified) or manifest['delete']:
        errors.append('created/modified overlap or forbidden deletion')
    modules = manifest['modules']
    if (len(modules) != 26 or len({m['module'] for m in modules}) != 26
        or len({m['path'] for m in modules}) != 26
        or {m['path'] for m in modules} != {path for path in created if path.endswith('.lean')}):
        errors.append('module inventory must be all 26 unique new Lean modules')
    for module in modules:
        if module['path'] != module['module'].replace('.', '/')+'.lean':
            errors.append('module inventory path mismatch: '+module['module'])
    for root in roots:
        if root['path'] != root['module'].replace('.', '/') + '.lean':
            errors.append('root module/path mismatch: ' + root['full_name'])
        if root['kind'] != 'THEOREM' or not root['required_for_full_pr']:
            errors.append('root kind/scope mismatch: ' + root['full_name'])
    return errors


def forbidden_lean(text):
    # Strings cannot carry mathematical tokens. Comments retain their newlines
    # so import/declaration line anchors stay truthful.
    code = strip_lean_comments(text)
    code = re.sub(r'"(?:\\.|[^"\\])*"', '""', code)
    return re.findall(r'\b(?:sorry|admit|axiom|native_decide|ofReduceBool)\b', code)


def protected_errors(repo: Path, protection):
    errors = []
    for entry in protection['byte_protected_files']:
        path = repo / entry['path']
        if not path.is_file():
            errors.append('protected file missing: ' + entry['path'])
            continue
        data = path.read_bytes()
        if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
            errors.append('protected bytes changed: ' + entry['path'])
    for name, key, baseline_key in [
        ('CLAIM_REGISTRY.json', 'claims', 'claim_objects_all_existing'),
        ('REGISTERED_THEOREM_BINDINGS.json', 'bindings', 'registered_bindings_all_existing'),
    ]:
        actual = read_json(repo / 'research/RHRC' / name)[key]
        old = protection[baseline_key]
        ids = [item['id'] for item in actual]
        if len(ids) != len(set(ids)):
            errors.append('duplicate existing registry identity: ' + name)
        by_id = {item['id']: item for item in actual}
        for item in old:
            if by_id.get(item['id']) != item:
                errors.append('historical registry object changed: ' + item['id'])
    return errors


def registration_errors(claims, bindings, roots, protection, manifest):
    """The final totals cannot substitute unrelated rows for required roots."""
    errors = []
    old_claim_ids = {item['id'] for item in protection['claim_objects_all_existing']}
    old_binding_ids = {item['id'] for item in protection['registered_bindings_all_existing']}
    root_ids = {root['id'] for root in roots}
    claim_ids, binding_ids = [item['id'] for item in claims], [item['id'] for item in bindings]
    if len(claim_ids) != len(set(claim_ids)) or set(claim_ids) != old_claim_ids | root_ids:
        errors.append('final claim identities must be exactly the protected baseline plus all OPICA roots')
    if len(binding_ids) != len(set(binding_ids)) or set(binding_ids) != old_binding_ids | root_ids:
        errors.append('final binding identities must be exactly the protected baseline plus all OPICA roots')
    if len(claims) != manifest['registry']['expected_final_claim_count']:
        errors.append('full acceptance requires 198 source-reviewed claims; planned roots are not registry authority')
    if len(bindings) != manifest['registry']['expected_final_binding_count']:
        errors.append('full acceptance requires 194 source-bound proved bindings')
    claim_by_id, binding_by_id = {item['id']:item for item in claims}, {item['id']:item for item in bindings}
    for root in roots:
        identity = root['id']
        claim, binding = claim_by_id.get(identity), binding_by_id.get(identity)
        if claim is None:
            errors.append('required OPICA claim absent: '+identity)
        else:
            if claim.get('source') != root['path'] or claim.get('theorem') != root['full_name']:
                errors.append('registered OPICA claim source/root mismatch: '+identity)
            if claim.get('status') != 'PROVED_UNCONDITIONAL' or claim.get('promotion_cap') != 'PROVED_UNCONDITIONAL':
                errors.append('OPICA supporting claim has wrong proof status or promotion cap: '+identity)
            if claim.get('route') is not None:
                errors.append('OPICA supporting claim must remain route-less: '+identity)
            if not isinstance(claim.get('statement'),str) or not claim['statement'].strip():
                errors.append('OPICA claim lacks its exact quantified implication statement: '+identity)
            dependencies = claim.get('dependencies')
            if (not isinstance(dependencies,list) or not all(isinstance(x,str) for x in dependencies)
                or len(dependencies) != len(set(dependencies)) or not set(dependencies) <= set(claim_ids)
                or identity in dependencies):
                errors.append('OPICA claim has invalid registered dependency identities: '+identity)
        if binding is None:
            errors.append('required OPICA binding absent: '+identity)
        elif binding.get('theorem') != root['full_name'] or binding.get('source') != root['path']:
            errors.append('registered OPICA source/root mismatch: '+identity)
        elif binding.get('route') is not None:
            errors.append('OPICA supporting binding must remain route-less: '+identity)
    return errors


def config_errors(classes, closure, baseline_classes, baseline_closure, modules, baseline_paths):
    errors = []
    old_rules = baseline_classes['rules']
    positions = [index for index,rule in enumerate(old_rules) if rule['id'] == 'zeta_lean']
    if len(positions) != 1:
        return ['immutable baseline has no unique generic zeta_lean classification rule']
    position = positions[0]
    expected_classes = {**baseline_classes,
        'rules':old_rules[:position]+OPICA_CLASS_RULES+old_rules[position:]}
    if classes != expected_classes:
        errors.append('file classes must preserve immutable baseline objects/order with only the three permitted OPICA rules')
    def classify(config,path):
        rule = next((r for r in config['rules'] if re.search(r['pattern'],path)),None)
        return (rule['file_class'],rule['trust_zone']) if rule else (config['unknown_class'],config['unknown_trust_zone'])
    for path in baseline_paths:
        if classify(classes,path) != classify(baseline_classes,path):
            errors.append('historical first-match classification changed: '+path)
    role_for_zone = {'AUDIT_ONLY':'OPICA_AUDIT_ONLY',
        'RH_FORMAL_CORE':'OPICA_SOURCE_BOUND_NATIVE_ADAPTER',
        'AUXILIARY_FORMALIZATION':'OPICA_GENERIC_FORMALIZATION'}
    new_roles = {}
    for module in modules:
        if module['trust_zone'] not in role_for_zone:
            errors.append('OPICA module has an unapproved standalone trust zone: '+module['module'])
        else:
            new_roles[module['module']] = role_for_zone[module['trust_zone']]
    old_roles = baseline_closure['standalone_module_roles']
    if set(old_roles) & set(new_roles):
        errors.append('new OPICA roles overlap an immutable historical module')
    expected_closure = {**baseline_closure,'standalone_module_roles':{**old_roles,**new_roles}}
    if closure != expected_closure:
        errors.append('semantic closure config must preserve every immutable field/role and append exactly the 26 OPICA roles')
    return errors


def classification_errors(classes, modules, register):
    """Only the literal two-path implementation refinement is permitted."""
    errors = []
    if register.get('implementation_file_classification_overrides') != OPICA_CLASSIFICATION_OVERRIDES:
        errors.append('implementation file classification overrides must be exactly the two documented native adapter refinements')
    by_path = {module['path']:module for module in modules}
    for override in OPICA_CLASSIFICATION_OVERRIDES:
        module = by_path.get(override['path'])
        if module is None or module.get('trust_zone') != override['specified_trust_zone']:
            errors.append('frozen native adapter specified trust zone changed: '+override['path'])
    implementation_zones = {item['path']:item['implementation_trust_zone']
        for item in OPICA_CLASSIFICATION_OVERRIDES}
    for module in modules:
        rule = next((r for r in classes['rules'] if re.search(r['pattern'],module['path'])),None)
        expected_zone = implementation_zones.get(module['path'],module['trust_zone'])
        if rule is None or rule['file_class'] != 'LEAN_SOURCE' or rule['trust_zone'] != expected_zone:
            errors.append('module classification mismatch: '+module['path'])
    return errors


def baseline_configs(repo, base):
    def frozen(path):
        return json.loads(subprocess.check_output(['git','show',base+':'+path],cwd=repo).decode('utf-8'))
    classes = frozen('research/RHRC/graph/FILE_CLASSES.json')
    closure = frozen('research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json')
    paths = subprocess.check_output(['git','ls-tree','-r','--name-only','--full-tree',base],cwd=repo,text=True).splitlines()
    return classes,closure,paths


def registered_dependency_errors(claims,bindings,roots,dependencies):
    """Check new claim edges against complete compiler uses, not shared names."""
    sys.path.insert(0,str(Path(__file__).resolve().parent))
    from build_receipt import mapped_registered_dependencies
    mapped = mapped_registered_dependencies([root['full_name'] for root in roots],bindings,dependencies)
    by_id = {claim['id']:claim for claim in claims}
    errors = []
    for root in roots:
        claim = by_id.get(root['id'])
        if claim is None:
            errors.append('required OPICA dependency claim absent: '+root['id'])
        elif claim.get('dependencies') != mapped[root['full_name']]:
            errors.append('registered OPICA dependencies differ from transitive compiler uses: '+root['id'])
    return errors


def formal_receipt_errors(repo, receipt, manifest, roots):
    errors = []
    head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
    tree = subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=repo,text=True).strip()
    if receipt.get('schema') != 'OPICA_COMPILER_RECEIPT_V1' or receipt.get('status') != 'COMPILER_VERIFIED':
        errors.append('formal receipt is not compiler verified')
    if receipt.get('checked_commit') != head or receipt.get('checked_tree') != tree:
        errors.append('stale formal receipt head/tree')
    if receipt.get('requested_base') != manifest['base_commit'] or receipt.get('mathlib_commit') != manifest['mathlib_commit']:
        errors.append('formal receipt base or Mathlib pin mismatch')
    expected_sources = {x['path'] for x in manifest['create'] + manifest['modify']}
    actual_sources = receipt.get('sources',{})
    if set(actual_sources) != expected_sources:
        errors.append('formal receipt source inventory mismatch')
    for path in expected_sources:
        if not (repo/path).is_file() or actual_sources.get(path) != hashlib.sha256((repo/path).read_bytes()).hexdigest():
            errors.append('formal receipt source identity mismatch: '+path)
    records = receipt.get('declarations',[])
    if not isinstance(records,list):
        errors.append('formal receipt declaration inventory malformed')
        records = []
    by_name = {r['name']:r for r in records if isinstance(r,dict) and isinstance(r.get('name'),str)}
    if len(records) != len(by_name):
        errors.append('duplicate formal receipt declaration')
    try:
        sys.path.insert(0,str(Path(__file__).resolve().parent))
        from build_receipt import validate_checkout_identity, validate_compiler_receipt, with_reviewed_root_types
        reviewed = read_json(repo/'research/RHRC/integration/opica/WORKFLOW_CONTRACT.json').get('reviewed_root_type_sha256',{})
        reviewed_roots = with_reviewed_root_types(roots,reviewed)
        parents = [] if receipt.get('requested_head')==head else subprocess.check_output(
            ['git','rev-list','--parents','-n','1',head],cwd=repo,text=True).strip().split()[1:]
        validate_checkout_identity(receipt,head,tree,parents)
        validate_compiler_receipt(receipt,manifest,reviewed_roots)
    except (KeyError,TypeError,ValueError) as exc:
        errors.append('formal receipt compiler evidence invalid: '+str(exc))
    else:
        try:
            claims = read_json(repo/'research/RHRC/CLAIM_REGISTRY.json')['claims']
            bindings = read_json(repo/'research/RHRC/REGISTERED_THEOREM_BINDINGS.json')['bindings']
            errors += registered_dependency_errors(claims,bindings,roots,receipt['dependencies'])
        except (KeyError,TypeError,ValueError) as exc:
            errors.append('formal receipt registered dependency mapping invalid: '+str(exc))
    reviewed = read_json(repo/'research/RHRC/integration/opica/WORKFLOW_CONTRACT.json').get('reviewed_root_type_sha256',{})
    if set(reviewed) != {r['full_name'] for r in roots}:
        errors.append('reviewed root type inventory incomplete')
    for root in roots:
        record = by_name.get(root['full_name'])
        if record is None or record.get('module') != root['module'] or record.get('kind') != 'THEOREM':
            errors.append('formal receipt missing exact source root: '+root['full_name'])
        elif record.get('type_sha256') != reviewed.get(root['full_name']) or not record.get('full_type'):
            errors.append('formal receipt reviewed type mismatch: '+root['full_name'])
    return errors


def import_cycle_errors(modules):
    errors = []
    visiting, visited = set(), set()

    def visit(module):
        if module in visiting:
            errors.append('import cycle: ' + module)
            return
        if module in visited:
            return
        visiting.add(module)
        for dependency in modules.get(module, []):
            if dependency in modules:
                visit(dependency)
        visiting.remove(module)
        visited.add(module)

    for module in modules:
        visit(module)
    return errors


def check(repo: Path):
    folder = repo / 'research/RHRC/integration/opica'
    manifest = read_json(folder / 'BUILD_MANIFEST.json')
    public = read_json(folder / 'PUBLIC_ROOTS.json')
    crosswalk = read_json(folder / 'PAPER_CROSSWALK.json')
    protection = read_json(folder / 'PROTECTED_STATE.json')
    errors = metadata_errors(manifest, public, crosswalk)
    errors += protected_errors(repo, protection)
    missing_files = [item['path'] for item in manifest['create'] if not (repo/item['path']).is_file()]
    errors += ['required file missing: ' + path for path in missing_files]
    register = read_json(folder / 'SOURCE_REGISTER.json')
    errors += frozen_source_errors(register)
    for source in register['paper_inputs'] + register['specification_sources'] + register.get('adapted_sources',[]):
        path = folder / source['path']
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != source['sha256']:
            errors.append('frozen source identity mismatch: ' + source['path'])
    modules = {}
    declared = []
    missing_roots = []
    for spec in manifest['modules']:
        path = repo / spec['path']
        if not path.is_file():
            continue
        text = path.read_text(encoding='utf-8')
        modules[spec['module']] = import_modules(text)
        bad = forbidden_lean(text)
        if bad:
            errors.append('forbidden mathematical token in ' + spec['path'] + ': ' + ', '.join(bad))
    for root in public['primary_roots']:
        path = repo / root['path']
        name = root['full_name'].removeprefix('Zeta23.OPICA.')
        present = path.is_file() and re.search(r'\btheorem\s+' + re.escape(name) + r'\b',
            strip_lean_comments(path.read_text(encoding='utf-8')))
        (declared if present else missing_roots).append(root['full_name'])
    errors += ['required theorem declaration absent: ' + name for name in missing_roots]
    claims = read_json(repo/'research/RHRC/CLAIM_REGISTRY.json')['claims']
    bindings = read_json(repo/'research/RHRC/REGISTERED_THEOREM_BINDINGS.json')['bindings']
    errors += registration_errors(claims,bindings,public['primary_roots'],protection,manifest)
    classes = read_json(repo/'research/RHRC/graph/FILE_CLASSES.json')
    closure = read_json(repo/'research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json')
    roles = closure['standalone_module_roles']
    baseline_classes,baseline_closure,baseline_paths = baseline_configs(repo,manifest['base_commit'])
    errors += config_errors(classes,closure,baseline_classes,baseline_closure,manifest['modules'],baseline_paths)
    errors += classification_errors(classes,manifest['modules'],register)
    for module in manifest['modules']:
        if module['module'] not in roles:
            errors.append('missing standalone module role: '+module['module'])
    errors += import_cycle_errors(modules)
    actual_imports = {name:[d for d in imports if d.startswith('Zeta23')] for name,imports in modules.items()}
    if register.get('implementation_project_imports') != actual_imports:
        errors.append('actual project import graph differs from source register')
    reachable = set()

    def reach(module):
        if module in reachable:
            return
        reachable.add(module)
        for dependency in modules.get(module, []):
            reach(dependency)

    reach('Zeta23.OPICA')
    for module in reachable:
        if module == 'Zeta23.OPICA.Validation' or module.startswith('Zeta23.RHRC.'):
            errors.append('audit module reachable from mathematical facade: ' + module)
    for item in manifest['modules']:
        if item['trust_zone'] != 'AUDIT_ONLY' and item['module'] not in reachable:
            errors.append('mathematical module absent from facade: ' + item['module'])
    allowed_new = {x['path'] for x in manifest['create']}
    allowed_old = {x['path'] for x in manifest['modify']} | set(manifest['regenerate']['paths'])
    changed = subprocess.check_output(['git', 'diff', '--no-renames', '--name-status',
        manifest['base_commit']], cwd=repo, text=True).splitlines()
    for line in changed:
        operation, path = line.split('\t', 1)
        if operation == 'D' or path not in allowed_new | allowed_old:
            errors.append('unauthorized tracked delta: ' + line)
    untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'],
        cwd=repo, text=True).splitlines()
    errors += ['unauthorized new path: ' + p for p in untracked if p not in allowed_new]
    return {'schema': 'OPICA_STATIC_CONTRACT_V1', 'status': 'FAIL' if errors else 'PASS',
        'errors': errors, 'required_roots': 76, 'declared_roots': declared,
        'missing_roots': missing_roots, 'missing_files': missing_files,
        'authority': 'Static presence and source checks only. A declaration name is not a proof/type/axiom receipt.',
        'formal_acceptance': 'PENDING_COMPILER_AND_SEMANTIC_REVIEW', 'RH': 'OPEN', 'Step4': 'OPEN'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    destination = parser.add_mutually_exclusive_group()
    destination.add_argument('--output-dir', type=Path)
    destination.add_argument('--output', type=Path)
    parser.add_argument('--phase', choices=['preflight','release'],default='preflight')
    parser.add_argument('--base',default='97926d6a949fed7af0429a373b47abc772012834')
    parser.add_argument('--formal-receipt',type=Path)
    args = parser.parse_args()
    report = check(REPO)
    manifest = read_json(HERE/'BUILD_MANIFEST.json')
    def git(*parts):
        return subprocess.check_output(['git',*parts],cwd=REPO,text=True).strip()
    report.update(checked_commit=git('rev-parse','HEAD'),checked_tree=git('rev-parse','HEAD^{tree}'),
        tracked_source_dirty=bool(git('status','--porcelain','--untracked-files=no')),
        source_sha256={item['path']:hashlib.sha256((REPO/item['path']).read_bytes()).hexdigest()
            for item in manifest['create']+manifest['modify'] if (REPO/item['path']).is_file()})
    if args.base != manifest['base_commit']:
        report['errors'].append('wrong immutable base precondition')
    if args.phase == 'release':
        if args.formal_receipt is None:
            report['errors'].append('release phase requires full formal receipt')
        else:
            report['errors'] += formal_receipt_errors(REPO,read_json(args.formal_receipt),manifest,
                read_json(HERE/'PUBLIC_ROOTS.json')['primary_roots'])
    report['phase'] = args.phase
    report['status'] = 'FAIL' if report['errors'] else 'PASS'
    if args.phase == 'release' and report['status'] == 'PASS':
        report['formal_acceptance'] = 'COMPILER_VERIFIED_INDEPENDENT_REVIEW_NOT_AUTO_APPROVED'
    encoded = json.dumps(report, indent=2) + '\n'
    if args.output_dir or args.output:
        target = args.output.resolve() if args.output else args.output_dir.resolve()/'static-contract.json'
        if target.is_relative_to(REPO.resolve()):
            parser.error('execution artifacts must be outside the repository')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(encoded, encoding='utf-8')
    print(encoded, end='')
    return 0 if report['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
