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


# One explicitly reviewed child extension; this changes only the parent's
# closed-world registry/configuration/delta view, never its mathematical gates.
FOLLOWUP_FOLDER = 'research/RHRC/integration/opica_followup'
FOLLOWUP_PARENT = 'd53dd70d38b0762af130b1d19b795af259f505f5'
FOLLOWUP_TREE = '12691099f1a155a8bfa3ad4f6689146175b233b2'
FOLLOWUP_EXTENSION_MODULE_SHA256 = '95475b33fa3365c96a82a42b70385b17e90ab088ff951501b06468825ba0e20d'
FOLLOWUP_GLOBAL_FILES = {
    'claim_registry': 'research/RHRC/CLAIM_REGISTRY.json',
    'theorem_bindings': 'research/RHRC/REGISTERED_THEOREM_BINDINGS.json',
    'file_classes': 'research/RHRC/graph/FILE_CLASSES.json',
    'semantic_closure': 'research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json',
}

# Separately reviewed Stage1 documentation navigation bytes. This exact seven-
# file exception is independent of the full100-root child extension below.
# Neither an editable child register nor a continuation manifest can repin it.
# The original PROTECTED_STATE.json and historical registry objects stay frozen.
FOLLOWUP_DOCUMENTATION_PATHS = frozenset({
    'AUDIT.md', 'FORK_NOTES.md',
    'research/RHRC/DOCUMENTATION_AUTHORITY.md',
    'research/RHRC/VALIDATION_PROTOCOL.md',
    'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md',
    'research/RHRC/graph/README.md', 'research/RHRC/integration/README.md',
})
FOLLOWUP_DOCUMENTATION_REVIEW = (
    ('AUDIT.md', 27928, '20f4d509f16ddbbe1ac16aa18a25a193f6cde0c967456e93b99fc5c23958e6d6'),
    ('FORK_NOTES.md', 21357, 'b186d9d72fde095838dd61192b361d7717916de74a4c754b87b06d7f1e98ee3d'),
    ('research/RHRC/DOCUMENTATION_AUTHORITY.md', 34335, 'd8b9170c288216e01a764b4a948ba3a44350d24c488be02516db65e9616519dc'),
    ('research/RHRC/VALIDATION_PROTOCOL.md', 41520, 'e08baedbe485245772b6055b1e1ef2951270b042355fe5aed0c5d6e8e8e36d9f'),
    ('research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md', 5403, 'de9aabe7985f839c39b62e82c3407c97bc21d831e283199ab5d81784fe68f327'),
    ('research/RHRC/graph/README.md', 17821, '806d732741e4d5358bf756b10268761aa269d462d98bd95d7432a6e112d32af5'),
    ('research/RHRC/integration/README.md', 5636, '0470a3181ea91a825ba72b05a53f9f54eb43ffcda14863295d121f9d6a0532d3'),
)
FOLLOWUP_DOCUMENTATION_REVIEW_SHA256 = '4132519489b06e10a4883cf694e9b5ab55c7e34bced08fa840bc6586f70b7c4d'
PROTECTED_STATE_OBJECT_SHA256 = '5ad6d198133f07a5ed7ac8abc9ec9bb6523db4a9729b69a61f7fe15a7820ce99'


def _canonical_object_sha256(document):
    return hashlib.sha256(json.dumps(document,sort_keys=True,separators=(',', ':'),
        ensure_ascii=False).encode('utf-8')).hexdigest()


def reviewed_documentation_paths(repo: Path):
    """Return the exact all-or-nothing documentation exception, never proof scope.

    A separate fixed seal prevents self-repinning the table while editing a
    manifest. The parent validator's own source identity is pinned by the full
    child builder; changing that trusted code requires independent review.
    """
    try:
        rows = [{'path':p,'bytes':size,'sha256':digest}
                for p,size,digest in FOLLOWUP_DOCUMENTATION_REVIEW]
        paths = [row['path'] for row in rows]
        if (len(rows) != 7 or len({p.casefold() for p in paths}) != 7
                or set(paths) != FOLLOWUP_DOCUMENTATION_PATHS
                or paths != sorted(paths)
                or _canonical_object_sha256(rows) != FOLLOWUP_DOCUMENTATION_REVIEW_SHA256):
            raise ValueError('exact sealed seven-path inventory required')
        identities = set()
        for row in rows:
            path = _safe_checkout_file(Path(repo).absolute(),row['path'])
            if path.resolve() != Path(repo).resolve()/row['path']:
                raise ValueError('aliased documentation path: '+row['path'])
            stat = path.stat()
            identity = (stat.st_dev,stat.st_ino)
            if stat.st_nlink != 1 or identity in identities:
                raise ValueError('aliased documentation file: '+row['path'])
            identities.add(identity)
            data = path.read_bytes()
            if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
                raise ValueError('reviewed documentation bytes changed: '+row['path'])
        return set(paths), []
    except (OSError,ValueError,TypeError,KeyError) as exc:
        return set(), ['documentation review rejected: '+str(exc)]


def _extension_require(condition, message):
    # Deliberately not an assert: python -O must retain every rejection.
    if not condition:
        raise ValueError('OPICA follow-up extension: ' + message)


def _safe_checkout_file(repo: Path, relative: str) -> Path:
    from pathlib import PurePosixPath
    _extension_require(isinstance(relative,str) and relative and '\\' not in relative
        and ':' not in relative and not PurePosixPath(relative).is_absolute()
        and all(p not in {'','.','..'} for p in relative.split('/')), 'unsafe path')
    path = repo / relative
    _extension_require(not any(p.is_symlink() for p in [path, *path.parents]
        if p.is_relative_to(repo)), 'symlink in source path: '+relative)
    _extension_require(path.is_file() and path.resolve().is_relative_to(repo.resolve()),
                       'missing or escaped source: '+relative)
    return path


def _git_tree_entries(repo: Path, revision: str):
    raw = subprocess.check_output(['git','ls-tree','-r','-z',revision],cwd=repo)
    result = {}
    for entry in raw.split(b'\0'):
        if not entry:
            continue
        meta, name = entry.split(b'\t',1)
        mode,kind,oid = meta.decode('ascii').split()
        path = name.decode('utf-8')
        _extension_require(kind=='blob' and mode in {'100644','100755'},
                           'unsupported committed source mode: '+path)
        _extension_require(path not in result, 'duplicate tree path')
        result[path] = (mode,oid)
    return result


def _source_bound_parent_baseline(repo: Path, baseline):
    """Verify the frozen capture against actual immutable Git objects, not HEAD.

    This permits a child checkout without moving HEAD or trusting a mutable
    capture. Batch mode avoids one Git process per source file.
    """
    tree = subprocess.check_output(['git','rev-parse',FOLLOWUP_PARENT+'^{tree}'],
                                   cwd=repo,text=True).strip()
    _extension_require(tree==FOLLOWUP_TREE, 'accepted parent tree mismatch')
    entries = _git_tree_entries(repo,FOLLOWUP_PARENT)
    rows = baseline.get('files')
    _extension_require(isinstance(rows,list) and all(isinstance(r,dict) for r in rows),
                       'parent source inventory malformed')
    by_path = {r.get('path'):r for r in rows}
    _extension_require(len(by_path)==len(rows) and set(by_path)==set(entries),
                       'parent source census differs from accepted Git tree')
    names = list(entries)
    request = b''.join((entries[name][1]+'\n').encode('ascii') for name in names)
    process = subprocess.run(['git','cat-file','--batch'],cwd=repo,input=request,
                             stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    output = process.stdout
    position = 0
    globals_from_git = {}
    for name in names:
        end = output.find(b'\n',position)
        _extension_require(end>=0, 'truncated parent object header')
        oid,kind,size_string = output[position:end].decode('ascii').split()
        size = int(size_string)
        start = end+1
        data = output[start:start+size]
        _extension_require(len(data)==size and output[start+size:start+size+1]==b'\n',
                           'truncated parent object body')
        position = start+size+1
        mode,expected_oid = entries[name]
        actual_oid = hashlib.sha1(b'blob '+str(size).encode()+b'\0'+data).hexdigest()
        expected = {'path':name,'mode':mode,'git_blob':expected_oid,
                    'bytes':size,'sha256':hashlib.sha256(data).hexdigest()}
        _extension_require(kind=='blob' and oid==expected_oid and actual_oid==oid
                           and by_path[name]==expected, 'parent bytes differ: '+name)
        if name in FOLLOWUP_GLOBAL_FILES.values():
            globals_from_git[name] = json.loads(data)
    _extension_require(position==len(output), 'unexpected parent object stream suffix')
    for key,name in FOLLOWUP_GLOBAL_FILES.items():
        _extension_require(baseline.get(key)==globals_from_git[name],
                           'parent registry/configuration capture differs: '+key)


def _reviewed_child_objects(repo: Path, roots, register, workflow, *, parent_claims=()):
    """Consume independently recorded review objects, never derive them from raw registries.

    These structural bindings are not compiler authority. The unchanged parent
    receipt gate and complete child compiler gate are still required separately.
    """
    required = {r['full_name']:r for r in roots}
    _extension_require(len(required)==100 and len(roots)==100,'100-root inventory required')
    types = workflow.get('implemented_root_type_sha256')
    _extension_require(isinstance(types,dict) and set(types)==set(required),
                       'full child reviewed type table absent; subset cannot extend parent')
    review = register.get('accepted_registry_extension')
    _extension_require(isinstance(review,dict)
        and review.get('schema')=='OPICA_FOLLOWUP_REVIEWED_REGISTRY_V2'
        and review.get('scope')=='FULL_100_ORIGINAL_ROOTS',
        'full independent registry-object review is absent')
    records = review.get('roots')
    _extension_require(isinstance(records,list) and len(records)==100
        and [r.get('full_name') for r in records]==[r['full_name'] for r in roots],
        'reviewed root order/identity mismatch')
    parent_ids = [row.get('id') for row in parent_claims]
    child_ids = [row.get('id') for row in roots]
    _extension_require(all(isinstance(identity, str) and identity for identity in parent_ids)
        and len(parent_ids) == len(set(parent_ids)), 'invalid immutable parent claim census')
    _extension_require(all(isinstance(identity, str) and identity for identity in child_ids)
        and len(child_ids) == len(set(child_ids))
        and not set(parent_ids).intersection(child_ids), 'invalid or reused child identity')
    known_claims = set(parent_ids) | set(child_ids)
    claims, bindings = [], []
    for root,record in zip(roots,records):
        name = root['full_name']
        digest = types[name]
        _extension_require(isinstance(digest,str) and re.fullmatch('[0-9a-f]{64}',digest)
            and record.get('type_sha256')==digest,'unreviewed exact type: '+name)
        source = _safe_checkout_file(repo,root['path'])
        _extension_require(record.get('source_sha256')==hashlib.sha256(source.read_bytes()).hexdigest(),
                           'stale reviewed proof source: '+name)
        consumer = record.get('expected_type_consumer')
        _extension_require(isinstance(consumer,dict), 'missing expected-type consumer: '+name)
        consumer_path = consumer.get('path')
        _extension_require(consumer_path=='Zeta23/OPICAFollowup/Validation.lean',
                           'wrong independent expected-type surface: '+name)
        consumer_file = _safe_checkout_file(repo,consumer_path)
        _extension_require(consumer.get('sha256')==hashlib.sha256(consumer_file.read_bytes()).hexdigest()
            and consumer.get('declaration')==root['expected_type_consumer'],
            'stale/mismatched independently stated consumer: '+name)
        _extension_require(record.get('status')=='PROOF_TYPE_AND_SOURCE_REVIEWED',
                           'unreviewed candidate cannot register: '+name)
        claim, binding = record.get('claim'),record.get('binding')
        _extension_require(isinstance(claim,dict) and isinstance(binding,dict),
                           'exact reviewed objects missing: '+name)
        for obj in (claim,binding):
            _extension_require(obj.get('id')==root['id'] and obj.get('theorem')==name
                and obj.get('source')==root['path'], 'reviewed source/name differs: '+name)
        _extension_require(claim.get('status')=='PROVED_UNCONDITIONAL'
            and claim.get('promotion_cap')=='PROVED_UNCONDITIONAL',
            'supporting theorem status differs: '+name)
        # These rows will be REMOVED from the parent projection. The parent's
        # registration_errors therefore cannot police their claim firewall.
        _extension_require(claim.get('route') is None and binding.get('route') is None,
                           'child supporting objects must remain route-less: '+name)
        statement = claim.get('statement')
        _extension_require(isinstance(statement, str) and bool(statement.strip()),
                           'child quantified statement missing: '+name)
        _extension_require(record.get('statement_sha256') ==
            hashlib.sha256(statement.encode('utf-8')).hexdigest(),
            'child quantified statement differs from reviewed text: '+name)
        dependencies = claim.get('dependencies')
        _extension_require(isinstance(dependencies, list)
            and all(isinstance(identity, str) and identity for identity in dependencies)
            and len(dependencies) == len(set(dependencies))
            and set(dependencies) <= known_claims and root['id'] not in dependencies,
            'child registered dependency identities invalid: '+name)
        claims.append(claim)
        bindings.append(binding)
    return claims,bindings


def _source_bound_followup_context_v1(repo: Path):
    """Return a validated extension, or None for an untouched parent checkout.

    Missing/incomplete child material never disables a check. It raises an
    explicit error; the caller then runs the original unprojected parent checks.
    """
    folder = repo/FOLLOWUP_FOLDER
    present = folder.exists() or any((repo/name).exists() for name in (
        'Zeta23/OPICAFollowup','Zeta23/OPICAFollowup.lean',
        'Zeta23/RHRC/OpicaFollowupBindings.lean'))
    if not present:
        return None
    extension_path = _safe_checkout_file(repo,FOLLOWUP_FOLDER+'/parent_extension.py')
    _extension_require(hashlib.sha256(extension_path.read_bytes()).hexdigest()==
        FOLLOWUP_EXTENSION_MODULE_SHA256,'unreviewed projection implementation')
    import importlib.util
    module_name = '_opica_source_bound_followup_extension'
    spec = importlib.util.spec_from_file_location(module_name,extension_path)
    extension = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = extension
    spec.loader.exec_module(extension)
    descriptor_bytes = _safe_checkout_file(repo,FOLLOWUP_FOLDER+'/PARENT_EXTENSION.json').read_bytes()
    roots_bytes = _safe_checkout_file(repo,FOLLOWUP_FOLDER+'/PUBLIC_ROOTS.json').read_bytes()
    baseline = read_json(_safe_checkout_file(repo,FOLLOWUP_FOLDER+'/PROTECTED_STATE.json'))
    _source_bound_parent_baseline(repo,baseline)
    roots = json.loads(roots_bytes)['roots']
    register = read_json(_safe_checkout_file(repo,FOLLOWUP_FOLDER+'/SOURCE_REGISTER.json'))
    workflow = read_json(_safe_checkout_file(repo,FOLLOWUP_FOLDER+'/WORKFLOW_CONTRACT.json'))
    claims,bindings = _reviewed_child_objects(repo,roots,register,workflow,
        parent_claims=baseline['claim_registry']['claims'])
    index_raw = subprocess.check_output(['git','ls-files','--stage','-z'],cwd=repo)
    files = []
    for item in index_raw.split(b'\0'):
        if not item:
            continue
        meta,name_bytes = item.split(b'\t',1)
        mode,oid,stage = meta.decode('ascii').split()
        name = name_bytes.decode('utf-8')
        _extension_require(stage=='0' and mode in {'100644','100755'},
                           'unmerged/symlink source entry: '+name)
        data = _safe_checkout_file(repo,name).read_bytes()
        actual_oid = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        _extension_require(oid==actual_oid,'unstaged source change: '+name)
        files.append({'path':name,'mode':mode,'git_blob':oid,'bytes':len(data),
                      'sha256':hashlib.sha256(data).hexdigest()})
    raw = {'parent_head':baseline['parent_head'],'parent_tree':FOLLOWUP_TREE,'files':files}
    raw.update({key:read_json(_safe_checkout_file(repo,name)) for key,name in FOLLOWUP_GLOBAL_FILES.items()})
    contract = {'descriptor_bytes':descriptor_bytes,'roots_bytes':roots_bytes,
                'reviewed_claim_objects':claims,'reviewed_binding_objects':bindings}
    context = extension.validate_extension_context(raw,baseline,contract)
    return (dict(extension.project_parent_context(context)),extension.allowed_child_delta(context))



# Version2 policy authority is distinct from compiler validity and human review.
# Bound to the actual independently reviewed exact-subject/caller objects.
TRUSTED_EXACT_EXTENSION_POLICY_SHA256 = 'd0a5b6927345383ad2693356b9ca85f316abee7b6c1db73501a317958d39a74d'
EXACT_EXTENSION_PROVIDER_SHA256 = '0b393f7d1b177a1c497917aa0aaade1355b0512338bc3a143991b4550fae5e44'


def _exact_source_extension_context(repo: Path):
    folder = repo/FOLLOWUP_FOLDER
    if not folder.exists():
        return None
    register = read_json(_safe_checkout_file(repo,FOLLOWUP_FOLDER+'/SOURCE_REGISTER.json'))
    if 'exact_source_extension_policy' not in register:
        return None
    _extension_require(isinstance(TRUSTED_EXACT_EXTENSION_POLICY_SHA256,str)
        and re.fullmatch('[0-9a-f]{64}',TRUSTED_EXACT_EXTENSION_POLICY_SHA256),
        'independently reviewed exact-subject policy anchor is not established')
    policy = register['exact_source_extension_policy']
    _extension_require(isinstance(policy,dict)
        and policy.get('schema') in {'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V2', 'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V3'},
        'malformed or unsupported exact source policy')
    provider_path = _safe_checkout_file(repo,FOLLOWUP_FOLDER+'/exact_extension.py')
    _extension_require(hashlib.sha256(provider_path.read_bytes()).hexdigest()==
        EXACT_EXTENSION_PROVIDER_SHA256,'exact source provider changed without review')
    import importlib.util
    name = '_opica_exact_source_extension_provider_v2'
    spec = importlib.util.spec_from_file_location(name,provider_path)
    provider = importlib.util.module_from_spec(spec)
    sys.modules[name] = provider
    spec.loader.exec_module(provider)
    from types import SimpleNamespace
    helpers = SimpleNamespace(_source_bound_parent_baseline=_source_bound_parent_baseline,
        _reviewed_child_objects=_reviewed_child_objects, FOLLOWUP_GLOBAL_FILES=FOLLOWUP_GLOBAL_FILES)
    return provider.source_bound_context(repo,policy,TRUSTED_EXACT_EXTENSION_POLICY_SHA256,
                                         helpers)


def _source_bound_followup_context(repo: Path):
    """Explicit version dispatcher: malformed/pending V2 never falls back to V1."""
    context = _exact_source_extension_context(repo)
    if context is None:
        return _source_bound_followup_context_v1(repo)
    return (json.loads(context.parent_json),context.exact_allowed_paths)


def exact_extension_binding(repo: Path):
    context = _exact_source_extension_context(repo)
    if context is None:
        return None
    return {'schema':'OPICA_EXACT_SUBJECT_POLICY_BINDING_V2',
        'policy_sha256':context.policy_sha256,'checked_commit':context.actual_commit,
        'checked_tree':context.actual_tree,
        'complete_actual_source_inventory_sha256':context.actual_source_inventory_sha256,
        'projection_scope':'REGISTRY_CONFIG_AND_CLOSED_WORLD_METADATA_ONLY',
        'compiler_source_type_axiom_dependency_projection':False}


def _parent_view_or_raw(repo: Path, keys=None):
    selected = set(FOLLOWUP_GLOBAL_FILES) if keys is None else set(keys)
    raw = {key:read_json(repo/name) for key,name in FOLLOWUP_GLOBAL_FILES.items() if key in selected}
    try:
        validated = _source_bound_followup_context(repo)
    except (KeyError,TypeError,ValueError,OSError,subprocess.CalledProcessError) as exc:
        return raw,frozenset(),['follow-up extension rejected: '+str(exc)]
    if validated is None:
        return raw,frozenset(),[]
    projected,allowed = validated
    return {key:value for key,value in projected.items() if key in selected},allowed,[]


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
    # Compare the passed object as well as the separately pinned input file.
    # Editing a protected entry alongside a changed document cannot re-freeze it.
    if _canonical_object_sha256(protection) != PROTECTED_STATE_OBJECT_SHA256:
        errors.append('frozen protection object changed')
    reviewed_paths, review_errors = set(), []
    documentation_exception_needed = False
    for entry in protection['byte_protected_files']:
        if entry['path'] in FOLLOWUP_DOCUMENTATION_PATHS:
            try:
                data = _safe_checkout_file(Path(repo).absolute(),entry['path']).read_bytes()
                if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
                    documentation_exception_needed = True
            except (OSError,ValueError):
                documentation_exception_needed = True
    try:
        exact_context = _exact_source_extension_context(Path(repo))
    except (KeyError,TypeError,ValueError,OSError,subprocess.SubprocessError) as exc:
        errors.append('exact source extension rejected: '+str(exc))
        exact_context = None
    if exact_context is not None:
        reviewed_paths = set(exact_context.documentation_paths) | set(getattr(exact_context, 'implementation_paths', ()))
    elif documentation_exception_needed:
        reviewed_paths, review_errors = reviewed_documentation_paths(repo)
        errors.extend(review_errors)
    seen_paths = set()
    for entry in protection['byte_protected_files']:
        relative = entry['path']
        if relative.casefold() in seen_paths:
            errors.append('duplicate or aliased protected path: '+relative)
        seen_paths.add(relative.casefold())
        try:
            path = _safe_checkout_file(Path(repo).absolute(),relative)
        except (OSError,ValueError) as exc:
            errors.append('protected file missing or unsafe: '+relative+': '+str(exc))
            continue
        data = path.read_bytes()
        if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
            if relative not in reviewed_paths:
                errors.append('protected bytes changed: ' + relative)
    for name, key, baseline_key in [
        ('CLAIM_REGISTRY.json', 'claims', 'claim_objects_all_existing'),
        ('REGISTERED_THEOREM_BINDINGS.json', 'bindings', 'registered_bindings_all_existing'),
    ]:
        try:
            actual = read_json(_safe_checkout_file(Path(repo).absolute(),'research/RHRC/'+name))[key]
        except (OSError,ValueError,KeyError) as exc:
            errors.append('protected registry missing or unsafe: '+name+': '+str(exc))
            continue
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


def _legacy_config_errors(classes, closure, baseline_classes, baseline_closure, modules, baseline_paths):
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


def config_errors(classes, closure, baseline_classes, baseline_closure, modules, baseline_paths):
    """Authenticate only the actual raw config pair before strict legacy checks."""
    raw_classes = read_json(REPO/FOLLOWUP_GLOBAL_FILES['file_classes'])
    raw_closure = read_json(REPO/FOLLOWUP_GLOBAL_FILES['semantic_closure'])
    if classes == raw_classes and closure == raw_closure:
        projected, _, errors = _parent_view_or_raw(REPO,
            keys={'file_classes','semantic_closure'})
        if errors:
            return errors
        classes, closure = projected['file_classes'], projected['semantic_closure']
    return _legacy_config_errors(classes,closure,baseline_classes,baseline_closure,
        modules,baseline_paths)


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
            parent_view,_,extension_errors = _parent_view_or_raw(repo,
                ('claim_registry','theorem_bindings'))
            errors += extension_errors
            claims = parent_view['claim_registry']['claims']
            bindings = parent_view['theorem_bindings']['bindings']
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
    parent_view,child_delta,extension_errors = _parent_view_or_raw(repo)
    errors += extension_errors
    claims = parent_view['claim_registry']['claims']
    bindings = parent_view['theorem_bindings']['bindings']
    errors += registration_errors(claims,bindings,public['primary_roots'],protection,manifest)
    classes = parent_view['file_classes']
    closure = parent_view['semantic_closure']
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
    allowed_new = {x['path'] for x in manifest['create']} | set(child_delta)
    allowed_old = {x['path'] for x in manifest['modify']} | set(manifest['regenerate']['paths']) | set(child_delta)
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
