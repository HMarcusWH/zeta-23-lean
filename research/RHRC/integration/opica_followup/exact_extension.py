"""V2 exact-subject extension provider proposal. No review anchor is configured here.
The original pure structural predicate remains byte-for-byte unchanged.
"""
from __future__ import annotations
from copy import deepcopy
from dataclasses import dataclass
import hashlib, importlib.util, json, re, subprocess, sys
from pathlib import Path, PurePosixPath
from types import MappingProxyType

PARENT='d53dd70d38b0762af130b1d19b795af259f505f5'
PARENT_TREE='12691099f1a155a8bfa3ad4f6689146175b233b2'
ORIGINAL_IMPLEMENTATION_SHA256='95475b33fa3365c96a82a42b70385b17e90ab088ff951501b06468825ba0e20d'
MANIFEST_SHA256='c99ec7acbfe996455525b31088a7d04addd20653787e12098e4e51a4a7ce296e'
FOLDER='research/RHRC/integration/opica_followup/'
FILE_FIELDS={'path','mode','git_blob','bytes','sha256'}
ROLES=frozenset({'PROJECT_RESEARCH_INSTRUCTIONS_NO_THEOREM_AUTHORITY',
 'CONTINUATION_RESEARCH_DOCUMENT_OR_LOG','CONTINUATION_SOURCE_PINNED_EVIDENCE_OR_METADATA',
 'CONTINUATION_AUDIT_LEAN_SOURCE_REQUIRES_EXACT_CLASS_REVIEW','CONTINUATION_AUDIT_RUNTIME_SOURCE'})

def require(ok, message):
    if not ok:
        raise ValueError(message)

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()

def digest(data):
    return hashlib.sha256(data).hexdigest()

def unique_json(data):
    def pairs(items):
        out = {}
        for key, value in items:
            require(key not in out, 'duplicate JSON key: ' + key)
            out[key] = value
        return out
    return json.loads(data, object_pairs_hook=pairs)

def safe_path(value):
    require(isinstance(value, str) and value and '\\' not in value and ':' not in value,
            'unsafe exact path')
    require(not PurePosixPath(value).is_absolute() and
            all(p not in {'', '.', '..'} for p in value.split('/')), 'unsafe exact path')
    return value

def file_map(rows):
    require(isinstance(rows, list), 'file rows required')
    out, folded = {}, set()
    for row in rows:
        require(isinstance(row, dict) and set(row) == FILE_FIELDS, 'exact file identity fields required')
        name = safe_path(row['path'])
        require(name not in out and name.casefold() not in folded, 'duplicate or case-aliased exact path')
        require(row['mode'] in {'100644', '100755'}, 'symlink or unsupported mode')
        require(isinstance(row['bytes'], int) and not isinstance(row['bytes'], bool) and row['bytes'] >= 0,
                'invalid byte count')
        require(isinstance(row['git_blob'], str) and re.fullmatch('[0-9a-f]{40}', row['git_blob']), 'invalid Git blob')
        require(isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']), 'invalid SHA256')
        out[name] = deepcopy(row)
        folded.add(name.casefold())
    return out

def inventory_digest(rows):
    files = file_map(rows)
    return digest(canonical([files[p] for p in sorted(files)]))

def strict_imports(text):
    """Conservative source import census, not a Lean proof-use dependency graph."""
    out, i, depth, string, escaped = [], 0, 0, False, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            ch = text[i]; out.append(ch); i += 1
            if escaped: escaped = False
            elif ch == '\\': escaped = True
            elif ch == '"': string = False
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n': out.append(' '); i += 1
        elif text.startswith('/-', i): depth = 1; out.extend('  '); i += 2
        else:
            ch = text[i]; out.append(ch); i += 1
            if ch == '"': string = True
    require(depth == 0 and not string, 'unterminated source comment/string')
    result = []
    for line in ''.join(out).splitlines():
        match = re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.*)$', line)
        if match:
            tokens = match.group(1).split()
            require(tokens and all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9\x27]*(?:\.[A-Za-z_][A-Za-z_0-9\x27]*)*', t)
                                   for t in tokens), 'ambiguous import tokens')
            result.extend(tokens)
    require(len(result) == len(set(result)), 'duplicate direct imports')
    return result

def source_import_snapshot(blobs, manifest, added_audit_paths):
    snapshots, project_diffs = [], []
    graph = {}
    for name, content in blobs.items():
        if name.endswith('.lean'):
            try:
                graph[name[:-5].replace('/', '.')] = strict_imports(content.decode('utf8'))
            except (ValueError, UnicodeDecodeError):
                # Non-exported historical/audit syntax is not silently treated
                # as a leaf if actually reached below.
                graph[name[:-5].replace('/', '.')] = None
    for module in manifest['modules']:
        source = blobs[module['path']]
        actual = strict_imports(source.decode('utf8'))
        project = [m for m in actual if m == 'Zeta23' or m.startswith('Zeta23.')]
        row = {'module':module['module'], 'path':module['path'], 'source_sha256':digest(source),
               'actual_all_ordered_imports':actual, 'actual_direct_project_imports':project,
               'frozen_planned_project_imports':module['direct_project_imports']}
        snapshots.append(row)
        if project != module['direct_project_imports']:
            project_diffs.append(row)
    seen, todo = set(), ['Zeta23.OPICAFollowup']
    while todo:
        module = todo.pop()
        if module in seen: continue
        seen.add(module)
        if module not in graph: continue  # External Mathlib/Lean, separately compiled.
        require(graph[module] is not None, 'unsupported source import syntax in mathematical closure: '+module)
        todo.extend(graph[module])
    reached = sorted(p for p in added_audit_paths if p.endswith('.lean') and p[:-5].replace('/', '.') in seen)
    return snapshots, project_diffs, reached

def load_original(repo):
    source = Path(repo) / FOLDER / 'parent_extension.py'
    require(digest(source.read_bytes()) == ORIGINAL_IMPLEMENTATION_SHA256,
            'original parent projection implementation changed')
    name = '_opica_original_extension_for_exact_amendment'
    spec = importlib.util.spec_from_file_location(name, source)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

def git(repo, *args, input=None):
    return subprocess.run(['git', '--no-optional-locks', '-C', str(repo), *args],
                          input=input, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout

def capture_commit(repo, commit):
    require(re.fullmatch('[0-9a-f]{40}', commit), 'exact committed source pin required')
    require(git(repo, 'rev-parse', commit+'^{commit}').decode().strip() == commit, 'commit alias rejected')
    tree = git(repo, 'rev-parse', commit+'^{tree}').decode().strip()
    entries = []
    for item in git(repo, 'ls-tree', '-r', '-z', commit).split(b'\0'):
        if not item:
            continue
        meta, raw_path = item.split(b'\t', 1)
        mode, kind, oid = meta.decode('ascii').split()
        name = safe_path(raw_path.decode('utf8'))
        require(kind == 'blob' and mode in {'100644', '100755'}, 'unsupported committed source entry')
        entries.append((name, mode, oid))
    stream = git(repo, 'cat-file', '--batch', input=('\n'.join(r[2] for r in entries)+'\n').encode())
    cursor, rows, blobs = 0, [], {}
    for name, mode, expected in entries:
        end = stream.index(b'\n', cursor)
        oid, kind, raw_size = stream[cursor:end].decode('ascii').split()
        size = int(raw_size)
        data = stream[end+1:end+1+size]
        cursor = end+2+size
        require(kind == 'blob' and oid == expected and len(data) == size and
                hashlib.sha1(b'blob '+str(size).encode()+b'\0'+data).hexdigest() == oid,
                'immutable Git blob stream mismatch')
        rows.append({'path': name, 'mode': mode, 'git_blob': oid, 'bytes': size, 'sha256': digest(data)})
        blobs[name] = data
    require(cursor == len(stream), 'trailing Git blob stream')
    file_map(rows)
    return tree, rows, blobs


@dataclass(frozen=True)
class ExactPolicyContext:
    parent_json: bytes
    exact_allowed_paths: frozenset[str]
    documentation_paths: frozenset[str]
    policy_sha256: str
    actual_commit: str
    actual_tree: str
    actual_source_inventory_sha256: str
    subject_imports_json: bytes


def mutable_original_paths(descriptor):
    """These are exact original authorities, never a new directory exemption."""
    sets = [set(descriptor[key]) for key in
            ['new_exact_paths', 'modified_exact_paths', 'generated_exact_paths']]
    require(all(not (sets[i] & sets[j]) for i in range(3) for j in range(i)),
            'overlapping original path authorities')
    for paths in sets:
        for path in paths:
            safe_path(path)
    return set().union(*sets)


def path_modes(files):
    rows = file_map(files)
    return [{'path': name, 'mode': rows[name]['mode']} for name in sorted(rows)]



AUDIT_CLASSIFICATION_ID = 'opica_followup_exact_continuation_audit_sources'


def exact_audit_classification(additional_rows):
    """Classify only individually bound audit sources, with no theorem authority."""
    paths = sorted(row['file']['path'] for row in additional_rows
                   if row['file']['path'].endswith('.lean'))
    require(len(paths) == len(set(paths)), 'duplicate audit classification subject')
    for row in additional_rows:
        if row['file']['path'].endswith('.lean'):
            safe_path(row['file']['path'])
            require(row['role'] == 'CONTINUATION_AUDIT_LEAN_SOURCE_REQUIRES_EXACT_CLASS_REVIEW'
                    and row['theorem_authority'] == 'NONE', 'non-audit classification subject')
    if not paths:
        return None
    return {'id': AUDIT_CLASSIFICATION_ID,
            'pattern': r'\A(?:' + '|'.join(re.escape(path) for path in paths) + r')\Z',
            'file_class': 'RESEARCH_FIXTURE', 'trust_zone': 'AUDIT_ONLY'}


def project_exact_audit_classification(classes, additional_rows, bound_rule):
    expected = exact_audit_classification(additional_rows)
    require(bound_rule == expected, 'exact audit classification policy differs')
    result = deepcopy(classes)
    rules = result['rules']
    indices = [i for i, row in enumerate(rules) if row.get('id') == AUDIT_CLASSIFICATION_ID]
    if expected is None:
        require(indices == [], 'unexpected audit classification without subjects')
        return result
    generic = [i for i, row in enumerate(rules) if row.get('id') == 'zeta_lean']
    require(len(indices) == len(generic) == 1 and indices[0] == generic[0] - 1
            and rules[indices[0]] == expected, 'actual exact audit classification or position differs')
    for row in additional_rows:
        name = row['file']['path']
        if name.endswith('.lean'):
            selected = next((rule for rule in rules if re.search(rule['pattern'], name)), None)
            require(selected == expected, 'audit source first-match classification differs: ' + name)
    rules.pop(indices[0])
    return result



AUDIT_ARTIFACT_CLASSIFICATION_ID = 'opica_followup_exact_continuation_audit_artifacts'


def exact_audit_artifact_classification(additional_rows):
    """An exact last-resort classification, preserving all prior first matches."""
    selected = [row for row in additional_rows if not row['file']['path'].endswith('.lean')]
    paths = sorted(safe_path(row['file']['path']) for row in selected)
    require(len(paths) == len(set(paths)), 'duplicate audit artifact subject')
    require(all(row['role'] in ROLES and row['theorem_authority'] == 'NONE' for row in selected),
            'non-audit artifact classification subject')
    if not paths:
        return None
    return {'id': AUDIT_ARTIFACT_CLASSIFICATION_ID,
            'pattern': r'\A(?:' + '|'.join(re.escape(path) for path in paths) + r')\Z',
            'file_class': 'RESEARCH_FIXTURE', 'trust_zone': 'AUDIT_ONLY'}


def project_exact_audit_artifact_classification(classes, additional_rows, bound_rule):
    expected = exact_audit_artifact_classification(additional_rows)
    require(bound_rule == expected, 'exact audit artifact policy differs')
    result = deepcopy(classes)
    rules = result['rules']
    indices = [i for i, row in enumerate(rules) if row.get('id') == AUDIT_ARTIFACT_CLASSIFICATION_ID]
    if expected is None:
        require(indices == [], 'unexpected artifact classification without subjects')
        return result
    require(len(indices) == 1 and indices[0] == len(rules) - 1 and rules[-1] == expected,
            'actual exact audit artifact fallback or last position differs')
    rules.pop()
    return result



def original_planned_lock_classification():
    """Classify the one named frozen dependency lock; grant no new path."""
    return {'id': 'opica_followup_original_planned_python_lock',
            'pattern': r'\A' + re.escape(FOLDER + 'python-checks.lock') + r'\Z',
            'file_class': 'RESEARCH_FIXTURE', 'trust_zone': 'AUDIT_ONLY'}


def project_original_planned_lock_classification(classes, bound_rule, planned_creates):
    require(FOLDER + 'python-checks.lock' in planned_creates,
            'named dependency lock is not an original frozen planned path')
    expected = original_planned_lock_classification()
    require(bound_rule == expected, 'original planned lock classification policy differs')
    result = deepcopy(classes)
    rules = result['rules']
    indices = [i for i, row in enumerate(rules) if row.get('id') == expected['id']]
    require(len(indices) == 1 and indices[0] == len(rules) - 1 and rules[-1] == expected,
            'actual original planned lock classification or position differs')
    rules.pop()
    return result


def policy_from_v1(candidate, files, descriptor_bytes):
    """Prepare V2 review input; this never supplies independent review authority."""
    descriptor = unique_json(descriptor_bytes)
    policy = {key: deepcopy(candidate[key]) for key in [
        'parent_head', 'parent_tree', 'descriptor_sha256', 'roots_sha256',
        'manifest_sha256', 'original_projection_sha256', 'additional_exact_paths',
        'protected_documentation_edits', 'direct_import_snapshots',
        'claim_or_type_amendments', 'new_primary_roots']}
    policy.update({'schema': 'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V2',
        'status': 'UNACCEPTED_EXACT_SUBJECT_REVIEW_INPUT',
        'reviewed_against_commit': candidate['checked_commit'],
        'reviewed_against_tree': candidate['checked_tree'],
        'complete_path_mode_census': path_modes(files),
        'additional_audit_file_class': exact_audit_classification(policy['additional_exact_paths']),
        'additional_audit_artifact_file_class': exact_audit_artifact_classification(policy['additional_exact_paths']),
        'original_planned_artifact_file_class': original_planned_lock_classification(),
        'original_content_authorities': sorted(mutable_original_paths(descriptor)),
        'separate_required_gates': [
            'FULL100_INDEPENDENT_SEMANTIC_TYPE_DOMAIN_DEFINITION_UNIT_REVIEW',
            'ACTUAL_CURRENT_FULL_COMPILER_SOURCE_TYPE_AXIOM_PRIVATE_DEPENDENCY_RECEIPT',
            'ACCEPTED_PARENT_AND_CURRENT_CHILD_P0_COMPILER_PRESERVATION',
            'EXACT_RUNTIME_REGRESSION_CANONICAL_AND_WORKFLOW_COMPANIONS'],
        'policy_grants_theorem_authority': False, 'RH': 'OPEN', 'Step4': 'OPEN'})
    return policy


def validate_policy_context(raw, parent, contract, policy_bytes, trusted_digest, original):
    """Authenticate exact subjects, then call the unchanged structural predicate.

    The checked HEAD and ALL actual bytes remain in raw/cold receipts. They are
    not inside the policy digest, whose original mutable paths derive solely
    from the frozen descriptor. This prevents seal-holder self-reference.
    """
    require(isinstance(trusted_digest, str) and re.fullmatch('[0-9a-f]{64}', trusted_digest),
            'no independently reviewed exact-subject policy anchor is configured')
    require(isinstance(policy_bytes, bytes) and digest(policy_bytes) == trusted_digest,
            'policy differs from independently trusted exact-subject anchor')
    policy = unique_json(policy_bytes)
    require(policy.get('schema') == 'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V2', 'unknown exact policy schema')
    require(policy.get('parent_head') == PARENT and policy.get('parent_tree') == PARENT_TREE,
            'immutable parent identity changed')
    require(policy.get('descriptor_sha256') == digest(contract['descriptor_bytes']) and
            policy.get('roots_sha256') == digest(contract['roots_bytes']), 'frozen descriptor/root differs')
    require(digest(contract['manifest_bytes']) == MANIFEST_SHA256 and
            policy.get('manifest_sha256') == MANIFEST_SHA256, 'frozen manifest differs')
    require(policy.get('original_projection_sha256') == ORIGINAL_IMPLEMENTATION_SHA256,
            'original pure projection implementation differs')
    for field in ['reviewed_against_commit', 'reviewed_against_tree']:
        require(isinstance(policy.get(field), str) and re.fullmatch('[0-9a-f]{40}', policy[field]),
                'review provenance requires exact Git identity')
    for field in ['checked_commit', 'checked_tree']:
        require(isinstance(raw.get(field), str) and re.fullmatch('[0-9a-f]{40}', raw[field]),
                'actual current source identity is missing')
    files, old = file_map(raw['files']), file_map(parent['files'])
    require(policy.get('complete_path_mode_census') == path_modes(raw['files']),
            'complete current path/mode census differs')
    descriptor = unique_json(contract['descriptor_bytes'])
    mutable = mutable_original_paths(descriptor)
    require(policy.get('original_content_authorities') == sorted(mutable),
            'content exclusions differ from exact original descriptor authorities')
    creates = set(descriptor['new_exact_paths'])
    exceptions = set(descriptor['modified_exact_paths']) | set(descriptor['generated_exact_paths'])
    require(set(old) | creates <= set(files), 'missing parent or original planned path')
    extras = policy.get('additional_exact_paths')
    require(isinstance(extras, list), 'exact extra-file subjects required')
    extra = file_map([row['file'] for row in extras])
    require(set(extra) == set(files) - set(old) - creates, 'unlisted or missing extra-file identity')
    for row in extras:
        name = row['file']['path']
        require(row['file'] == files[name], 'exact extra-file bytes changed: ' + name)
        require(row.get('role') in ROLES and row.get('theorem_authority') == 'NONE',
                'unsupported role or theorem promotion: ' + name)
        require(row.get('review_status') == 'OPEN_REQUIRES_INDEPENDENT_REVIEW',
                'inventory status cannot manufacture approval')
        if name.endswith('.lean'):
            require(row['role'] == 'CONTINUATION_AUDIT_LEAN_SOURCE_REQUIRES_EXACT_CLASS_REVIEW',
                    'extra Lean source acquired mathematical authority')
        if name == 'AGENTS.md':
            require(row['role'] == 'PROJECT_RESEARCH_INSTRUCTIONS_NO_THEOREM_AUTHORITY',
                    'instruction file acquired theorem authority')
    docs = policy.get('protected_documentation_edits')
    require(isinstance(docs, list), 'exact original/current documentation subjects required')
    changed = {name for name in old if name not in exceptions and files[name] != old[name]}
    doc_names = [row['current']['path'] for row in docs]
    require(len(doc_names) == len(set(doc_names)) and set(doc_names) == changed,
            'protected file changes differ from exact documentation subjects')
    for row in docs:
        name = safe_path(row['current']['path'])
        require(name.endswith(('.md', '.txt')) and row.get('role') == 'DOCUMENTATION_ONLY_NO_THEOREM_AUTHORITY',
                'protected mathematical/runtime/config change disguised as documentation')
        require(row['original'] == old[name] and row['current'] == files[name],
                'protected document original/current bytes changed')
    imports = policy.get('direct_import_snapshots')
    require(isinstance(imports, list) and imports == raw.get('direct_import_snapshots'),
            'actual ordered imports or their exact source bytes changed')
    manifest = unique_json(contract['manifest_bytes'])
    require([(row['module'], row['path']) for row in imports] ==
            [(row['module'], row['path']) for row in manifest['modules']],
            'complete ordered frozen43-module subjects required')
    for row in imports:
        require(row['source_sha256'] == files[row['path']]['sha256'],
                'mathematical/audit module source not bound to actual source census')
    require(raw.get('added_audit_sources_in_math_facade') == [], 'audit source reached mathematical facade')
    require(policy.get('claim_or_type_amendments') == [] and policy.get('new_primary_roots') == 0
            and policy.get('policy_grants_theorem_authority') is False,
            'path policy cannot change claims/types or grant theorem authority')
    expected_gates = policy_from_v1({**policy, 'checked_commit':policy['reviewed_against_commit'],
                                    'checked_tree':policy['reviewed_against_tree']}, raw['files'],
                                   contract['descriptor_bytes'])['separate_required_gates']
    require(policy.get('separate_required_gates') == expected_gates, 'separate original release gates removed')
    require(policy.get('RH') == 'OPEN' and policy.get('Step4') == 'OPEN', 'claim firewall changed')
    metadata = deepcopy(raw)
    metadata['files'] = [deepcopy(old[name] if name in changed else files[name])
                         for name in files if name not in extra]
    metadata['file_classes'] = project_exact_audit_artifact_classification(
        metadata['file_classes'], extras, policy.get('additional_audit_artifact_file_class'))
    metadata['file_classes'] = project_original_planned_lock_classification(
        metadata['file_classes'], policy.get('original_planned_artifact_file_class'), creates)
    metadata['file_classes'] = project_exact_audit_classification(
        metadata['file_classes'], extras, policy.get('additional_audit_file_class'))
    original_context = original.validate_extension_context(metadata, parent, contract)
    projected = dict(original.project_parent_context(original_context))
    require(projected == {key:parent[key] for key in
            ['claim_registry','theorem_bindings','file_classes','semantic_closure']},
            'immutable parent values changed')
    allowed = original.allowed_child_delta(original_context) | set(extra) | changed
    return ExactPolicyContext(canonical(projected), frozenset(allowed), frozenset(changed),
        trusted_digest, raw['checked_commit'], raw['checked_tree'], inventory_digest(raw['files']),
        canonical(imports))


def project(context):
    require(isinstance(context, ExactPolicyContext), 'raw context cannot be projected')
    return MappingProxyType(unique_json(context.parent_json))


def regular_source(repo, relative):
    safe_path(relative)
    repo = Path(repo).absolute()
    path = repo / relative
    for part in [path, *path.parents]:
        if part.is_relative_to(repo):
            require(not part.is_symlink() and not getattr(part, 'is_junction', lambda:False)(),
                    'symlink/junction in actual source path: ' + relative)
    require(path.is_file() and path.resolve() == repo.resolve()/relative,
            'missing, escaped or aliased source: ' + relative)
    return path


def capture_working_source(repo):
    """Keep all actual bytes/head for independent cold/compiler gates."""
    require(not git(repo, 'status', '--porcelain', '--untracked-files=all').strip(),
            'source checkout must be completely clean')
    head = git(repo, 'rev-parse', 'HEAD').decode().strip()
    tree, files, blobs = capture_commit(repo, head)
    for row in files:
        data = regular_source(repo, row['path']).read_bytes()
        require(data == blobs[row['path']], 'actual bytes differ from checked Git object: '+row['path'])
    require(git(repo, 'rev-parse', 'HEAD').decode().strip() == head and
            not git(repo, 'status', '--porcelain', '--untracked-files=all').strip(),
            'source changed during actual working-source capture')
    return head, tree, files, blobs


def source_bound_context(repo, policy, trusted_digest, parent_helpers):
    """Production provider; authentic caller supplies an independently reviewed anchor.

    No caller boolean, status string, raw registry or freshly calculated digest
    becomes a trusted review. The parent reader's default anchor remains None.
    """
    require(isinstance(trusted_digest, str) and re.fullmatch('[0-9a-f]{64}', trusted_digest),
            'no independently reviewed exact-subject policy anchor is configured')
    require(digest(canonical(policy)) == trusted_digest, 'policy differs from independently trusted anchor')
    head, tree, files, blobs = capture_working_source(repo)
    register = unique_json(blobs[FOLDER+'SOURCE_REGISTER.json'])
    require(register.get('exact_source_extension_policy') == policy, 'policy differs from actual SOURCE_REGISTER')
    baseline = unique_json(blobs[FOLDER+'PROTECTED_STATE.json'])
    parent_helpers._source_bound_parent_baseline(Path(repo), baseline)
    roots_bytes = blobs[FOLDER+'PUBLIC_ROOTS.json']
    roots = unique_json(roots_bytes)['roots']
    workflow = unique_json(blobs[FOLDER+'WORKFLOW_CONTRACT.json'])
    claims, bindings = parent_helpers._reviewed_child_objects(Path(repo), roots, register, workflow,
        parent_claims=baseline['claim_registry']['claims'])
    manifest_bytes = blobs[FOLDER+'BUILD_MANIFEST.json']
    manifest = unique_json(manifest_bytes)
    extra_paths = [row['file']['path'] for row in policy['additional_exact_paths']]
    snapshots, _, reached = source_import_snapshot(blobs, manifest, extra_paths)
    raw = {'parent_head':baseline['parent_head'], 'parent_tree':PARENT_TREE, 'checked_commit':head,
           'checked_tree':tree, 'files':files, 'direct_import_snapshots':snapshots,
           'added_audit_sources_in_math_facade':reached}
    for key, path in parent_helpers.FOLLOWUP_GLOBAL_FILES.items():
        raw[key] = unique_json(blobs[path])
    contract = {'descriptor_bytes':blobs[FOLDER+'PARENT_EXTENSION.json'], 'roots_bytes':roots_bytes,
        'manifest_bytes':manifest_bytes, 'reviewed_claim_objects':claims, 'reviewed_binding_objects':bindings}
    original = load_original(repo)
    context = validate_policy_context(raw, baseline, contract, canonical(policy), trusted_digest, original)
    require(head == git(repo, 'rev-parse', 'HEAD').decode().strip() and
            not git(repo, 'status', '--porcelain', '--untracked-files=all').strip(),
            'source changed during source-bound projection')
    return context
