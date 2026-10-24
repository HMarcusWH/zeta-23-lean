"""Preparation gate for the full, still incomplete OPICA follow-up.

A preflight pass validates frozen inputs and parent preservation. It cannot
establish mathematical coverage, register a theorem, or open the release gate.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PROTECTED_SHA256 = 'c62aad1d5dba23e0413f084a4deb9ecdaeb655e803fe809cd603c8efc7bc1779'
FROZEN_SPEC = {
    'BUILD_SPEC.md': 'cacab08834aeb9badd578d90828be99cff33c7a617c609e75bb878eb5fa3b29c',
    'BUILD_MANIFEST.json': 'c99ec7acbfe996455525b31088a7d04addd20653787e12098e4e51a4a7ce296e',
    'PUBLIC_ROOTS.json': '2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41',
    'PAPER_CROSSWALK.json': '9e1252631f26fb81f4a5c60ac714e483c076be5c9858e25056e3835933ce6451',
    'PARENT_EXTENSION.json': '2b88b5497861679e6b1f686af6c8b5b7dbe5a5887841be43d862ba9836187ac3',
}
FROZEN_PAPER = {
    'OPICA_Followup_Final_Audited_Paper_2026-10-21.md':
        '9525d5dad6f0a2e3abd6050edeb39e3a234b6a361046e746878a181970a789f0',
}
AMENDMENT_V11_SHA256 = '16bb41d7ecc1b199ed97ace5ba37beb5ffc691ca648b4bc12597911be7250cbd'
C1_SUPPORTING_DECLARATIONS = (
    'sharpNormAlpha', 'sharpNormAlpha_pos', 'sharpNormAlpha_one_le',
    'sharpNormAlpha_le_one_add', 'sharpNormAlpha_quadratic', 'sharpNormAlpha_sub_inv',
    'sharpNormAlpha_zero', 'sharpNormAlpha_log_eq_arsinh',
    'sharp_norm_first_scalar_identity', 'sharp_norm_first_scalar_bound',
    'sharp_norm_first_log_upper', 'sharp_norm_first_log_norms',
    'sharp_norm_first_arsinh_bound', 'sharp_norm_first_scalar_attained',
    'sharp_norm_first_log_comparison',
)
C1_EXPECTED_TYPE_CONSUMERS = (
    'expected_sharp_norm_first_arsinh_bound',
    'expected_sharp_norm_first_scalar_attained',
    'expected_sharp_norm_first_log_comparison',
    'expected_sharp_norm_first_recovers_primary',
)
C1_EXPECTED_TYPE_CHECKS = ('Validation.lean explicitly checks sharp bound, equality witness, '
    'positive-part bound and recovery of original primary comparison.')
DEPENDENCY_REFINEMENTS = {
    'Zeta23.OPICAFollowup.NativeSourceFamily': [
        'Zeta23.CCM.OriginalSincNativeSource',
        'Zeta23.CCM.UniversalSincInverseGevreyBounds',
        'Zeta23.CCM.OriginalSincWeightedPoleMoments',
        'Zeta23.CCM.NativeIntegerPrimeConvolution'],
    'Zeta23.OPICAFollowup.BalancedCoefficients': ['Zeta23.OPICA.NativeArithmeticAdapter'],
    'Zeta23.OPICAFollowup.Counterexamples': [
        'Zeta23.OPICAFollowup.NormFirstTransfer', 'Zeta23.OPICAFollowup.JointObservation'],
    'Zeta23.OPICAFollowup.NativeSourceTransforms': [
        'Zeta23.OPICAFollowup.NativeSourceFamily', 'Zeta23.OPICA.LocalData',
        'Zeta23.CCM.NativeIntegerDriveComplexLaplace', 'Zeta23.CCM.NativeIntegerPrimeConvolution',
        'Zeta23.ExceptionalZero.NativeOriginalSourceLaplaceVisibility',
        'Zeta23.ExceptionalZero.NativeZeroJetAnalyticFactors'],
    'Zeta23.OPICAFollowup.NativeExplicitFormula': [
        'Zeta23.RvM.LocalCount', 'Zeta23.WeilEF.Main', 'Zeta23.OPICAFollowup.NativeSourceTransforms',
        'Zeta23.CCM.DictionaryArchSourceBridge', 'Zeta23.GammaFacts.Complete'],
    'Zeta23.OPICAFollowup.ZetaLeftLineBounds': [
        'Zeta23.RvM.ZetaGrowth', 'Zeta23.GammaFacts.Complete', 'Zeta23.Analytic.Stirling', 'Zeta23.WeilEF.VerticalLine',
        'Zeta23.OPICAFollowup.SourceVerticalBounds'],
    'Zeta23.OPICAFollowup.NativeFilters': [
        'Zeta23.OPICAFollowup.NativeSourceTransforms', 'Zeta23.OPICA.NativeArithmeticAdapter',
        'Zeta23.CCM.NativeCompactTranslateCalculus'],
    'Zeta23.OPICAFollowup.NativeTransformationWords': [
        'Zeta23.OPICAFollowup.NativeFilters', 'Zeta23.OPICA.LocalObstruction'],
    'Zeta23.OPICAFollowup.UniformSourceBounds': [
        'Zeta23.OPICAFollowup.NativeExplicitFormula', 'Zeta23.OPICAFollowup.SourceVerticalBounds',
        'Zeta23.CCM.UniversalSincInverseGevreyBounds', 'Zeta23.CCM.NativeAbelDiscrepancy',
        'Zeta23.CCM.OriginalSincDriveLp'],
}
DEPENDENCY_V1_SHA256 = '32f2c2e57743f5c1a98176ac64f3b2671e8c45f8355361130ff0271361105a91'
DEPENDENCY_V2_SHA256 = '54aa023b5d2c483abab95b696381ad7ce6eaeb7a1b17e66c2ce80eee2aed78e7'
CONTINUATION_MANIFEST_SHA256 = '1f4accffab9b27205b17f097c2a7a40e96790c28ad01c2c12266d5b0f1664f60'
CONTINUATION_FOLDER = 'research/RHRC/integration/opica_followup'
CONTINUATION_ARTIFACT_PREFIX = CONTINUATION_FOLDER + '/continuation/2026-10-22/'
CONTINUATION_DOCUMENTATION_PATHS = frozenset({
    'AUDIT.md',
    'FORK_NOTES.md',
    'research/RHRC/DOCUMENTATION_AUTHORITY.md',
    'research/RHRC/VALIDATION_PROTOCOL.md',
    'research/RHRC/graph/README.md',
    'research/RHRC/integration/README.md',
    'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md',
})


def continuation_checkpoint(root: Path, here: Path) -> tuple[set[str], list[str]]:
    """Authorize exact pinned draft artifacts only; never sources or proof authority.

    Any invalid record rejects the entire exception. The frozen create/modify
    inventory and mathematical release requirements remain separate inputs.
    """
    root, here = Path(root).absolute(), Path(here).absolute()
    manifest_relative = CONTINUATION_FOLDER + '/CONTINUATION_MANIFEST.json'
    errors = []

    def reject(message):
        raise ValueError(message)

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                reject('duplicate checkpoint JSON key: ' + key)
            result[key] = value
        return result

    def regular_file(relative):
        if (not isinstance(relative, str) or not relative
                or '\\' in relative or ':' in relative
                or any(part in {'', '.', '..'} for part in relative.split('/'))
                or any(ord(char) < 32 or ord(char) == 127 for char in relative)):
            reject('unsafe artifact path')
        path = root / relative
        if any(parent.is_symlink() for parent in [path, *path.parents]
               if parent.is_relative_to(root)):
            reject('symlink in checkpoint path: ' + relative)
        resolved_root, resolved_path = root.resolve(), path.resolve()
        if (not path.is_file() or not resolved_path.is_relative_to(resolved_root)
                or resolved_path != resolved_root / relative):
            reject('missing or escaped checkpoint file: ' + relative)
        return path

    try:
        if here != root / CONTINUATION_FOLDER:
            reject('checkpoint location differs from exact child directory')
        data = regular_file(manifest_relative).read_bytes()
        if hashlib.sha256(data).hexdigest() != CONTINUATION_MANIFEST_SHA256:
            reject('unreviewed continuation manifest bytes')
        document = json.loads(data, object_pairs_hook=unique_object)
        required = {
            'schema': 'OPICA_CONTINUATION_CHECKPOINT_V1',
            'id': 'CP_2026_10_22_01',
            'status': 'DRAFT_NO_FULL_ACCEPTANCE',
            'base_commit': '9b6a9a3a2badb4cff62a56c1158d9cef8759d30d',
            'parent_commit': 'd53dd70d38b0762af130b1d19b795af259f505f5',
            'original_primary_roots': 100,
            'acceptance_units': 28,
            'frozen_public_roots_sha256': '2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41',
            'release_ready': False,
            'RH': 'OPEN', 'Step4': 'OPEN', 'independent_closing_inequalities': 'OPEN',
        }
        if not isinstance(document, dict):
            reject('checkpoint manifest must be an object')
        for key, expected in required.items():
            actual = document.get(key)
            if type(actual) is not type(expected) or actual != expected:
                reject('checkpoint scope or authority changed: ' + key)
        rows = document.get('artifacts')
        if not isinstance(rows, list) or not rows:
            reject('nonempty exact artifact inventory required')
        if any(not isinstance(row, dict) or set(row) != {'path', 'bytes', 'sha256'}
               for row in rows):
            reject('artifact records must contain exactly path, bytes and sha256')
        paths = [row['path'] for row in rows]
        if any(not isinstance(path, str) for path in paths):
            reject('artifact path must be a string')
        if paths != sorted(paths) or len({path.casefold() for path in paths}) != len(paths):
            reject('artifact paths must be sorted and unique, including case aliases')
        verified = set()
        for row in rows:
            relative = row['path']
            if (relative != 'AGENTS.md'
                    and relative not in CONTINUATION_DOCUMENTATION_PATHS
                    and not relative.startswith(CONTINUATION_ARTIFACT_PREFIX)):
                reject('artifact outside exact continuation scope: ' + relative)
            if (type(row['bytes']) is not int or row['bytes'] < 0
                    or not isinstance(row['sha256'], str)
                    or re.fullmatch('[0-9a-f]{64}', row['sha256']) is None):
                reject('invalid artifact byte count or SHA256: ' + relative)
            payload = regular_file(relative).read_bytes()
            if len(payload) != row['bytes'] or hashlib.sha256(payload).hexdigest() != row['sha256']:
                reject('checkpoint artifact bytes changed: ' + relative)
            verified.add(relative)
        return {manifest_relative, *verified}, []
    except (OSError, ValueError, TypeError, KeyError, RecursionError) as exc:
        errors.append('continuation checkpoint rejected: ' + str(exc))
        return set(), errors



PARENT_EXACT_WRAPPER_SHA256 = '08bf4ed8f1e105650d21826c4f20a80cbaa04088160869f578bd483808f053dd'


def exact_policy_context(root: Path):
    """Read a genuine source-bound context; no boolean/status can activate it."""
    register_path = root/'research/RHRC/integration/opica_followup/SOURCE_REGISTER.json'
    register = json.loads(register_path.read_text(encoding='utf-8'))
    if 'exact_source_extension_policy' not in register:
        return None
    path = root/'research/RHRC/integration/opica/validate_contract.py'
    if path.is_symlink() or not path.is_file() or digest(path)!=PARENT_EXACT_WRAPPER_SHA256:
        raise ValueError('exact parent wrapper changed without independent caller review')
    import sys
    name = '_opica_exact_parent_wrapper_for_child_preflight'
    spec = importlib.util.spec_from_file_location(name,path)
    parent = importlib.util.module_from_spec(spec)
    sys.modules[name] = parent
    spec.loader.exec_module(parent)
    return parent._exact_source_extension_context(root)


def _dependency_amendment_errors_v3(register: dict, manifest: dict, root: Path = REPO) -> list[str]:
    """Check the narrow versioned import refinement, separately from proof authority.

    The frozen statements and scope remain inputs; this does not establish that
    importing a proved lemma proves any child theorem.
    """
    errors = []
    exact_context = None
    if 'exact_source_extension_policy' in register:
        try:
            exact_context = exact_policy_context(root)
        except (KeyError,TypeError,ValueError,OSError,subprocess.SubprocessError) as exc:
            errors.append('exact import policy rejected: '+str(exc))
    amendment = register.get('implementation_dependency_amendment', {})
    required = {
        'schema': 'OPICA_IMPLEMENTATION_DEPENDENCY_AMENDMENT_V1',
        'id': 'DEP_2026_10_21_03',
        'supersedes': 'DEP_2026_10_21_02',
        'previous_amendment_sha256': DEPENDENCY_V2_SHA256,
        'status': 'IMPLEMENTATION_ONLY_NO_MATHEMATICAL_SCOPE_CHANGE',
        'frozen_manifest_sha256': FROZEN_SPEC['BUILD_MANIFEST.json'],
        'frozen_public_roots_sha256': FROZEN_SPEC['PUBLIC_ROOTS.json'],
        'primary_roots': 100, 'acceptance_units': 28, 'new_paths': 84,
        'promoted_supporting_lemmas': [], 'theorem_statement_changes': [], 'new_assumptions': [],
        'RH': 'OPEN', 'Step4': 'OPEN', 'independent_closing_inequalities': 'OPEN',
    }
    for key, value in required.items():
        if amendment.get(key) != value:
            errors.append('implementation dependency amendment changed: ' + key)
    history = register.get('implementation_dependency_history', [])
    if (not isinstance(history, list) or len(history) != 2
            or any(hashlib.sha256(json.dumps(row, sort_keys=True, separators=(',', ':'),
                ensure_ascii=False).encode('utf-8')).hexdigest() != expected
                for row, expected in zip(history, [DEPENDENCY_V1_SHA256, DEPENDENCY_V2_SHA256]))):
        errors.append('previous dependency amendment missing or changed')
    rows = amendment.get('rows', [])
    if (not isinstance(rows, list) or len(rows) != len(DEPENDENCY_REFINEMENTS)
            or {r.get('module') for r in rows} != set(DEPENDENCY_REFINEMENTS)):
        return errors + ['exact versioned dependency refinement inventory required']
    plans = {r['module']: r for r in manifest['modules']}
    for row in rows:
        name = row['module']
        plan = plans[name]
        if (row.get('path') != plan['path']
                or row.get('planned_direct_project_imports') != plan['direct_project_imports']
                or row.get('approved_direct_project_imports') != DEPENDENCY_REFINEMENTS[name]
                or not isinstance(row.get('reason'), str) or not row['reason'].strip()
                or row.get('theorem_statement_changes') != [] or row.get('new_assumptions') != []):
            errors.append('unreviewed implementation dependency refinement: ' + name)
        path = root / plan['path']
        actual = (re.findall(r'^import\s+(Zeta23\.[A-Za-z0-9_.]+)\s*$',
                             path.read_text(encoding='utf-8'), re.MULTILINE)
                  if path.is_file() else [])
        if exact_context is None and actual != DEPENDENCY_REFINEMENTS[name]:
            errors.append('implementation imports differ from versioned refinement: ' + name)
    return errors


def lean_declaration_names(source: str) -> list[str]:
    """Lexical inventory only: comments/strings cannot masquerade as declarations.

    This does not elaborate a type or establish a proof; the external source-bound
    compiler receipt has that separate responsibility.
    """
    clean, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        char, pair = source[index], source[index:index + 2]
        if depth:
            if pair == '/-':
                depth += 1
                clean.extend('  ')
                index += 2
            elif pair == '-/':
                depth -= 1
                clean.extend('  ')
                index += 2
            else:
                clean.append('\n' if char == '\n' else ' ')
                index += 1
        elif quoted:
            if char == '\\':
                clean.extend('  ')
                index += 2
            else:
                quoted = char != '"'
                clean.append('\n' if char == '\n' else ' ')
                index += 1
        elif pair == '/-':
            depth = 1
            clean.extend('  ')
            index += 2
        elif pair == '--':
            end = source.find('\n', index)
            if end == -1:
                break
            clean.append('\n')
            index = end + 1
        elif char == '"':
            quoted = True
            clean.append(' ')
            index += 1
        else:
            clean.append(char)
            index += 1
    return re.findall(r'(?m)^(?:@\[[^\]\n]+\]\s*)?(?:noncomputable\s+)?'
                      r'(?:def|lemma|theorem)\s+([A-Za-z_][A-Za-z0-9_]*)\b', ''.join(clean))


def candidate1_source_errors(mathematical_source: str, validation_source: str) -> list[str]:
    """Require the exact optional helper/consumer inventory, without claiming Lean validity."""
    errors = []
    helpers = [name for name in lean_declaration_names(mathematical_source)
               if name.startswith('sharp')]
    consumers = [name for name in lean_declaration_names(validation_source)
                 if name.startswith('expected_sharp_')]
    if helpers != list(C1_SUPPORTING_DECLARATIONS):
        errors.append('C1 optional source helper inventory changed')
    if consumers != list(C1_EXPECTED_TYPE_CONSUMERS):
        errors.append('C1 explicit expected-type consumer inventory changed')
    return errors


def supplemental_errors(register: dict) -> list[str]:
    errors = []
    if register.get('RH') != 'OPEN' or register.get('Step4') != 'OPEN':
        errors.append('top-level supplemental claim firewall changed')
    inputs = register.get('supplemental_research_inputs', [])
    if len(inputs) != 1:
        return ['one exact supplemental v1.1 research input required']
    amendment = inputs[0]
    payload = amendment.get('utf8', '').encode('utf-8')
    if (amendment.get('id') != 'POST_GREEN_V1_1'
            or amendment.get('sha256') != AMENDMENT_V11_SHA256
            or hashlib.sha256(payload).hexdigest() != AMENDMENT_V11_SHA256
            or amendment.get('bytes') != len(payload)):
        errors.append('supplemental source identity changed')
    if (amendment.get('required') is not False or amendment.get('new_mandatory_roots') != []
            or amendment.get('new_paths') != []):
        errors.append('v1.1 may not silently expand primary acceptance scope')
    overlay = register.get('supplemental_crosswalk', [])
    if len(overlay) != 4 or {row.get('candidate_id') for row in overlay} != {
            'POST_GREEN_V1_1_C1', 'POST_GREEN_V1_1_C2', 'POST_GREEN_V1_1_C3', 'POST_GREEN_V1_1_C4'}:
        errors.append('four distinct optional candidate crosswalk rows required')
    for row in overlay:
        if row.get('required') is not False or row.get('new_primary_root_ids') != []:
            errors.append('optional helper promoted without a versioned mandatory amendment')
        if (row.get('RH') != 'OPEN' or row.get('Step4') != 'OPEN'
                or row.get('independent_closing_inequalities') != 'OPEN'):
            errors.append('supplemental claim firewall changed')
        if row.get('candidate_id') == 'POST_GREEN_V1_1_C1':
            if row.get('status') != 'PROVED_LOCAL_OPTIONAL':
                errors.append('C1 local optional proof status changed')
            if row.get('home') != 'Zeta23/OPICAFollowup/NormFirstTransfer.lean':
                errors.append('C1 defining source changed')
            if row.get('supporting_declarations') != list(C1_SUPPORTING_DECLARATIONS):
                errors.append('C1 exact optional helper inventory changed')
            if row.get('expected_type_checks') != C1_EXPECTED_TYPE_CHECKS:
                errors.append('C1 explicit expected-type check description changed')
        if row.get('candidate_id') in {'POST_GREEN_V1_1_C2', 'POST_GREEN_V1_1_C4'} and row.get('status') != 'DERIVED_NOT_FORMALIZED':
            errors.append('unformalized measure proposal promoted')
        if row.get('candidate_id') == 'POST_GREEN_V1_1_C3' and row.get('status') != 'FIRST_INEQUALITY_FALSE_WITHOUT_EPSILON_RANGE_SECOND_BOUND_SURVIVES':
            errors.append('C3 falsification/repaired-domain boundary changed')
    c3_evaluations = [row for row in register.get('amendment_v1_1_evaluation', {}).get('candidates', [])
                      if row.get('id') == 'C3']
    if (len(c3_evaluations) != 1 or c3_evaluations[0].get('counterexample_json_pointer')
            != '/supplemental_crosswalk/2/falsification'):
        errors.append('C3 embedded counterexample pointer missing or changed')
    elif (len(overlay) < 3 or overlay[2].get('candidate_id') != 'POST_GREEN_V1_1_C3'
            or not isinstance(overlay[2].get('falsification'), dict)
            or overlay[2]['falsification'].get('authority')
                != 'DERIVED_ANALYTIC_COUNTEREXAMPLE_NOT_LEAN_FORMALIZED'
            or not {'regularizer', 'measure', 'facts'} <= set(overlay[2]['falsification'])
            or not overlay[2]['falsification'].get('facts')):
        errors.append('C3 embedded counterexample pointer does not resolve to its analytic record')
    return errors


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def metadata_errors(manifest: dict, public: dict, crosswalk: dict, extension: dict) -> list[str]:
    errors = []
    roots = public.get('roots', [])
    if roots != manifest.get('primary_roots'):
        errors.append('manifest/public roots differ')
    for key in ('id', 'full_name'):
        values = [row.get(key) for row in roots]
        if len(values) != 100 or len(set(values)) != 100 or None in values:
            errors.append('exact 100 unique roots required: ' + key)
    units = crosswalk.get('scope_units', [])
    if len(units) != 28 or len({u.get('paper_id') for u in units}) != 28:
        errors.append('28 distinct acceptance units required')
    for unit in units:
        expected = [row['full_name'] for row in roots if unit['paper_id'] in row['paper_ids']]
        if not expected or set(unit['required_roots']) != set(expected):
            errors.append('incomplete crosswalk: ' + unit['paper_id'])
    for descriptor_key, manifest_key in [('new_exact_paths', 'create'),
                                          ('modified_exact_paths', 'modify')]:
        if extension.get(descriptor_key) != [row['path'] for row in manifest[manifest_key]]:
            errors.append('path inventory mismatch: ' + descriptor_key)
    if extension.get('generated_exact_paths') != manifest['regenerate']['paths']:
        errors.append('generated allowlist mismatch')
    if extension.get('child_claim_ids') != [row['id'] for row in roots]:
        errors.append('child root identities differ')
    if manifest.get('delete') or manifest.get('rename'):
        errors.append('deletions/renames forbidden')
    return errors


def exact_preparation_projection(context, protected, root):
    """Accept only the actual strict provider type and its unchanged parent view."""
    import sys
    provider = sys.modules.get(type(context).__module__)
    expected = root/'research/RHRC/integration/opica_followup/exact_extension.py'
    if (provider is None or type(context) is not getattr(provider,'ExactPolicyContext',None)
            or Path(getattr(provider,'__file__','')).resolve()!=expected.resolve()
            or expected.is_symlink() or not expected.is_file()
            or digest(expected)!='0b393f7d1b177a1c497917aa0aaade1355b0512338bc3a143991b4550fae5e44'):
        raise ValueError('genuine strict exact provider context required for preparation projection')
    projected = dict(provider.project(context))
    baseline = {key:protected[key] for key in
        ('claim_registry','theorem_bindings','file_classes','semantic_closure')}
    if projected!=baseline:
        raise ValueError('strict preparation projection changed protected parent values')
    return projected


def preflight(root: Path = REPO, here: Path = HERE, *, full_registry_verified: bool = False) -> dict:
    errors = []
    for name, expected in {**FROZEN_SPEC, 'PROTECTED_STATE.json': PROTECTED_SHA256}.items():
        path = here / name
        if not path.is_file() or path.is_symlink() or digest(path) != expected:
            errors.append('frozen input changed: ' + name)
    if errors:
        return {'status': 'FAIL', 'errors': errors, 'release_ready': False}
    read = lambda name: json.loads((here / name).read_text(encoding='utf-8'))
    manifest, public, crosswalk, descriptor, protected = map(read,
        ('BUILD_MANIFEST.json', 'PUBLIC_ROOTS.json', 'PAPER_CROSSWALK.json',
         'PARENT_EXTENSION.json', 'PROTECTED_STATE.json'))
    checkpoint_paths, checkpoint_errors = continuation_checkpoint(root, here)
    errors += checkpoint_errors
    errors += metadata_errors(manifest, public, crosswalk, descriptor)
    register = read('SOURCE_REGISTER.json')
    errors += supplemental_errors(register)
    errors += dependency_amendment_errors(register, manifest, root)
    exact_context = None
    exact_projection = None
    if 'exact_source_extension_policy' in register:
        try:
            exact_context = exact_policy_context(root)
            exact_projection = exact_preparation_projection(exact_context,protected,root)
        except (KeyError,TypeError,ValueError,OSError,subprocess.SubprocessError) as exc:
            exact_context = None
            errors.append('exact source policy rejected: '+str(exc))
    candidate1_source = root / 'Zeta23/OPICAFollowup/NormFirstTransfer.lean'
    candidate1_validation = root / 'Zeta23/OPICAFollowup/Validation.lean'
    if not candidate1_source.is_file() or not candidate1_validation.is_file():
        errors.append('C1 optional helper/consumer source missing')
    else:
        errors += candidate1_source_errors(candidate1_source.read_text(encoding='utf-8'),
                                           candidate1_validation.read_text(encoding='utf-8'))
    for row in manifest['paper_sources']:
        path = here / 'paper' / row['source']
        if not path.is_file() or len(path.read_bytes()) != row['bytes'] or digest(path) != row['sha256']:
            errors.append('paper source changed: ' + row['source'])
    for name, expected in FROZEN_PAPER.items():
        if digest(here / 'paper' / name) != expected:
            errors.append('controlling paper changed')
    for row in manifest['regression_sources']:
        path = root / row['path']
        if not path.is_file() or len(path.read_bytes()) != row['bytes'] or digest(path) != row['sha256']:
            errors.append('frozen checker changed: ' + row['path'])
    exceptions = (set(descriptor['modified_exact_paths'] + descriptor['generated_exact_paths'])
                  | (checkpoint_paths & CONTINUATION_DOCUMENTATION_PATHS))
    if exact_context is not None:
        exceptions |= set(exact_context.documentation_paths) | set(getattr(exact_context, 'implementation_paths', ()))
    for row in protected['files']:
        path = root / row['path']
        if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
            errors.append('parent path missing/escaped: ' + row['path'])
        elif row['path'] not in exceptions and digest(path) != row['sha256']:
            errors.append('protected parent changed: ' + row['path'])
    # Planned claims are deliberately absent from the global registry.
    # Until the full exact projection and formal gate are wired, require the
    # parent's complete raw registry/config bytes, including all OPEN objects.
    for key, relative in [('claim_registry', 'research/RHRC/CLAIM_REGISTRY.json'),
                           ('theorem_bindings', 'research/RHRC/REGISTERED_THEOREM_BINDINGS.json'),
                           ('file_classes', 'research/RHRC/graph/FILE_CLASSES.json'),
                           ('semantic_closure', 'research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json')]:
        if not full_registry_verified and exact_projection is None and json.loads((root / relative).read_text(encoding='utf-8')) != protected[key]:
            errors.append('pre-registration parent context changed: ' + key)
    creates = {row['path'] for row in manifest['create']}
    parent_paths = {row['path'] for row in protected['files']}
    inventory = subprocess.run(['git', '-C', str(root), 'ls-files', '-z', '--cached',
                                '--others', '--exclude-standard'], check=True,
                               stdout=subprocess.PIPE).stdout.decode().split('\0')
    exact_paths = set(exact_context.exact_allowed_paths) if exact_context is not None else set()
    extra = sorted(set(filter(None, inventory)) - parent_paths - creates - checkpoint_paths - exact_paths)
    if extra:
        errors.append('unlisted files: ' + ', '.join(extra))
    missing = sorted(path for path in creates if not (root / path).is_file())
    return {'schema': 'OPICA_FOLLOWUP_PREPARATION_V1',
            'status': 'FAIL' if errors else 'PASS_PREPARATION_ONLY', 'errors': errors,
            'parent_head': protected['parent_head'], 'parent_tree': protected['parent_tree'],
            'planned_roots': len(public['roots']), 'coverage_units': len(crosswalk['scope_units']),
            'missing_planned_files': missing, 'planned_files_present': len(creates) - len(missing),
            'compiler_coverage_audited': False, 'release_ready': False,
            'continuation_checkpoint': {
                'status': 'REJECTED' if checkpoint_errors else 'HASH_PINNED_ARTIFACT_INVENTORY_ONLY',
                'manifest_sha256': CONTINUATION_MANIFEST_SHA256,
                'verified_artifacts': max(0, len(checkpoint_paths) - 1),
                'proof_established_by_this_gate': False,
                'formal_acceptance': False,
            },
            'optional_candidate1_evidence': {
                'reported_status': 'PROVED_LOCAL_OPTIONAL',
                'checked_here': 'EXACT_METADATA_AND_LEXICAL_SOURCE_INVENTORY_ONLY',
                'expected_type_consumers': list(C1_EXPECTED_TYPE_CONSUMERS),
                'compiler_receipt': 'EXTERNAL_NOT_VALIDATED_BY_PREPARATION',
                'proof_established_by_this_gate': False,
            },
            'release_blockers': ['Full 100-root exact type and physical-consumer coverage pending',
                                 'Complete current-tree P0 and child compiler receipts pending',
                                 'Full regression/runtime lock and canonical generated-state gate pending',
                                 'Parent-extension wrapper and full child CI acceptance pending'],
            'RH': 'OPEN', 'Step4': 'OPEN'}


def full_compiler_gate(formal_receipt: Path, output: Path, *, root: Path = REPO, lake: str = 'lake') -> dict:
    """Validate supplied evidence, then execute a fresh full100 compiler replay.

    This is one release gate. Its success never establishes parent acceptance,
    runtime/regression, generated-state freshness or completed workflow review.
    """
    spec = importlib.util.spec_from_file_location('opica_followup_full_release_builder',
        root/'research/RHRC/integration/opica_followup/build_receipt.py')
    builder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder)
    if formal_receipt.is_symlink() or not formal_receipt.is_file():
        raise ValueError('full compiler receipt must be an actual regular artifact')
    receipt = builder.unique_json(formal_receipt.read_bytes())
    return builder.verify_full_receipt_replay(receipt,root,formal_receipt.parent,
        output.parent/(output.stem+'.fresh-full-replay'),lake)


"""Embedded release companions; external execution after all required jobs finish."""
import os
import shutil
import sys
import time
import zipfile

# Replaced only by the exact independently reviewed capture implementation.
RELEASE_INTAKE_READER_SHA256 = '201b16b4f8b9c3721f14b3271dd397d7c269ddb68f8ce665f8711f90e04a2030'
RELEASE_RUNTIME_LOCK_SHA256 = '1d507a182bcc46d6cb8689b842b87ecf6b1352da3bc70e9c21e81f7b187d3556'
RELEASE_COMPANIONS_STATUS = 'ALL_ORIGINAL_RELEASE_COMPANIONS_EXECUTED_AND_REVALIDATED'


def release_require(condition, message):
    if not condition:
        raise ValueError(message)


def release_artifact(path):
    path = Path(path).absolute()
    for ancestor in (path, *path.parents):
        release_require(not ancestor.is_symlink()
            and not getattr(ancestor, 'is_junction', lambda: False)(),
            'release symlink/junction path is forbidden: '+str(path))
    return path


def write_release_artifact(path, payload):
    path = release_artifact(path)
    release_require(not path.exists(), 'fresh external release artifact required: '+str(path))
    with path.open('xb') as stream:
        stream.write(payload)


def release_json(path):
    path = release_artifact(path)
    release_require(path.is_file(), 'missing actual release artifact: '+str(path))
    def pairs(items):
        result = {}
        for key, value in items:
            release_require(key not in result, 'duplicate release JSON key: '+key)
            result[key] = value
        return result
    return json.loads(path.read_bytes(), object_pairs_hook=pairs,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite release JSON')))


def load_release_intake(root):
    path = release_artifact(root/'research/RHRC/integration/opica_followup/capture_parent.py')
    release_require(path.is_file()
        and hashlib.sha256(path.read_bytes()).hexdigest()==RELEASE_INTAKE_READER_SHA256,
        'reviewed parent intake implementation is missing or changed')
    spec = importlib.util.spec_from_file_location('opica_actual_release_intake',path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def execute_release_command(root, command, output, name, *, environment=None):
    """Execute prescribed commands, retaining failures and exact logs immediately."""
    release_require(isinstance(command,list) and command
        and all(isinstance(token,str) and token for token in command), 'literal release command required')
    release_require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_.-]*\.log',name) is not None,
        'safe release log name required')
    path = release_artifact(output/name)
    release_require(not path.exists() and not path.with_suffix('.command.json').exists(),
        'fresh release command artifacts required')
    env = {key:value for key,value in os.environ.items()
        if not key.upper().startswith(('PYTHON','OPICA_'))
        and key not in ('LEAN_PATH','LEAN_SRC_PATH')}
    env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONUTF8='1',PYTHONNOUSERSITE='1')
    if environment is not None:
        env.update(environment)
    started = time.monotonic()
    timed_out = False
    spawn_error = None
    try:
        result = subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,timeout=14400)
        payload, code = result.stdout, result.returncode
    except subprocess.TimeoutExpired as exc:
        payload, code, timed_out = exc.stdout or b'', -1, True
    except OSError as exc:
        spawn_error = str(exc)
        payload, code = spawn_error.encode('utf-8'), -2
    write_release_artifact(path,payload)
    row = {'argv':command,'exit_code':code,'timed_out':timed_out,'spawn_error':spawn_error,'log':name,
        'log_sha256':hashlib.sha256(payload).hexdigest(),'seconds':time.monotonic()-started}
    write_release_artifact(path.with_suffix('.command.json'),
        (json.dumps(row,indent=2)+'\n').encode('utf-8'))
    release_require(code==0 and not timed_out,'release process failed; preserved evidence: '+str(path))
    return row


def require_complete_unittest_log(path):
    value = release_artifact(path).read_text(encoding='utf-8')
    counts = re.findall(r'(?m)^Ran ([0-9]+) tests? in ',value)
    release_require(len(counts)==1 and int(counts[0])>0
        and re.search(r'(?m)^OK\s*$',value) is not None and 'skipped=' not in value,
        'complete non-skipped unit-test execution required')
    return int(counts[0])


def python_runtime_identity(root, python, output, name):
    row = execute_release_command(root,[python,'-I','-c',
        'import json,sys; print(json.dumps({"version":list(sys.version_info[:3]),"executable":sys.executable}))'],
        output,name)
    value = release_json(output/name)
    release_require(value.get('version')==[3,13,5], 'exact Python3.13.5 required')
    return {'identity':value,'execution':row}


def fresh_locked_scientific_runtime(root, python313, output, *, wheelhouse=None):
    """Install only the two unchanged hash-locked wheels into a fresh venv."""
    lock = release_artifact(root/'research/RHRC/integration/opica_followup/python-checks.lock')
    release_require(lock.is_file()
        and hashlib.sha256(lock.read_bytes()).hexdigest()==RELEASE_RUNTIME_LOCK_SHA256,
        'scientific dependency hash lock changed')
    identity = python_runtime_identity(root,python313,output,'python313-identity.log')
    runtime, wheels = output/'scientific-runtime', output/'locked-wheels'
    release_require(not runtime.exists() and not wheels.exists(), 'fresh runtime and wheel folders required')
    release_artifact(runtime)
    wheels.mkdir()
    commands = []
    if wheelhouse is None:
        commands.append(execute_release_command(root,[python313,'-I','-m','pip','--isolated','download',
            '--only-binary=:all:','--no-deps','--require-hashes','--index-url','https://pypi.org/simple',
            '--dest',str(wheels),'-r',str(lock)],output,'download-locked-wheels.log'))
    else:
        wheelhouse = release_artifact(wheelhouse)
        release_require(wheelhouse.is_dir(), 'actual wheel folder required')
        for source in wheelhouse.iterdir():
            release_require(release_artifact(source).is_file() and source.suffix=='.whl',
                'only regular locked wheels may be supplied')
            shutil.copyfile(source,wheels/source.name)
    expected = set(re.findall(r'--hash=sha256:([0-9a-f]{64})',lock.read_text(encoding='utf-8')))
    actual = {path.name:hashlib.sha256(release_artifact(path).read_bytes()).hexdigest()
        for path in wheels.iterdir() if path.is_file()}
    release_require(len(actual)==2 and len(list(wheels.iterdir()))==2 and set(actual.values())==expected,
        'wheel bytes must exactly match both locked artifacts')
    commands.append(execute_release_command(root,[python313,'-I','-m','venv',str(runtime)],
        output,'create-scientific-runtime.log'))
    python = str(runtime/('Scripts/python.exe' if os.name=='nt' else 'bin/python'))
    # venv's interpreter may itself be a standard interpreter symlink. Every
    # artifact/source/wheel path remains regular, and venv creation was executed.
    commands.append(execute_release_command(root,[python,'-I','-m','pip','--isolated','install',
        '--no-index','--only-binary=:all:','--no-deps','--require-hashes','--find-links',str(wheels),
        '-r',str(lock)],output,'install-locked-wheels.log'))
    versions = execute_release_command(root,[python,'-I','-c',
        'import json,sys,sympy,mpmath; print(json.dumps({"python":list(sys.version_info[:3]),'
        '"sympy":sympy.__version__,"mpmath":mpmath.__version__,"prefix":sys.prefix}))'],
        output,'installed-scientific-runtime.log')
    installed = release_json(output/'installed-scientific-runtime.log')
    release_require(installed.get('python')==[3,13,5] and installed.get('sympy')=='1.14.0'
        and installed.get('mpmath')=='1.3.0' and Path(installed['prefix']).resolve()==runtime.resolve(),
        'fresh locked runtime identity differs')
    commands.append(versions)
    return python, {'runtime':identity,'wheel_sha256':actual,'dependency_lock_sha256':RELEASE_RUNTIME_LOCK_SHA256,
        'fresh_environment':True,'installed_runtime':installed,'commands':commands}


def verify_regression_summary(summary, *, artifacts=None, replay=None):
    release_require(summary.get('schema')=='OPICA_FOLLOWUP_REGRESSION_REPLAY_V1'
        and summary.get('status')=='PASS_FROZEN_REGRESSION_ONLY'
        and summary.get('python')=='3.13.5' and summary.get('python313_runtime') is True
        and summary.get('packages')=={'sympy':'1.14.0','mpmath':'1.3.0'},
        'wrong actual frozen regression runtime/scope')
    release_require(artifacts is not None and replay is not None,
        'actual fresh regression artifacts and unchanged checker inventory required')
    expected = {label:(count,digest) for label,_,count,digest in replay.EXACT}
    release_require({name:row[0] for name,row in expected.items()}
        =={'p0':5112,'round1':18862,'round2':14672,'final':1274},
        'original exact 39920-check inventory changed')
    rows = summary.get('exact',[])
    release_require(len(rows)==8 and {(row['suite'],row['mode']) for row in rows}
        =={(name,mode) for name in expected for mode in ['normal','optimized']},
        'both complete frozen exact modes required')
    retained = []
    exact_status = {'p0':'PASS','round1':'PASS_FINITE_EXACT_CONTROLS_ONLY',
        'round2':'PASS_EXACT_ALGEBRA_CONTROLS_ONLY','final':'PASS_FINITE_EXACT_ONLY'}
    for row in rows:
        result, (count, expected_hash) = row['result'], expected[row['suite']]
        actual_count = replay.exact_count(result)
        release_require(actual_count==count and type(row.get('exit_code')) is int and row['exit_code']==0
            and row.get('expected_checks')==count and row.get('checker_sha256')==expected_hash
            and row.get('executed_script_sha256')==expected_hash,
            'frozen exact count, script or command changed')
        release_require(result.get('status')==exact_status[row['suite']]
            and result.get('script_sha256',result.get('checker_sha256'))==expected_hash
            and result.get('python')=='3.13.5', 'frozen checker disposition or runtime changed')
        if row['suite']!='p0':
            release_require(result.get('optimized') is (row['mode']=='optimized'),
                'frozen checker optimization mode differs')
        retained.append((row,row['suite']+'-'+row['mode']+'.json'))
    numeric = summary.get('numerical',[])
    release_require(len(numeric)==3 and {row['suite'] for row in numeric}=={'copoisson','round2','final'},
        'complete separate numerical stream required')
    hashes = {label:digest for label,_,digest in replay.NUMERIC}
    for row in numeric:
        replay.validate_numeric_scope(row['suite'],row['result'])
        release_require(type(row.get('exit_code')) is int and row['exit_code']==0
            and row.get('checker_sha256')==hashes[row['suite']]
            and row.get('executed_script_sha256')==hashes[row['suite']], 'numeric script/command changed')
        release_require(row['result'].get('script_sha256')==hashes[row['suite']],
            'numeric result is not bound to its executed frozen script')
        retained.append((row,'numeric-'+row['suite']+'.json'))
    total = sum(len(row['result']['cases']) if isinstance(row['result']['cases'],list)
        else row['result']['cases'] for row in numeric)
    release_require(type(total) is int and total==33 and summary.get('interval_certified') is False
        and summary.get('Lean_proof_authority') is False and summary.get('RH')=='OPEN'
        and summary.get('Step4')=='OPEN', 'numerical scope or count promoted')
    records = []
    for row,name in retained:
        path = release_artifact(artifacts/name)
        release_require(row['result']==release_json(path)
            and row.get('receipt_sha256')==hashlib.sha256(path.read_bytes()).hexdigest(),
            'actual fresh checker artifact differs: '+name)
        log = release_artifact(path.with_suffix('.log'))
        release_require(log.is_file(), 'actual checker log missing: '+name)
        records.append({'receipt':name,'receipt_sha256':row['receipt_sha256'],
            'log':log.name,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
    return {'exact_checks_per_mode':39920,'modes':['normal','optimized'],'numerical_cases':33,
        'interval_certified':False,'Lean_proof_authority':False,'artifacts':records}


def unchanged_parent_tool(root, relative):
    protected_path = root/'research/RHRC/integration/opica_followup/PROTECTED_STATE.json'
    release_require(hashlib.sha256(release_artifact(protected_path).read_bytes()).hexdigest()==PROTECTED_SHA256,
        'frozen parent preservation inventory changed')
    rows = [row for row in release_json(protected_path)['files'] if row['path']==relative]
    path = release_artifact(root/relative)
    release_require(len(rows)==1 and path.is_file()
        and hashlib.sha256(path.read_bytes()).hexdigest()==rows[0]['sha256'],
        'original parent execution tool changed: '+relative)
    return path


def require_completed_child_workflow(document, harvester, head, tree):
    """A caller policy cannot turn absence of the configured child CI into release."""
    raw = document.get('raw_collection')
    release_require(isinstance(raw,dict), 'complete raw final workflow inventory required')
    result = harvester.harvest(raw)
    release_require(result['head_sha']==head and result['head_tree']==tree,
        'final child workflow head differs from actual checkout')
    scopes = {(run['event'],run['head_sha']) for run in result['all_workflow_runs']
        if run['path'].split('@',1)[0]==harvester.WORKFLOW and run['head_sha']==head}
    release_require(bool(scopes), 'actual configured current-head child workflow execution is missing')
    jobs = result['effective_jobs']
    counts = []
    for event,source in sorted(scopes):
        selected = [job for job in jobs if job['workflow']==harvester.WORKFLOW
            and job['event']==event and job['head_sha']==source]
        for name,classification in harvester.CHILD_JOBS.items():
            matches = [job for job in selected if job['name']==name]
            release_require(len(matches)==1, 'required actual child job is missing or duplicated: '+name)
            job = matches[0]
            release_require(job.get('required') is True and job.get('classification')==classification
                and job.get('status')=='completed' and job.get('conclusion')=='success'
                and job.get('review_status')=='RECORDED_NOT_INDEPENDENT_APPROVAL'
                and job.get('review',{}).get('checked_tree')==tree,
                'required actual child job incomplete or unreviewed: '+name)
        counts.append({'event':event,'head_sha':source,'original_required_job_instances':len(harvester.CHILD_JOBS)})
    return {'status':'ALL_ORIGINAL_CHILD_JOBS_COMPLETED_AND_REVIEWED_IN_EACH_ACTUAL_SCOPE','scopes':counts}


def full_release_companions(args, output, *, root=REPO):
    """Fresh execution and source/provider revalidation; no status-only authority."""
    root, output = Path(root).resolve(), release_artifact(output)
    release_require(not output.resolve().is_relative_to(root), 'release companion output must be external')
    release_require(args.parent_intake is not None and args.parent_formal_receipt is not None,
        'accepted parent intake and actual current-child P0 compiler artifacts are required')
    release_require(args.workflow_harvest is not None,
        'completed final workflow harvest with genuine independent output reviews required')
    intake = load_release_intake(root)
    output.mkdir(exist_ok=False)
    exact = intake.load_evidence_tool(root,'research/RHRC/integration/opica_followup/exact_extension.py',
        'opica_release_exact_source',intake.EXACT_SOURCE_READER_SHA256)
    head,tree,source_before,_ = exact.capture_working_source(root)
    write_release_artifact(output/'source-binding.json',(json.dumps({'checked_commit':head,'checked_tree':tree,
        'complete_source_inventory':source_before,'complete_source_inventory_sha256':exact.inventory_digest(source_before)},
        indent=2)+'\n').encode('utf-8'))
    baseline_path = args.accepted_parent_formal_receipt or args.parent_intake.parent/'accepted-main/compiler-receipt.json'
    parent_harvest = args.parent_workflow_harvest or args.parent_intake.parent/'parent-harvest.json'
    supplied_intake = release_json(args.parent_intake)
    actual_intake = intake.acceptance_from_evidence(root,intake.ACCEPTED_PARENT,intake.PINNED_TREE,
        baseline_path,parent_harvest,artifact_folder=args.parent_workflow_artifacts,
        previous_harvest=args.parent_previous_workflow_harvest)
    release_require(supplied_intake==actual_intake,
        'source-only/stale/forged acceptance intake differs from actual revalidation')
    baseline,baseline_binding = intake.verify_p0_evidence(root,baseline_path,intake.ACCEPTED_PARENT,intake.PINNED_TREE)
    current,current_binding = intake.verify_p0_evidence(root,args.parent_formal_receipt,head,tree)
    delta = intake.load_evidence_tool(root,'research/RHRC/integration/opica_followup/dependency_delta.py',
        'opica_actual_release_delta')
    parent = intake.load_evidence_tool(root,'research/RHRC/integration/opica/build_receipt.py',
        'opica_actual_release_parent_reader',intake.PARENT_READER_SHA256)
    preservation = delta.compare_parent_exports(baseline,current,parent)
    # This external gate cannot finish while its required summary is unfinished.
    workflow = intake.verify_workflow_evidence(root,args.workflow_harvest,expected_head=head,
        expected_tree=tree,artifact_folder=args.workflow_artifacts,previous_harvest=args.previous_workflow_harvest)
    harvester = intake.load_evidence_tool(root,'research/RHRC/integration/opica_followup/harvest_workflows.py',
        'opica_final_release_child_job_inventory')
    child_workflow = require_completed_child_workflow(release_json(args.workflow_harvest),harvester,head,tree)
    python,scientific = fresh_locked_scientific_runtime(root,args.python313 or sys.executable,
        output,wheelhouse=args.release_wheelhouse)
    commands, units = [], []
    lake_environment = {}
    if args.lake!='lake':
        lake_path = Path(args.lake).absolute()
        release_require(lake_path.is_file() and lake_path.name.lower() in {'lake','lake.exe'},
            'actual standard-named lake executable required for unchanged parent producer')
        lake_environment['PATH'] = str(lake_path.parent)+os.pathsep+os.environ.get('PATH','')
    fresh_p0 = output/'fresh-parent-p0'
    producer = unchanged_parent_tool(root,'research/RHRC/integration/opica/build_receipt.py')
    commands.append(execute_release_command(root,[python,'-B',str(producer),'--requested-head',head,
        '--requested-base','97926d6a949fed7af0429a373b47abc772012834','--output-dir',str(fresh_p0)],
        output,'fresh-parent-compiler-producer.log',environment=lake_environment))
    replayed,replayed_binding = intake.verify_p0_evidence(root,fresh_p0/'compiler-receipt.json',head,tree)
    delta.compare_parent_exports(current,replayed,parent)
    commands.append(execute_release_command(root,[python,'-B',str(root/'research/RHRC/integration/opica/validate_contract.py'),
        '--phase','release','--formal-receipt',str(fresh_p0/'compiler-receipt.json'),
        '--output',str(output/'parent-release.json')],output,'actual-parent-release-validation.log'))
    parent_report = release_json(output/'parent-release.json')
    release_require(parent_report.get('status')=='PASS' and parent_report.get('phase')=='release'
        and not parent_report.get('errors') and parent_report.get('checked_commit')==head
        and parent_report.get('checked_tree')==tree, 'actual current-tree P0 contract validation failed')
    for label,folder in [('parent','opica'),('child','opica_followup')]:
        for mode,flags in [('normal',[]),('optimized',['-O'])]:
            name = label+'-tests-'+mode+'.log'
            commands.append(execute_release_command(root,[python,'-B',*flags,'-m','unittest','discover','-s',
                str(root/'research/RHRC/integration'/folder/'tests'),'-p','test_*.py','-v'],output,name))
            units.append({'suite':label,'mode':mode,'tests':require_complete_unittest_log(output/name),
                'python':'3.13.5','filtered':False,'skipped':0})
    regression = output/'regression'
    replay = intake.load_evidence_tool(root,'research/RHRC/integration/opica_followup/replay_controls.py',
        'opica_actual_release_frozen_replay')
    commands.append(execute_release_command(root,[python,'-B',str(root/'research/RHRC/integration/opica_followup/replay_controls.py'),
        '--modes','normal','optimized','--include-numerical','--output-dir',str(regression)],
        output,'actual-frozen-regression.log'))
    regression_scope = verify_regression_summary(release_json(regression/'summary.json'),artifacts=regression,replay=replay)
    for name,relative,flags in [('actual-rhrc-suite.log','research/RHRC/tools/run_suite.py',[]),
            ('actual-canonical-check.log','research/RHRC/tools/materialize_derived_state.py',['--check'])]:
        script = unchanged_parent_tool(root,relative)
        commands.append(execute_release_command(root,[python,'-B',str(script),*flags],output,name,
            environment=lake_environment))
    commands.append(execute_release_command(root,[python,'-B',str(root/'research/RHRC/integration/opica_followup/dependency_delta.py'),
        '--parent-intake',str(args.parent_intake),'--formal-receipt',str(args.formal_receipt),
        '--parent-formal-receipt',str(baseline_path),'--current-parent-formal-receipt',str(fresh_p0/'compiler-receipt.json'),
        '--repo',str(root),'--output',str(output/'dependency-delta.json')],output,'actual-dependency-delta.log'))
    dependency = release_json(output/'dependency-delta.json')
    release_require(dependency.get('status')=='SOURCE_BOUND_COMPILER_DELTA_VERIFIED_NOT_RELEASE_ACCEPTANCE'
        and dependency.get('checked_commit')==head and dependency.get('checked_tree')==tree
        and len(dependency.get('original100_child_uses',[]))==100, 'actual all100 compiler dependency delta missing')
    # Recollect all provider metadata; rehash/reparse actual logs and archive
    # members against official digests after the long execution gates.
    workflow_final = intake.verify_workflow_evidence(root,args.workflow_harvest,expected_head=head,
        expected_tree=tree,artifact_folder=args.workflow_artifacts,previous_harvest=args.previous_workflow_harvest)
    release_require(workflow==workflow_final, 'final reviewed workflow evidence changed during release verification')
    after_head,after_tree,source_after,_ = exact.capture_working_source(root)
    release_require((head,tree,source_before)==(after_head,after_tree,source_after),
        'complete actual source changed during release verification')
    return {'status':RELEASE_COMPANIONS_STATUS,'checked_commit':head,'checked_tree':tree,
        'complete_source_inventory_sha256':exact.inventory_digest(source_before),
        'accepted_parent':actual_intake,'baseline_P0':baseline_binding,'supplied_current_P0':current_binding,
        'fresh_current_P0':replayed_binding,'parent_type_axiom_dependency_preservation':preservation,
        'locked_scientific_runtime':scientific,'unit_tests':units,'frozen_regression_scope':regression_scope,
        'commands':commands,'final_workflows':workflow_final,
        'required_child_workflows':child_workflow,
        'dependency_delta_sha256':hashlib.sha256((output/'dependency-delta.json').read_bytes()).hexdigest(),
        'independent_output_review_provenance':workflow_final['output_review_provenance'],
        'independent_human_review':'NOT_ESTABLISHED','RH':'OPEN','Step4':'OPEN',
        'independent_closing_inequalities':'OPEN'}



def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=['preflight', 'release'], required=True)
    parser.add_argument('--parent-intake', type=Path)
    parser.add_argument('--formal-receipt', type=Path)
    parser.add_argument('--parent-formal-receipt', type=Path)
    parser.add_argument('--accepted-parent-formal-receipt', type=Path,
                        help='actual accepted-parent P0 receipt with adjacent original logs')
    parser.add_argument('--parent-workflow-harvest', type=Path,
                        help='accepted-parent complete raw provider harvest and genuine output reviews')
    parser.add_argument('--parent-workflow-artifacts', type=Path)
    parser.add_argument('--parent-previous-workflow-harvest', type=Path,
                        help='optional previous accepted-parent harvest for original exact-fixture comparisons')
    parser.add_argument('--workflow-harvest', type=Path,
                        help='final child complete raw provider harvest and genuine independent output reviews')
    parser.add_argument('--workflow-artifacts', type=Path)
    parser.add_argument('--previous-workflow-harvest', type=Path,
                        help='optional original previous harvest used to compute exact-fixture dispositions')
    parser.add_argument('--python313', help='exact Python3.13.5 used to create a fresh locked runtime')
    parser.add_argument('--release-wheelhouse', type=Path,
                        help='optional offline folder containing exactly both unchanged hash-locked wheels')
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        release_artifact(args.output)
    except ValueError as exc:
        parser.error(str(exc))
    if args.output.resolve().is_relative_to(REPO.resolve()):
        parser.error('execution receipts must be outside the repository')
    full_gate = None
    gate_error = None
    if args.phase == 'release':
        try:
            if args.formal_receipt is None:
                raise ValueError('full100 formal receipt is required; preparation/subset receipts are not accepted')
            full_gate = full_compiler_gate(args.formal_receipt,args.output,lake=args.lake)
        except (KeyError,TypeError,ValueError,OSError,RuntimeError,subprocess.SubprocessError) as exc:
            gate_error = 'full compiler gate rejected: '+str(exc)
    # Only the actual fresh compiler gate can authorize full registered context
    # in this CLI. A caller-supplied status or JSON boolean is never consulted.
    report = preflight(full_registry_verified=full_gate is not None)
    if args.phase == 'release':
        report['status'] = 'FAIL_RELEASE_INCOMPLETE'
        report['full_compiler_gate'] = full_gate or {'status':'REJECTED','release_ready':False}
        if gate_error:
            report['errors'].append(gate_error)
        report['unwired_release_companions'] = [
            'Exact trusted parent acceptance intake and current-tree P0 compiler replay',
            'Complete source-bound runtime/regression and numerical dispositions',
            'Canonical generated-state freshness and complete required workflow harvest']
        report['release_ready'] = False
        report['full_release_accepted'] = False
        report['independent_closing_inequalities'] = 'OPEN'
        report['independent_human_review'] = 'NOT_ESTABLISHED'
        if full_gate is not None and not report['errors']:
            try:
                companions = full_release_companions(args,
                    args.output.parent/(args.output.stem+'.release-companions'))
                release_require(full_gate.get('status')=='FRESH_COMPILER_REPLAY_VERIFIED_FULL_100'
                    and companions.get('status')==RELEASE_COMPANIONS_STATUS
                    and all(full_gate.get(key)==companions.get(key)
                        for key in ('checked_commit','checked_tree')),
                    'fresh full compiler and companion checkout identities differ')
                supplied_formal = release_json(args.formal_receipt)
                current_formal_digest = hashlib.sha256(json.dumps(supplied_formal,sort_keys=True,
                    separators=(',',':'),ensure_ascii=False).encode('utf-8')).hexdigest()
                release_require(full_gate.get('receipt_sha256')==current_formal_digest,
                    'full compiler receipt changed after its actual fresh replay')
                report['release_companions'] = companions
                report['status'] = 'PASS_FULL_FOLLOWUP_RELEASE'
                report['release_ready'] = True
                report['full_release_accepted'] = True
                report['compiler_coverage_audited'] = True
                report['release_blockers'] = []
                report['unwired_release_companions'] = []
            except (KeyError,TypeError,ValueError,OSError,RuntimeError,subprocess.SubprocessError,zipfile.BadZipFile) as exc:
                report['errors'].append('release companions rejected: '+str(exc))
        if not report['release_ready'] and not report['errors']:
            report['errors'].append('full compiler and every original release companion must execute successfully')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k != 'missing_planned_files'}, indent=2))
    return 1 if report['errors'] else 0



# Install this fragment after the byte-preserved legacy function, renamed
# _dependency_amendment_errors_v3. This is structural metadata validation only.
DEPENDENCY_V3_SHA256 = '028339b2bdd4a70182424031215010ae8c91ad771cba1089966c36f82431d564'


def _dependency_amendment_errors_v4(register: dict, manifest: dict, root: Path) -> list[str]:
    """Require the authenticated exact-subject policy and every frozen module.

    Source/import permission does not establish a mathematical theorem or a
    semantic review. The full compiler reader separately binds the independently
    reviewed canonical amendment hash, original types and original domains.
    """
    errors = []

    def require(condition, message):
        if not condition:
            raise ValueError(message)

    def canonical(value):
        return json.dumps(value, sort_keys=True, separators=(',', ':'),
                          ensure_ascii=False).encode('utf-8')

    def object_hash(value):
        return hashlib.sha256(canonical(value)).hexdigest()

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate dependency input JSON key: ' + key)
            result[key] = value
        return result

    def safe_file(relative):
        path = root / relative
        require(path.is_file(), 'missing actual dependency subject: ' + relative)
        require(not any(part.is_symlink() or getattr(part, 'is_junction', lambda: False)()
                        for part in [path, *path.parents] if part.is_relative_to(root)),
                'aliased dependency subject: ' + relative)
        require(path.resolve() == root.resolve() / relative,
                'escaped dependency subject: ' + relative)
        return path

    try:
        root = Path(root).absolute()
        folder = 'research/RHRC/integration/opica_followup/'
        actual_register = json.loads(safe_file(folder + 'SOURCE_REGISTER.json').read_bytes(),
                                     object_pairs_hook=unique_object)
        require(register == actual_register, 'amendment differs from actual SOURCE_REGISTER')
        manifest_bytes = safe_file(folder + 'BUILD_MANIFEST.json').read_bytes()
        require(hashlib.sha256(manifest_bytes).hexdigest() == FROZEN_SPEC['BUILD_MANIFEST.json'],
                'frozen dependency manifest bytes changed')
        actual_manifest = json.loads(manifest_bytes, object_pairs_hook=unique_object)
        require(manifest == actual_manifest, 'supplied manifest differs from frozen actual manifest')
        policy = register.get('exact_source_extension_policy')
        require(isinstance(policy, dict)
                and policy.get('schema') in {'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V2', 'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V3'},
                'authenticated exact V2 import policy required')
        context = exact_policy_context(root)
        require(context is not None, 'authenticated exact V2 import context required')
        require(context.policy_sha256 == object_hash(policy),
                'dependency policy digest differs from authenticated context')
        snapshots = json.loads(context.subject_imports_json, object_pairs_hook=unique_object)
        plans = manifest['modules']
        require(isinstance(snapshots, list) and len(snapshots) == len(plans) == 43,
                'complete authenticated frozen43-module import inventory required')
        require([(row['module'], row['path']) for row in snapshots] ==
                [(row['module'], row['path']) for row in plans],
                'authenticated dependency subjects/order differ from frozen manifest')
        amendment = register.get('implementation_dependency_amendment')
        require(isinstance(amendment, dict), 'dependency04 amendment object required')
        required = {
            'schema': 'OPICA_IMPLEMENTATION_DEPENDENCY_AMENDMENT_V1',
            'id': 'DEP_2026_10_24_04', 'supersedes': 'DEP_2026_10_21_03',
            'previous_amendment_sha256': DEPENDENCY_V3_SHA256,
            'status': 'IMPLEMENTATION_ONLY_NO_MATHEMATICAL_SCOPE_CHANGE',
            'frozen_manifest_sha256': FROZEN_SPEC['BUILD_MANIFEST.json'],
            'frozen_public_roots_sha256': FROZEN_SPEC['PUBLIC_ROOTS.json'],
            'primary_roots': 100, 'acceptance_units': 28, 'new_paths': 84,
            'promoted_supporting_lemmas': [], 'theorem_statement_changes': [], 'new_assumptions': [],
            'authority': 'Explicit implementation dependency refinement; compiler receipts separately establish actual TYPE/VALUE/STRUCTURE dependencies and validity.',
            'RH': 'OPEN', 'Step4': 'OPEN', 'independent_closing_inequalities': 'OPEN',
        }
        require(set(amendment) == set(required) | {'rows'},
                'dependency04 amendment fields differ from original contract')
        for key, value in required.items():
            require(type(amendment.get(key)) is type(value) and amendment[key] == value,
                    'implementation dependency04 scope changed: ' + key)
        history = register.get('implementation_dependency_history')
        require(isinstance(history, list) and len(history) == 3,
                'three exact previous dependency amendments required')
        require([object_hash(row) for row in history] ==
                [DEPENDENCY_V1_SHA256, DEPENDENCY_V2_SHA256, DEPENDENCY_V3_SHA256],
                'previous dependency amendment missing or changed')
        rows = amendment.get('rows')
        require(isinstance(rows, list) and len(rows) == 43,
                'complete dependency04 ordered43-module rows required')
        for row, snap, plan in zip(rows, snapshots, plans):
            require(isinstance(row, dict), 'dependency04 row must be an object')
            expected = {
                'module': plan['module'], 'path': plan['path'],
                'source_sha256': snap['source_sha256'],
                'actual_all_ordered_imports': snap['actual_all_ordered_imports'],
                'planned_direct_project_imports': plan['direct_project_imports'],
                'approved_direct_project_imports': snap['actual_direct_project_imports'],
                'theorem_statement_changes': [], 'new_assumptions': [],
            }
            require(set(row) == set(expected) | {'reason'},
                    'dependency04 row fields changed: ' + plan['module'])
            for key, value in expected.items():
                require(type(row.get(key)) is type(value) and row[key] == value,
                        'dependency04 exact source/import/plan changed: ' + plan['module'] + ':' + key)
            require(isinstance(row['reason'], str) and row['reason'].strip(),
                    'dependency04 explanation missing: ' + plan['module'])
            require(snap['frozen_planned_project_imports'] == plan['direct_project_imports'],
                    'authenticated dependency snapshot rewrote frozen plan')
            all_imports = snap['actual_all_ordered_imports']
            require(isinstance(all_imports, list) and all(isinstance(name, str) for name in all_imports)
                    and len(set(all_imports)) == len(all_imports),
                    'invalid authenticated ordered imports')
            require([name for name in all_imports if name == 'Zeta23' or name.startswith('Zeta23.')]
                    == snap['actual_direct_project_imports'],
                    'authenticated project imports differ from complete ordered imports')
            source = safe_file(plan['path']).read_bytes()
            require(hashlib.sha256(source).hexdigest() == snap['source_sha256'],
                    'actual dependency source changed after authenticated context: ' + plan['module'])
    except (OSError, ValueError, TypeError, KeyError, AttributeError, UnicodeError,
            RecursionError, subprocess.SubprocessError) as exc:
        errors.append('dependency04 rejected: ' + str(exc))
    return errors


def dependency_amendment_errors(register: dict, manifest: dict, root: Path = REPO) -> list[str]:
    """Explicit version dispatch; unknown or pending04 never falls back to03."""
    amendment = register.get('implementation_dependency_amendment') if isinstance(register, dict) else None
    if not isinstance(amendment, dict):
        return ['versioned implementation dependency amendment object required']
    version = amendment.get('id')
    if version == 'DEP_2026_10_21_03':
        return _dependency_amendment_errors_v3(register, manifest, root)
    if version == 'DEP_2026_10_24_04':
        return _dependency_amendment_errors_v4(register, manifest, root)
    return ['unsupported implementation dependency amendment version']

if __name__ == '__main__':
    raise SystemExit(main())
