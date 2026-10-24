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
CONTINUATION_MANIFEST_SHA256 = '980663cbc18ba15e997b3ce2da0736940796b1e22f4e6ad4eefc4179a378056e'
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


def dependency_amendment_errors(register: dict, manifest: dict, root: Path = REPO) -> list[str]:
    """Check the narrow versioned import refinement, separately from proof authority.

    The frozen statements and scope remain inputs; this does not establish that
    importing a proved lemma proves any child theorem.
    """
    errors = []
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
        if actual != DEPENDENCY_REFINEMENTS[name]:
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
        if not full_registry_verified and json.loads((root / relative).read_text(encoding='utf-8')) != protected[key]:
            errors.append('pre-registration parent context changed: ' + key)
    creates = {row['path'] for row in manifest['create']}
    parent_paths = {row['path'] for row in protected['files']}
    inventory = subprocess.run(['git', '-C', str(root), 'ls-files', '-z', '--cached',
                                '--others', '--exclude-standard'], check=True,
                               stdout=subprocess.PIPE).stdout.decode().split('\0')
    extra = sorted(set(filter(None, inventory)) - parent_paths - creates - checkpoint_paths)
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=['preflight', 'release'], required=True)
    parser.add_argument('--parent-intake', type=Path)
    parser.add_argument('--formal-receipt', type=Path)
    parser.add_argument('--parent-formal-receipt', type=Path)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
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
        report['errors'].append('full release remains closed until all independent release companions are wired and verified')
        report['release_ready'] = False
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k != 'missing_planned_files'}, indent=2))
    return 1 if report['errors'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
