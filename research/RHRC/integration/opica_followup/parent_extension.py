"""Pure parent-context preservation checks; no compiler authority is produced here.

Inputs must already be source-bound by the caller. In particular the reviewed
child objects are exact expected objects, never inferred from the raw registry.
This module deliberately does not call either validator, Git, or a subprocess.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import PurePosixPath
from types import MappingProxyType
from typing import Any, Mapping

PARENT_TREE = '12691099f1a155a8bfa3ad4f6689146175b233b2'
PARENT_HEADS = frozenset({'553b4263b58d9fec178320de251ff299a0bd702a',
                         'd53dd70d38b0762af130b1d19b795af259f505f5'})
EXTENSION_SHA256 = '2b88b5497861679e6b1f686af6c8b5b7dbe5a5887841be43d862ba9836187ac3'
ROOTS_SHA256 = '2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41'


class ExtensionError(ValueError):
    pass


def _require(condition: bool, message: str) -> None:
    # Checks must remain active with python -O.
    if not condition:
        raise ExtensionError(message)


def _unique(rows: list, field: str, label: str) -> dict:
    _require(isinstance(rows, list) and all(isinstance(r, dict) for r in rows), label + ': rows')
    ids = [r.get(field) for r in rows]
    _require(all(isinstance(i, str) and i for i in ids), label + ': identity missing')
    _require(len(ids) == len(set(ids)), label + ': duplicate identity')
    return {r[field]: r for r in rows}


def _paths(paths: list, label: str) -> frozenset[str]:
    _require(isinstance(paths, list) and all(isinstance(p, str) and p for p in paths), label)
    for value in paths:
        path = PurePosixPath(value)
        _require(not path.is_absolute() and '\\' not in value and ':' not in value
                 and all(part not in {'', '.', '..'} for part in value.split('/')),
                 'unsafe path: ' + value)
    _require(len(paths) == len(set(paths)), 'duplicate path: ' + label)
    return frozenset(paths)


def _append_exact(parent: list, child: list, raw: list, key: str, label: str) -> None:
    old = _unique(parent, key, label + ' parent')
    new = _unique(child, key, label + ' child')
    _unique(raw, key, label + ' raw')
    _require(not old.keys() & new.keys(), label + ': historical identity reused')
    # Both values and order are protected. No parent row may disappear or change.
    _require(raw == parent + child, label + ': raw objects differ from exact append')


@dataclass(frozen=True)
class ValidatedContext:
    # Store canonical bytes so later mutation of any input cannot change the
    # validated result. Projection deserializes fresh values each time.
    parent_json: bytes
    new_paths: frozenset[str]
    modified_paths: frozenset[str]
    generated_paths: frozenset[str]


def validate_extension_context(raw_state: Mapping[str, Any], parent_baseline: Mapping[str, Any],
                               child_contract: Mapping[str, Any]) -> ValidatedContext:
    """Validate raw context before projecting any child contribution.

    raw_state includes file hashes and complete registry/config values. The
    caller must obtain file hashes from resolved, nonsymlinked checkout files.
    This is a structural check, not type review or permission to register proofs.
    """
    try:
        descriptor_bytes = child_contract['descriptor_bytes']
        _require(isinstance(descriptor_bytes, bytes), 'descriptor must retain frozen bytes')
        _require(hashlib.sha256(descriptor_bytes).hexdigest() == EXTENSION_SHA256,
                 'unreviewed child descriptor')
        descriptor = json.loads(descriptor_bytes)
        roots_bytes = child_contract['roots_bytes']
        _require(isinstance(roots_bytes, bytes)
                 and hashlib.sha256(roots_bytes).hexdigest() == ROOTS_SHA256,
                 'unreviewed root inventory')
        root_document = json.loads(roots_bytes)
        roots = _unique(root_document['roots'], 'id', 'frozen roots')
        _require(descriptor['child_id'] == 'OPICA_FOLLOWUP_V1', 'unknown extension')
        _require(descriptor['child_namespace'] == 'Zeta23.OPICAFollowup', 'namespace changed')
        _require(parent_baseline['parent_head'] in PARENT_HEADS
                 and parent_baseline['parent_tree'] == PARENT_TREE, 'parent identity changed')
        _require(raw_state['parent_head'] == parent_baseline['parent_head']
                 and raw_state['parent_tree'] == PARENT_TREE, 'raw parent identity changed')
        creates = _paths(descriptor['new_exact_paths'], 'creates')
        modifies = _paths(descriptor['modified_exact_paths'], 'modifies')
        generated = _paths(descriptor['generated_exact_paths'], 'generated')
        _require(not creates & modifies and not creates & generated and not modifies & generated,
                 'overlapping file categories')
        parent_files = _unique(parent_baseline['files'], 'path', 'parent files')
        raw_files = _unique(raw_state['files'], 'path', 'raw files')
        _paths(list(raw_files), 'raw inventory')
        _require(not creates & parent_files.keys(), 'created path already in parent')
        _require(modifies | generated <= parent_files.keys(), 'exception absent in parent')
        _require(raw_files.keys() == parent_files.keys() | creates,
                 'missing or unlisted tracked file')
        for path, row in raw_files.items():
            _require(row.get('mode') in {'100644', '100755'}, 'symlink or unsupported file: ' + path)
            digest = row.get('sha256')
            _require(isinstance(digest, str) and len(digest) == 64
                     and all(c in '0123456789abcdef' for c in digest), 'invalid SHA256: ' + path)
            if path in parent_files and path not in modifies | generated:
                _require(row == parent_files[path], 'protected parent file changed: ' + path)
        claims = child_contract['reviewed_claim_objects']
        bindings = child_contract['reviewed_binding_objects']
        _require([c['id'] for c in claims] == descriptor['child_claim_ids'],
                 'incomplete or unlisted child claim inventory')
        _require(len(bindings) == len(claims), 'binding inventory incomplete')
        parent_registry = parent_baseline['claim_registry']
        raw_registry = raw_state['claim_registry']
        _require({k: v for k, v in raw_registry.items() if k != 'claims'} ==
                 {k: v for k, v in parent_registry.items() if k != 'claims'},
                 'registry metadata changed')
        _append_exact(parent_registry['claims'], claims, raw_registry['claims'], 'id', 'claims')
        parent_bindings = parent_baseline['theorem_bindings']
        raw_bindings = raw_state['theorem_bindings']
        _require({k: v for k, v in raw_bindings.items() if k != 'bindings'} ==
                 {k: v for k, v in parent_bindings.items() if k != 'bindings'},
                 'binding metadata/candidates changed')
        # Binding objects use the repository's exact id identity.
        _append_exact(parent_bindings['bindings'], bindings, raw_bindings['bindings'],
                      'id', 'bindings')
        _require([b['id'] for b in bindings] == descriptor['child_claim_ids'],
                 'binding identities differ from child roots')
        for binding, claim in zip(bindings, claims):
            _require(binding.get('theorem') == claim.get('theorem')
                     and binding.get('source') == claim.get('source'),
                     'claim/binding source mismatch')
            root = roots[binding['id']]
            _require(binding.get('theorem') == root['full_name']
                     and binding.get('source') == root['path'],
                     'child theorem/source differs from frozen root')
        old_theorems = {b['theorem'] for b in parent_bindings['bindings']}
        new_theorems = [b['theorem'] for b in bindings]
        _require(len(new_theorems) == len(set(new_theorems))
                 and not old_theorems.intersection(new_theorems),
                 'duplicate theorem declaration')
        expected_classes = deepcopy(parent_baseline['file_classes'])
        rules = expected_classes['rules']
        generic = [i for i, rule in enumerate(rules) if rule.get('id') == 'zeta_lean']
        _require(len(generic) == 1, 'missing unique generic class insertion point')
        _require(not {r['id'] for r in descriptor['child_classes']} &
                 {r['id'] for r in rules}, 'child class identity already exists')
        for rule in descriptor['child_classes']:
            _require(not any(re.search(rule['pattern'], p) for p in parent_files),
                     'child class shadows a parent file')
        rules[generic[0]:generic[0]] = deepcopy(descriptor['child_classes'])
        _require(raw_state['file_classes'] == expected_classes,
                 'file_classes: unauthorized delta')
        expected_roles = deepcopy(parent_baseline['semantic_closure'])
        roles = expected_roles['standalone_module_roles']
        _require(not roles.keys() & descriptor['child_roles'].keys(),
                 'child role changes historical role')
        roles.update(descriptor['child_roles'])
        _require(raw_state['semantic_closure'] == expected_roles,
                 'semantic_closure: unauthorized delta')
        parent = {k: deepcopy(parent_baseline[k]) for k in
                  ('claim_registry', 'theorem_bindings', 'file_classes', 'semantic_closure')}
        return ValidatedContext(json.dumps(parent, sort_keys=True).encode(), creates, modifies, generated)
    except (KeyError, TypeError, json.JSONDecodeError) as exc:
        raise ExtensionError('missing or malformed extension context') from exc


def project_parent_context(validated_context: ValidatedContext) -> Mapping[str, Any]:
    _require(isinstance(validated_context, ValidatedContext), 'raw state cannot be projected')
    return MappingProxyType(json.loads(validated_context.parent_json))


def allowed_child_delta(validated_context: ValidatedContext) -> frozenset[str]:
    _require(isinstance(validated_context, ValidatedContext), 'unvalidated delta')
    return (validated_context.new_paths | validated_context.modified_paths |
            validated_context.generated_paths)
