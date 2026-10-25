#!/usr/bin/env python3
"""Prepare/apply the Stage 19 ledger and documentation record, after narrow proof gates.

SCRATCH ONLY: creating this file does not execute it or update the repository.
The default invocation validates and prints a plan; --write is required for edits.
The owner separately runs refresh_navigation.py and refresh_manifest.py afterward.

Required evidence layout, relative to the continuation directory:
  STAGE19_HANDOVER.md
  evidence/current-codex/stage19/STATUS.json
  evidence/current-codex/stage19/runner/{CHECK_RESULT.json,source-before.json[.gz],logs}
STATUS must identify the clean checked code commit/tree and name the new primary.
Runner evidence must include the full-type/domain consumers ExpectedForceSampling,
ExpectedWordJet and ExpectedSampleSign, with matching committed source/log hashes.
ExpectedSampleSign remains supporting mathematics and is never counted as a root.
"""
from __future__ import annotations

import argparse
import ast
import copy
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

CONTINUATION = 'research/RHRC/integration/opica_followup/continuation/2026-10-22'
NEW_ROOT = 'Zeta23.OPICAFollowup.actual_force_sampling_consumer'
WORD_ROOT = 'Zeta23.OPICAFollowup.step123_word_jet_consumer'
CONSUMERS_SOURCE = 'Zeta23/OPICAFollowup/Consumers.lean'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
NARROW = 'PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING'
ABSENT = 'OPEN_NO_COMPLETE_CANDIDATE'
HISTORICAL = 'PROVED_IN_ORIGINAL_41_ROOT_SOURCE_BOUND_SUBSET'
FROZEN_ROOTS_SHA256 = '2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41'
STATUS_RELATIVE = 'evidence/current-codex/stage19/STATUS.json'
RUNNER_RELATIVE = 'evidence/current-codex/stage19/runner/CHECK_RESULT.json'


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return digest(path.read_bytes())


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(repo), *args])


def read_evidence(path: Path) -> bytes:
    """Allow the preserved lossless .gz convention without altering evidence."""
    if path.is_file():
        return path.read_bytes()
    compressed = path.with_name(path.name + '.gz')
    require(compressed.is_file(), f'Missing required verification file: {path}')
    return gzip.decompress(compressed.read_bytes())


def read_json(path: Path) -> dict:
    return json.loads(read_evidence(path).decode('utf-8-sig'))


def preserved_text_bytes(path: Path, normalized: str) -> bytes:
    raw = path.read_bytes()
    if b'\r\n' in raw:
        require(b'\n' not in raw.replace(b'\r\n', b''), f'Mixed newlines: {path}')
        return normalized.replace('\n', '\r\n').encode('utf-8')
    return normalized.encode('utf-8')


def literal_runner_tuple(path: Path, name: str) -> tuple:
    module = ast.parse(path.read_text(encoding='utf-8'))
    matches = [n.value for n in module.body if isinstance(n, ast.Assign)
               and any(isinstance(t, ast.Name) and t.id == name for t in n.targets)]
    require(len(matches) == 1, f'Missing or duplicate runner literal: {name}')
    value = ast.literal_eval(matches[0])
    require(isinstance(value, tuple) and all(isinstance(x, str) for x in value), name)
    require(len(value) == len(set(value)), f'Duplicate runner {name}')
    return value


def validate_evidence(repo: Path, c: Path, head: str, tree: str) -> tuple[dict, dict, dict]:
    require(re.fullmatch(r'[0-9a-f]{40}', head) is not None, 'Use a full code-commit SHA')
    require(re.fullmatch(r'[0-9a-f]{40}', tree) is not None, 'Use a full code-tree SHA')
    require(git(repo, 'rev-parse', 'HEAD').decode().strip() == head,
            'HEAD differs from supplied checked code commit; reconcile before editing')
    require(git(repo, 'rev-parse', head + '^{tree}').decode().strip() == tree,
            'Code commit does not resolve to supplied tree')
    status = read_json(c / STATUS_RELATIVE)
    runner_dir = c / 'evidence/current-codex/stage19/runner'
    runner = read_json(runner_dir / 'CHECK_RESULT.json')
    snapshot = read_json(runner_dir / 'source-before.json')
    require(status.get('checked_commit') == head and status.get('checked_tree') == tree,
            'Stage 19 STATUS does not pin this code commit/tree')
    require(status.get('dirty_status_during_checks') == '',
            'Stage 19 STATUS must record a clean source tree during verification')
    require(isinstance(status.get('status'), str) and status['status'].startswith('PASS'),
            'Stage 19 STATUS is not a passing narrow disposition')
    require(NEW_ROOT in status.get('roots', {}), 'STATUS omits the original new primary root')
    require(status.get('RH') == 'OPEN' and status.get('Step4') == 'OPEN', 'Claim firewall changed')
    require(runner.get('status') == 'PASS_NARROW_ONLY', 'Narrow runner did not pass')
    require(runner.get('head') == head and runner.get('tree') == tree, 'Runner source pin differs')
    require(runner.get('dirty_status') == '' and runner.get('source_unchanged') is True,
            'Runner must establish clean and unchanged checked sources')
    require(runner.get('full_release_accepted') is False
            and runner.get('aggregate_registration_accepted') is False,
            'Narrow runner must not claim aggregate/full-release acceptance')
    require(runner.get('RH') == 'OPEN' and runner.get('Step4') == 'OPEN', 'Runner claim cap changed')
    require(runner.get('independent_closing_inequalities') == 'OPEN', 'Closing inequalities changed')
    handover = c / 'STAGE19_HANDOVER.md'
    require(handover.is_file(), 'Write/review STAGE19_HANDOVER.md before updating pointers')
    handover_text = handover.read_text(encoding='utf-8')
    require(head[:8] in handover_text and 'actual_force_sampling_consumer' in handover_text,
            'Stage 19 handover does not identify the checked source and new root')

    runner_source = c / 'run_candidate_checks.py'
    modules = literal_runner_tuple(runner_source, 'MODULES')
    names = literal_runner_tuple(runner_source, 'CONSUMERS')
    require('Consumers' in modules, 'Changed Consumers module is absent from the narrow build')
    must_have = {'ExpectedForceSampling', 'ExpectedWordJet', 'ExpectedSampleSign'}
    require(must_have <= set(names), 'Stage 19 independent consumers absent from runner')
    receipts = runner.get('consumers')
    require(isinstance(receipts, list), 'Missing narrow consumer receipts')
    by_name = {r['name']: r for r in receipts}
    require(len(by_name) == len(receipts) and set(by_name) == set(names),
            'Incomplete/duplicate runner consumer coverage')
    commands = runner.get('commands')
    require(isinstance(commands, list) and commands, 'Missing actual runner command receipts')
    labels = [r.get('label') for r in commands]
    require(len(labels) == len(set(labels)) and {'version', 'build'} | set(names) <= set(labels),
            'Missing/duplicate build or consumer commands')
    for cmd in commands:
        require(type(cmd.get('exit_code')) is int and cmd['exit_code'] == 0,
                f'Failed/unexecuted runner command: {cmd.get("label")}')
        log_name = cmd.get('log')
        require(isinstance(log_name, str) and Path(log_name).name == log_name,
                'Runner log reference must be a local basename')
        log = read_evidence(runner_dir / log_name)
        require(digest(log) == cmd.get('log_sha256'), f'Runner log hash differs: {log_name}')
        text = log.decode('utf-8', errors='replace')
        require('sorryAx' not in text and not re.search(r'declaration uses [\x27\x60]sorry', text),
                f'Placeholder in successful runner log: {log_name}')
    version = read_evidence(runner_dir / 'version.log').decode('utf-8', errors='replace')
    require('4.33.0-rc2' in version
            and 'd8b18978322de05a8f3dba51ef03cf5461676c17' in version,
            'Actual pinned compiler identity missing')
    require((repo / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0-rc2',
            'Pinned toolchain changed')
    packages = json.loads((repo / 'lake-manifest.json').read_text())['packages']
    require(next(p for p in packages if p['name'] == 'mathlib')['rev'] ==
            '51e6992efd06126df61a496bebf8f49482a4e129', 'Pinned Mathlib changed')
    source_paths = [CONSUMERS_SOURCE, CONTINUATION + '/run_candidate_checks.py',
                    'lean-toolchain', 'lake-manifest.json']
    source_paths += [CONTINUATION + '/consumers/' + n + '.lean' for n in must_have]
    for relative in source_paths:
        current = (repo / relative).read_bytes()
        require(current == git(repo, 'show', head + ':' + relative),
                f'Current source differs from checked committed bytes: {relative}')
        if relative in snapshot:
            require(digest(current) == snapshot[relative], f'Runner source hash differs: {relative}')
    for name in names:
        rec = by_name[name]
        source = c / 'consumers' / (name + '.lean')
        requested = re.findall(r'^#print axioms (\S+)\s*$', source.read_text(encoding='utf-8'), re.M)
        require(rec.get('source_sha256') == sha(source), f'Consumer source receipt differs: {name}')
        require(requested and len(requested) == len(set(requested)), f'No/duplicate axioms: {name}')
        require(set(requested) == set(rec.get('axioms', {})), f'Incomplete axiom inventory: {name}')
        require(rec.get('status') == 'PASS_NARROW_TYPE_DOMAIN_AND_AXIOM_CHECK_ONLY', name)
        require(all(set(xs) <= STANDARD_AXIOMS for xs in rec['axioms'].values()), name)
    require('OPICAForceSamplingIndependent.expected_actual_force_sampling_consumer'
            in by_name['ExpectedForceSampling']['axioms'], 'Expected full force type not verified')
    require('OPICAForceSamplingIndependent.actual_offline_domain'
            in by_name['ExpectedForceSampling']['axioms'], 'Actual off-line domain not verified')
    require('OPICAWordJetIndependent.expected_step123_word_jet_consumer'
            in by_name['ExpectedWordJet']['axioms'], 'Changed word/jet source was not revalidated')
    negative_controls = status.get('negative_controls')
    require(isinstance(negative_controls, list) and negative_controls,
            'Stage 19 STATUS must preserve explicit rejected negative controls')
    evidence_dir = (c / 'evidence/current-codex/stage19').resolve()
    for control in negative_controls:
        require(control.get('expected') == 'REJECTED'
                and str(control.get('observed', '')).startswith('REJECTED'),
                'Negative control did not reach its intended rejected disposition')
        source_relative = control.get('file')
        require(isinstance(source_relative, str), 'Missing negative-control source reference')
        negative_source = (evidence_dir / source_relative).resolve()
        require(negative_source.is_relative_to(evidence_dir) and negative_source.is_file(),
                'Negative-control reference escaped or is absent from the evidence directory')
        log_relative = control.get('log', str(Path(source_relative).with_suffix('.log')))
        negative_log = (evidence_dir / log_relative).resolve()
        require(negative_log.is_relative_to(evidence_dir), 'Negative-control log escaped evidence')
        log_bytes = read_evidence(negative_log)
        require(digest(log_bytes) == control.get('log_sha256'), 'Negative-control log hash differs')
        require('error:' in log_bytes.decode('utf-8', errors='replace'),
                'Negative-control log lacks an actual compiler rejection')
        if 'exit_code' in control:
            require(type(control['exit_code']) is int and control['exit_code'] != 0,
                    'Negative-control process unexpectedly succeeded')
    return status, runner, {'modules': modules, 'consumers': names, 'receipts': by_name}


def updated_ledger(repo: Path, c: Path, head: str, tree: str, verified: dict) -> bytes:
    path = c / 'ROOT_LEDGER_100.json'
    original = json.loads(path.read_bytes())
    d = copy.deepcopy(original)
    frozen_path = repo / 'research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json'
    require(sha(frozen_path) == FROZEN_ROOTS_SHA256, 'Frozen original root contract bytes changed')
    frozen = json.loads(frozen_path.read_bytes())
    frozen_rows = frozen['roots'] if isinstance(frozen, dict) else frozen
    contracts = {r['full_name']: r for r in frozen_rows}
    require(len(d['roots']) == 100 and d['required_roots'] == 100 and d['acceptance_units'] == 28,
            'Original100/28 scope changed')
    require(all(r['contract'] == contracts[r['full_name']] for r in d['roots']),
            'Embedded original root contracts changed')
    require(d.get('current_aggregate_accepted') is False
            and d['verification_summary'].get('current_aggregate_accepted') is False,
            'Aggregate acceptance must remain false')
    require(d['status_counts'] == {ABSENT: 10, HISTORICAL: 41, NARROW: 49},
            'Reconcile newer ledger work before applying Stage 19')
    roots = {r['full_name']: r for r in d['roots']}
    force, word = roots[NEW_ROOT], roots[WORD_ROOT]
    require(force['current_status'] == ABSENT and word['current_status'] == NARROW,
            'Unexpected original primary or retained word/jet status')
    retained_word_status = word['current_status']
    retained_word_gates = copy.deepcopy(word['gates'])
    retained_word_source = word['source_sha256']
    retained_word_evidence = copy.deepcopy(word['evidence'])
    src = sha(repo / CONSUMERS_SOURCE)
    for r in d['roots']:
        if r['path'] == CONSUMERS_SOURCE:
            # Shared-file provenance only: other absent primaries remain absent.
            r['source_sha256'] = src
    force.update(current_status=NARROW, source_file_present=True,
                 declaration_lexically_present=True, source_sha256=src)
    force['gates'] = {
        'implementation': 'IMPLEMENTED_FULL_FROZEN_CONTRACT_REVIEWED_NARROW',
        'module_compilation': 'PASS_EXACT_COMMITTED_SOURCE_PINNED_COMPILER',
        'expected_type_consumer': 'PASS_INDEPENDENT_FULL_TYPE_AND_DEFINITION_AUDITS',
        'actual_domain_consumer': 'PASS_ACTUAL_STRIP_ZERO_OFFLINE_KAPPA_BOTH_FOURIER_CONVENTIONS_FORCE_SPECTRAL_SAMPLE_AND_REFLECTED_BOUNDARY',
        'axiom_check': 'STANDARD_ONLY_TRANSITIVE_PRINTED_CLOSURES',
        'aggregate_current_source_export': 'OPEN', 'full_release_acceptance': 'OPEN'}
    force['evidence'] = [STATUS_RELATIVE, RUNNER_RELATIVE]
    force['independent_consumer'] = {
        'path': 'consumers/ExpectedForceSampling.lean',
        'sha256': sha(c / 'consumers/ExpectedForceSampling.lean')}
    force['statement_formalization'] = (
        'For every actual zeta zero rho with 0 < Re rho < 1 and Im(kappa) != 0, '
        'kappa = rho(1-rho): compose the literal compact-test log-lattice force, its actual '
        'tempered Fourier transform, logFourier f xi = Fourier f (xi/(2*pi)), the sawtooth '
        'transform, the weak forced log-unitary equation, and the arithmetic resolvent quotient '
        'in both Fourier conventions. Retain d omega = |zeta(1/2+i xi)|^2 d xi/(2*pi), '
        'b = kappa M(kappa), and the right-half-strip representative rho\' in {rho,1-rho} '
        'with the same kappa, zero boundary amplitude, generic profile equal to the actual '
        'zero profile and the same log-unitary profile. No scalar makes the Euler image a '
        'homogeneous multiple of the profile. The independent physical consumer derives '
        'Im(kappa) != 0 from the actual off-line strip-zero domain; no existence of an '
        'off-line zero is asserted. No actual construction is replaced by a synthetic object.')
    for ev in (STATUS_RELATIVE, RUNNER_RELATIVE):
        if ev not in word['evidence']:
            word['evidence'].append(ev)
    word.setdefault('revalidations', []).append({
        'stage': 19, 'checked_commit': head, 'checked_tree': tree,
        'source_sha256': src, 'evidence': [STATUS_RELATIVE, RUNNER_RELATIVE],
        'module_compilation': 'PASS_EXACT_COMMITTED_SOURCE_PINNED_WINDOWS_STAGE19_REVALIDATION',
        'consumer': {'path': 'consumers/ExpectedWordJet.lean',
                     'sha256': sha(c / 'consumers/ExpectedWordJet.lean')},
        'status': 'PASS_EXISTING_PRIMARY_REVALIDATION_ONLY_NOT_ADDITIONAL_ROOT',
        'historical_source_provenance': {
            'source_sha256': retained_word_source,
            'current_status': retained_word_status,
            'gates': retained_word_gates,
            'evidence': retained_word_evidence,
            'scope': ('Prior complete gate record at its earlier source hash only. Its Linux '
                      'compilation disposition is not evidence for the Stage 19 Consumers bytes.')},
        'axioms': sorted(STANDARD_AXIOMS)})
    current_word_compilation = 'PASS_EXACT_COMMITTED_SOURCE_PINNED_WINDOWS_STAGE19_REVALIDATION'
    word['gates']['module_compilation'] = current_word_compilation
    expected_word_gates = dict(retained_word_gates, module_compilation=current_word_compilation)
    require(word['current_status'] == retained_word_status and word['gates'] == expected_word_gates,
            'Only the current word/jet compilation provenance gate may change in Stage 19')
    require(all(word['gates'][key] == value for key, value in retained_word_gates.items()
                if key != 'module_compilation'), 'Other retained word/jet gates changed')
    counts = {}
    for r in d['roots']:
        counts[r['current_status']] = counts.get(r['current_status'], 0) + 1
    require(counts == {HISTORICAL: 41, NARROW: 50, ABSENT: 9}, 'Stage 19 count mismatch')
    d['status_counts'] = dict(sorted(counts.items()))
    vs = d['verification_summary']
    vs['independently_verified_narrow_roots'] = 50
    vs['open_no_complete_candidate_roots'] = 9
    vs['receipt'] = 'STAGE19_HANDOVER.md'
    vs['meaning'] = ('41 historical plus 50 narrow local results is not aggregate 91-root acceptance. '
                     '9 absent implementations and all remaining integration/release gates remain OPEN; '
                     'original100/28 scope unchanged.')
    vs['receipt_scope'] = ('One Stage 19 original primary and revalidation of the existing Stage 4 '
                           'word/jet root; supporting ExpectedSampleSign is not a primary. Prior index: '
                           + vs['receipt_scope'])
    vs['additional_stage19_primary_roots'] = ['actual_force_sampling_consumer']
    vs['stage19_checked_source'] = {'commit': head, 'tree': tree, 'source_sha256': src,
                                  'status': STATUS_RELATIVE, 'runner': RUNNER_RELATIVE}
    vs['stage19_supporting_only'] = {'consumer': 'consumers/ExpectedSampleSign.lean',
        'counted_as_primary': False, 'sha256': sha(c / 'consumers/ExpectedSampleSign.lean'),
        'verified_declarations': sorted(verified['receipts']['ExpectedSampleSign']['axioms'])}
    require(all(r['contract'] == contracts[r['full_name']] for r in d['roots']),
            'Frozen contracts changed while composing the ledger update')
    require(d['current_aggregate_accepted'] is False and vs['current_aggregate_accepted'] is False,
            'Aggregate acceptance changed')
    text = json.dumps(d, indent=2, ensure_ascii=True) + '\n'
    return preserved_text_bytes(path, text)


# Exact reviewed documentation edit data is appended below. No repository edit occurs on import.

DOC_EDIT_DATA = json.loads(r'''
{
  "expected_input_sha256": {
    "AGENTS.md": "9cc0684419e909bbdd288608a0e1439c7838165080483c39b9f336e5ef4a2295",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md": "23cd8f94d4c884da1497af192306213595efb50b861eac2c7f4d05a512a3f671",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md": "e195b414e44251ad7467a9df88a0034eedc6633ea9f4f1d5d18f03044f28c40a",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/DOCUMENTATION_INDEX.md": "0de7b66d5ab69a383c87d353c7cc26ce9989a84bfd51448c7ab7984319b6fcff",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md": "7fccdca5b0cb7d40e02981a085403aff831a4ea77f222ce304f673c2f237d21b",
    "research/RHRC/integration/opica_followup/README.md": "7ebb9ef6ea7d592c3f14293f3f7cb4bd7964f309202d9dcef109ea094cc20d2d",
    "research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md": "de9aabe7985f839c39b62e82c3407c97bc21d831e283199ab5d81784fe68f327"
  },
  "edits": [
    {
      "path": "AGENTS.md",
      "old": "Forty-nine additional roots passed narrow gates and 10 original roots still lack\ncomplete implementations. Read the continuation STAGE18_HANDOVER.md (and the",
      "new": "Fifty additional roots passed narrow gates and 9 original roots still lack\ncomplete implementations. Read the continuation STAGE19_HANDOVER.md (and the"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
      "old": "The latest [Stage 18 handover](STAGE18_HANDOVER.md) records the multiplicity-sensitive zero-jet\n",
      "new": "The latest [Stage 19 handover](STAGE19_HANDOVER.md) records the original actual force-sampling\nconsumer (F1-F3), with both Fourier conventions, the actual lattice force, spectral sample identity\nand reflected boundary amplitude. The existing word/jet consumer is revalidated; the sample-sign\nconsumer is supporting mathematics and is not counted as a primary.\n[Stage 18](STAGE18_HANDOVER.md) records the multiplicity-sensitive zero-jet\n"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
      "old": "axioms and aggregate acceptance. `REMAINING_WORK.md` lists the 10 absent proofs.",
      "new": "axioms and aggregate acceptance. `REMAINING_WORK.md` lists the 9 absent proofs."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
      "old": "- Forty-nine additional original roots passed independent local module, full-type/",
      "new": "- Fifty additional original roots passed independent local module, full-type/"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
      "old": "  square-defect roots (Stage 16), the two boundary-amplitude roots (Stage 17) and\n  the zero-jet root (Stage 18); aggregate and full acceptance remain pending.\n- 10 original primary implementations are still absent.",
      "new": "  square-defect roots (Stage 16), the two boundary-amplitude roots (Stage 17),\n  the zero-jet root (Stage 18) and the actual force-sampling consumer (Stage 19);\n  aggregate and full acceptance remain pending.\n- 9 original primary implementations are still absent."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
      "old": "The second command builds nine repaired modules from current source, checks\nthe explicit independent consumers and their named standard-only axiom closures,",
      "new": "The second command builds {{MODULE_COUNT}} candidate modules from current source, checks\n{{CONSUMER_COUNT}} explicit independent consumer files and their named standard-only axiom closures,"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
      "old": "Complete the 10 absent roots without replacing them by supporting lemmas.",
      "new": "Complete the 9 absent roots without replacing them by supporting lemmas."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
      "old": "roots (Stage 16), the two boundary-amplitude roots (Stage 17) and the zero-jet root\n(Stage 18) now have narrow gates.",
      "new": "roots (Stage 16), the two boundary-amplitude roots (Stage 17), the zero-jet root\n(Stage 18) and the actual force-sampling consumer (Stage 19) now have narrow gates."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
      "old": "- `consumers/`: eight independent expected-type/domain consumer files covering\n  nine repaired modules. They are actual Lean sources used by narrow replay.",
      "new": "- `consumers/`: {{CONSUMER_COUNT}} independent expected-type/domain and supporting consumer files\n  used by the {{MODULE_COUNT}}-module narrow replay. Supporting files do not increase the primary-root count."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
      "old": "- 49: `PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`,",
      "new": "- 50: `PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`,"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
      "old": "and the [Stage 18](STAGE18_HANDOVER.md) multiplicity-sensitive zero-jet measures\n- 10: `OPEN_NO_COMPLETE_CANDIDATE`",
      "new": "the [Stage 18](STAGE18_HANDOVER.md) multiplicity-sensitive zero-jet measures, and the [Stage 19](STAGE19_HANDOVER.md) actual force-sampling consumer\n- 9: `OPEN_NO_COMPLETE_CANDIDATE`"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
      "old": "## 10 roots without complete candidate implementations",
      "new": "## 9 roots without complete candidate implementations"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
      "old": "- `actual_force_sampling_consumer`\n",
      "new": ""
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
      "old": "Implement the 10 absent roots above. Forty-nine roots now have narrow module,",
      "new": "Implement the 9 absent roots above. Fifty roots now have narrow module,"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
      "old": "and one Stage 18 root (zero-jet measures) are documented separately.",
      "new": "one Stage 18 root (zero-jet measures) and one Stage 19 root (actual force-sampling consumer) are documented separately."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
      "old": "both BoundaryAmplitude roots and the CoPoissonJets root now have narrow gates;",
      "new": "both BoundaryAmplitude roots, the CoPoissonJets root and the actual force-sampling consumer now have narrow gates;"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
      "old": "square-defect, boundary-amplitude and zero-jet formalization choices are recorded in the ledger.",
      "new": "square-defect, boundary-amplitude, zero-jet and force-sampling formalization choices are recorded in the ledger. The existing word/jet primary is revalidated at the changed Consumers source hash; ExpectedSampleSign is supporting mathematics, not an additional root."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/DOCUMENTATION_INDEX.md",
      "old": "checkpoint and its staged repairs; read [STAGE18_HANDOVER.md](STAGE18_HANDOVER.md)",
      "new": "checkpoint and its staged repairs; read [STAGE19_HANDOVER.md](STAGE19_HANDOVER.md)"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/DOCUMENTATION_INDEX.md",
      "old": "[Stage 18](STAGE18_HANDOVER.md) proves the CoPoissonJets root (R2-H1): at an actual strip zero of",
      "new": "[Stage 19](STAGE19_HANDOVER.md) proves the original actual force-sampling consumer (F1-F3):\nfor actual strip zeros with nonreal kappa, both Fourier conventions, the physical lattice force,\nforced log-unitary profile, arithmetic spectral density/sample identity and reflected generic\nboundary amplitude are composed without a homogeneous-eigenproblem conclusion. The existing\nword/jet primary is revalidated at the changed Consumers source hash; ExpectedSampleSign is\nsupporting mathematics and is not counted as a primary. The\n[evidence](evidence/current-codex/stage19/STATUS.json) pins the checked commit, tree, sources and logs.\n[Stage 18](STAGE18_HANDOVER.md) proves the CoPoissonJets root (R2-H1): at an actual strip zero of"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "ROOT_LEDGER_100.json, the latest [STAGE18_HANDOVER.md](STAGE18_HANDOVER.md) and the unchanged",
      "new": "ROOT_LEDGER_100.json, the latest [STAGE19_HANDOVER.md](STAGE19_HANDOVER.md) and the unchanged"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "- **Head.** `7360d44a` (Stage 18 record). Lean v4.33.0-rc2 and Mathlib `51e6992e` are pinned; never\n  run `lake update`.",
      "new": "- **Checked code checkpoint.** `{{CODE_COMMIT}}`, tree `{{CODE_TREE}}` (Stage 19).\n  Reconcile the live head before editing; later record commits do not inherit a new compiler receipt.\n  Lean v4.33.0-rc2 and Mathlib `51e6992e` remain pinned; never run `lake update`."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "- **Ledger.** 41 historical, 49 narrow (`PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`) and 10 absent",
      "new": "- **Ledger.** 41 historical, 50 narrow (`PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`) and 9 absent"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "- **Done this session (Stages 15 to 18).**",
      "new": "- **Stage 19.** The original `actual_force_sampling_consumer` is verified at narrow gates, with\n  ExpectedForceSampling and its actual-domain audits. ExpectedWordJet revalidates the existing\n  primary at the changed Consumers source hash. ExpectedSampleSign proves supporting sign\n  restrictions and does not add a primary root. Read the Stage 19 handover and STATUS.\n- **Retained previous sessions (Stages 15 to 18).**"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "- **CI.** On `c6ce649d`, 19 of 22 runs were green apart from the designed fail-closed gates (Stage 17\n  partial harvest). CI on `02c0ce8f` and `ff7b7c70` was superseded by later pushes. CI on `7360d44a`\n  was in progress at handoff.\n  - **First action:** harvest every run and job on the newest pushed head into the next stage record.\n  - The designed red gates are: Full release readiness (PR and push), opica-contract,\n    opica-component-summary, python-rhrc and rhkg-compiler-receipt.\n",
      "new": "- **CI and source authority.** The Stage 19 STATUS records the checked code commit/tree and\n  narrow gates, and links the bounded workflow harvest. Inspect every exact run/job disposition.\n  Companion PR evidence cannot pass a queued push job; pending, skipped, cancelled and failed\n  work remains explicit. Earlier source-head replays confer no new code-commit CI authority.\n  - **First action:** reconcile every run and job on the newest pushed head before changing proofs.\n  - The designed red gates remain Full release readiness (PR and push), opica-contract,\n    opica-component-summary, python-rhrc and rhkg-compiler-receipt.\n"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "## The 10 absent roots, in a workable order",
      "new": "## The 9 absent roots, in a workable order"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "1. **`Consumers.actual_force_sampling_consumer`** (F1-F3). A compiled draft is in\n   [drafts/](drafts/README.md). Install it into `Zeta23/OPICAFollowup/Consumers.lean` with\n   `import Zeta23.OPICAFollowup.BoundaryAmplitude` and re-verify the W01 word/jet consumer there.\n",
      "new": ""
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "2. **`ConfluentProfiles`**",
      "new": "1. **`ConfluentProfiles`**"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "3. **`FiniteSpanSeparation`**",
      "new": "2. **`FiniteSpanSeparation`**"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "4. **`NativeWindowRate.native_fixed_source_window_rate`**",
      "new": "3. **`NativeWindowRate.native_fixed_source_window_rate`**"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "5. **`MovingSourceWindowRate.native_slow_source_window_rate`**",
      "new": "4. **`MovingSourceWindowRate.native_slow_source_window_rate`**"
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "(MS1), after item 4.",
      "new": "(MS1), after item 3."
    },
    {
      "path": "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
      "old": "6. **The remaining `Consumers` roots.**",
      "new": "5. **The remaining `Consumers` roots.**"
    },
    {
      "path": "research/RHRC/integration/opica_followup/README.md",
      "old": "# Current draft checkpoint — 22 October 2026\n\nThe combined source and handover are now in the repository. Start at\n[the continuation guide](continuation/2026-10-22/README.md), read root AGENTS.md,\nand use its exact 100-root stage ledger. The original scope remains 100 roots /\n28 acceptance units; full release acceptance, RH, Step 4 and independent closing\ninequalities remain OPEN.\n\nThe checkpoint retains the historical 41-root exact-source subset and records six\nadditional primary roots with narrow local module, independent consumer and axiom\nchecks. It preserves five other unchecked candidates plus all 48 absent primary\nobligations. Local proof evidence and aggregate acceptance remain separate.\nThe cold exporter prerequisite fix and repaired parent metadata checks are included.\nThe new narrow candidate CI lane does not replace the full release gate.\n\nBoth foundational PDFs, preserved source inputs, independent consumers, prior\nCodex audits, new evidence review and a next-agent prompt are under that guide.\nThe versioned CONTINUATION_MANIFEST.json records these additional audit/handover\npaths without altering the frozen original footprint or mandatory theorem scope.\nFinal full-extension reconciliation and all-100 compiler linkage remain required.\n\nThe following text preserves the earlier 9b baseline description and research\nhistory. Its statements that the newly repaired candidate primaries remain open\nrefer to that earlier checkpoint; use the current ledger for individual gates.\n",
      "new": "# Current draft checkpoint — 24 October 2026\n\nStart at [the continuation guide](continuation/2026-10-22/README.md), root AGENTS.md,\n[Stage 19](continuation/2026-10-22/STAGE19_HANDOVER.md) and the\n[current ledger](continuation/2026-10-22/ROOT_LEDGER_100.json).\nAll 100 original primary roots and 28 acceptance units remain required.\n\nThe ledger records 41 historical source-bound roots, 50 additional narrow-gate\nroots and 9 absent implementations. This is not aggregate 91-root acceptance.\nStage 19 verifies the original actual force-sampling consumer at code commit\n`{{CODE_COMMIT}}`, tree `{{CODE_TREE}}`, revalidates the existing word/jet primary\nat its changed source hash and records supporting sample-sign mathematics without\ncounting another root. Read the\n[source-pinned STATUS](continuation/2026-10-22/evidence/current-codex/stage19/STATUS.json)\nfor exact compilation, expected types, physical domains, axioms and workflow dispositions.\n\nThe cold full100 receipt, independent review, parent extension, registration,\ncanonical regeneration and complete required workflow harvest remain OPEN.\nFull release acceptance, RH, Step 4 and independent closing inequalities remain OPEN.\n\nBoth foundational PDFs, frozen contracts, prior evidence and the stage pipeline\nremain under the continuation guide. The following text preserves the earlier\n9b-baseline description and research history; its historical counts and statements\nabout unfinished roots retain their earlier source scope. Use the current ledger\nfor moving status.\n"
    },
    {
      "path": "research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md",
      "old": "This is a **manual navigation view**, dated 22 October 2026, for",
      "new": "This is a **manual navigation view**, updated 24 October 2026, for"
    },
    {
      "path": "research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md",
      "old": "All **100 roots and 28 acceptance units remain required**.",
      "new": "All **100 roots and 28 acceptance units remain required**.\nThe latest [Stage 19 handover](../integration/opica_followup/continuation/2026-10-22/STAGE19_HANDOVER.md)\nand [source-pinned STATUS](../integration/opica_followup/continuation/2026-10-22/evidence/current-codex/stage19/STATUS.json)\nrecord the actual force-sampling consumer and retained word/jet revalidation. Supporting\nsample-sign results do not add roots. Aggregate and full-release acceptance remain OPEN."
    }
  ],
  "allowed_document_paths": [
    "AGENTS.md",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/REMAINING_WORK.md",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/DOCUMENTATION_INDEX.md",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/NEXT_AGENT_PROMPT.md",
    "research/RHRC/integration/opica_followup/README.md",
    "research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md"
  ],
  "manual_graph_role": "Navigation only; no arrow or generated graph changes",
  "preserve_parent_readme_suffix_after_first_separator": true
}
''')


# Parent documentation bytes have their own fixed review seal. The continuation
# inventory cannot authorize edits to this manual graph. Preserve the draft
# edit data above as provenance; exclude it from the executable record plan.
SEALED_MANUAL_GRAPH = 'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md'
DOC_EDIT_DATA['edits'] = [e for e in DOC_EDIT_DATA['edits'] if e['path'] != SEALED_MANUAL_GRAPH]
DOC_EDIT_DATA['allowed_document_paths'] = [p for p in DOC_EDIT_DATA['allowed_document_paths'] if p != SEALED_MANUAL_GRAPH]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path,
                        default=Path(os.environ.get('OPICA_REPO',
                            str(Path(__file__).resolve().parents[1] / 'opica-followup-repo'))))
    parser.add_argument('--code-commit', required=True)
    parser.add_argument('--code-tree', required=True)
    parser.add_argument('--write', action='store_true',
                        help='Apply the fully validated plan; default is validation/plan only')
    parser.add_argument('--report', type=Path,
                        default=Path(__file__).resolve().parent / 'record-update-plan.json')
    args = parser.parse_args()
    repo = args.repo.resolve(strict=True)
    require(not args.report.resolve().is_relative_to(repo),
            'Keep the update-plan receipt outside the checkout')
    c = repo / CONTINUATION
    status, runner, verified = validate_evidence(repo, c, args.code_commit, args.code_tree)
    ledger_path = c / 'ROOT_LEDGER_100.json'
    plans = {ledger_path: updated_ledger(repo, c, args.code_commit, args.code_tree, verified)}
    old_docs = {}
    new_docs = {}
    for relative in DOC_EDIT_DATA['allowed_document_paths']:
        path = repo / relative
        require(path.is_file() and not path.is_symlink(), f'Unexpected document target: {path}')
        require(sha(path) == DOC_EDIT_DATA['expected_input_sha256'][relative],
                f'Reviewed document bytes drifted; reconcile exact replacements first: {relative}')
        old_docs[relative] = path.read_bytes().decode('utf-8').replace('\r\n', '\n')
        new_docs[relative] = old_docs[relative]
    replacements = {'{{CODE_COMMIT}}': args.code_commit, '{{CODE_TREE}}': args.code_tree,
                    '{{MODULE_COUNT}}': str(len(verified['modules'])),
                    '{{CONSUMER_COUNT}}': str(len(verified['consumers']))}
    for edit in DOC_EDIT_DATA['edits']:
        relative, old, new = edit['path'], edit['old'], edit['new']
        require(relative in new_docs, 'Documentation edit escaped the explicit allowed path list')
        for token, value in replacements.items():
            new = new.replace(token, value)
        require(new_docs[relative].count(old) == 1,
                f'Expected exact unique documentation text changed: {relative}: {old[:70]!r}')
        new_docs[relative] = new_docs[relative].replace(old, new)
    parent_readme = 'research/RHRC/integration/opica_followup/README.md'
    require(old_docs[parent_readme].split('\n---\n', 1)[1]
            == new_docs[parent_readme].split('\n---\n', 1)[1],
            'Historical parent follow-up README suffix changed')
    manual = 'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md'
    require(sha(repo / manual) == DOC_EDIT_DATA['expected_input_sha256'][manual],
            'Independently sealed manual graph bytes changed; continuation inventory cannot repin them')
    for relative, text in new_docs.items():
        require(not any(token in text for token in replacements), f'Unresolved document template: {relative}')
        plans[repo / relative] = preserved_text_bytes(repo / relative, text)
    allowed_targets = {repo / p for p in DOC_EDIT_DATA['allowed_document_paths']} | {ledger_path}
    require(set(plans) == allowed_targets, 'Record plan changed its explicit path scope')
    require(all(path.is_relative_to(repo) for path in plans), 'Record plan escaped repository')
    require(not any('/sources/' in path.as_posix() or '/graph/generated/' in path.as_posix()
                    for path in plans), 'Read-only source or generated product in write plan')
    report = {
        'schema': 'OPICA_STAGE19_RECORD_UPDATE_PLAN_V1',
        'mode': 'APPLY' if args.write else 'VALIDATE_AND_PLAN_ONLY',
        'checked_commit': args.code_commit, 'checked_tree': args.code_tree,
        'status': STATUS_RELATIVE, 'status_sha256': sha(c / STATUS_RELATIVE),
        'runner': RUNNER_RELATIVE,
        'runner_sha256': digest(read_evidence(c / RUNNER_RELATIVE)),
        'only_new_primary': NEW_ROOT, 'existing_primary_revalidated': WORD_ROOT,
        'supporting_only': 'ExpectedSampleSign',
        'expected_counts': {HISTORICAL: 41, NARROW: 50, ABSENT: 9},
        'current_aggregate_accepted': False, 'full_release_accepted': False,
        'modules_checked': len(verified['modules']), 'consumer_files_checked': len(verified['consumers']),
        'changes': [{'path': path.relative_to(repo).as_posix(),
                     'before_sha256': sha(path), 'after_sha256': digest(data), 'bytes': len(data)}
                    for path, data in sorted(plans.items())],
        'owner_next_steps': ['Review this exact plan', 'Apply only after proof/evidence review',
                            'refresh_navigation.py --write then --check',
                            'refresh_manifest.py', 'preparation and full-release disposition gates',
                            'record commit, final exact-head source/workflow reconciliation'],
        'RH': 'OPEN', 'Step4': 'OPEN', 'independent_closing_inequalities': 'OPEN'}
    args.report.resolve().parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    if args.write:
        # All proof receipts, hashes, contracts, counts and exact edits were validated first.
        for path, data in plans.items():
            path.write_bytes(data)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
