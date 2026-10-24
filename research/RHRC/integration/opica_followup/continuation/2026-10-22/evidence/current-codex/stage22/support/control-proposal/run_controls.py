"""Replay31 source-pinned controls against the exact clean Stage22 code pin.

This never grants aggregate acceptance or independent review. No owner source,
Lean output, build trace, registry, or approval file is written by this runner.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
SOURCE_READER = 'research/RHRC/integration/opica_followup/build_receipt.py'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
ERROR = re.compile(r'\berror(?:\([^\r\n)]*\))?:', re.I)
INFRASTRUCTURE = re.compile(
    r'unknown\s+(?:module|identifier|constant|namespace)|invalid\s+import|'
    r'error\(lean\.(?:unknownIdentifier|unknownNamespace|unknownConstant|invalidImport)\)|'
    r'object file[^\r\n]*(?:does not exist|not found|missing)|'
    r'(?:failed|unable|cannot) to (?:open|read|load) (?:file|module|object)|'
    r'no such file|cannot find (?:the file|module)|'
    r'maximum (?:recursion depth|number of heartbeats)|heartbeats? exceeded|'
    r'stack overflow|out of memory|internal exception|failed to execute|'
    r'\b(?:timeout|timed out|interrupted|segmentation fault|access violation|resource exhausted)\b', re.I)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def requested_names(source):
    return re.findall(r'^\s*#print\s+axioms\s+(\S+)\s*$', source, re.M)


def printed_axioms(log):
    result = {}
    for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S):
        require(name not in result, 'duplicate printed axiom audit: ' + name)
        result[name] = [item.strip() for item in values.split(',') if item.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        require(name not in result, 'duplicate printed axiom audit: ' + name)
        result[name] = []
    return result


def classify(row, source, log, exit_code):
    """Do not treat an unrelated infrastructure failure as a mutation rejection."""
    reasons = []
    try:
        axioms = printed_axioms(log)
    except ValueError as error:
        axioms = {}
        reasons.append(str(error))
    infrastructure = INFRASTRUCTURE.findall(log)
    if infrastructure:
        reasons.append('infrastructure/name-resolution failure: ' + repr(infrastructure))
    requested = requested_names(source)
    if row['expected'] == 'PASS':
        if exit_code != 0:
            reasons.append('positive control did not compile')
        if ERROR.search(log):
            reasons.append('compiler error in positive control')
        if not requested or any('.' not in name for name in requested):
            reasons.append('positive control requires explicit fully qualified axiom requests')
        if len(requested) != len(set(requested)):
            reasons.append('duplicate axiom request')
        if not set(requested) <= set(axioms):
            reasons.append('missing exact-name axiom output: ' + repr(sorted(set(requested)-set(axioms))))
        if 'sorryAx' in log or any(set(values) - ALLOWED for values in axioms.values()):
            reasons.append('positive control has an unadmitted axiom or error-recovery placeholder')
        observed = 'PASS_ACTUAL_FALSIFICATION_CONTROL'
    else:
        if exit_code == 0 or exit_code is None:
            reasons.append('negative control was not rejected by the compiler')
        if not ERROR.search(log):
            reasons.append('negative control has no recognized Lean error')
        needles = row['required_diagnostic_regex']
        if not needles:
            reasons.append('negative control has no intended-diagnostic requirements')
        missing = [needle for needle in needles if not re.search(needle, log, re.I | re.S)]
        if missing:
            reasons.append('wrong rejection/missing intended diagnostic: ' + repr(missing))
        if any(set(values) - (ALLOWED | {'sorryAx'}) for values in axioms.values()):
            reasons.append('negative output includes unexpected nonstandard axioms')
        # Lean may print sorryAx for an explicitly rejected declaration after
        # elaboration recovery. Such failed declarations receive no authority.
        observed = 'REJECTED_INTENDED_MUTATION'
    return {'passed': not reasons, 'observed': observed if not reasons else 'FAILED_CONTROL',
            'failure_reasons': reasons, 'requested_axiom_names': requested, 'axioms': axioms,
            'error_recovery_sorryAx_in_rejected_output': row['expected'] != 'PASS' and 'sorryAx' in log,
            'formal_authority_from_failed_declarations': False}


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()


def check_pin(repo, plan):
    require(git(repo, 'rev-parse', 'HEAD') == plan['checked_commit'], 'owner HEAD drift')
    require(git(repo, 'rev-parse', 'HEAD^{tree}') == plan['checked_tree'], 'owner tree drift')
    require(not git(repo, 'status', '--porcelain'), 'owner worktree must remain clean')


def cache_snapshot(repo):
    """Metadata guard detects shared build-cache writes, without modifying it."""
    result = {}
    cache = repo / '.lake/build'
    if cache.exists():
        for path in sorted(cache.rglob('*')):
            if path.is_file():
                stat = path.stat()
                result[path.relative_to(repo).as_posix()] = [stat.st_size, stat.st_mtime_ns]
    for name in ['.lake/lakefile.olean', '.lake/lakefile.olean.trace']:
        path = repo / name
        if path.is_file():
            stat = path.stat()
            result[name] = [stat.st_size, stat.st_mtime_ns, sha(path)]
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=HERE.parent / 'opica-followup-repo')
    parser.add_argument('--output-dir', required=True, type=Path, help='New external result folder; must not exist.')
    parser.add_argument('--lake', default='C:/Users/macka/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lake.exe')
    parser.add_argument('--workers', type=int, choices=[1, 2], default=2)
    parser.add_argument('--timeout-seconds', type=int, default=1800)
    args = parser.parse_args(argv)
    repo = args.repo.resolve()
    output = args.output_dir.resolve()
    require(not output.exists(), 'fresh output directory required')
    require(not output.is_relative_to(repo), 'all output must be outside the owner repository')
    plan_file = HERE / 'CONTROL_PLAN.json'
    plan = json.loads(plan_file.read_bytes())
    rows = plan['controls']
    require(len(rows) == 31 and sum(row['expected'] == 'PASS' for row in rows) == 4,
            'full31 inventory with27 negatives and4 positives required')
    require(len({row['name'] for row in rows}) == 31, 'duplicate control identity')
    require(sha(HERE / plan['planned_owner_source_manifest']) == plan['planned_owner_source_manifest_sha256'],
            'planned owner snapshot changed')
    require(sha(repo / SOURCE_READER) == plan['source_reader_sha256'], 'source reader changed')
    for row in rows:
        require(sha(HERE / 'sources' / row['file']) == row['source_sha256'], 'control source changed: ' + row['name'])
    check_pin(repo, plan)
    output.mkdir(parents=True)
    (output / 'sources').mkdir()
    (output / 'objects').mkdir()
    for row in rows:
        (output / 'sources' / row['file']).write_bytes((HERE / 'sources' / row['file']).read_bytes())
    write_json(output / 'CONTROL_PLAN.json', plan)
    env = dict(os.environ, LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    receipt = {'schema': 'OPICA_STAGE22_31_CLEAN_CONTROLS_V1', 'status': 'INCOMPLETE',
               'checked_commit': plan['checked_commit'], 'checked_tree': plan['checked_tree'],
               'original21_preserved_byte_exact': True, 'source_count': 31,
               'negative_source_files': 27, 'positive_source_files': 4,
               'plan_sha256': sha(plan_file), 'runner_sha256': sha(__file__),
               'started_at': started, 'controls': [], 'aggregate_accepted': False,
               'independent_review': 'NOT_ESTABLISHED', 'RH': 'OPEN', 'Step4': 'OPEN'}
    try:
        spec = importlib.util.spec_from_file_location('unchanged_stage22_source_reader', repo / SOURCE_READER)
        reader = importlib.util.module_from_spec(spec)
        # The accepted source reader is read only. Avoid .pyc output in owner.
        import sys
        sys.dont_write_bytecode = True
        spec.loader.exec_module(reader)
        before = reader.full_source_manifest(repo)
        planned = json.loads((HERE / plan['planned_owner_source_manifest']).read_bytes())
        require(before == planned, 'owner tracked source bytes differ from planned exact pin')
        write_json(output / 'source-before.json', before)
        caches_before = cache_snapshot(repo)
        write_json(output / 'cache-before.json', caches_before)
        version_command = [args.lake, 'env', 'lean', '--version']
        version_result = subprocess.run(version_command, cwd=repo, env=env, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, timeout=120)
        (output / 'compiler-version.log').write_bytes(version_result.stdout)
        version = version_result.stdout.decode('utf-8', errors='replace').strip()
        require(version_result.returncode == 0 and '4.33.0-rc2' in version and LEAN_COMMIT in version,
                'unexpected native compiler/version failure')
        receipt.update({'compiler': version, 'compiler_version_command': version_command,
                        'compiler_version_log_sha256': sha(output / 'compiler-version.log'),
                        'native_lake_sha256': sha(args.lake), 'environment': {'LEAN_NUM_THREADS': '1'},
                        'workers': args.workers})

        def run(row):
            source = output / 'sources' / row['file']
            log_file = output / (row['name'] + '.log')
            command = [args.lake, 'env', 'lean', '--root=' + str(output / 'sources'),
                       '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                       '-DmaxHeartbeats=800000', str(source), '-o', str(output / 'objects' / (row['name'] + '.olean'))]
            start = time.monotonic()
            try:
                check_pin(repo, plan)
                require(sha(source) == row['source_sha256'], 'control source drift')
                result = subprocess.run(command, cwd=repo, env=env, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, timeout=args.timeout_seconds)
                log_file.write_bytes(result.stdout)
                outcome = classify(row, source.read_text(encoding='utf-8'),
                                   result.stdout.decode('utf-8', errors='replace'), result.returncode)
                check_pin(repo, plan)
                require(sha(source) == row['source_sha256'], 'control source drift during compiler')
                exit_code = result.returncode
            except Exception as error:
                output_bytes = getattr(error, 'stdout', None) or b''
                if isinstance(output_bytes, str):
                    output_bytes = output_bytes.encode('utf-8')
                if not log_file.exists():
                    log_file.write_bytes(output_bytes + ('\nRUNNER_FAILURE: ' + repr(error)).encode('utf-8'))
                outcome = {'passed': False, 'observed': 'FAILED_CONTROL', 'failure_reasons': [repr(error)]}
                exit_code = None
            record = dict(row, **outcome, command=command, exit_code=exit_code,
                          log=log_file.name, log_sha256=sha(log_file), seconds=time.monotonic()-start)
            write_json(output / (row['name'] + '.receipt.json'), record)
            print(row['name'] + ': ' + outcome['observed'], flush=True)
            return record

        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            receipt['controls'] = list(pool.map(run, rows))
        check_pin(repo, plan)
        after = reader.full_source_manifest(repo)
        caches_after = cache_snapshot(repo)
        write_json(output / 'source-after.json', after)
        write_json(output / 'cache-after.json', caches_after)
        receipt['source_unchanged'] = before == after == planned
        receipt['shared_build_cache_unchanged'] = caches_before == caches_after
        for row in rows:
            require(sha(HERE / 'sources' / row['file']) == row['source_sha256'], 'plan source changed during run')
        require(receipt['source_unchanged'], 'owner source changed during run')
        require(receipt['shared_build_cache_unchanged'], 'shared build-cache changed during run')
        receipt['source_snapshot_sha256'] = sha(output / 'source-before.json')
        receipt['status'] = 'PASS_CONTROLS_ONLY' if all(row['passed'] for row in receipt['controls']) else 'FAIL_CONTROLS'
    except Exception as error:
        receipt['status'] = 'FAIL_PROTOCOL'
        receipt['protocol_failure'] = repr(error)
    receipt['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    write_json(output / 'CHECK_RESULT.json', receipt)
    print(receipt['status'], flush=True)
    return 0 if receipt['status'] == 'PASS_CONTROLS_ONLY' else 1


if __name__ == '__main__':
    raise SystemExit(main())
