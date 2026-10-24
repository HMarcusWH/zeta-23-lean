"""Replay narrow candidate gates. This never grants full-release acceptance."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
MODULES = ('MaskedNativeRate', 'ComplexLocalMeasures', 'AuxiliaryCompletions',
           'MultiplicityTail', 'DilatedComb', 'RenormalizedCoPoisson', 'FirstCellCost',
           'WeightedMixing', 'NearGapLimits', 'ProfileEulerMaclaurin', 'ZeroProfiles',
           'LogFourierSobolev', 'ForcedEuler', 'SamplingCompatibility',
           'SawtoothForce', 'WeightedSpectralMeasure', 'NativeResolvent', 'SquareDefect',
           'BoundaryAmplitude', 'CoPoissonJets', 'Consumers')
CONSUMERS = ('ExpectedMasks', 'ExpectedComplex', 'ExpectedAuxiliary',
             'ExpectedMultiplicity', 'ExpectedComb', 'ExpectedFirstCell',
             'ExpectedWeighted', 'ExpectedNearGap', 'ExpectedNearGapLimit',
             'ExpectedNormalizedLimit', 'ExpectedWeightedInverse',
             'ExpectedCoPoissonFamily', 'ExpectedCoPoissonOrderZero', 'ExpectedZeroMeasure',
             'ExpectedEulerMaclaurin', 'ExpectedZeroProfiles', 'ExpectedLogFourierSobolev',
             'ExpectedForcedEuler', 'ExpectedSamplingCompatibility', 'ExpectedSawtoothForce',
             'ExpectedWeightedSpectralMeasure', 'ExpectedNativeResolvent',
             'ExpectedSquareDefect', 'ExpectedBoundaryAmplitude',
             'ExpectedCoPoissonJets', 'ExpectedWordJet', 'ExpectedForceSampling',
             'ExpectedSampleSign')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--timeout', type=int, default=3600)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    require(not output.is_relative_to(REPO), 'Evidence must be outside the checkout')
    require(not output.exists() or not any(output.iterdir()), 'Fresh output directory required')
    output.mkdir(parents=True, exist_ok=True)
    records = []
    report = {'schema': 'OPICA_NARROW_CANDIDATE_REPLAY_V1',
              'status': 'FAILED_OR_BLOCKED', 'full_release_accepted': False,
              'aggregate_registration_accepted': False, 'RH': 'OPEN', 'Step4': 'OPEN',
              'independent_closing_inequalities': 'OPEN', 'commands': records}
    env = dict(os.environ)
    env.update(LEAN_NUM_THREADS='2', PYTHONDONTWRITEBYTECODE='1')

    def snapshot():
        paths = list((REPO/'Zeta23').rglob('*.lean'))
        paths += list((HERE/'consumers').glob('*.lean'))
        paths += [REPO/'lean-toolchain', REPO/'lake-manifest.json', REPO/'lakefile.toml']
        return {p.relative_to(REPO).as_posix(): sha(p) for p in sorted(paths)}

    def command(label, argv):
        start = time.monotonic()
        log = output/(label+'.log')
        with log.open('wb') as stream:
            try:
                proc = subprocess.run(argv, cwd=REPO, env=env, stdout=stream,
                                      stderr=subprocess.STDOUT, timeout=args.timeout)
                code = proc.returncode
            except subprocess.TimeoutExpired:
                code = 124
        records.append({'label': label, 'command': argv, 'exit_code': code,
                        'seconds': time.monotonic()-start, 'log': log.name,
                        'log_sha256': sha(log)})
        (output/'commands.json').write_text(json.dumps(records, indent=2)+'\n', encoding='utf-8')
        require(code == 0, 'Command failed: '+label)
        text = log.read_text(encoding='utf-8', errors='replace')
        require('sorryAx' not in text and not re.search(r'declaration uses [\x27\x60]sorry', text),
                'Placeholder found: '+label)
        return text

    try:
        before = snapshot()
        (output/'source-before.json').write_text(json.dumps(before, indent=2)+'\n', encoding='utf-8')
        report['head'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip()
        report['tree'] = subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=REPO, text=True).strip()
        report['dirty_status'] = subprocess.check_output(['git', 'status', '--porcelain'], cwd=REPO, text=True)
        require((REPO/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0-rc2', 'Wrong toolchain')
        packages = json.loads((REPO/'lake-manifest.json').read_text())['packages']
        require(next(p for p in packages if p['name'] == 'mathlib')['rev'] ==
                '51e6992efd06126df61a496bebf8f49482a4e129', 'Wrong Mathlib pin')
        version = command('version', [args.lake, 'env', 'lean', '--version'])
        require('4.33.0-rc2' in version and 'd8b18978322de05a8f3dba51ef03cf5461676c17' in version,
                'Actual compiler identity differs')
        command('build', [args.lake, 'build', *('Zeta23.OPICAFollowup.'+m for m in MODULES)])
        report['consumers'] = []
        for name in CONSUMERS:
            source = HERE/'consumers'/(name+'.lean')
            requested = re.findall(r'^#print axioms (\S+)\s*$', source.read_text(encoding='utf-8'), re.M)
            require(requested and len(requested) == len(set(requested)), 'Missing/duplicate axiom commands')
            text = command(name, [args.lake, 'env', 'lean', '-DmaxHeartbeats=800000',
                                 '-DrelaxedAutoImplicit=false', str(source.relative_to(REPO))])
            found = {name: set(a.strip() for a in axioms.split(',') if a.strip()) for name, axioms in
                     re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)}
            found.update({name: set() for name in re.findall(r"'([^']+)' does not depend on any axioms", text)})
            require(set(requested) <= set(found), 'Incomplete axiom output: '+name)
            require(all(found[n] <= ALLOWED_AXIOMS for n in requested), 'Unexpected axioms: '+name)
            report['consumers'].append({'name': name, 'source_sha256': sha(source),
                'axioms': {n: sorted(found[n]) for n in requested},
                'status': 'PASS_NARROW_TYPE_DOMAIN_AND_AXIOM_CHECK_ONLY'})
        require(before == snapshot(), 'Sources changed during execution')
        report['source_unchanged'] = True
        report['status'] = 'PASS_NARROW_ONLY'
    except (OSError, ValueError, KeyError, StopIteration, subprocess.SubprocessError) as error:
        report['error'] = str(error)
    (output/'CHECK_RESULT.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k not in {'commands', 'consumers'}}, indent=2))
    return 0 if report['status'] == 'PASS_NARROW_ONLY' else 1


if __name__ == '__main__':
    raise SystemExit(main())
