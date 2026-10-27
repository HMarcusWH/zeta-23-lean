"""Create/verify the exact ancestor checkout and run its unchanged receipt CLIs.

Compiler and package setup must already be available. Artifacts remain outside
the source checkout. Source capture alone has no compiler proof authority.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid

try:
    from . import ancestor_projection as projection
    from .certificate_io import InvalidCertificate, failure_envelope
except ImportError:
    import ancestor_projection as projection
    from certificate_io import InvalidCertificate, failure_envelope

REPO = projection.REPO
FROZEN = projection.contract.FROZEN_COMMIT
LEGACY = {
    '76': ('research/RHRC/integration/opica/build_receipt.py',
           '97926d6a949fed7af0429a373b47abc772012834'),
    '100': ('research/RHRC/integration/opica_followup/build_receipt.py',
            'd53dd70d38b0762af130b1d19b795af259f505f5'),
}


def legacy_command(population: str, output: Path, *, python: str, lake: str) -> list[str]:
    projection.require(population in LEGACY, 'Unknown original root population')
    relative, base = LEGACY[population]
    result = [python, '-B', relative, '--requested-head', FROZEN,
              '--requested-base', base, '--output-dir', str(output)]
    # The 76 producer intentionally fixes its own `lake` executable. Its
    # executable search path is set to the selected pinned runtime's directory.
    if population == '100':
        result.extend(('--lake', lake))
    return result


def capture(repo: Path, checkout: Path, output: Path, *, populations: tuple[str, ...]=(),
            python: str=sys.executable, lake: str='lake', timeout: int=7200) -> dict:
    repo, checkout, output = repo.resolve(), checkout.resolve(), output.resolve()
    projection.require(type(timeout) is int and 1<=timeout<=86400, 'Invalid capture timeout')
    projection.require(not output.is_relative_to(repo) and not output.is_relative_to(checkout),
                       'Capture artifacts must be outside both source checkouts')
    projection.require(len(populations)==len(set(populations)) and set(populations)<=set(LEGACY),
                       'Unknown or duplicate root population')
    if checkout.exists():
        source = projection.verify_projection(checkout, reference_repo=repo)
    else:
        source = projection.create_projection(repo, checkout)
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema':'OPICA2_ANCESTOR_CAPTURE_V1', 'scope':'FROZEN_ANCESTOR_ONLY',
        'source_projection':source, 'commands':[], 'status':'SOURCE_CAPTURE_ONLY',
        'current_tree_compatibility_accepted':False,'baseline_replay_accepted':False,
        'full_core_accepted':False,'full_release_accepted':False,'RH':'OPEN','Step4':'OPEN'}
    result_path = output/'ancestor-capture.json'
    def save():
        result_path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    save()
    if populations:
        projection.require((checkout/'.lake/packages/mathlib').is_dir(),
                           'A compatible pinned package environment must be prepared in the private checkout')
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '2'
    if Path(lake).is_absolute():
        projection.require(Path(lake).is_file(), 'Selected pinned Lake runtime is missing')
        env['PATH'] = str(Path(lake).parent)+os.pathsep+env.get('PATH','')
    for population in populations:
        folder = output/('original-'+population)
        command = legacy_command(population,folder,python=python,lake=lake)
        stdout, stderr = output/(population+'.stdout.log'), output/(population+'.stderr.log')
        timed_out = False
        with stdout.open('wb') as out, stderr.open('wb') as err:
            try:
                run = subprocess.run(command,cwd=checkout,env=env,stdout=out,stderr=err,timeout=timeout)
                code = run.returncode
            except subprocess.TimeoutExpired:
                code, timed_out = None, True
        row = {'population':population,'argv':command,'cwd':str(checkout),'exit_code':code,
               'timed_out':timed_out,'stdout':stdout.name,'stderr':stderr.name,
               'stdout_sha256':hashlib.sha256(stdout.read_bytes()).hexdigest(),
               'stderr_sha256':hashlib.sha256(stderr.read_bytes()).hexdigest()}
        report['commands'].append(row)
        report['source_after_command'] = projection.verify_projection(checkout,reference_repo=repo)
        if code != 0:
            report['status'] = 'FAILED_OR_INCOMPLETE_LEGACY_REPLAY'
            save()
            return report
        receipt = folder/'compiler-receipt.json'
        projection.require(receipt.is_file(), 'Legacy producer returned success without its receipt')
        row['raw_receipt'] = str(receipt.relative_to(output))
        row['raw_receipt_sha256'] = hashlib.sha256(receipt.read_bytes()).hexdigest()
        # Recording a process and receipt is deliberately separate from the
        # independent parser/export comparison in dependency_delta.py.
        report['status'] = 'LEGACY_RECEIPTS_PRODUCED_NOT_YET_INDEPENDENTLY_REPLAY_VERIFIED'
        save()
    return report


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=REPO)
    parser.add_argument('--projection',type=Path)
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--population',action='append',choices=tuple(LEGACY),default=[])
    parser.add_argument('--lake',default='lake')
    parser.add_argument('--timeout',type=int,default=7200)
    args=parser.parse_args()
    run_id=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:8]
    run_root=args.repo.resolve().parent/'opica2-ancestor-runs'/run_id
    checkout=args.projection or run_root/'source'
    output=args.output_dir or run_root/'evidence'
    try:
        result=capture(args.repo,checkout,output,populations=tuple(args.population),lake=args.lake,timeout=args.timeout)
        print(json.dumps(result,indent=2))
        return 1 if result['status']=='FAILED_OR_INCOMPLETE_LEGACY_REPLAY' else 0
    except (InvalidCertificate,OSError,subprocess.SubprocessError,ValueError,KeyError) as exc:
        print(json.dumps(failure_envelope('ANCESTOR_CAPTURE_FAILED',str(exc)),indent=2))
        return 1


if __name__=='__main__':
    raise SystemExit(main())
