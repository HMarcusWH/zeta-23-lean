"""Fail-closed, source-locked verification of reviewed supporting source.

Not an unrestricted candidate executor, full Round 4 integration gate, or
proof of Step 4. Run in a disposable checkout after an accepted-parent review.
"""
from __future__ import annotations
import argparse
import ast
from hashlib import sha1,sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

BASE='8109728135135a58eb98920180e03f77439c1da4'
PINNED_TREE='5442650eb749576e4a82e2d57460a4b97e19b5a9'
PREFIX=Path('research/RHRC/integration/opica_round4_support')
LEAN_MODULES=(
    'Zeta23.OPICARound4.ScalarShift',
    'Zeta23.OPICARound4.NativeRayConsumer',
    'Zeta23.OPICARound4.WitnessNorms',
    'Zeta23.OPICARound4',
    'Zeta23.OPICARound4.Validation',
)
ROOTS=(
  'shell_sub_norm_sq','regular_witness_norm_sq',
  'resonant_witness_norm_sq','regular_witness_rayleigh','resonant_witness_rayleigh',
  'common_scalar_shift_invariant','orthogonal_source_row_shift',
  'no_even_eigen_from_independent_ray_bound','no_odd_eigen_from_independent_ray_bound',
)
CONSUMERS=(
  'physical_shell_norm_consumer','regular_witness_norm_consumer',
  'resonant_witness_norm_consumer','regular_witness_rayleigh_consumer',
  'resonant_witness_rayleigh_consumer','common_scalar_shift_consumer',
  'orthogonal_source_row_consumer','even_source_bound_consumer',
  'odd_source_bound_consumer',
)
ALLOWED_AXIOMS=frozenset({'propext','Classical.choice','Quot.sound'})


def git_blob(data:bytes)->str:
    return sha1(b'blob '+str(len(data)).encode('ascii')+b'\0'+data).hexdigest()

def run(command:list[str],cwd:Path,log:Path,timeout:int,*,expect_success=True)->tuple[int,str]:
    with log.open('w',encoding='utf-8') as out:
        try:
            result=subprocess.run(command,cwd=cwd,stdout=out,stderr=subprocess.STDOUT,
                                  timeout=timeout,check=False,shell=False,
                                  env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(f'TIMEOUT {command!r}') from exc
        except FileNotFoundError as exc:
            raise RuntimeError(f'MISSING_EXECUTABLE {command[0]!r}') from exc
    content=log.read_text(encoding='utf-8',errors='replace')
    if expect_success and result.returncode!=0:
        raise RuntimeError(f'FAILED_EXIT_{result.returncode} in {log}')
    return result.returncode,content

def git(repo:Path,*args:str)->str:
    p=subprocess.run(['git',*args],cwd=repo,capture_output=True,text=True,check=True)
    return p.stdout.strip()

def strict_json_loads(text: str):
    """No duplicate keys, NaN, or Infinity in trusted evidence data."""
    def unique_pairs(pairs):
        obj = {}
        for key, value in pairs:
            if key in obj:
                raise ValueError(f'DUPLICATE_JSON_KEY:{key}')
            obj[key] = value
        return obj
    def reject_constant(value):
        raise ValueError(f'NONFINITE_JSON_CONSTANT:{value}')
    return json.loads(text, object_pairs_hook=unique_pairs, parse_constant=reject_constant)


def strict_json_file(path: Path):
    if path.is_symlink() or not path.is_file():
        raise ValueError(f'MISSING_OR_SYMLINKED_JSON:{path}')
    return strict_json_loads(path.read_text(encoding='utf-8'))


def validate_manifest(repo: Path) -> tuple[dict, list[str]]:
    manifest_path = repo/PREFIX/'PACKAGE_MANIFEST.json'
    manifest = strict_json_file(manifest_path)
    if not isinstance(manifest, dict) or set(manifest) != {
        'schema','parent_head','self_hash_policy','files'}:
        raise ValueError('INVALID_MANIFEST_KEYS')
    if manifest['schema'] != 'OPICA4_SUPPORT_PACKAGE_MANIFEST_V3':
        raise ValueError('INVALID_MANIFEST_SCHEMA')
    if manifest['parent_head'] != BASE or manifest['self_hash_policy'] != 'manifest excluded from its own hash':
        raise ValueError('INVALID_MANIFEST_BASE')
    entries = manifest['files']
    if type(entries) is not list or not entries:
        raise ValueError('EMPTY_MANIFEST_ENTRIES')
    paths = []
    for row in entries:
        if not isinstance(row, dict) or set(row) != {'path','bytes','sha256'}:
            raise ValueError('INVALID_MANIFEST_ROW')
        p = row['path']
        if type(p) is not str or not p or any(x in ('','.', '..') for x in p.split('/')) or \
           any(x in p for x in ('\\', ':', '\x00')) or p.startswith('/'):
            raise ValueError(f'INVALID_MANIFEST_PATH:{p!r}')
        if type(row['bytes']) is not int or row['bytes'] < 0:
            raise ValueError('INVALID_MANIFEST_SIZE')
        if type(row['sha256']) is not str or not re.fullmatch(r'[0-9a-f]{64}', row['sha256']):
            raise ValueError('INVALID_MANIFEST_DIGEST')
        paths.append(p)
    if len(paths) != len(set(paths)):
        raise ValueError('DUPLICATE_PACKAGE_PATH')
    prefix = repo.resolve()
    actual = []
    for root in (repo/PREFIX,repo/'Zeta23'/'OPICARound4'):
        if root.is_symlink() or not root.is_dir():
            raise ValueError(f'UNSAFE_PACKAGE_ROOT:{root}')
        for node in root.rglob('*'):
            if node.is_symlink():
                raise ValueError(f'SYMLINK_IN_PACKAGE:{node}')
            if node.is_file() and '__pycache__' not in node.parts:
                actual.append(node.relative_to(repo).as_posix())
    root_entry = repo/'Zeta23/OPICARound4.lean'
    if root_entry.is_symlink() or not root_entry.is_file():
        raise ValueError('MISSING_OR_SYMLINKED_ROOT_ENTRY')
    actual.append(root_entry.relative_to(repo).as_posix())
    if len(actual) != len(set(actual)):
        raise ValueError('DUPLICATE_PACKAGE_INVENTORY')
    exempt = {f'{PREFIX.as_posix()}/PACKAGE_MANIFEST.json'}
    if set(actual) != set(paths)|exempt:
        raise ValueError(f'PACKAGE_INVENTORY_MISMATCH:missing={sorted(set(paths)-set(actual))} '
                         f'unexpected={sorted(set(actual)-set(paths)-exempt)}')
    for p in paths:
        file = repo/p
        if file.is_symlink() or not file.is_file() or not file.resolve().is_relative_to(prefix):
            raise ValueError(f'UNSAFE_PACKAGE_SOURCE:{p}')
        blob = file.read_bytes()
        row = next(x for x in entries if x['path'] == p)
        if sha256(blob).hexdigest() != row['sha256'] or len(blob) != row['bytes']:
            raise ValueError(f'PACKAGE_HASH_OR_SIZE_MISMATCH:{p}')
        if file.suffix == '.py':
            ast.parse(blob, filename=str(file))
    return manifest, paths


AXIOM_PATTERN = re.compile(
    r"(?m)^[^\n]*?'(?P<name>Zeta23\.OPICARound4(?:\.Validation)?\.[A-Za-z_][A-Za-z0-9_']*)'[ \t]+"
    r"(?:(?P<none>does not depend on any axioms)|depends on axioms:[ \t]*\[(?P<axioms>[^\]]*)\])[ \t]*$"
)


def verify_axioms(text: str) -> dict[str,list[str]]:
    expected = {f'Zeta23.OPICARound4.{x}' for x in ROOTS}
    expected |= {f'Zeta23.OPICARound4.Validation.{x}' for x in CONSUMERS}
    matches = list(AXIOM_PATTERN.finditer(text))
    result = {}
    for match in matches:
        name = match.group('name')
        if name not in expected:
            raise RuntimeError(f'UNEXPECTED_AXIOM_RECORD:{name}')
        if name in result:
            raise RuntimeError(f'DUPLICATE_AXIOM_RECORD:{name}')
        if match.group('none'):
            result[name] = []
            continue
        axioms = [x.strip() for x in re.sub(r'\.\{[^}]*\}', '',
                  match.group('axioms')).split(',') if x.strip()]
        if set(axioms)-ALLOWED_AXIOMS:
            raise RuntimeError(f'UNAPPROVED_AXIOMS:{name}:{axioms}')
        result[name] = axioms
    if set(result) != expected:
        raise RuntimeError(f'AXIOM_INVENTORY_MISMATCH:missing={sorted(expected-set(result))}')
    return result


def verify_mutation_diagnostics(code: int, output: str) -> None:
    """A target type mismatch is necessary; process crashes/import failures are not enough."""
    if code != 1:
        raise RuntimeError(f'MUTATION_EXIT_NOT_EXPECTED:{code}')
    errors = [line.casefold() for line in output.splitlines() if 'error:' in line.casefold()]
    if not errors or not any('type mismatch' in line for line in errors):
        raise RuntimeError('MUTATION_DID_NOT_REJECT_STRONGER_TYPE')
    forbidden = ('unknown module','unknown identifier','file not found',
                 'unknown constant','no such file','segmentation fault','panic',
                 'killed','timeout','out of memory')
    if any(flag in output.casefold() for flag in forbidden):
        raise RuntimeError('MUTATION_FAILED_FOR_ENVIRONMENT_OR_UNEXPECTED_CAUSE')
    if any('type mismatch' not in line for line in errors):
        raise RuntimeError('MUTATION_EXTRA_UNEXPECTED_ERROR')


def require_pinned_parent(head: str, tree: str) -> None:
    if head != BASE or tree != PINNED_TREE:
        raise RuntimeError('EXACT_PINNED_PARENT_AND_TREE_REQUIRED')


def check_source_register(repo: Path) -> tuple[dict, dict[str,str]]:
    """Require the original commit/tree and every inspected blob at this exact HEAD."""
    lock = strict_json_file(repo/PREFIX/'SOURCE_REFERENCES.json')
    if not isinstance(lock, dict) or lock.get('schema') != 'OPICA4_SUPPORT_SOURCE_REFS_V2' or \
       lock.get('head') != BASE or lock.get('tree') != PINNED_TREE:
        raise RuntimeError('SOURCE_REGISTER_INVALID')
    refs = lock.get('source_blobs')
    if type(refs) is not list or not refs:
        raise RuntimeError('EMPTY_SOURCE_REGISTER')
    verified = {}
    for item in refs:
        if not isinstance(item,dict) or set(item) != {'path','blob','sha256'}:
            raise RuntimeError('INVALID_SOURCE_ENTRY')
        path = item['path']
        if not isinstance(path,str) or not path or path.startswith('/') or \
           any(x in ('','.', '..') for x in path.split('/')) or \
           any(x in path for x in ('\\', ':', '\x00')):
            raise RuntimeError('UNSAFE_SOURCE_PATH')
        if path in verified:
            raise RuntimeError('DUPLICATE_SOURCE_LOCK')
        if not isinstance(item['blob'],str) or not re.fullmatch('[0-9a-f]{40}',item['blob']) or \
           not isinstance(item['sha256'],str) or not re.fullmatch('[0-9a-f]{64}',item['sha256']):
            raise RuntimeError('INVALID_SOURCE_DIGEST')
        file=repo/path
        if file.is_symlink() or not file.is_file() or not file.resolve().is_relative_to(repo.resolve()):
            raise RuntimeError(f'MISSING_OR_UNSAFE_SOURCE:{path}')
        data=file.read_bytes()
        if git_blob(data)!=item['blob'] or sha256(data).hexdigest()!=item['sha256']:
            raise RuntimeError(f'UPSTREAM_SOURCE_MISMATCH:{path}')
        if git(repo,'rev-parse',f'{BASE}:{path}') != item['blob']:
            raise RuntimeError(f'UPSTREAM_COMMIT_BLOB_MISMATCH:{path}')
        verified[path]=item['blob']
    if not {'lean-toolchain','lake-manifest.json'}.issubset(verified):
        raise RuntimeError('MISSING_TOOLCHAIN_SOURCE_LOCK')
    if (repo/'lean-toolchain').read_text(encoding='utf-8').strip() != lock.get('toolchain'):
        raise RuntimeError('TOOLCHAIN_CONTENT_MISMATCH')
    return lock, verified

NEGATIVE_MUTATION='''import Zeta23.OPICARound4
noncomputable section
namespace Zeta23.OPICARound4
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
example (J : E →ₗᵢ[ℂ] F) (e : CCM.isometricDetectorComplement J) (x : E) :
    ‖(e : F) - J x‖ ^ 2 = ‖(e : F)‖ ^ 2 := by
  exact shell_sub_norm_sq J e x
end Zeta23.OPICARound4
'''

def main()->int:
    cli=argparse.ArgumentParser()
    cli.add_argument('--repo',required=True,type=Path)
    cli.add_argument('--evidence',type=Path,help='must name a fresh, nonexistent evidence directory')
    cli.add_argument('--timeout',type=int,default=7200)
    args=cli.parse_args()
    if args.timeout<1:cli.error('timeout must be positive')
    repo=args.repo.resolve()
    evidence=(args.evidence if args.evidence else Path(tempfile.gettempdir())/
              f'opica4-support-{os.getpid()}-{time.monotonic_ns()}').resolve()
    if evidence.is_relative_to(repo):
        cli.error('evidence directory must be outside the checkout')
    evidence.mkdir(parents=True,exist_ok=False)
    report={'schema':'OPICA4_SUPPORT_VERIFICATION_V3','status':'NOT_VERIFIED',
            'full_round4_accepted':False,'RH':'OPEN','Step4':'OPEN',
            'expected_head':BASE,'evidence_directory':str(evidence),'checks':[]}
    try:
        head=git(repo,'rev-parse','HEAD'); tree=git(repo,'rev-parse','HEAD^{tree}')
        report['head']=head; report['tree']=tree
        require_pinned_parent(head,tree)
        if git(repo,'status','--porcelain','--untracked-files=no'):
            raise RuntimeError('DIRTY_PARENT_TRACKED_FILES')
        lock, verified_sources = check_source_register(repo)
        source_reg_digest=sha256((repo/PREFIX/'SOURCE_REFERENCES.json').read_bytes()).hexdigest()
        report['checks'].append('source_identity:PASS')
        manifest,paths=validate_manifest(repo)
        initial={p:sha256((repo/p).read_bytes()).hexdigest() for p in paths}
        report['checks'].append('complete_overlay_inventory:PASS')
        for mode,flags in (('normal',[]),('optimized',['-O'])):
            code,contents=run([sys.executable,*flags,'-B',str(repo/PREFIX/'run_python_tests.py')],
                         repo,evidence/f'python-{mode}.log',args.timeout)
            # The last complete nonempty JSON line is the *test runner* result.
            rows=[strict_json_loads(s) for s in contents.splitlines()
                  if s.lstrip().startswith('{') and s.rstrip().endswith('}')]
            if len(rows)!=1 or rows[0].get('status')!='PASS' or rows[0].get('optimized')!=bool(flags):
                raise RuntimeError('PYTHON_TEST_RECEIPT_MISMATCH:'+mode)
            if rows[0].get('expected')!=rows[0].get('executed') or rows[0].get('skips') or \
               rows[0].get('failures') or rows[0].get('errors') or \
               rows[0].get('expected_failures') or rows[0].get('unexpected_successes'):
                raise RuntimeError('PYTHON_TEST_COUNTS_INVALID:'+mode)
            report['checks'].append('python-'+mode+':PASS')
            report[mode+'_test_count']=rows[0]['executed']
        _,version=run(['lake','env','lean','--version'],repo,evidence/'lean-version.log',args.timeout)
        report['lean_version']=version.strip()
        if '4.33.0-rc2' not in version:
            raise RuntimeError('LEAN_VERSION_MISMATCH')
        # Build the inherited imports in the project toolchain without updating pins.
        run(['lake','build','Zeta23.OPICARound3.SchurNegativeWitness',
             'Zeta23.CCM.CanonicalPoleNeutralShiftedSecular'],
            repo,evidence/'parent-lake.log',args.timeout)
        # The proper library build creates and imports actual current .olean files.
        run(['lake','build',*LEAN_MODULES],repo,evidence/'new-lake.log',args.timeout)
        _,text=run(['lake','env','lean','Zeta23/OPICARound4/Validation.lean'],
                   repo,evidence/'axiom-log.txt',args.timeout)
        report['axioms']=verify_axioms(text)
        report['checks'].append('lean_current_modules_and_axioms:PASS')
        # Isolate a syntactically real but false stronger conclusion.
        with tempfile.TemporaryDirectory(prefix='opica4-negative-',dir=str(repo)) as td:
            mutation=Path(td)/'RejectedNormMutation.lean'
            mutation.write_text(NEGATIVE_MUTATION,encoding='utf-8')
            rc,diags=run(['lake','env','lean',str(mutation)],repo,
                         evidence/'mutation.log',args.timeout,expect_success=False)
            verify_mutation_diagnostics(rc,diags)
        report['checks'].append('stronger_statement_mutation:REJECTED')
        final_manifest, final_paths=validate_manifest(repo)
        if final_manifest!=manifest or final_paths!=paths:
            raise RuntimeError('PACKAGE_MANIFEST_CHANGED_DURING_CHECK')
        if sha256((repo/PREFIX/'SOURCE_REFERENCES.json').read_bytes()).hexdigest()!=source_reg_digest:
            raise RuntimeError('SOURCE_REGISTER_CHANGED_DURING_CHECK')
        final_lock, final_sources=check_source_register(repo)
        if final_lock!=lock or final_sources!=verified_sources:
            raise RuntimeError('UPSTREAM_SOURCES_CHANGED_DURING_CHECK')
        for p,d in initial.items():
            if sha256((repo/p).read_bytes()).hexdigest()!=d:
                raise RuntimeError('OVERLAY_CHANGED_DURING_CHECK:'+p)
        if git(repo,'rev-parse','HEAD')!=head or \
           git(repo,'rev-parse','HEAD^{tree}')!=tree or \
           git(repo,'status','--porcelain','--untracked-files=no'):
            raise RuntimeError('HEAD_TREE_OR_PARENT_CHANGED_DURING_CHECK')
        report['checks'].append('final_inventory_and_upstream_source_recheck:PASS')
        report['status']='PASS_SUPPORT_SCOPE_ONLY'
        return 0
    except (OSError,ValueError,KeyError,RuntimeError,subprocess.SubprocessError,SyntaxError) as exc:
        report['status']='FAILED_OR_BLOCKED';report['error']=f'{type(exc).__name__}: {exc}'
        return 1
    finally:
        (evidence/'result.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n',encoding='utf-8')
        print(str(evidence/'result.json'))

if __name__=='__main__':raise SystemExit(main())
