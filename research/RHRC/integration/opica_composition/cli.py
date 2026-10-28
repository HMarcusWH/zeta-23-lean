"""Trusted Round4 lane coordinator. All generated evidence stays outside Git."""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid
from .canonical import require,canonical_bytes,load_bytes,digest
from .snapshot import file_hash,unlinked
from .descendant import validate_descendant,BASE,BASE_TREE,git
from .accept import ROUND4_LANES,verify_lane_bundle,require_test_receipt,accept_application_scope

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
PROFILE=HERE/'PROFILE.json'

def write(path,row):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(canonical_bytes(row)+b'\n')

def external(repo,path):
    path=unlinked(path).resolve()
    require(not path.is_relative_to(Path(repo).resolve()),'Evidence must be outside the source checkout')
    return path

def experiment(repo,run_id,attempt):
    require(type(run_id)is str and run_id and type(attempt)is int and attempt>0,'Exact run identity required')
    return {'run_id':run_id,'attempt':attempt,'requested_commit':git(repo,'rev-parse','HEAD'),
            'requested_tree':git(repo,'rev-parse','HEAD^{tree}'),'profile_digest':file_hash(PROFILE)}

def lane_expected(lane,exp):
    require(lane in ROUND4_LANES,'Unknown required lane')
    scope='FROZEN_BASELINE' if lane=='PARENT_REGRESSION' else 'SELECTED_PROVIDER' if lane=='PROVIDER_SELECTED' else 'CURRENT_HOST'
    if scope=='FROZEN_BASELINE': checked={'commit':BASE,'tree':BASE_TREE}
    elif scope=='SELECTED_PROVIDER':
        from .provider import configuration
        config=configuration();checked={'repository':config['repository'],'commit':config['commit'],'toolchain':config['toolchain']}
    else:checked={'commit':exp['requested_commit'],'tree':exp['requested_tree']}
    return {'id':lane,'scope':scope,'checked':checked}

def worker_from_environment():
    from .contracts import WorkerConfig
    require('OPICA_NATIVE_CONFIG' in os.environ,'Prepared production worker configuration required')
    worker=WorkerConfig.from_dict(load_bytes(Path(os.environ['OPICA_NATIVE_CONFIG']).read_bytes()))
    require(worker.production,'Production worker required; development output cannot qualify')
    return worker

def native_output(label):
    require('OPICA_NATIVE_OUTPUT' in os.environ,'Provisioned bounded native volume required')
    root=unlinked(os.environ['OPICA_NATIVE_OUTPUT']).resolve()
    require(root.is_dir(),'Native volume absent')
    return root/(label+'-'+uuid.uuid4().hex)

def run_command(repo,argv,output,label):
    output=Path(output);log=output/(label+'.log')
    with log.open('xb') as stream:result=subprocess.run(argv,cwd=repo,stdout=stream,stderr=subprocess.STDOUT,timeout=30000)
    require(result.returncode==0,'Required command failed: '+str(log))
    return {'argv':list(map(str,argv)),'exit_code':result.returncode,'log':log.name,'sha256':file_hash(log)}

def generated_state(repo,output):
    # The original writer is preserved. Qualification checks products without rewriting source.
    before=git(repo,'status','--porcelain','--untracked-files=all')
    require(not before,'Generated-state qualification requires clean committed source')
    paths=load_bytes((Path(repo)/'research/RHRC/integration/opica_round4/BUILD_MANIFEST.json').read_bytes())['generated']
    require(len(paths)==81 and len({r['path'] for r in paths})==81,'Exact81 canonical products required')
    products={r['path']:file_hash(Path(repo)/r['path']) for r in paths}
    from .cache_owner import CacheWriterLease
    with CacheWriterLease(Path(repo)/'.lake/build'):
        canonical=run_command(repo,[sys.executable,'-B','research/RHRC/tools/materialize_derived_state.py','--check'],output,'canonical-current')
    records=[canonical,run_command(repo,[sys.executable,'-B','-m','unittest','research.RHRC.integration.opica_round2.tests.test_file_classes'],output,'classification')]
    require(not git(repo,'status','--porcelain','--untracked-files=all'),'Canonical checker changed source')
    require(products=={r['path']:file_hash(Path(repo)/r['path']) for r in paths},'Canonical check changed products')
    from .journal import Journal
    from .views import export_state
    with Journal(output/'determinism.db') as journal:
        first=export_state(journal);second=export_state(journal)
        require(first==second,'External views are not deterministic')
        for name,data in first.items():(output/name).write_bytes(data)
    return {'status':'PASS_GENERATED_STATE','canonical_products':products,'commands':records,
            'view_hashes':{k:file_hash(output/k) for k in first},'RH':'OPEN','Step4':'OPEN'}

def support_regressions(repo,output):
    rows=[]
    for mode in ([],['-O']):
        row=run_command(repo,[sys.executable,*mode,'-B','research/RHRC/integration/opica_round4_support/run_python_tests.py'],
                        output,'support-tests-'+('optimized' if mode else 'normal'))
        raw=(output/row['log']).read_bytes().splitlines()
        receipt=load_bytes(next(line for line in reversed(raw) if line.startswith(b'{')))
        require(receipt['status']=='PASS' and receipt['executed']==receipt['expected']==49 and receipt['skips']==
                receipt['errors']==receipt['failures']==receipt['expected_failures']==receipt['unexpected_successes']==0,
                'Exact49 support regressions incomplete')
        require(receipt['optimized'] is bool(mode),'Support regression mode differs')
        rows.append({'command':row,'receipt':receipt})
    return rows

def run_lane(lane,repo,output,exp,*,provider_root=None):
    repo=Path(repo).resolve();output=external(repo,output)
    require(not output.exists(),'Fresh lane output directory required');output.mkdir(parents=True)
    source=validate_descendant(repo,require_clean=True);write(output/'source.json',source)
    from .testing import run_modes,checked_inventory
    methods=[r for r in checked_inventory()['tests'] if r['lane']==lane]
    results={}
    if methods:results['tests']=run_modes(lane,output/'tests',repo)
    if lane=='CONTRACT':
        from .config import check_configuration
        results['contract']=check_configuration(repo)
    elif lane=='PARENT_REGRESSION':
        from .baseline import replay_parent
        results['parent']=replay_parent(repo,output/'frozen-parent')
    elif lane=='CURRENT_COMPATIBILITY':
        from .qualification import check_current_compatibility
        results['current']=check_current_compatibility(repo,native_output('current-native'),worker_from_environment())
    elif lane=='MATHEMATICAL_SUPPORT':
        from .qualification import check_mathematical_support
        results['mathematics']=check_mathematical_support(repo,native_output('mathematics-native'),worker_from_environment())
    elif lane=='SOURCE_NUMERICS':
        from research.RHRC.integration.opica_round4.source_evaluator import lane as numerical_lane
        results['independent']=numerical_lane(output/'source-producer',bits=256,seconds=60,require_clean=True)
        for mode in ([],['-O']):
            run_command(repo,[sys.executable,*mode,'-B','-m','unittest','research.RHRC.integration.opica_round4.tests.test_source_evaluator'],output,'source-tests-'+('optimized' if mode else 'normal'))
    elif lane=='PROVIDER_SELECTED':
        from .provider import produce,verify
        require(provider_root is not None,'Pinned provider checkout required')
        results['provider']=produce(Path(provider_root),output/'provider-producer')
        results['provider_independent']=verify(Path(provider_root),output/'provider-producer',output/'provider-independent')
    elif lane=='GENERATED_STATE':results['generated']=generated_state(repo,output)
    elif lane in {'COMPOSITION_FORMAL','SEMANTIC_NEGATIVES','REPLAY_CAMPAIGN','FRAMEWORK_ADAPTERS'}:
        require(methods,'Actual required lane tests absent')
        if lane=='FRAMEWORK_ADAPTERS':results['support_regressions']=support_regressions(repo,output)
    else:raise ValueError('Unsupported lane')
    # Test native evidence is generated on the bounded external volume. Copy its
    # complete tree after the test process exits; no omitted producer directories.
    native=os.environ.get('OPICA_NATIVE_OUTPUT')
    if lane in {'COMPOSITION_FORMAL','SEMANTIC_NEGATIVES','REPLAY_CAMPAIGN','CURRENT_COMPATIBILITY','MATHEMATICAL_SUPPORT'}:
        require(native,'Native evidence volume required')
        import shutil
        native_path=Path(native).resolve()
        require(not output.is_relative_to(native_path),'Bundle output must be outside the bounded native volume')
        shutil.copytree(native_path,output/'native-evidence')
    write(output/'results.json',results)
    write(output/'source-after.json',validate_descendant(repo,require_clean=True))
    files=sorted(p for p in output.rglob('*') if p.is_file())
    record={'schema':'OPICA4_LANE_BUNDLE_V1','lane_id':lane,'scope':lane_expected(lane,exp)['scope'],
            'experiment':exp,'checked':lane_expected(lane,exp)['checked'],'conclusion':'success',
            'artifacts':[{'path':p.relative_to(output).as_posix(),'bytes':p.stat().st_size,'sha256':file_hash(p)} for p in files],
            'records':['results.json','source.json','source-after.json']}
    write(output/'lane.json',record);return record

def verify_lane_raw(expected,record,files,repo,independent_output,provider_root=None):
    """Fixed trusted recipes, selected by the lane, never by a receipt callback."""
    from .testing import checked_inventory,run_modes
    lane=expected['id'];results=load_bytes(files['results.json'].read_bytes())
    source=load_bytes(files['source.json'].read_bytes());after=load_bytes(files['source-after.json'].read_bytes())
    current=validate_descendant(repo,require_clean=True)
    require(source==after==current,'Lane source differs from the clean current checkout')
    independent_output=external(repo,independent_output);independent_output.mkdir(parents=True,exist_ok=False)
    methods=sorted(r['method'] for r in checked_inventory()['tests'] if r['lane']==lane)
    if methods:
        for optimized,name in ((False,'normal'),(True,'optimized')):
            receipt=load_bytes(files['tests/'+name+'.json'].read_bytes());require_test_receipt(receipt,methods,optimized=optimized)
        # Reconstruct actual behavior from immutable source, not producer PASS flags.
        run_modes(lane,independent_output/'tests',repo)
    if lane=='CONTRACT':
        from .config import check_configuration
        require(results['contract']==check_configuration(repo),'Contract reconstruction differs')
    elif lane=='PARENT_REGRESSION':
        from .baseline import replay_parent
        fresh=replay_parent(repo,independent_output/'frozen-parent');old=results['parent']
        require((fresh['checked_commit'],fresh['checked_tree'],fresh['status'])==(old['checked_commit'],old['checked_tree'],old['status']),'Parent scope differs')
    elif lane=='CURRENT_COMPATIBILITY':
        from .qualification import check_current_compatibility
        fresh=check_current_compatibility(repo,native_output('current-native-independent'),worker_from_environment())
        require(fresh['compiler_rows']==results['current']['compiler_rows'],'Current complete compiler inventory differs')
    elif lane=='MATHEMATICAL_SUPPORT':
        from .qualification import check_mathematical_support
        fresh=check_mathematical_support(repo,native_output('mathematics-native-independent'),worker_from_environment())
        require(fresh['status']=='PASS_MATHEMATICAL_SUPPORT','Mathematical native replay failed')
    elif lane=='SOURCE_NUMERICS':
        from research.RHRC.integration.opica_round4.source_checker import verify_evaluator_evidence
        root=files['results.json'].parent
        verify_evaluator_evidence(root/'source-producer',independent_output/'source-independent',require_clean=True,
            expected_head=record['experiment']['requested_commit'],expected_tree=record['experiment']['requested_tree'])
    elif lane=='PROVIDER_SELECTED':
        from .provider import verify
        require(provider_root is not None,'Independent pinned provider required')
        verify(Path(provider_root),files['results.json'].parent/'provider-producer',independent_output/'provider-independent')
    elif lane=='GENERATED_STATE':generated_state(repo,independent_output)
    elif lane=='FRAMEWORK_ADAPTERS':support_regressions(repo,independent_output)
    return True

def aggregate(repo,bundles,output,exp,*,provider_root=None):
    output=external(repo,output);require(not output.exists(),'Fresh aggregate output required');output.mkdir(parents=True)
    requirements=[lane_expected(lane,exp) for lane in ROUND4_LANES]
    roots={lane:Path(bundles)/lane for lane in ROUND4_LANES}
    checkers={lane:(lambda expected,record,files,lane=lane:verify_lane_raw(expected,record,files,repo,output/lane,provider_root)) for lane in ROUND4_LANES}
    result=accept_application_scope(requirements,roots,experiment=exp,checkers=checkers,
                                    required_needs={lane:'success' for lane in ROUND4_LANES})
    write(output/'acceptance.json',result);return result

def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='command',required=True)
    for name in ('inspect','prepare','lane','accept'):
        q=sub.add_parser(name,aliases=['check-descendant'] if name=='inspect' else []);q.add_argument('--repo',type=Path,default=REPO);q.add_argument('--output','--out',type=Path,required=True)
        if name in {'lane','accept'}:
            q.add_argument('--run-id',required=True);q.add_argument('--attempt',type=int,required=True);q.add_argument('--provider-root',type=Path)
        if name=='lane':q.add_argument('--lane',choices=ROUND4_LANES,required=True)
        if name=='accept':q.add_argument('--bundles',type=Path,required=True)
    for name in ('freeze','inventory','plan','run-one','verify','replay','export'):
        q=sub.add_parser(name);q.add_argument('--repo',type=Path,default=REPO)
        q.add_argument('--output','--out',type=Path,required=True)
        if name=='freeze':q.add_argument('--experiment',required=True,type=Path)
        if name in {'inventory','plan','run-one','verify'}:q.add_argument('--snapshot',required=True,type=Path)
        if name=='plan':
            q.add_argument('--inventory',type=Path);q.add_argument('--target',required=True)
        if name=='run-one':
            q.add_argument('--proposals',required=True,type=Path);q.add_argument('--budget',type=int,default=1)
        if name in {'run-one','replay','export'}:q.add_argument('--journal',required=True,type=Path)
        if name=='verify':q.add_argument('--receipt',required=True,type=Path)
    a=p.parse_args()
    if a.command in {'inspect','check-descendant'}:write(external(a.repo,a.output),validate_descendant(a.repo,require_clean=True))
    elif a.command=='prepare':
        from .qualification import prepare_native
        from .cache_owner import CacheWriterLease
        with CacheWriterLease(Path(a.repo)/'.lake/build'):
            prepare_native(a.repo,external(a.repo,a.output))
    elif a.command=='lane':run_lane(a.lane,a.repo,a.output,experiment(a.repo,a.run_id,a.attempt),provider_root=a.provider_root)
    elif a.command=='accept':aggregate(a.repo,a.bundles,a.output,experiment(a.repo,a.run_id,a.attempt),provider_root=a.provider_root)
    else:
        from . import service
        if a.command=='freeze':service.freeze(a.repo,a.experiment,a.output,worker=worker_from_environment())
        elif a.command=='inventory':service.inventory(a.repo,a.snapshot,a.output,worker=worker_from_environment())
        elif a.command=='plan':service.plan(a.repo,a.snapshot,a.inventory or a.snapshot.parent/'inventory/inventory.json',a.target,a.output)
        elif a.command=='run-one':service.run_one(a.repo,a.snapshot,a.proposals,a.journal,a.output,worker=worker_from_environment(),budget=a.budget)
        elif a.command=='verify':service.verify(a.repo,a.snapshot,a.receipt,a.output,worker=worker_from_environment())
        elif a.command=='replay':service.replay(a.repo,a.journal,a.output)
        elif a.command=='export':service.export(a.repo,a.journal,a.output)
    return 0

if __name__=='__main__':sys.exit(main())
