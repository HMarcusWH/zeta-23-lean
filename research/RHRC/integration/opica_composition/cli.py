"""Trusted Round4 lane coordinator. All generated evidence stays outside Git."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import stat
import subprocess
import sys
import uuid
from contextlib import contextmanager
from .canonical import require,canonical_bytes,load_bytes,digest,MAX_BYTES,closed_keys
from .snapshot import (file_hash,unlinked,seal_evidence_tree,copy_evidence_tree,verify_evidence_tree,evidence_bytes,
                       pack_evidence_bundle,unpack_evidence_bundle,_evidence_directory,_transport_new_directory,_transport_seal,
                       _evidence_file,_evidence_identity,_evidence_regular,_transport_new_file,
                       _transport_identity,_transport_manifest,_transport_hash,_transport_zip_inventory,
                       TRANSPORT_MAX_ENTRIES,TRANSPORT_MAX_DEPTH,TRANSPORT_MAX_FILE_BYTES,
                       TRANSPORT_MAX_BYTES,TRANSPORT_MAX_CONTAINER_BYTES)
from .snapshot import retire_copied_evidence_tree
from .descendant import validate_descendant,BASE,BASE_TREE,git
from .accept import (ROUND4_LANES,verify_lane_bundle,require_test_receipt,accept_application_scope,
                     REPLAY_GROUP_IDS,group_lanes,verify_independent_group,join_independent_groups)

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
PROFILE=HERE/'PROFILE.json'
FAILURE_DIAGNOSTIC_MAX_FILES=512
FAILURE_DIAGNOSTIC_MAX_FILE_BYTES=16*1024*1024
FAILURE_DIAGNOSTIC_MAX_TOTAL_BYTES=128*1024*1024
FAILURE_DIAGNOSTIC_MAX_ENTRIES=20000
FAILURE_DIAGNOSTIC_MAX_OMISSIONS=256
NATIVE_EVIDENCE_LANES=frozenset({'COMPOSITION_FORMAL','SEMANTIC_NEGATIVES','REPLAY_CAMPAIGN',
                               'CURRENT_COMPATIBILITY','MATHEMATICAL_SUPPORT'})


def _publish_native_evidence(native,output):
    native=unlinked(native);output=unlinked(output)
    require(native.is_dir() and not output.is_relative_to(native) and not native.is_relative_to(output),
            'Native evidence and lane output must be disjoint')
    sealed=seal_evidence_tree(native)
    require(sealed[0]['files'],'Nonempty complete native evidence required')
    manifest=copy_evidence_tree(native,output/'native-evidence',sealed)
    write(output/'native-evidence-inventory.json',manifest)
    return manifest


def _failure_diagnostic_bytes(root,relative,maximum):
    """Bounded authenticated bytes; Linux keeps no-follow directory handles."""
    require(not Path(relative).is_absolute() and '..' not in Path(relative).parts,
            'Diagnostic relative path required')
    path=root/relative;unlinked(path)
    descriptors=[]
    try:
        if os.name!='nt':
            flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW
            descriptors.append(os.open(root,flags))
            for part in Path(relative).parts[:-1]:
                descriptors.append(os.open(part,flags,dir_fd=descriptors[-1]))
            fd=os.open(Path(relative).name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=descriptors[-1])
        else:
            import ctypes,msvcrt
            from ctypes import wintypes
            kernel=ctypes.WinDLL('kernel32',use_last_error=True)
            create=kernel.CreateFileW;create.restype=wintypes.HANDLE
            create.argtypes=[wintypes.LPCWSTR,wintypes.DWORD,wintypes.DWORD,
              wintypes.LPVOID,wintypes.DWORD,wintypes.DWORD,wintypes.HANDLE]
            close=kernel.CloseHandle;close.argtypes=[wintypes.HANDLE]
            query=kernel.GetFileInformationByHandleEx
            query.argtypes=[wintypes.HANDLE,ctypes.c_int,wintypes.LPVOID,wintypes.DWORD]
            class AttributeTag(ctypes.Structure):
                _fields_=[('attributes',wintypes.DWORD),('tag',wintypes.DWORD)]
            # OPEN_REPARSE_POINT opens the leaf itself rather than its target.
            handle=create(str(path),0x80000000,7,None,3,0x00200000|0x08000000,None)
            require(handle!=wintypes.HANDLE(-1).value,'Diagnostic no-follow handle unavailable')
            try:
                attributes=AttributeTag()
                require(query(handle,9,ctypes.byref(attributes),ctypes.sizeof(attributes)) and
                  not(attributes.attributes&(1024|16)),'Diagnostic reparse/directory handle refused')
                fd=msvcrt.open_osfhandle(handle,os.O_RDONLY|os.O_BINARY);handle=None
            finally:
                if handle is not None:close(handle)
        with os.fdopen(fd,'rb') as stream:
            before=os.fstat(stream.fileno())
            require(stat.S_ISREG(before.st_mode) and before.st_size<=maximum,'Diagnostic regular file/size differs')
            data=stream.read(maximum+1);after=os.fstat(stream.fileno())
            require(len(data)<=maximum and len(data)==before.st_size and
              (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns)==
              (after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns),'Diagnostic file changed while reading')
        unlinked(path)
        return data,hashlib.sha256(data).hexdigest()
    finally:
        for fd in reversed(descriptors):os.close(fd)


def _collect_failed_native_diagnostics(lane,repo,output):
    """Best-effort fixed test receipts and native files, outside lane acceptance."""
    repo=unlinked(repo).resolve();output=external(repo,output)
    require(output.is_dir(),'Validated existing lane output required for diagnostics')
    native=os.environ.get('OPICA_NATIVE_OUTPUT')
    if native:
        native=unlinked(native).resolve()
        require(native.is_dir() and not native.is_relative_to(repo) and
          not native.is_relative_to(output) and not output.is_relative_to(native),
          'Diagnostic native volume must be disjoint from source and lane output')
    destination=unlinked(output/'failure-diagnostics')
    require(not destination.exists(),'Fresh diagnostic directory required');destination.mkdir()
    report={'schema':'OPICA_FAILED_NATIVE_DIAGNOSTICS_V1','authority':'DIAGNOSTIC_ONLY_NOT_ACCEPTANCE',
      'lane':lane,'native_root':str(native) if native else None,'files':[],'omissions':[],'omission_counts':{},
      'traversal_truncated':False,'omissions_truncated':False,'retained_bytes':0,
      'limits':{'files':FAILURE_DIAGNOSTIC_MAX_FILES,'file_bytes':FAILURE_DIAGNOSTIC_MAX_FILE_BYTES,
        'total_bytes':FAILURE_DIAGNOSTIC_MAX_TOTAL_BYTES,'entries':FAILURE_DIAGNOSTIC_MAX_ENTRIES}}
    def omit(relative,reason,**details):
        report['omission_counts'][reason]=report['omission_counts'].get(reason,0)+1
        if len(report['omissions'])<FAILURE_DIAGNOSTIC_MAX_OMISSIONS:
            report['omissions'].append({'path':relative,'reason':reason,**details})
        else:report['omissions_truncated']=True
    stack=[native] if native else [];candidates=[];entries=0
    while stack:
        directory=stack.pop();relative=directory.relative_to(native).as_posix()
        scan_descriptors=[]
        try:
            unlinked(directory)
            if os.name!='nt':
                flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW
                scan_descriptors.append(os.open(native,flags))
                for part in directory.relative_to(native).parts:
                    scan_descriptors.append(os.open(part,flags,dir_fd=scan_descriptors[-1]))
            with os.scandir(scan_descriptors[-1] if scan_descriptors else directory) as iterator:
                for entry in iterator:
                    entries+=1
                    if entries>FAILURE_DIAGNOSTIC_MAX_ENTRIES:
                        report['traversal_truncated']=True;omit('.', 'TRAVERSAL_LIMIT');stack.clear();break
                    path=directory/entry.name;rel=path.relative_to(native).as_posix();info=os.lstat(path)
                    if scan_descriptors and not(stat.S_ISLNK(info.st_mode) or getattr(info,'st_file_attributes',0)&1024):
                        info=os.stat(entry.name,dir_fd=scan_descriptors[-1],follow_symlinks=False)
                    if stat.S_ISLNK(info.st_mode) or getattr(info,'st_file_attributes',0)&1024:
                        omit(rel,'LINK_OR_REPARSE_REFUSED');continue
                    if stat.S_ISDIR(info.st_mode):
                        if len(Path(rel).parts)>64:omit(rel,'DEPTH_LIMIT')
                        else:stack.append(path)
                    elif not stat.S_ISREG(info.st_mode):omit(rel,'NONREGULAR_REFUSED')
                    elif path.name in {'lane.json','acceptance.json'}:omit(rel,'ACCEPTANCE_RECORD_REFUSED')
                    elif path.suffix not in {'.log','.json','.lean'}:omit(rel,'UNSELECTED_EXTENSION')
                    else:candidates.append((rel,info.st_size))
        except (OSError,ValueError) as error:omit(relative,'DIRECTORY_READ_FAILED',error=type(error).__name__)
        finally:
            for fd in reversed(scan_descriptors):os.close(fd)
        if report['traversal_truncated']:break
    def priority(row):
        path=Path(row[0]);return (0 if path.name=='result.json' else
          1 if path.suffix=='.log' else 2 if path.suffix=='.lean' else 3,row[0])
    def save(path,data):
        unlinked(path.parent);path.parent.mkdir(parents=True,exist_ok=True);unlinked(path.parent)
        fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0),0o600)
        with os.fdopen(fd,'wb') as stream:stream.write(data)
    # Test lanes can fail before native work starts. Only these six authored
    # test output paths and the fixed canonical command log are eligible:
    # receipt fields cannot redirect collection.
    # They share the native collector's byte/file budgets and no-follow reads.
    fixed_outputs=['tests/'+mode+suffix for mode in ('normal','optimized')
                   for suffix in ('.json','.log','.driver.log')]+['canonical-current.log']
    for relative in fixed_outputs:
        try:
            path=unlinked(output/relative);info=os.lstat(path)
            if not stat.S_ISREG(info.st_mode):omit(relative,'NONREGULAR_REFUSED');continue
            if info.st_size>FAILURE_DIAGNOSTIC_MAX_FILE_BYTES:
                omit(relative,'PER_FILE_LIMIT',bytes=info.st_size);continue
            if len(report['files'])>=FAILURE_DIAGNOSTIC_MAX_FILES:
                omit(relative,'FILE_COUNT_LIMIT',bytes=info.st_size);continue
            remaining=FAILURE_DIAGNOSTIC_MAX_TOTAL_BYTES-report['retained_bytes']
            if info.st_size>remaining:omit(relative,'TOTAL_BYTES_LIMIT',bytes=info.st_size);continue
            data=evidence_bytes(output,relative,min(remaining,FAILURE_DIAGNOSTIC_MAX_FILE_BYTES))
            value=hashlib.sha256(data).hexdigest()
            save(destination/relative,data)
            report['files'].append({'path':relative,'bytes':len(data),'sha256':value})
            report['retained_bytes']+=len(data)
        except FileNotFoundError:continue
        except (OSError,ValueError) as error:
            omit(relative,'FILE_READ_OR_COPY_FAILED',error=type(error).__name__)
    for relative,size in sorted(candidates,key=priority):
        if size>FAILURE_DIAGNOSTIC_MAX_FILE_BYTES:omit(relative,'PER_FILE_LIMIT',bytes=size);continue
        if len(report['files'])>=FAILURE_DIAGNOSTIC_MAX_FILES:omit(relative,'FILE_COUNT_LIMIT',bytes=size);continue
        remaining=FAILURE_DIAGNOSTIC_MAX_TOTAL_BYTES-report['retained_bytes']
        if size>remaining:omit(relative,'TOTAL_BYTES_LIMIT',bytes=size);continue
        try:
            data,value=_failure_diagnostic_bytes(native,relative,min(remaining,FAILURE_DIAGNOSTIC_MAX_FILE_BYTES))
            save(destination/'native'/relative,data)
            report['files'].append({'path':'native/'+relative,'bytes':len(data),'sha256':value})
            report['retained_bytes']+=len(data)
        except (OSError,ValueError) as error:omit(relative,'FILE_READ_OR_COPY_FAILED',error=type(error).__name__)
    save(destination/'index.json',canonical_bytes(report)+b'\n')
    return report


def run_lane(lane,repo,output,exp,*,provider_root=None):
    repo=unlinked(repo).resolve();output=external(repo,output)
    require(not output.exists(),'Fresh lane output directory required');output.mkdir(parents=True)
    try:return _run_lane_impl(lane,repo,output,exp,provider_root=provider_root)
    except BaseException:
        try:_collect_failed_native_diagnostics(lane,repo,output)
        except Exception as error:
            try:sys.stderr.write('OPICA_DIAGNOSTIC_ONLY_COLLECTION_FAILED '+type(error).__name__+'\n')
            except (OSError,ValueError,AttributeError):pass
        raise

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


def _independent_native_parent(repo, output):
    """Production admission: resident scratch and retained disk are distinct."""
    worker_from_environment()
    require(sys.platform == 'linux', 'Independent native replay requires Linux production storage')
    original = os.environ.get('OPICA_NATIVE_OUTPUT')
    require(original, 'Provisioned native replay root required')
    parent = unlinked(original).resolve()
    require(parent.is_dir() and not parent.is_relative_to(Path(repo).resolve()) and
            not output.is_relative_to(parent) and not parent.is_relative_to(output),
            'Native replay root, source and independent evidence must be disjoint')
    require(os.stat(parent).st_dev != os.stat(output).st_dev and
            os.stat(output.parent.parent).st_dev == os.stat(output).st_dev,
            'Independent native archive must leave the provisioned native volume')
    observed = subprocess.run(['/usr/bin/findmnt', '--noheadings', '--output', 'FSTYPE',
                               '--target', str(output)], stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=10)
    require(observed.returncode == 0 and len(observed.stdout) <= 128 and
            len(observed.stdout.splitlines()) == 1 and
            re.fullmatch(rb'[A-Za-z0-9_+.-]+', observed.stdout.strip()) is not None and
            observed.stdout.strip() not in {b'tmpfs', b'ramfs'},
            'Ordinary evidence filesystem required for retained native archives')
    return parent


@contextmanager
def _independent_native_scope(lane, repo, output, exp):
    """Keep only the active native lane resident; preserve its complete bytes."""
    if lane not in NATIVE_EVIDENCE_LANES:
        yield
        return
    from .testing import emit_phase_diagnostic
    original = os.environ.get('OPICA_NATIVE_OUTPUT')
    parent = _independent_native_parent(repo, output)
    scratch = parent / ('acceptance-' + lane + '-' + uuid.uuid4().hex)
    owned = _transport_new_directory(scratch)
    # The archive remains on the ordinary evidence filesystem, outside both
    # this lane's tmpfs subtree and the volume shared with subsequent workers.
    archive = output.parent.parent / ('opica4-independent-native-' + lane + '-' + uuid.uuid4().hex)
    os.environ['OPICA_NATIVE_OUTPUT'] = str(scratch)
    try:
        emit_phase_diagnostic(lane, 'native.start')
        try:
            yield
        except BaseException:
            try:
                _collect_failed_native_diagnostics(lane, repo, output)
            except BaseException:
                pass
            raise
        emit_phase_diagnostic(lane, 'native.archive.start')
        sealed = _transport_seal(scratch)
        require(sealed[0]['files'], 'Complete nonempty independent native evidence required')
        require(sealed[1][''][:3] == owned[''], 'Owned native replay root changed')
        manifest = copy_evidence_tree(scratch, archive, sealed)
        # Explicit directory entries and hidden files survive the outer
        # artifact upload as the existing closed stored transport container.
        transport = pack_evidence_bundle(archive, output / 'independent-native-transport',
                                         {'lane_id': lane, 'experiment': exp})
        retire_copied_evidence_tree(scratch, archive, sealed,
                                   approved_parent=parent, owned_identity=owned[''])
        write(output / 'independent-native-archive.json',
              {'schema': 'OPICA_INDEPENDENT_NATIVE_ARCHIVE_V1', 'lane': lane,
               'experiment': exp, 'complete_inventory': manifest,
               'transport': transport, 'scratch_retired': True})
        emit_phase_diagnostic(lane, 'native.archive.end')
    finally:
        os.environ['OPICA_NATIVE_OUTPUT'] = original

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

def _run_lane_impl(lane,repo,output,exp,*,provider_root=None):
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
            name='optimized' if mode else 'normal'
            run_command(repo,[sys.executable,*mode,'-B','-m','research.RHRC.integration.opica_round4.source_research',
                '--output-dir',str(output/('source-research-'+name))],output,'source-research-'+name)
            run_command(repo,[sys.executable,*mode,'-B','-m','unittest','research.RHRC.integration.opica_round4.tests.test_source_research'],output,'source-research-tests-'+name)
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
    native_manifest=None
    if lane in NATIVE_EVIDENCE_LANES:
        require(native,'Native evidence volume required')
        native_path=unlinked(native)
        require(not native_path.is_relative_to(repo) and not Path(repo).is_relative_to(native_path),
                'Native evidence must be disjoint from source')
        native_manifest=_publish_native_evidence(native_path,output)
    write(output/'results.json',results)
    write(output/'source-after.json',validate_descendant(repo,require_clean=True))
    files=sorted(p for p in output.rglob('*') if p.is_file())
    record={'schema':'OPICA4_LANE_BUNDLE_V1','lane_id':lane,'scope':lane_expected(lane,exp)['scope'],
            'experiment':exp,'checked':lane_expected(lane,exp)['checked'],'conclusion':'success',
            'artifacts':[{'path':p.relative_to(output).as_posix(),'bytes':p.stat().st_size,'sha256':file_hash(p)} for p in files],
            'records':['results.json','source.json','source-after.json']}
    if native_manifest is not None:
        require(load_bytes(evidence_bytes(output,'native-evidence-inventory.json',MAX_BYTES))==native_manifest,
                'Sealed native evidence manifest changed')
        verify_evidence_tree(output/'native-evidence',native_manifest)
    write(output/'lane.json',record);return record

def verify_lane_raw(expected,record,files,repo,independent_output,provider_root=None):
    """Fixed trusted recipes, selected by the lane, never by a receipt callback."""
    from .testing import checked_inventory,run_modes
    lane=expected['id'];results=load_bytes(files['results.json'].read_bytes())
    source=load_bytes(files['source.json'].read_bytes());after=load_bytes(files['source-after.json'].read_bytes())
    current=validate_descendant(repo,require_clean=True)
    require(source==after==current,'Lane source differs from the clean current checkout')
    if lane in NATIVE_EVIDENCE_LANES:
        require('native-evidence-inventory.json' in files,'Complete native evidence manifest required')
        manifest_path=unlinked(files['native-evidence-inventory.json'])
        manifest=load_bytes(evidence_bytes(manifest_path.parent,manifest_path.name,MAX_BYTES))
        verify_evidence_tree(manifest_path.parent/'native-evidence',manifest)
        require({name for name in files if name.startswith('native-evidence/')}==
                {'native-evidence/'+row['path'] for row in manifest['files']},
                'Bundle native evidence file inventory differs')
    independent_output=external(repo,independent_output);independent_output.mkdir(parents=True,exist_ok=False)
    from .testing import emit_phase_diagnostic
    emit_phase_diagnostic(lane, 'replay.start')
    with _independent_native_scope(lane, repo, independent_output, record['experiment']):
        _replay_lane_behavior(lane, results, record, files, repo, independent_output, provider_root)
    emit_phase_diagnostic(lane, 'replay.end')
    return True


def _replay_lane_behavior(lane, results, record, files, repo, independent_output, provider_root):
    from .testing import checked_inventory, run_modes, emit_phase_diagnostic
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
        emit_phase_diagnostic(lane, 'compiler.atlas.start')
        fresh=check_current_compatibility(repo,native_output('current-native-independent'),worker_from_environment())
        require(fresh['compiler_rows']==results['current']['compiler_rows'],'Current complete compiler inventory differs')
        emit_phase_diagnostic(lane, 'compiler.atlas.end')
    elif lane=='MATHEMATICAL_SUPPORT':
        from .qualification import check_mathematical_support
        emit_phase_diagnostic(lane, 'compiler.mathematics.start')
        fresh=check_mathematical_support(repo,native_output('mathematics-native-independent'),worker_from_environment())
        require(fresh['status']=='PASS_MATHEMATICAL_SUPPORT','Mathematical native replay failed')
        emit_phase_diagnostic(lane, 'compiler.mathematics.end')
    elif lane=='SOURCE_NUMERICS':
        from research.RHRC.integration.opica_round4.source_checker import verify_evaluator_evidence
        root=files['results.json'].parent
        fresh=verify_evaluator_evidence(root/'source-producer',independent_output/'source-independent',require_clean=True,
            expected_head=record['experiment']['requested_commit'],expected_tree=record['experiment']['requested_tree'])
        write(independent_output/'source-independent-result.json',fresh)
        from research.RHRC.integration.opica_round4.source_research import verify_campaign
        for name in ('normal','optimized'):
            verify_campaign(root/('source-research-'+name),independent_output/('source-research-independent-'+name),require_clean=True)
    elif lane=='PROVIDER_SELECTED':
        from .provider import verify
        require(provider_root is not None,'Independent pinned provider required')
        verify(Path(provider_root),files['results.json'].parent/'provider-producer',independent_output/'provider-independent')
    elif lane=='GENERATED_STATE':
        emit_phase_diagnostic(lane, 'canonical.start')
        fresh=generated_state(repo,independent_output)
        write(independent_output/'generated-state.json',fresh)
        emit_phase_diagnostic(lane, 'canonical.end')
    elif lane=='FRAMEWORK_ADAPTERS':support_regressions(repo,independent_output)
    return True

def aggregate(repo,bundles,output,exp,*,provider_root=None):
    output=external(repo,output);require(not output.exists(),'Fresh aggregate output required');output.mkdir(parents=True)
    requirements=[lane_expected(lane,exp) for lane in ROUND4_LANES]
    roots={lane:Path(bundles)/lane for lane in ROUND4_LANES}
    checkers={lane:(lambda expected,record,files,lane=lane:verify_lane_raw(expected,record,files,repo,output/lane,provider_root)) for lane in ROUND4_LANES}
    original = os.environ.get('OPICA_ACCEPTANCE_DIAGNOSTICS')
    os.environ['OPICA_ACCEPTANCE_DIAGNOSTICS'] = '1'
    try:
        result=accept_application_scope(requirements,roots,experiment=exp,checkers=checkers,
                                        required_needs={lane:'success' for lane in ROUND4_LANES})
    finally:
        if original is None:
            os.environ.pop('OPICA_ACCEPTANCE_DIAGNOSTICS', None)
        else:
            os.environ['OPICA_ACCEPTANCE_DIAGNOSTICS'] = original
    write(output/'acceptance.json',result);return result


def pack_lane_bundle(repo,bundle,output,lane,exp):
    """Transport publication requires the completed, exact lane record."""
    bundle=external(repo,bundle);output=external(repo,output)
    native=os.environ.get('OPICA_NATIVE_OUTPUT')
    if native:
        native=unlinked(native)
        require(not output.is_relative_to(native) and not native.is_relative_to(output),
                'Transport staging and native output must be disjoint')
    current=validate_descendant(repo,require_clean=True)
    sealed=_transport_seal(bundle)
    record=load_bytes(evidence_bytes(bundle,'lane.json',MAX_BYTES))
    closed_keys(record,{'schema','lane_id','scope','experiment','checked','conclusion','artifacts','records'})
    expected=lane_expected(lane,exp)
    require(record['schema']=='OPICA4_LANE_BUNDLE_V1' and record['lane_id']==lane and
            record['scope']==expected['scope'] and record['checked']==expected['checked'] and
            record['experiment']==exp and record['conclusion']=='success','Completed exact lane required for transport')
    require(type(record['artifacts'])is list and
            sorted(record['artifacts'],key=lambda row:row['path'])==
            [row for row in sealed[0]['files'] if row['path']!='lane.json'],
            'Transport lane artifact inventory/content differs')
    files={row['path'] for row in sealed[0]['files'] if row['path']!='lane.json'}
    require(type(record['records'])is list and record['records'] and set(record['records'])<=files,
            'Transport lane scientific/command records absent')
    # Descriptor-bound reads avoid the legacy verifier's path-based reads at
    # this new boundary. Acceptance still runs that verifier and its fixed
    # independent scientific/native reconstruction, without changed semantics.
    require(load_bytes(evidence_bytes(bundle,'source.json',MAX_BYTES))==current==
            load_bytes(evidence_bytes(bundle,'source-after.json',MAX_BYTES)),
            'Transport lane source differs from clean current checkout')
    if lane in NATIVE_EVIDENCE_LANES:
        manifest=load_bytes(evidence_bytes(bundle,'native-evidence-inventory.json',MAX_BYTES))
        verify_evidence_tree(bundle/'native-evidence',manifest,maximum_entries=TRANSPORT_MAX_ENTRIES,maximum_depth=TRANSPORT_MAX_DEPTH)
    return pack_evidence_bundle(bundle,output,{'lane_id':lane,'experiment':exp},sealed=sealed)


def unpack_lane_bundles(repo,input_root,output,exp):
    """Only the eleven distinct current-attempt artifacts can reach acceptance."""
    input_root=external(repo,input_root);output=external(repo,output)
    prefix='opica4-'+exp['run_id']+'-'+str(exp['attempt'])+'-lane-'
    expected={prefix+lane for lane in ROUND4_LANES}
    with _evidence_directory(input_root) as (fd,path):
        with os.scandir(fd if fd is not None else path) as entries:names=[entry.name for entry in entries]
        require(len(names)==len(expected) and set(names)==expected,'Exact attempt eleven-lane transport set differs')
    require(not output.exists() and not output.is_relative_to(input_root) and not input_root.is_relative_to(output),
            'Fresh disjoint bundle reconstruction required')
    owned=_transport_new_directory(output)
    for lane in ROUND4_LANES:
        unpack_evidence_bundle(input_root/(prefix+lane),output/lane,{'lane_id':lane,'experiment':exp})
    with _evidence_directory(output,identities=owned):pass
    # The accept command immediately runs verify_lane_bundle, the complete native
    # inventory verification, and independent scientific/native replay.
    return output


def _group_native_lanes(group):
    return tuple(lane for lane in group_lanes(group) if lane in NATIVE_EVIDENCE_LANES)


def _group_pair_paths(group):
    return {lane+'/independent-native-transport/'+name
            for lane in _group_native_lanes(group) for name in ('bundle.zip','transport.json')}


def _group_fixed_directories(root,expected):
    with _evidence_directory(root) as (fd,path):
        with os.scandir(fd if fd is not None else path) as entries:names=[entry.name for entry in entries]
        require(len(names)==len(expected) and set(names)==set(expected),'Exact evidence directory inventory required')
        for name in names:
            info=os.lstat(path/name) if fd is None else os.stat(name,dir_fd=fd,follow_symlinks=False)
            _evidence_regular(info,directory=True)


def _group_manifest(manifest,group):
    """Only fixed native-container roles may exceed the ordinary member cap."""
    closed_keys(manifest,{'schema','directories','total_bytes','files'})
    require(type(manifest['files']) is list,'Complete group file inventory required')
    pairs=_group_pair_paths(group);files=manifest['files'];adjusted=[];total=0
    for row in files:
        closed_keys(row,{'path','bytes','sha256'})
        require(type(row['path']) is str and type(row['bytes']) is int and row['bytes']>=0,
                'Invalid complete group file record')
        total+=row['bytes'];mapped=dict(row)
        if row['path'] in pairs:
            cap=TRANSPORT_MAX_CONTAINER_BYTES if row['path'].endswith('/bundle.zip') else MAX_BYTES
            require(row['bytes']<=cap,'Native group component exceeds its existing role limit')
            mapped['bytes']=0
        adjusted.append(mapped)
    require(type(manifest['total_bytes']) is int and total==manifest['total_bytes'] and
            total<=TRANSPORT_MAX_BYTES,'Complete group logical byte budget exceeded')
    require(pairs<={row['path'] for row in files},'Complete fixed native transport pairs required')
    # Reuse every generic path/alias/order/parent/count/depth/hash check. The
    # zero sizes here only select already bounded container roles for validation;
    # original sizes remain in the published complete manifest and every copy.
    _transport_manifest({**manifest,'files':adjusted,'total_bytes':sum(row['bytes'] for row in adjusted)})
    return manifest


def _group_metadata_manifest(manifest,group):
    files=[row for row in manifest['files'] if row['path'] not in _group_pair_paths(group)]
    projected={**manifest,'files':files,'total_bytes':sum(row['bytes'] for row in files)}
    _transport_manifest(projected)
    return projected


def _group_tree_shape(manifest,group):
    members=set(group_lanes(group));ordinary={'group.json','source.json','source-after.json'}
    require({name for name in manifest['directories'] if '/' not in name}==members,
            'Exact independent group lane directories required')
    for row in manifest['files']:
        name=row['path']
        require(name in ordinary or '/' in name and name.split('/',1)[0] in members,
                'Unexpected independent group output path')
    for lane in members-NATIVE_EVIDENCE_LANES:
        require(not any(name==lane+'/independent-native-transport' or
                        name.startswith(lane+'/independent-native-transport/')
                        for name in manifest['directories']) and
                not any(row['path']==lane+'/independent-native-archive.json' for row in manifest['files']),
                'Nonnative group lane cannot carry a native archive')


def _verify_group_raw_receipts(repo,bundle,group,exp,manifest):
    """Cheap receipt completeness after source-owned replay, with no new execution."""
    from .testing import checked_inventory
    inventory=checked_inventory();hashes={row['path']:row['sha256'] for row in manifest['files']}
    def hashed(name):
        require(name in hashes,'Required independent raw file absent: '+name)
        return hashes[name]
    for lane in group_lanes(group):
        methods=sorted(row['method'] for row in inventory['tests'] if row['lane']==lane)
        if methods:
            for optimized,name in ((False,'normal'),(True,'optimized')):
                prefix=lane+'/tests/'+name
                receipt=load_bytes(evidence_bytes(bundle,prefix+'.json',MAX_BYTES))
                require_test_receipt(receipt,methods,optimized=optimized)
                require(receipt.get('schema')=='OPICA_EXACT_TEST_RECEIPT_V1' and
                        receipt.get('log_sha256')==hashed(prefix+'.log'),'Independent test log binding differs')
                hashed(prefix+'.driver.log')
    if 'GENERATED_STATE' in group_lanes(group):
        prefix='GENERATED_STATE/'
        row=load_bytes(evidence_bytes(bundle,prefix+'generated-state.json',MAX_BYTES))
        closed_keys(row,{'status','canonical_products','commands','view_hashes','RH','Step4'})
        paths=load_bytes((Path(repo)/'research/RHRC/integration/opica_round4/BUILD_MANIFEST.json').read_bytes())['generated']
        require(len(paths)==81 and len({item['path'] for item in paths})==81,'Exact81 canonical products required')
        require(row['status']=='PASS_GENERATED_STATE' and row['RH']==row['Step4']=='OPEN' and
                row['canonical_products']=={item['path']:file_hash(Path(repo)/item['path']) for item in paths},
                'Independent canonical product receipt differs')
        recipes=[([sys.executable,'-B','research/RHRC/tools/materialize_derived_state.py','--check'],'canonical-current.log'),
                 ([sys.executable,'-B','-m','unittest','research.RHRC.integration.opica_round2.tests.test_file_classes'],'classification.log')]
        require(type(row['commands']) is list and len(row['commands'])==2,'Both canonical commands required')
        for command,(argv,log) in zip(row['commands'],recipes):
            closed_keys(command,{'argv','exit_code','log','sha256'})
            require(command['argv']==argv and type(command['exit_code']) is int and command['exit_code']==0 and
                    command['log']==log and command['sha256']==hashed(prefix+log),
                    'Independent canonical command/log binding differs')
        # These are precisely export_state's three empty-journal views. Read
        # existing bytes only: opening an uploaded SQLite DB would mutate it.
        expected_views={'EVENTS.jsonl':b'','APPLICATIONS.jsonl':b'',
                        'CURRENT_STATE.json':canonical_bytes({'generation':None,'source':None,'revision':0,
                                          'applications':0,'RH':'OPEN','Step4':'OPEN'})+b'\n'}
        require(row['view_hashes']=={name:hashlib.sha256(raw).hexdigest() for name,raw in expected_views.items()} and
                all(hashed(prefix+name)==row['view_hashes'][name] for name in expected_views),
                'Independent deterministic views differ')
        hashed(prefix+'determinism.db')
    if 'SOURCE_NUMERICS' in group_lanes(group):
        from ..opica_round4 import source_evaluator as evaluator,source_research as research
        from ..opica_round4.source_checker import PASS_STATUS,caps
        prefix='SOURCE_NUMERICS/';row=load_bytes(evidence_bytes(bundle,prefix+'source-independent-result.json',MAX_BYTES))
        ids=evaluator.EXPECTED_IDS;identity=evaluator.B.source_identity();caps(row)
        require(row.get('schema')=='OPICA4_SOURCE_NUMERICS_LANE_V1' and row.get('status')==PASS_STATUS and
                row.get('acceptance_eligible') is True and row.get('checked_commit')==exp['requested_commit'] and
                row.get('checked_tree')==exp['requested_tree'] and row.get('source_identity')==identity and
                row.get('modes')==['normal','optimized'] and row.get('case_ids')==ids and
                type(row.get('independently_recomputed_cases')) is int and row['independently_recomputed_cases']==len(ids) and
                row.get('authority')=='FINITE_INTERVAL_EVIDENCE_ONLY' and row.get('is_zero_generated_detector') is False and
                row.get('kernel_or_cell_authority') is False and
                row.get('identity_ball_checks')=='CONSISTENCY_ONLY_EXISTING_LEAN_IDENTITIES_RETAIN_THEOREM_AUTHORITY',
                'Independent finite-source receipt differs')
        require(row.get('direct_case_sha256')=={name:hashed(prefix+'source-independent/'+name+'.json') for name in ids},
                'Independent finite-source raw cases differ')
        for case in evaluator.prescribed_cases():
            raw=load_bytes(evidence_bytes(bundle,prefix+'source-independent/'+case['id']+'.json',MAX_BYTES));caps(raw)
            require(raw.get('schema')=='OPICA4_FINITE_SOURCE_CASE_V1' and raw.get('request')==case and
                    raw.get('status')=='FINITE_ENCLOSURES' and raw.get('representation')=='direct' and
                    type(raw.get('precision_bits')) is int and raw['precision_bits'] in (512,1024) and
                    type(raw.get('export_bits')) is int and raw['export_bits']==112 and
                    raw.get('authority')=='FINITE_INTERVAL_EVIDENCE_ONLY' and raw.get('is_zero_generated_detector') is False and
                    type(raw.get('execution')) is dict and raw['execution'].get('source_identity')==identity and
                    raw['execution'].get('producer_kind')=='DIRECT_CHECKER','Independent direct case scope differs')
        for mode in ('normal','optimized'):
            folder=prefix+'source-research-independent-'+mode+'/'
            result=load_bytes(evidence_bytes(bundle,folder+'result.json',MAX_BYTES))
            require(result.get('schema')=='OPICA4_SOURCE_RESEARCH_VERIFICATION_V1' and
                    result.get('status')=='PASS_INDEPENDENT_SOURCE_RESEARCH' and result.get('source_identity')==research.identity() and
                    result.get('uniform_estimate_proved') is False and result.get('RH')==result.get('Step4')=='OPEN' and
                    type(result.get('cases')) is list and [case.get('id') for case in result['cases']]==ids,
                    'Independent source research receipt differs')
            for name in ids:hashed(folder+name+'.json')


def _checked_group_bundle(repo,bundle,group,exp):
    current=validate_descendant(repo,require_clean=True)
    sealed=_transport_seal(bundle);manifest=sealed[0]
    _group_manifest(manifest,group);_group_tree_shape(manifest,group)
    wrapper=load_bytes(evidence_bytes(bundle,'group.json',MAX_BYTES))
    closed_keys(wrapper,{'schema','group_id','record','artifacts','directories','records','source_refs'})
    require(wrapper['schema']=='OPICA4_INDEPENDENT_GROUP_BUNDLE_V1' and wrapper['group_id']==group,
            'Independent group wrapper identity differs')
    record=closed_keys(wrapper['record'],{'schema','group_id','experiment','checked','conclusion','independently_reconstructed_lanes'})
    require(record['schema']=='OPICA4_INDEPENDENT_REPLAY_GROUP_V1' and record['group_id']==group and
            record['experiment']==exp and record['checked']=={'commit':exp['requested_commit'],'tree':exp['requested_tree']} and
            record['conclusion']=='success','Completed source-bound independent group required')
    rows=record['independently_reconstructed_lanes']
    require(type(rows) is list and len(rows)==len(group_lanes(group)),'Complete group lane records required')
    from .canonical import digest_text
    for lane,row in zip(group_lanes(group),rows):
        closed_keys(row,{'id','scope','evidence_digest'});digest_text(row['evidence_digest'])
        require(row['id']==lane and row['scope']==lane_expected(lane,exp)['scope'],
                'Independent group member order/scope differs')
    require(wrapper['artifacts']==[row for row in manifest['files'] if row['path']!='group.json'] and
            wrapper['directories']==manifest['directories'],'Independent group complete inventory differs')
    require(wrapper['source_refs']=={'before':'source.json','after':'source-after.json'} and
            wrapper['records']==['source.json','source-after.json'],'Fixed independent source records required')
    require(load_bytes(evidence_bytes(bundle,'source.json',MAX_BYTES))==current==
            load_bytes(evidence_bytes(bundle,'source-after.json',MAX_BYTES)),
            'Independent group source differs from clean current checkout')
    _verify_group_raw_receipts(repo,bundle,group,exp,manifest)
    require(_transport_seal(bundle)==sealed,'Independent group changed during verification')
    return record,sealed


def run_group(group,repo,bundles,output,exp,*,provider_root=None):
    """Mandatory actual replay for a fixed scheduling group, never acceptance."""
    members=group_lanes(group);repo=unlinked(repo).resolve();bundles=external(repo,bundles)
    _group_fixed_directories(bundles,ROUND4_LANES)
    output=external(repo,output)
    require(not output.exists() and not output.is_relative_to(bundles) and not bundles.is_relative_to(output),
            'Fresh disjoint independent group output required')
    output.mkdir(parents=True);write(output/'source.json',validate_descendant(repo,require_clean=True))
    requirements=[lane_expected(lane,exp) for lane in ROUND4_LANES]
    roots={lane:bundles/lane for lane in members}
    checkers={lane:(lambda expected,record,files,lane=lane:
                    verify_lane_raw(expected,record,files,repo,output/lane,provider_root)) for lane in members}
    original=os.environ.get('OPICA_ACCEPTANCE_DIAGNOSTICS');os.environ['OPICA_ACCEPTANCE_DIAGNOSTICS']='1'
    try:
        record=verify_independent_group(group,requirements,roots,experiment=exp,
                                        checkers=checkers,required_needs={'lanes':'success'})
        current=validate_descendant(repo,require_clean=True)
        require(load_bytes(evidence_bytes(output,'source.json',MAX_BYTES))==current,
                'Source changed during independent group replay')
        write(output/'source-after.json',current)
        manifest=_transport_seal(output)[0];_group_manifest(manifest,group)
        wrapper={'schema':'OPICA4_INDEPENDENT_GROUP_BUNDLE_V1','group_id':group,'record':record,
                 'artifacts':manifest['files'],'directories':manifest['directories'],
                 'records':['source.json','source-after.json'],
                 'source_refs':{'before':'source.json','after':'source-after.json'}}
        write(output/'group.json',wrapper)
        _checked_group_bundle(repo,output,group,exp)
        return wrapper
    except BaseException:
        # Fixed member paths only; optional collection cannot replace the
        # original replay/compilation/storage exception or create a group PASS.
        for lane in members:
            try:
                if (output/lane).is_dir():_collect_failed_native_diagnostics(lane,repo,output/lane)
            except BaseException:pass
        raise
    finally:
        if original is None:os.environ.pop('OPICA_ACCEPTANCE_DIAGNOSTICS',None)
        else:os.environ['OPICA_ACCEPTANCE_DIAGNOSTICS']=original


def _group_new_directories(root,directories,owned):
    for relative in sorted(directories,key=lambda name:(len(name.split('/')),name)):
        parent=Path(relative).parent.as_posix()
        with _evidence_directory(root,'' if parent=='.' else parent,owned) as (fd,path):
            name=Path(relative).name
            if fd is None:os.mkdir(path/name,0o700)
            else:os.mkdir(name,0o700,dir_fd=fd)
            info=os.lstat(path/name) if fd is None else os.stat(name,dir_fd=fd,follow_symlinks=False)
            _evidence_regular(info,directory=True);owned[relative]=_evidence_identity(info)[:3]


def _group_copy_file(source,relative,source_ids,target,target_relative,owned,row):
    with _evidence_file(source,relative,source_ids) as (stream,before), \
            _transport_new_file(target,target_relative,owned) as destination:
        value=hashlib.sha256();count=0
        while True:
            data=stream.read(min(1024*1024,row['bytes']-count+1))
            if not data:break
            count+=len(data);require(count<=row['bytes'],'Group evidence grew during copy')
            value.update(data);destination.write(data)
        require(count==before.st_size==row['bytes'] and value.hexdigest()==row['sha256'],
                'Group evidence bytes changed during copy')


def _native_component(component,lane,exp):
    """Validate an unchanged ordinary transport without extracting it twice."""
    identity={'lane_id':lane,'experiment':exp};_transport_identity(identity)
    sealed=_transport_seal(component);manifest,identities=sealed
    require(manifest['directories']==[] and [row['path'] for row in manifest['files']]==['bundle.zip','transport.json'],
            'Exact detached native transport pair required')
    envelope=load_bytes(evidence_bytes(component,'transport.json',MAX_BYTES))
    closed_keys(envelope,{'schema','lane_id','experiment','container','manifest'})
    require(envelope['schema']=='OPICA_EVIDENCE_TRANSPORT_V1' and
            envelope['lane_id']==lane and envelope['experiment']==exp,'Detached native identity differs')
    _transport_manifest(envelope['manifest'])
    closed_keys(envelope['container'],{'bytes','sha256'})
    with _evidence_file(component,'bundle.zip',identities) as (stream,info):
        require(22<=info.st_size<=TRANSPORT_MAX_CONTAINER_BYTES and
                _transport_hash(stream,TRANSPORT_MAX_CONTAINER_BYTES)==envelope['container'],
                'Detached native transport bytes differ')
        with _transport_zip_inventory(stream,envelope['manifest'],info.st_size):pass
    require(_transport_seal(component)==sealed,'Detached native component changed during verification')
    return envelope,sealed


def _group_archive_record(bundle,lane,exp,envelope):
    archive=load_bytes(evidence_bytes(bundle,lane+'/independent-native-archive.json',MAX_BYTES))
    closed_keys(archive,{'schema','lane','experiment','complete_inventory','transport','scratch_retired'})
    require(archive['schema']=='OPICA_INDEPENDENT_NATIVE_ARCHIVE_V1' and archive['lane']==lane and
            archive['experiment']==exp and archive['scratch_retired'] is True and
            archive['transport']==envelope and archive['complete_inventory']==envelope['manifest'],
            'Complete independent native archive binding differs')
    return archive


def pack_group_bundle(repo,bundle,output,group,exp):
    """Lossless fixed multipart transport; existing ordinary/container caps remain."""
    bundle=external(repo,bundle);output=external(repo,output)
    require(not output.exists() and not output.is_relative_to(bundle) and not bundle.is_relative_to(output),
            'Fresh disjoint group transport required')
    record,sealed=_checked_group_bundle(repo,bundle,group,exp)
    manifest,source_ids=sealed;metadata_manifest=_group_metadata_manifest(manifest,group)
    owned=_transport_new_directory(output)
    projection=output.parent/(output.name+'-metadata-source-'+uuid.uuid4().hex)
    projection_ids=_transport_new_directory(projection)
    _group_new_directories(projection,metadata_manifest['directories'],projection_ids)
    for row in metadata_manifest['files']:
        _group_copy_file(bundle,row['path'],source_ids,projection,row['path'],projection_ids,row)
    projected,projected_ids=_transport_seal(projection)
    require(projected==metadata_manifest and set(projected_ids)==set(projection_ids) and
            all(projected_ids[name][:len(identity)]==identity for name,identity in projection_ids.items()) and
            _transport_seal(bundle)==sealed,
            'Complete metadata projection changed')
    metadata=pack_evidence_bundle(projection,output/'metadata',
                                  {'lane_id':group_lanes(group)[0],'experiment':exp},sealed=(projected,projected_ids))
    components={}
    for lane in _group_native_lanes(group):
        component=bundle/lane/'independent-native-transport'
        envelope,component_sealed=_native_component(component,lane,exp)
        _group_archive_record(bundle,lane,exp,envelope)
        copy_evidence_tree(component,output/('native-'+lane),component_sealed)
        require(_native_component(output/('native-'+lane),lane,exp)[0]==envelope,
                'Detached component changed during publication')
        components[lane]=envelope
    require(_transport_seal(bundle)==sealed,'Complete group changed before transport publication')
    descriptor={'schema':'OPICA4_INDEPENDENT_GROUP_TRANSPORT_V1','group_id':group,'experiment':exp,
                'complete_inventory':manifest,'metadata':metadata,'native_components':components}
    raw=canonical_bytes(descriptor)+b'\n';require(len(raw)<=MAX_BYTES,'Group descriptor exceeds bounded JSON limit')
    with _transport_new_file(output,'group-transport.json',owned) as stream:stream.write(raw)
    with _evidence_directory(output,identities=owned):pass
    return descriptor


def _unpack_group_bundle(repo,staging,destination,group,exp):
    staging=external(repo,staging);destination=external(repo,destination)
    require(not destination.exists() and not destination.is_relative_to(staging) and not staging.is_relative_to(destination),
            'Fresh disjoint group reconstruction required')
    source_sealed=_transport_seal(staging)
    expected_names={'group-transport.json','metadata'}|{'native-'+lane for lane in _group_native_lanes(group)}
    with _evidence_directory(staging) as (fd,path):
        with os.scandir(fd if fd is not None else path) as entries:names=[entry.name for entry in entries]
        require(len(names)==len(expected_names) and set(names)==expected_names,'Closed group transport components required')
    descriptor=load_bytes(evidence_bytes(staging,'group-transport.json',MAX_BYTES))
    closed_keys(descriptor,{'schema','group_id','experiment','complete_inventory','metadata','native_components'})
    require(descriptor['schema']=='OPICA4_INDEPENDENT_GROUP_TRANSPORT_V1' and descriptor['group_id']==group and
            descriptor['experiment']==exp,'Group transport source/run/attempt/profile differs')
    manifest=_group_manifest(descriptor['complete_inventory'],group)
    _group_tree_shape(manifest,group)
    require(type(descriptor['native_components']) is dict and
            set(descriptor['native_components'])==set(_group_native_lanes(group)),
            'Exact fixed native component map required')
    metadata=unpack_evidence_bundle(staging/'metadata',destination,
                                   {'lane_id':group_lanes(group)[0],'experiment':exp})
    require(metadata==descriptor['metadata'] and metadata['manifest']==_group_metadata_manifest(manifest,group),
            'Group metadata projection differs from complete inventory')
    restored,restored_ids=_transport_seal(destination)
    require(restored==metadata['manifest'],'Reconstructed metadata changed before native components')
    owned={name:(identity[:3] if name=='' or name in restored['directories'] else identity)
           for name,identity in restored_ids.items()}
    for lane in _group_native_lanes(group):
        component=staging/('native-'+lane)
        envelope,component_sealed=_native_component(component,lane,exp)
        require(envelope==descriptor['native_components'][lane],'Detached native component descriptor differs')
        target=destination/lane/'independent-native-transport'
        empty,empty_ids=_transport_seal(target)
        require(empty['files']==[] and empty['directories']==[],'Native component reconstruction target must be empty')
        require(empty_ids[''][:3]==owned[lane+'/independent-native-transport'][:3],
                'Native component destination directory changed')
        target_ids={'':empty_ids[''][:3]}
        for row in component_sealed[0]['files']:
            _group_copy_file(component,row['path'],component_sealed[1],target,row['path'],target_ids,row)
        require(_transport_seal(component)==component_sealed and _transport_seal(target)[0]==component_sealed[0],
                'Native component changed during reconstruction')
        for name,identity in target_ids.items():
            if name:owned[lane+'/independent-native-transport/'+name]=identity
        _group_archive_record(destination,lane,exp,envelope)
    require(_transport_seal(staging)==source_sealed,'Group transport changed during reconstruction')
    actual,actual_ids=_transport_seal(destination)
    require(actual==manifest and set(actual_ids)==set(owned),'Reconstructed complete group inventory differs')
    for name,identity in owned.items():
        require(actual_ids[name][:len(identity)]==identity,'Reconstructed group physical identity changed')
    _checked_group_bundle(repo,destination,group,exp)
    return descriptor


def unpack_group_bundles(repo,input_root,output,exp):
    input_root=external(repo,input_root);output=external(repo,output)
    prefix='opica4-'+exp['run_id']+'-'+str(exp['attempt'])+'-independent-'
    expected={prefix+group for group in REPLAY_GROUP_IDS}
    with _evidence_directory(input_root) as (fd,path):
        with os.scandir(fd if fd is not None else path) as entries:names=[entry.name for entry in entries]
        require(len(names)==len(expected) and set(names)==expected,'Exact attempt three-group transport set differs')
    require(not output.exists() and not output.is_relative_to(input_root) and not input_root.is_relative_to(output),
            'Fresh disjoint independent group reconstruction required')
    owned=_transport_new_directory(output)
    for group in REPLAY_GROUP_IDS:_unpack_group_bundle(repo,input_root/(prefix+group),output/group,group,exp)
    with _evidence_directory(output,identities=owned):pass
    return output


def _verify_original_lane_bytes(expected,record,files,repo):
    """Final join authenticates original bytes; group jobs already replayed them."""
    root=files['source.json'].parent;current=validate_descendant(repo,require_clean=True)
    require(load_bytes(evidence_bytes(root,'source.json',MAX_BYTES))==current==
            load_bytes(evidence_bytes(root,'source-after.json',MAX_BYTES)),
            'Original producer source differs from clean current checkout')
    require('results.json' in files,'Original producer scientific records missing')
    load_bytes(evidence_bytes(root,'results.json',MAX_BYTES))
    if expected['id'] in NATIVE_EVIDENCE_LANES:
        require('native-evidence-inventory.json' in files,'Original native inventory missing')
        manifest=load_bytes(evidence_bytes(root,'native-evidence-inventory.json',MAX_BYTES))
        verify_evidence_tree(root/'native-evidence',manifest,maximum_entries=TRANSPORT_MAX_ENTRIES,
                             maximum_depth=TRANSPORT_MAX_DEPTH)
        require({name for name in files if name.startswith('native-evidence/')}==
                {'native-evidence/'+row['path'] for row in manifest['files']},'Original native file inventory differs')
    return True


def _verify_archived_native_receipts(repo,lane,root,manifest,exp,producer_results):
    """Check relocated raw completeness; execution/isolation remains group-job authority.

    Recorded absolute execution paths are never reopened or rewritten here.
    The mandatory source-owned group job already checked exact worker recipes.
    """
    if lane not in {'CURRENT_COMPATIBILITY','MATHEMATICAL_SUPPORT'}:return
    from . import qualification as q
    from .executor import native_resource_failure
    hashes={row['path']:row['sha256'] for row in manifest['files']}
    stem='current-native-independent-' if lane=='CURRENT_COMPATIBILITY' else 'mathematics-native-independent-'
    folders=[name for name in manifest['directories'] if re.fullmatch(re.escape(stem)+r'[0-9a-f]{32}',name)]
    require(len(folders)==1,'One fixed independent native report root required')
    prefix=folders[0]+'/'
    def hashed(name):
        require(name in hashes,'Archived required native file absent: '+name)
        return hashes[name]
    def read(name):
        raw=evidence_bytes(root,name,MAX_BYTES)
        require(hashlib.sha256(raw).hexdigest()==hashed(name),'Archived native record changed')
        return load_bytes(raw)
    report=read(prefix+'result.json')
    if lane=='CURRENT_COMPATIBILITY':
        atlas=q.frozen_atlas(Path(repo))
        require(report.get('schema')=='OPICA_CURRENT_COMPATIBILITY_V1' and
                report.get('status')=='PASS_CURRENT_COMPATIBILITY' and
                report.get('checked_commit')==exp['requested_commit'] and report.get('checked_tree')==exp['requested_tree'] and
                report.get('atlas_sha256')==q.ATLAS_SHA256 and report.get('declarations')==462 and
                report.get('memberships')==696 and report.get('required_root_memberships')==221 and
                report.get('historical_contacts')==185 and report.get('cohorts')==q.COHORTS and
                report.get('RH')==report.get('Step4')=='OPEN' and report.get('semantic_exhaustion') is False and
                report.get('semantic_review_promotion') is False and
                report.get('source_sha256')==q._source(Path(repo),{row['module'] for row in atlas}|{'Zeta23.RHRC.OpicaRound3AtlasExport'}) and
                report.get('compiler_rows')==producer_results['current']['compiler_rows'] and
                report.get('native_export_sha256')==hashed(prefix+'native-export.jsonl'),
                'Independent current atlas receipt differs')
        batches=report.get('batches');require(type(batches) is list and len(batches)==29,'All29 atlas batches required')
        for index,batch in enumerate(batches):
            source='AtlasBatch'+str(index).zfill(3)+'.lean';folder=prefix+'batch-'+str(index).zfill(3)+'/'
            native=batch.get('native',{})
            require(batch.get('index')==index and
                    batch.get('declarations')==[row['declaration'] for row in atlas[index*16:(index+1)*16]] and
                    type(native.get('exit_code')) is int and native['exit_code']==0 and
                    native.get('capability')=='LINUX_ISOLATED' and not native_resource_failure(native) and
                    batch.get('source_sha256')==hashed(folder+source) and
                    batch.get('object_sha256')==hashed(folder+source[:-5]+'.olean') and
                    native.get('log_sha256')==hashed(folder+source+'.log'),'Independent atlas batch raw binding differs')
        return
    gate=Path(repo)/'research/RHRC/integration/opica_round4/math_gate.py'
    require(report.get('schema')=='OPICA_MATHEMATICAL_SUPPORT_QUALIFICATION_V1' and
            report.get('status')=='PASS_MATHEMATICAL_SUPPORT' and report.get('gate_sha256')==file_hash(gate) and
            report.get('worker_config_sha256')==hashed(prefix+'worker-config.json') and
            report.get('native_result_sha256')==hashed(prefix+'native/result.json'),
            'Independent mathematical qualification binding differs')
    native_result=read(prefix+'native/result.json');worker=read(prefix+'worker-config.json')
    require(report.get('native_result')==native_result and native_result.get('worker')==worker and
            worker.get('production') is True and native_result.get('status')=='PASS' and
            native_result.get('execution_mode')=='PRODUCTION_ISOLATED' and
            native_result.get('authority')=='CURRENT_SOURCE_ISOLATED_NATIVE_SUPPORT' and
            native_result.get('head')==exp['requested_commit'] and native_result.get('committed_tree')==exp['requested_tree'] and
            native_result.get('module_count')==q.EXPECTED_MODULE_COUNT and
            native_result.get('declaration_count')==q.EXPECTED_DECLARATION_COUNT and
            native_result.get('baseline_module_count')==16 and native_result.get('baseline_declaration_count')==98 and
            native_result.get('integration_module_count')==40 and native_result.get('integration_declaration_count')==397 and
            native_result.get('semantic_mutation_count')==q.SEMANTIC_MUTATION_COUNT and
            native_result.get('worker_config_sha256')==report.get('worker_config_sha256') and
            native_result.get('checker_sha256')==file_hash(gate) and
            native_result.get('toolchain_sha256')==file_hash(Path(repo)/'lean-toolchain') and
            native_result.get('manifest_sha256')==file_hash(Path(repo)/'lake-manifest.json') and
            native_result.get('roots_sha256')==file_hash(Path(repo)/'research/RHRC/integration/opica_round4/ROOTS.json') and
            native_result.get('source_hashes')=={module:file_hash(Path(repo)/(module.replace('.','/')+'.lean'))
                                                for module in q.MATHEMATICAL_MODULES} and
            native_result.get('RH')==native_result.get('Step4')=='OPEN',
            'Independent complete mathematical census/authority differs')
    command=report.get('command',{})
    require(type(command.get('returncode')) is int and command['returncode']==0 and command.get('timeout') is False and
            command.get('stdout')=='mathematical-support.stdout.log' and command.get('stderr')=='mathematical-support.stderr.log' and
            command.get('stdout_sha256')==hashed(prefix+'mathematical-support.stdout.log') and
            command.get('stderr_sha256')==hashed(prefix+'mathematical-support.stderr.log'),
            'Independent mathematical command logs differ')
    rows=native_result.get('module_records')
    require(type(rows) is list and len(rows)==q.EXPECTED_MODULE_COUNT and
            {row.get('module') for row in rows}==set(q.MATHEMATICAL_MODULES),'All isolated mathematical modules required')
    for row in rows:
        module=row['module'];source=module.replace('.','/')+'.lean';folder=prefix+'native/workers/'+module+'/'
        native=row.get('native',{});products=row.get('products',{})
        require(row.get('exit_code')==0 and native.get('exit_code')==0 and native.get('capability')=='LINUX_ISOLATED' and
                not native_resource_failure(native) and row.get('argv')==native.get('command') and
                row.get('source_sha256')==file_hash(Path(repo)/source)==hashed(folder+source) and
                row.get('log_sha256')==native.get('log_sha256')==hashed(folder+source+'.log')==hashed(prefix+'native/'+module+'.log'),
                'Independent isolated mathematical source/log binding differs')
        base=source[:-5];required={base+'.olean',base+'.ilean'};allowed=required|{base+'.olean.private',base+'.olean.server'}
        require(type(products) is dict and required<=set(products)<=allowed and
                all(value==hashed(folder+name)==hashed(prefix+'native/lib/'+name) for name,value in products.items()) and
                row.get('object_sha256')==products[base+'.olean'],'Independent mathematical objects differ')
    from ..opica_round4.math_gate import SEMANTIC_MUTATIONS,audit_validation
    validation=evidence_bytes(root,prefix+'native/Zeta23.OPICARound4.Validation.log',MAX_BYTES).decode('utf-8')
    types=read(prefix+'native/types-and-axioms.json')
    require(native_result.get('types_and_axioms_sha256')==hashed(prefix+'native/types-and-axioms.json') and
            audit_validation(validation)==types,'Independent full-type/transitive-axiom audit differs')
    mutation=native_result.get('mutation',{});native=mutation.get('native',{});folder=prefix+'native/workers/semantic-mutations/'
    require(mutation.get('exit_code')==native.get('exit_code')==1 and native.get('capability')=='LINUX_ISOLATED' and
            not native_resource_failure(native) and
            mutation.get('error_count')==q.SEMANTIC_MUTATION_COUNT and
            mutation.get('source_sha256')==hashlib.sha256(SEMANTIC_MUTATIONS.encode('utf-8')).hexdigest()==
            hashed(folder+'RejectedSemanticMutations.lean')==hashed(prefix+'native/RejectedSemanticMutations.lean') and
            mutation.get('log_sha256')==native.get('log_sha256')==hashed(folder+'RejectedSemanticMutations.lean.log')==
            hashed(prefix+'native/semantic-mutations.log'),'All intended semantic controls and logs required')
    text=evidence_bytes(root,prefix+'native/semantic-mutations.log',MAX_BYTES).decode('utf-8',errors='replace')
    errors=[line for line in text.splitlines() if 'error:' in line or 'error(' in line]
    require(len(errors)==q.SEMANTIC_MUTATION_COUNT and all('type mismatch' in line.casefold() for line in errors) and
            not any(term in text.casefold() for term in ('unknown module','unknown identifier','unknown constant',
                        'file not found','maximum number of heartbeats','maximum recursion','out of memory','panic')),
            'Independent semantic controls were not the intended type errors')
    require(not any(name.startswith(folder) and name.endswith(('.olean','.olean.private','.olean.server','.ilean'))
                    for name in hashes),'Rejected semantic controls emitted compiler products')


def _verify_research_raw_pairing(producer,group_root,original):
    """Recheck retained interval relations without repeating numerical evaluation."""
    from ..opica_round4.source_evaluator import EXPECTED_IDS,prescribed_cases
    from ..opica_round4.source_checker import compare_case,scientific_disposition
    hashes={row['path']:row['sha256'] for row in original['artifacts']}
    def producer_json(relative):
        raw=evidence_bytes(producer,relative,MAX_BYTES)
        require(relative in hashes and hashlib.sha256(raw).hexdigest()==hashes[relative],
                'Original source research record changed')
        return load_bytes(raw)
    reports={mode:producer_json('source-producer/'+mode+'/result.json')
             for mode in ('normal','optimized')}
    require(all(type(row.get('precision_bits')) is int and row['precision_bits'] in (256,512)
                for row in reports.values()),'Original source precision differs')
    direct_bits=2*max(row['precision_bits'] for row in reports.values())
    result=load_bytes(evidence_bytes(group_root,'SOURCE_NUMERICS/source-independent-result.json',MAX_BYTES))
    comparisons=0;dispositions={}
    for case in prescribed_cases():
        name=case['id']
        refined=load_bytes(evidence_bytes(group_root,'SOURCE_NUMERICS/source-independent/'+name+'.json',MAX_BYTES))
        require(type(refined.get('precision_bits')) is int and refined['precision_bits']==direct_bits,
                'Independent source precision does not match original producers')
        for mode,row in reports.items():
            claimed=producer_json('source-producer/'+mode+'/'+name+'.json')
            comparisons+=compare_case(claimed,refined,case,row['precision_bits'])
        dispositions[name]=scientific_disposition(refined)
    require(type(result.get('contained_interval_comparisons')) is int and
            result['contained_interval_comparisons']==comparisons and result.get('dispositions')==dispositions,
            'Independent source interval relations or dispositions differ')
    for mode in ('normal','optimized'):
        old=producer_json('source-research-'+mode+'/result.json')
        folder='SOURCE_NUMERICS/source-research-independent-'+mode+'/'
        fresh=load_bytes(evidence_bytes(group_root,folder+'result.json',MAX_BYTES))
        require([row.get('id') for row in old['cases']]==EXPECTED_IDS,'Original research case inventory differs')
        for prior,replayed in zip(old['cases'],fresh['cases']):
            name=prior['id']
            require(replayed.get('id')==name and
                    replayed.get('intervals_independently_contained')==prior.get('intervals_independently_contained') and
                    load_bytes(evidence_bytes(group_root,folder+name+'.json',MAX_BYTES))==
                    producer_json('source-research-'+mode+'/'+name+'.checker.json'),
                    'Independent research direct replay differs from original checked quantities')


def aggregate_groups(repo,bundles,groups,output,exp,needs):
    """Verify complete group archives, then require all eleven actual replays."""
    closed_keys(needs,{'lanes','independent'})
    for key in ('lanes','independent'):
        require(type(needs[key]) is dict and needs[key].get('result')=='success',
                'Trusted producer and independent workflow jobs must succeed')
    bundles=external(repo,bundles);groups=external(repo,groups);output=external(repo,output)
    _group_fixed_directories(bundles,ROUND4_LANES);_group_fixed_directories(groups,REPLAY_GROUP_IDS)
    require(not output.exists() and all(not output.is_relative_to(root) and not root.is_relative_to(output)
                                       for root in (bundles,groups)),'Fresh disjoint final acceptance output required')
    output.mkdir(parents=True);current=validate_descendant(repo,require_clean=True)
    write(output/'source.json',current)
    requirements=[lane_expected(lane,exp) for lane in ROUND4_LANES];original_records={}
    for expected in requirements:
        lane=expected['id'];root=bundles/lane;sealed=_transport_seal(root)
        verify_lane_bundle(expected,root,experiment=exp,
                           replay=lambda e,r,f:_verify_original_lane_bytes(e,r,f,repo))
        original_records[lane]=load_bytes(evidence_bytes(root,'lane.json',MAX_BYTES))
        require(_transport_seal(root)==sealed,'Original producer changed during final verification')
    records=[]
    for group in REPLAY_GROUP_IDS:
        root=groups/group;record,sealed=_checked_group_bundle(repo,root,group,exp)
        if 'SOURCE_NUMERICS' in group_lanes(group):
            _verify_research_raw_pairing(bundles/'SOURCE_NUMERICS',root,original_records['SOURCE_NUMERICS'])
        destination=output/group;_transport_new_directory(destination)
        native_receipts={}
        for lane in _group_native_lanes(group):
            component=root/lane/'independent-native-transport'
            envelope,_=_native_component(component,lane,exp)
            archive=_group_archive_record(root,lane,exp,envelope)
            replayed=unpack_evidence_bundle(component,destination/lane,{'lane_id':lane,'experiment':exp})
            require(replayed==envelope and _transport_seal(destination/lane)[0]==archive['complete_inventory'],
                    'Independent native raw archive reconstruction differs')
            _verify_archived_native_receipts(repo,lane,destination/lane,archive['complete_inventory'],exp,
                load_bytes(evidence_bytes(bundles/lane,'results.json',MAX_BYTES)))
            verify_evidence_tree(destination/lane,archive['complete_inventory'],
                                 maximum_entries=TRANSPORT_MAX_ENTRIES,maximum_depth=TRANSPORT_MAX_DEPTH)
            native_receipts[lane]={'transport':envelope,'complete_inventory':archive['complete_inventory']}
        require(_transport_seal(root)==sealed,'Independent group changed during final native verification')
        write(destination/'verification.json',{'schema':'OPICA4_GROUP_ARCHIVE_VERIFICATION_V1',
              'group_id':group,'experiment':exp,'complete_inventory':sealed[0],
              'native_archives':native_receipts,'record':record})
        records.append(record)
    require(validate_descendant(repo,require_clean=True)==current,'Source changed during final group join')
    result=join_independent_groups(requirements,original_records,records,experiment=exp,
                                   required_needs={key:needs[key]['result'] for key in ('lanes','independent')})
    write(output/'source-after.json',current);write(output/'acceptance.json',result)
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='command',required=True)
    for name in ('inspect','prepare','lane','accept','transport-pack','transport-unpack',
                 'accept-group','group-transport-pack','group-transport-unpack','accept-groups'):
        q=sub.add_parser(name,aliases=['check-descendant'] if name=='inspect' else []);q.add_argument('--repo',type=Path,default=REPO);q.add_argument('--output','--out',type=Path,required=True)
        if name in {'lane','accept','transport-pack','transport-unpack','accept-group',
                    'group-transport-pack','group-transport-unpack','accept-groups'}:
            q.add_argument('--run-id',required=True);q.add_argument('--attempt',type=int,required=True);q.add_argument('--provider-root',type=Path)
        if name in {'lane','transport-pack'}:q.add_argument('--lane',choices=ROUND4_LANES,required=True)
        if name in {'accept-group','group-transport-pack'}:q.add_argument('--group',choices=REPLAY_GROUP_IDS,required=True)
        if name in {'accept','accept-group','accept-groups'}:q.add_argument('--bundles',type=Path,required=True)
        if name=='accept-groups':
            q.add_argument('--groups',type=Path,required=True);q.add_argument('--needs-json',required=True)
        if name in {'transport-pack','transport-unpack','group-transport-pack','group-transport-unpack'}:
            q.add_argument('--input',type=Path,required=True)
            q.add_argument('--requested-commit',required=True);q.add_argument('--requested-tree',required=True)
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
    elif a.command=='accept-group':run_group(a.group,a.repo,a.bundles,a.output,experiment(a.repo,a.run_id,a.attempt),provider_root=a.provider_root)
    elif a.command=='accept-groups':aggregate_groups(a.repo,a.bundles,a.groups,a.output,experiment(a.repo,a.run_id,a.attempt),load_bytes(a.needs_json.encode('utf-8')))
    elif a.command in {'transport-pack','transport-unpack','group-transport-pack','group-transport-unpack'}:
        exp=experiment(a.repo,a.run_id,a.attempt)
        require((exp['requested_commit'],exp['requested_tree'])==(a.requested_commit,a.requested_tree),
                'Workflow requested source differs from checked transport source')
        if a.command=='transport-pack':pack_lane_bundle(a.repo,a.input,a.output,a.lane,exp)
        elif a.command=='transport-unpack':unpack_lane_bundles(a.repo,a.input,a.output,exp)
        elif a.command=='group-transport-pack':pack_group_bundle(a.repo,a.input,a.output,a.group,exp)
        else:unpack_group_bundles(a.repo,a.input,a.output,exp)
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
