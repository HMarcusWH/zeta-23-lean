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
                       TRANSPORT_MAX_ENTRIES,TRANSPORT_MAX_DEPTH)
from .snapshot import retire_copied_evidence_tree
from .descendant import validate_descendant,BASE,BASE_TREE,git
from .accept import ROUND4_LANES,verify_lane_bundle,require_test_receipt,accept_application_scope

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
    # output paths are eligible: receipt fields cannot redirect collection.
    # They share the native collector's byte/file budgets and no-follow reads.
    for mode in ('normal','optimized'):
        for suffix in ('.json','.log','.driver.log'):
            relative='tests/'+mode+suffix
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
        verify_evaluator_evidence(root/'source-producer',independent_output/'source-independent',require_clean=True,
            expected_head=record['experiment']['requested_commit'],expected_tree=record['experiment']['requested_tree'])
        from research.RHRC.integration.opica_round4.source_research import verify_campaign
        for name in ('normal','optimized'):
            verify_campaign(root/('source-research-'+name),independent_output/('source-research-independent-'+name),require_clean=True)
    elif lane=='PROVIDER_SELECTED':
        from .provider import verify
        require(provider_root is not None,'Independent pinned provider required')
        verify(Path(provider_root),files['results.json'].parent/'provider-producer',independent_output/'provider-independent')
    elif lane=='GENERATED_STATE':
        emit_phase_diagnostic(lane, 'canonical.start')
        generated_state(repo,independent_output)
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

def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='command',required=True)
    for name in ('inspect','prepare','lane','accept','transport-pack','transport-unpack'):
        q=sub.add_parser(name,aliases=['check-descendant'] if name=='inspect' else []);q.add_argument('--repo',type=Path,default=REPO);q.add_argument('--output','--out',type=Path,required=True)
        if name in {'lane','accept','transport-pack','transport-unpack'}:
            q.add_argument('--run-id',required=True);q.add_argument('--attempt',type=int,required=True);q.add_argument('--provider-root',type=Path)
        if name in {'lane','transport-pack'}:q.add_argument('--lane',choices=ROUND4_LANES,required=True)
        if name=='accept':q.add_argument('--bundles',type=Path,required=True)
        if name in {'transport-pack','transport-unpack'}:
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
    elif a.command in {'transport-pack','transport-unpack'}:
        exp=experiment(a.repo,a.run_id,a.attempt)
        require((exp['requested_commit'],exp['requested_tree'])==(a.requested_commit,a.requested_tree),
                'Workflow requested source differs from checked transport source')
        if a.command=='transport-pack':pack_lane_bundle(a.repo,a.input,a.output,a.lane,exp)
        else:unpack_lane_bundles(a.repo,a.input,a.output,exp)
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
