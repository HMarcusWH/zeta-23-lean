"""Actual current-child Lean preparation and source-bound qualification gates.

The root cache build has one owner. All candidate drivers and independent
outputs live in the CI-provisioned bounded native volume. No historical atlas,
theorem, source pin or generated parent file is rewritten here.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import asdict,replace
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import shutil
import stat
import subprocess
import sys
import time
from .canonical import require,canonical_bytes,load_bytes,digest,ContractError
from .contracts import WorkerConfig,SearchBudget,as_record
from .snapshot import unlinked,file_hash,git,hash_inventory,discover_source_paths
from .executor import (run_worker,worker_environment,lean_name,lean_string,_recipe,MATH_SUPPORT_RECIPE,
                       LEAN_ADDRESS_SPACE_BYTES,native_resource_failure)
from .inventory import expression_hash,validate_telescope
from ..opica_round4.math_gate import (MODULES as MATHEMATICAL_MODULES,
    EXPECTED_MODULE_COUNT, EXPECTED_DECLARATION_COUNT,
    BASELINE_MODULE_COUNT, BASELINE_DECLARATION_COUNT)

ATLAS='research/RHRC/integration/opica_round3/atlas/CONSTRAINT_ATLAS.jsonl'
ATLAS_SHA256='c0becd027e18be98c29647b85e0d18aeb0748a66c2c6ab6690a4940b2945150e'
LEAN_PIN='leanprover/lean4:v4.33.0-rc2'
CORE_MODULES=(
 'Zeta23.RHRC.OpicaComposition.Protocol','Zeta23.RHRC.OpicaComposition.Elaborate',
 'Zeta23.RHRC.OpicaComposition.Export','Zeta23.RHRC.OpicaComposition.Audit',
 'Zeta23.RHRC.OpicaComposition.FiniteWorlds','Zeta23.OPICAComposition.Calibration',
 'Zeta23.RHRC.OpicaComposition.Validation','Zeta23.RHRC.OpicaComposition.ResearchTargets',
 'Zeta23.RHRC.OpicaComposition.SearchExamples',
 'Zeta23.RHRC.RegisteredClaimBindings','Zeta23.RHRC.DeclarationDependencyExport',
 'Zeta23.RHRC.SourceCandidateResolution',
 'Zeta23.OPICARound4.Validation','Zeta23.RHRC.OpicaRound3AtlasExport')+tuple(MATHEMATICAL_MODULES)
COHORTS={'UCDP_HISTORICAL216':216,'UCDP_CONTACT185':185,'OPICA_FOLLOWUP100':100,
 'OPICA_ORIGINAL76':76,'REVIEWED_SUPPORT_IDENTITY':51,'OPICA_ROUND2_40':40,
 'UCDP_PRIORITY_TRIPLE18':18,'ROUND3_INDEPENDENT_CONSUMERS5':5,'OPICA_ROUND3_5':5}
ATLAS_FIELDS={'schema','declaration','module','kind','universe_parameters','type_text','type_expression',
 'outer_telescope','conclusion_text','type_constants','value_constants','structure_constants','axioms'}


def _packages(repo):
    manifest=load_bytes((repo/'lake-manifest.json').read_bytes());require(manifest['packagesDir']=='.lake/packages','Package location override')
    result={}
    for row in manifest['packages']:
        require(row['type']=='git' and re.fullmatch('[A-Za-z0-9_-]+',row['name']) and re.fullmatch('[0-9a-f]{40}',row['rev']),'Unsupported pinned package')
        root=unlinked(repo/'.lake/packages'/row['name']).resolve()
        require(git(root,'rev-parse','HEAD')==row['rev'],'Actual package revision differs: '+row['name'])
        require(not git(root,'-c','core.autocrlf=false','status','--porcelain','--untracked-files=all'),'Dirty native package source: '+row['name'])
        result[row['name']]={'commit':row['rev'],'tree':git(root,'rev-parse','HEAD^{tree}'),'url':row['url']}
    require(result.get('mathlib',{}).get('commit')=='51e6992efd06126df61a496bebf8f49482a4e129','Host Mathlib pin drift')
    return result


def _materialize_pinned_benchmark_alias(package_root,*,expected_commit,expected_blob):
    """Check out one reviewed benchmark alias as its exact Git link-text bytes.

    This is trusted dependency preparation, never permission to follow a source
    link. The sole admitted path is Mathlib's unused benchmark runner alias;
    no Lean, configuration, import-object or evidence alias is projected.
    """
    relative='scripts/bench/size/run.py';expected=b'run'
    require(re.fullmatch('[0-9a-f]{40}',expected_commit) and
            re.fullmatch('[0-9a-f]{40}',expected_blob),'Pinned benchmark identity required')
    require(hashlib.sha1(b'blob 3\0'+expected).hexdigest()==expected_blob,
            'Pinned benchmark link blob differs')
    root=unlinked(package_root).resolve();require(root.is_dir(),'Pinned benchmark package absent')
    path=root/relative;unlinked(path.parent)
    require(git(root,'rev-parse','HEAD')==expected_commit,'Pinned benchmark package commit differs')
    tree=git(root,'rev-parse','HEAD^{tree}')
    require(not git(root,'-c','core.autocrlf=false','status','--porcelain','--untracked-files=all'),
            'Pinned benchmark package must be clean before projection')
    env={'PATH':os.environ.get('PATH',''),'SYSTEMROOT':os.environ.get('SYSTEMROOT',''),
         'GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':os.devnull,
         'GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'}
    def raw(*args,input=None):
        result=subprocess.run(['git','-C',str(root),*args],env=env,input=input,
          stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
        require(result.returncode==0,'Pinned benchmark Git command failed: '+args[0])
        return result.stdout
    encoded=relative.encode('utf-8')
    want_tree=b'120000 blob '+expected_blob.encode('ascii')+b'\t'+encoded+b'\0'
    want_index=b'120000 '+expected_blob.encode('ascii')+b' 0\t'+encoded+b'\0'
    require(raw('ls-tree','-z',expected_commit,'--',relative)==want_tree,
            'Pinned benchmark source tree mode/blob differs')
    require(raw('ls-files','--stage','-z','--',relative)==want_index,
            'Pinned benchmark index mode/blob/stage differs')
    blob=raw('cat-file','blob',expected_commit+':'+relative)
    require(blob==expected,'Pinned benchmark raw link target differs')
    info=os.lstat(path)
    require(not(getattr(info,'st_file_attributes',0)&1024),'Pinned benchmark reparse point refused')
    if stat.S_ISLNK(info.st_mode):
        require(os.fsencode(os.readlink(path))==blob,'Pinned benchmark checkout link target differs')
        before='SYMLINK'
    else:
        require(stat.S_ISREG(info.st_mode) and path.read_bytes()==blob,
                'Pinned benchmark regular link-text bytes differ')
        before='REGULAR_LINK_TEXT'
    # Persist only the checkout representation; HEAD, tree and index stay pinned.
    git(root,'config','--local','core.symlinks','false')
    if before=='SYMLINK':
        # Git may retain an already-clean symlink despite checkout-index --force.
        # Remove only this verified leaf, without opening or following its target.
        def same_leaf(current):
            fields=('st_dev','st_ino','st_mode','st_size','st_mtime_ns')
            require(stat.S_ISLNK(current.st_mode) and
                    not(getattr(current,'st_file_attributes',0)&1024) and
                    tuple(getattr(current,k) for k in fields)==tuple(getattr(info,k) for k in fields),
                    'Pinned benchmark symlink identity changed before unlink')
        unlinked(path.parent)
        if os.name!='nt':
            descriptors=[]
            try:
                flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW
                descriptors.append(os.open(root,flags))
                for part in Path(relative).parts[:-1]:
                    descriptors.append(os.open(part,flags,dir_fd=descriptors[-1]))
                parent_fd=descriptors[-1];parent=os.fstat(parent_fd);current_parent=os.lstat(path.parent)
                require((parent.st_dev,parent.st_ino)==(current_parent.st_dev,current_parent.st_ino),
                        'Pinned benchmark parent identity changed before unlink')
                same_leaf(os.stat(path.name,dir_fd=parent_fd,follow_symlinks=False))
                require(os.fsencode(os.readlink(path.name,dir_fd=parent_fd))==blob,
                        'Pinned benchmark raw target changed before unlink')
                unlinked(path.parent)
                same_leaf(os.stat(path.name,dir_fd=parent_fd,follow_symlinks=False))
                os.unlink(path.name,dir_fd=parent_fd)
            finally:
                for descriptor in reversed(descriptors):os.close(descriptor)
        else:
            same_leaf(os.lstat(path))
            require(os.fsencode(os.readlink(path))==blob,
                    'Pinned benchmark raw target changed before unlink')
            unlinked(path.parent);same_leaf(os.lstat(path))
            os.unlink(path)
    raw('checkout-index','--force','-z','--stdin',input=encoded+b'\0')
    info=os.lstat(path)
    require(stat.S_ISREG(info.st_mode) and not(getattr(info,'st_file_attributes',0)&1024),
            'Pinned benchmark projection must be a regular non-reparse file')
    sha256=hashlib.sha256(blob).hexdigest()
    require(hash_inventory(root,[relative])[relative]==sha256 and path.read_bytes()==blob,
            'Pinned benchmark projected raw bytes/hash differ')
    require(git(root,'config','--local','--get','core.symlinks')=='false' and
            git(root,'rev-parse','HEAD')==expected_commit and git(root,'rev-parse','HEAD^{tree}')==tree and
            raw('ls-files','--stage','-z','--',relative)==want_index,
            'Pinned benchmark package/index changed during projection')
    require(not git(root,'-c','core.autocrlf=false','status','--porcelain','--untracked-files=all'),
            'Pinned benchmark package dirty after projection')
    return {'policy':'EXACT_PINNED_BENCHMARK_LINK_TEXT_V1','path':relative,'commit':expected_commit,
      'tree':tree,'git_mode':'120000','git_blob':expected_blob,'raw_link_text':blob.decode('ascii'),
      'input_leaf_kind':before,'checkout_leaf_kind':'REGULAR_LINK_TEXT','checkout_core_symlinks':False,
      'checkout_sha256':sha256,'target_dereferenced':False}


def _worker_version(repo,output,worker):
    require(Path(worker.lean).resolve().is_relative_to(Path(worker.toolchain_root).resolve()),'Worker compiler prefix differs')
    env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN_','ELAN_'))}
    c=_command([worker.lean,'--version'],repo,env,output,'worker-version',30)
    require(c['returncode']==0 and not c['timeout'],'Actual worker compiler unavailable')
    text=(output/c['stdout']).read_text(encoding='utf-8').strip()
    require(text.startswith('Lean (version 4.33.0-rc2,') and 'd8b18978322de05a8f3dba51ef03cf5461676c17' in text,'Wrong current-child worker compiler')
    return c


def frozen_atlas(repo):
    repo=unlinked(repo).resolve();path=repo/ATLAS
    require(file_hash(path)==ATLAS_SHA256,'Frozen atlas bytes changed')
    rows=[load_bytes(line) for line in path.read_bytes().splitlines() if line]
    require(len(rows)==462 and len({r['declaration'] for r in rows})==462,'Exact462-declaration atlas required')
    counts=Counter(m['cohort'] for r in rows for m in r['memberships'])
    require(dict(counts)==COHORTS and sum(counts.values())==696,'Frozen696 cohort memberships differ')
    for row in rows:
        lean_name(row['declaration']);lean_name(row['module'])
        source=row['source'];require(source['path']==row['module'].replace('.','/')+'.lean','Atlas source/module origin differs')
        require(file_hash(repo/source['path'])==source['sha256'],'Frozen atlas mathematical source changed: '+source['path'])
        require(expression_hash(row['statement']['type_expression'])==row['type_sha256'],'Frozen atlas type digest differs')
    return rows


def _external(repo,output,production):
    repo=unlinked(repo).resolve();output=unlinked(output).resolve()
    require(not output.is_relative_to(repo),'Native qualification output must be outside source')
    if production:
        require(platform.system()=='Linux','Production native qualification requires Linux')
        value=os.environ.get('OPICA_NATIVE_OUTPUT');require(value,'OPICA_NATIVE_OUTPUT bounded volume is required')
        native=unlinked(value).resolve();require(native.is_dir() and output.is_relative_to(native),'All native qualification outputs must remain in OPICA_NATIVE_OUTPUT')
    require(not output.exists(),'Fresh native qualification output required');output.mkdir(parents=True);return output


def _emit_failed_command_tails(stdout,stderr,label):
    """Expose bounded failure diagnostics without admitting a failed command."""
    limit=4096;streams={}
    for name,path in (('stdout',stdout),('stderr',stderr)):
        path=unlinked(path)
        flags=os.O_RDONLY|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_BINARY',0)
        with os.fdopen(os.open(path,flags),'rb') as source:
            info=os.fstat(source.fileno())
            require(stat.S_ISREG(info.st_mode),'Regular failed-command diagnostic log required')
            source.seek(max(0,info.st_size-limit));tail=source.read(limit)
        streams[name]={'file_bytes':info.st_size,'captured_bytes':len(tail),
          'tail':tail.decode('utf-8',errors='replace')}
    # JSON escaping keeps compiler output from becoming terminal control syntax.
    row={'label':label,'maximum_bytes_per_stream':limit,'streams':streams}
    try:
        sys.stderr.write('OPICA_PREPARATION_COMMAND_FAILURE\t'+json.dumps(row,ensure_ascii=True,sort_keys=True)+'\n')
        sys.stderr.flush()
    except (OSError,ValueError,AttributeError):
        pass  # Only diagnostic transport is best-effort; log reads stay fail-closed.


def _command(argv,repo,env,output,label,seconds):
    stdout=output/(label+'.stdout.log');stderr=output/(label+'.stderr.log');started=time.monotonic()
    with stdout.open('xb') as a,stderr.open('xb') as b:
        try:code=subprocess.run(argv,cwd=repo,env=env,stdout=a,stderr=b,timeout=seconds,check=False).returncode;timeout=False
        except subprocess.TimeoutExpired:code=None;timeout=True
    elapsed_ms=int((time.monotonic()-started)*1000)
    stdout_sha256=file_hash(stdout);stderr_sha256=file_hash(stderr)
    if timeout or code!=0:_emit_failed_command_tails(stdout,stderr,label)
    return {'argv':list(map(str,argv)),'returncode':code,'timeout':timeout,'elapsed_ms':elapsed_ms,
      'stdout':stdout.name,'stderr':stderr.name,'stdout_sha256':stdout_sha256,'stderr_sha256':stderr_sha256}


def _source(repo,modules):
    paths={m.replace('.','/')+'.lean' for m in modules}|{'lean-toolchain','lake-manifest.json','lakefile.toml',ATLAS}
    return {p:file_hash(repo/p) for p in sorted(paths)}


SMOKE_DIAGNOSTIC_TIMEOUT=10
SMOKE_DIAGNOSTIC_TRACE_BYTES=262144
SMOKE_DIAGNOSTIC_LOG_BYTES=65536


def _smoke_diagnostic_capture(path,limit):
    """Bounded no-follow text plus a hash of the actual regular diagnostic file."""
    path=unlinked(path)
    flags=os.O_RDONLY|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_NONBLOCK',0)|getattr(os,'O_BINARY',0)
    with os.fdopen(os.open(path,flags),'rb') as stream:
        before=os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode) and not(getattr(before,'st_file_attributes',0)&1024),
                'Regular no-reparse smoke diagnostic required')
        stream.seek(max(0,before.st_size-limit));raw=stream.read(limit);stream.seek(0)
        sha256=hashlib.file_digest(stream,'sha256').hexdigest();after=os.fstat(stream.fileno())
        require((before.st_ino,before.st_dev,before.st_size,before.st_mtime_ns)==
                (after.st_ino,after.st_dev,after.st_size,after.st_mtime_ns),'Smoke diagnostic changed during capture')
    return {'file_bytes':before.st_size,'captured_bytes':len(raw),'sha256':sha256,'capture':'TAIL',
            'truncated':before.st_size>len(raw),'text':raw.decode('utf-8',errors='replace')}


def _smoke_resource_snapshot():
    """Diagnostic observation only: coordinator limits and host/cgroup counters."""
    row={'scope':'DIAGNOSTIC_COORDINATOR_HOST_AND_CGROUP_NOT_LEAN_PROCESS','errors':[],
         'nproc_scope':'Worker sets NPROC=64 inside its new user namespace; inherited coordinator NPROC can still constrain ancestor accounting',
         'nproc_precondition':'These observations neither raise inherited NPROC limits nor identify the original pthread error'}
    try:
        import resource
        row['rlimits']={name:list(resource.getrlimit(getattr(resource,'RLIMIT_'+name)))
                       for name in ('AS','NPROC','STACK','NOFILE')}
        row['cpu_affinity']=sorted(os.sched_getaffinity(0))
        status=Path('/proc/self/status').read_text(encoding='ascii')
        row['coordinator_status']={line.split(':',1)[0]:line.split(':',1)[1].strip() for line in status.splitlines()
                                   if line.split(':',1)[0] in {'VmSize','VmPeak','VmRSS','Threads','Uid','NSpid'}}
        uid=os.getuid();tasks=0;scanned=0;unreadable=0;truncated=False
        for path in Path('/proc').iterdir():
            if not path.name.isdecimal():continue
            if scanned>=4096:truncated=True;break
            scanned+=1
            try:
                fields=dict(line.split(':',1) for line in (path/'status').read_text(encoding='ascii').splitlines() if ':' in line)
                if int(fields['Uid'].split()[0])==uid:tasks+=int(fields['Threads'])
            except (OSError,KeyError,ValueError):unreadable+=1
        row['host_real_uid_tasks']={'uid':uid,'tasks':tasks,'scanned_processes':scanned,
                                    'unreadable_processes':unreadable,'truncated':truncated,
                                    'incomplete':bool(unreadable or truncated)}
        groups=[line.split(':',2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::')]
        require(len(groups)==1 and groups[0].startswith('/') and '..' not in Path(groups[0]).parts,'Diagnostic cgroup path differs')
        group=Path('/sys/fs/cgroup')/groups[0].lstrip('/');row['cgroup']=groups[0]
        row['cgroup_counters']={}
        for name in ('pids.current','pids.max','pids.events','memory.current','memory.max','memory.events','memory.peak'):
            try:row['cgroup_counters'][name]=(group/name).read_text(encoding='ascii').strip()
            except OSError as exc:row['errors'].append(name+': '+str(exc))
        row['global_limits']={name:(Path('/proc/sys/kernel')/name).read_text(encoding='ascii').strip()
                              for name in ('threads-max','pid_max')}
    except (OSError,ValueError,KeyError,AttributeError,ImportError,ContractError) as exc:row['errors'].append(str(exc))
    return row


def _infrastructure_probe_source(probe):
    require(type(probe)is str and probe in {'stdlib','project'},'Closed infrastructure probe selector required')
    if probe=='stdlib':
        return ('import Lean\nopen Lean Elab Command\n'
                'run_cmd do\n  let _ \u2190 getEnv\n  pure ()\n'
                'example : True := True.intro\n')
    return ('import Zeta23.RHRC.OpicaComposition.FiniteWorlds\n'
            'import Zeta23.RHRC.OpicaComposition.Export\n'
            'run_cmd Zeta23.RHRC.OpicaComposition.exportTarget '
            '`Zeta23.RHRC.OpicaComposition.FiniteWorlds.IdentityTarget "value"\n')


def _failed_smoke_diagnostics(output,worker,budget,*,probe='stdlib'):
    """One bounded traced replay can explain failure, never authorize a pass."""
    from ..opica_round4.math_gate import _copy_regular
    source_text=_infrastructure_probe_source(probe)
    row={'schema':'OPICA_FAILED_SMOKE_DIAGNOSTIC_V1','status':'DIAGNOSTIC_ONLY',
         'probe':probe,
         'authority':'NO_ACCEPTANCE_OR_PROOF_AUTHORITY','accepted':False,'disposition':'ERROR',
         'maximum_seconds':min(SMOKE_DIAGNOSTIC_TIMEOUT,budget.wall_seconds),
         'trace_capture_bytes':SMOKE_DIAGNOSTIC_TRACE_BYTES,'log_capture_bytes':SMOKE_DIAGNOSTIC_LOG_BYTES,
         'trace_file_count':1,'per_file_hard_bytes':budget.output_bytes,
         'poll_output_limit_bytes':min(budget.output_bytes,SMOKE_DIAGNOSTIC_TRACE_BYTES+SMOKE_DIAGNOSTIC_LOG_BYTES),
         'overhead_caveat':'Tracer adds a process; this replay cannot prove the original failure errno',
         'before':_smoke_resource_snapshot()}
    folder=Path(output)/'diagnostic-only';proc=None;created=False
    try:
        folder=unlinked(folder)
        require(worker.production is True,'Failed smoke diagnostics require production worker')
        require(not folder.exists(),'Fresh smoke diagnostic directory required');folder.mkdir();created=True
        tracer=unlinked('/usr/bin/strace')
        if not tracer.is_file():
            row['disposition']='UNAVAILABLE';row['reason']='Trusted /usr/bin/strace is absent'
        else:
            row['tracer_sha256']=file_hash(tracer)
            source='OpicaInfrastructureSmoke.lean';obj='OpicaInfrastructureSmoke.olean'
            expected_source=hashlib.sha256(source_text.encode('utf-8')).hexdigest()
            require(file_hash(Path(output)/source)==expected_source,
                    'Diagnostic source differs from fixed infrastructure probe')
            row['source_sha256']=_copy_regular(Path(output)/source,folder/source)
            require(row['source_sha256']==expected_source,'Copied diagnostic source differs from fixed infrastructure probe')
            command,env=_recipe(worker,folder,source,obj,budget)
            position=command.index(str(Path(worker.lean)))
            command[position:position]=[str(tracer),'-f','-qq','-yy','-s','128','-e',
                'trace=openat,read,lseek,brk,mmap,mprotect,munmap,clone,clone3,prlimit64',
                '-e','status=failed','-o','/out/syscalls.trace','--']
            row['command']=command;row['same_worker_budget']=budget.to_dict()
            log=folder/'diagnostic.log';trace=folder/'syscalls.trace';started=time.monotonic()
            flags=os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0)
            with os.fdopen(os.open(log,flags,0o600),'wb') as stream:
                proc=subprocess.Popen(command,cwd=folder,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
                row['disposition']='COMPLETED'
                while proc.poll() is None:
                    size=sum(p.lstat().st_size for p in (log,trace) if p.exists() or p.is_symlink())
                    if time.monotonic()-started>=row['maximum_seconds']:row['disposition']='TIMED_OUT'
                    elif size>row['poll_output_limit_bytes']:row['disposition']='OUTPUT_LIMIT'
                    else:time.sleep(0.025);continue
                    try:os.killpg(proc.pid,signal.SIGKILL)
                    except ProcessLookupError:pass
                    break
                row['exit_code']=proc.wait(timeout=1)
            row['elapsed_ms']=int((time.monotonic()-started)*1000)
            require(file_hash(folder/source)==row['source_sha256'],'Diagnostic smoke source changed')
            row['log']=_smoke_diagnostic_capture(log,SMOKE_DIAGNOSTIC_LOG_BYTES)
            if trace.exists() or trace.is_symlink():row['trace']=_smoke_diagnostic_capture(trace,SMOKE_DIAGNOSTIC_TRACE_BYTES)
            else:row['trace_unavailable']=True
            allowed={source,obj,obj+'.private',obj+'.server','diagnostic.log','syscalls.trace'}
            for path in folder.iterdir():
                path=unlinked(path);info=path.lstat()
                require(path.name in allowed and stat.S_ISREG(info.st_mode) and
                        not(getattr(info,'st_file_attributes',0)&1024),'Unexpected smoke diagnostic output file')
    except (OSError,ValueError,AttributeError,ContractError,RuntimeError,subprocess.SubprocessError) as exc:row['error']=str(exc);row['disposition']='ERROR'
    finally:
        if proc is not None and proc.poll() is None:
            try:os.killpg(proc.pid,signal.SIGKILL)
            except OSError as exc:row['cleanup_group_error']=str(exc)
            try:
                if proc.poll() is None:proc.kill()
                proc.wait(timeout=1)
            except (OSError,subprocess.SubprocessError) as exc:row['cleanup_error']=str(exc);row['disposition']='ERROR'
        row['after']=_smoke_resource_snapshot()
        if created:
            try:(unlinked(folder/'result.json')).write_bytes(canonical_bytes(row)+b'\n')
            except (OSError,ContractError) as exc:row['artifact_error']=str(exc)
        try:
            summary={key:value for key,value in row.items() if key not in {'trace','log'}}
            for key in ('trace','log'):
                if key in row:summary[key]={**row[key],'text':row[key]['text'][-4096:]}
            sys.stderr.write('OPICA_FAILED_SMOKE_DIAGNOSTIC_ONLY\t'+json.dumps(summary,ensure_ascii=True,sort_keys=True)+'\n');sys.stderr.flush()
        except (OSError,ValueError,AttributeError):pass
    return row


def _raised_smoke_diagnostics(error):
    """Record an unknown execution boundary without replaying failed guards."""
    text=str(error);limit=4096
    return {'schema':'OPICA_FAILED_SMOKE_DIAGNOSTIC_V1','status':'DIAGNOSTIC_ONLY',
            'authority':'NO_ACCEPTANCE_OR_PROOF_AUTHORITY','accepted':False,
            'disposition':'NOT_REPLAYED_WORKER_EXCEPTION','replay_attempted':False,
            'execution_boundary':'NO_RETURNED_NATIVE_RECEIPT','compiler_reached':'NOT_ESTABLISHED',
            'exception_type':type(error).__name__[:128],'exception_message':text[:limit],
            'maximum_exception_message_characters':limit,'exception_message_truncated':len(text)>limit}


def _safe_smoke_resource_snapshot():
    """Optional observations must not mask the actual worker exception."""
    try:return _smoke_resource_snapshot()
    except Exception as exc:
        return {'scope':'DIAGNOSTIC_COORDINATOR_HOST_AND_CGROUP_NOT_LEAN_PROCESS',
                'errors':['RESOURCE_SNAPSHOT_UNAVAILABLE:'+type(exc).__name__[:128]]}


def _native_infrastructure_smoke(output,worker,*,probe='stdlib'):
    """Exercise the production recipe before the expensive project build.

    The separate helper makes the exact worker/source recipe inspectable in
    portable tests. Actual qualification still requires run_worker's Linux
    isolation, cgroup and tmpfs checks; development execution cannot pass here.
    """
    require(type(worker)is WorkerConfig and worker.production is True,
            'Infrastructure smoke requires the actual production worker')
    source_text=_infrastructure_probe_source(probe)
    standard=unlinked(Path(worker.toolchain_root)/'lib/lean').resolve()
    if probe=='stdlib':
        require(worker.lean_paths==[str(standard)],'Infrastructure smoke imports only pinned Lean standard library')
    else:
        require(str(standard) in worker.lean_paths and len(worker.lean_paths)>1,
                'Project export probe requires full prepared native import paths')
        for module in ('FiniteWorlds','Export'):
            relative='Zeta23/RHRC/OpicaComposition/'+module+'.olean'
            require(any(unlinked(Path(root)/relative).is_file() for root in worker.lean_paths),
                    'Project export probe object absent: '+module)
    output=unlinked(output).absolute();require(not output.exists(),'Fresh infrastructure smoke output required')
    output.mkdir(parents=True)
    source='OpicaInfrastructureSmoke.lean';obj='OpicaInfrastructureSmoke.olean'
    (output/source).write_text(source_text,encoding='utf-8',newline='\n')
    before=file_hash(output/source)
    require(before==hashlib.sha256(source_text.encode('utf-8')).hexdigest(),'Fixed infrastructure probe source differs')
    report={'schema':'OPICA_NATIVE_INFRASTRUCTURE_SMOKE_V1','status':'ENVIRONMENT_ERROR',
      'authority':'INFRASTRUCTURE_ONLY_NO_RH_AUTHORITY','probe':probe,'source':source,'source_sha256':before,
      'object':obj,'native':None,'RH':'OPEN','Step4':'OPEN'}
    worker_raised=False
    try:
        budget=SearchBudget(**worker.budget) if worker.budget else SearchBudget()
        report['resource_observations']={'authority':'DIAGNOSTIC_ONLY','before':_safe_smoke_resource_snapshot()}
        try:native=run_worker(worker,output,source,obj,budget);report['native']=native
        except Exception as exc:
            worker_raised=True
            try:report['diagnostics']=_raised_smoke_diagnostics(exc)
            except Exception:
                report['diagnostics']={'schema':'OPICA_FAILED_SMOKE_DIAGNOSTIC_V1','status':'DIAGNOSTIC_ONLY',
                  'authority':'NO_ACCEPTANCE_OR_PROOF_AUTHORITY','accepted':False,'disposition':'ERROR',
                  'replay_attempted':False,'execution_boundary':'NO_RETURNED_NATIVE_RECEIPT',
                  'compiler_reached':'NOT_ESTABLISHED','reason':'Worker exception diagnostic unavailable'}
            raise
        finally:report['resource_observations']['after']=_safe_smoke_resource_snapshot()
        require(file_hash(output/source)==before,'Infrastructure smoke source changed during execution')
        if native['exit_code']==0 and native['resource_status'] is None and (output/obj).is_file():
            require(native['capability']=='LINUX_ISOLATED','Infrastructure smoke was not isolated production execution')
            if probe=='project':
                records=[line.split(b'\t',1)[1] for line in (output/(source+'.log')).read_bytes().splitlines()
                         if line.startswith(b'OPICA_TARGET\t')]
                require(len(records)==1,'Project infrastructure target export incomplete')
                report['target_type_expression_sha256']=expression_hash(load_bytes(records[0]))
            report['object_sha256']=file_hash(output/obj)
            report['status']='PASS_INFRASTRUCTURE_SMOKE'
        else:
            try:report['diagnostics']=_failed_smoke_diagnostics(output,worker,budget,probe=probe)
            except Exception as exc:
                # A diagnostic failure cannot replace the actual failed worker.
                report['diagnostics']={'status':'DIAGNOSTIC_ONLY','accepted':False,'disposition':'ERROR','error':str(exc)}
        return report
    finally:
        try:(output/'result.json').write_bytes(canonical_bytes(report)+b'\n')
        except Exception:
            if not worker_raised:raise


def prepare_native(repo,output):
    """Single-owner Linux bootstrap; root calls this after the implementation freeze."""
    require(platform.system()=='Linux','Production native preparation requires Linux')
    repo=unlinked(repo).resolve();require((repo/'lean-toolchain').read_text(encoding='utf-8').strip()==LEAN_PIN,'Host toolchain pin drift')
    require(not git(repo,'status','--porcelain','--untracked-files=all'),'Production native preparation requires clean source')
    packages=_packages(repo)
    rows=frozen_atlas(repo);modules=sorted(set(CORE_MODULES)|{r['module'] for r in rows})
    before=_source(repo,modules);output=_external(repo,output,True)
    report={'schema':'OPICA_NATIVE_PREPARATION_V1','status':'ENVIRONMENT_ERROR','commands':[],
      'checked_commit':git(repo,'rev-parse','HEAD'),'checked_tree':git(repo,'rev-parse','HEAD^{tree}'),
      'source_sha256':before,'requested_modules':modules,'RH':'OPEN','Step4':'OPEN'}
    report['pinned_packages']=packages
    env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN_','ELAN_'))}
    env.update({'ELAN_TOOLCHAIN':LEAN_PIN,'LEAN_NUM_THREADS':'2','GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'})
    lake=shutil.which('lake');require(lake,'Pinned host Lake is missing')
    def run(argv,label,seconds=60):
        c=_command(argv,repo,env,output,label,seconds);report['commands'].append(c)
        require(c['returncode']==0 and c['timeout'] is False,'Native preparation command failed: '+label);return output/c['stdout']
    try:
        import resource
        soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE)
        report['coordinator_file_descriptor_limit']={'scope':'ACTUAL_PREPARATION_COORDINATOR_RLIMIT_NOFILE',
          'soft':soft,'hard':hard}
        projection=_materialize_pinned_benchmark_alias(repo/'.lake/packages/mathlib',
          expected_commit='51e6992efd06126df61a496bebf8f49482a4e129',
          expected_blob='e5224d533ef27b001224859a9b36696846a7e7fe')
        report['dependency_source_projections']=[{'package':'mathlib',**projection}]
        require(_packages(repo)==packages,'Pinned package identity changed during source preparation')
        scope=discover_source_paths(repo)
        report['source_scope_preflight']={'status':'PASS_STRICT_NO_LINK_SOURCE_DISCOVERY',
          'source_path_count':len(scope),
          'source_parent_directory_count':len({'.'}|{p.as_posix() for relative in scope for p in Path(relative).parents}),
          'path_inventory_digest':digest(sorted(scope),domain='OPICA_NATIVE_SOURCE_PATHS_V1')}
        source_files=hash_inventory(repo,scope)
        report['source_hash_preflight']={'source_file_count':len(source_files),
          'source_digest':digest(source_files,domain='OPICA_SOURCE_FILES_V1')}
        mount=load_bytes(run(['/usr/bin/findmnt','--json','--bytes','--target',os.environ['OPICA_NATIVE_OUTPUT'],'--output','FSTYPE,SIZE,TARGET'],'volume').read_bytes())
        fs=mount['filesystems'];require(len(fs)==1 and fs[0]['fstype']=='tmpfs' and 0<int(fs[0]['size'])<=SearchBudget().disk_bytes,'Actual native tmpfs volume is absent or exceeds disk budget')
        report['native_volume']=fs[0]
        version=run([lake,'env','lean','--version'],'compiler').read_text(encoding='utf-8').strip()
        require(version.startswith('Lean (version 4.33.0-rc2,') and 'd8b18978322de05a8f3dba51ef03cf5461676c17' in version,'Wrong actual host compiler')
        prefix=unlinked(run([lake,'env','lean','--print-prefix'],'prefix').read_text(encoding='utf-8').strip()).resolve()
        lean=unlinked(run([lake,'env','which','lean'],'lean-path').read_text(encoding='utf-8').strip()).resolve()
        require(lean.is_relative_to(prefix),'Host Lean binary/prefix mismatch')
        smoke_worker=WorkerConfig(str(lean),str(prefix),[str(unlinked(prefix/'lib/lean').resolve())],
          production=True,budget=asdict(SearchBudget()))
        report['infrastructure_smoke']=_native_infrastructure_smoke(output/'smoke',smoke_worker)
        require(report['infrastructure_smoke']['status']=='PASS_INFRASTRUCTURE_SMOKE',
                'Actual isolated Lean infrastructure smoke failed before project build')
        run([lake,'build',*modules],'selected-build',7200)
        text=run([lake,'env','printenv','LEAN_PATH'],'import-paths').read_text(encoding='utf-8').strip()
        paths=[]
        for p in text.split(os.pathsep):
            path=unlinked(repo/p).resolve()
            require(path.is_relative_to(repo/'.lake') or path==prefix/'lib/lean','Foreign compiler/import cache path')
            if path.is_dir() and str(path) not in paths:paths.append(str(path))
        require(str(repo/'.lake/build/lib/lean') in paths,'Fresh host object root absent')
        budget=asdict(SearchBudget());worker=WorkerConfig(str(lean),str(prefix),paths,production=True,budget=budget)
        summary=worker_environment(worker,manifest_output=output/'native-objects.json')
        report['project_export_probe']=_native_infrastructure_smoke(output/'project-export-probe',worker,probe='project')
        require(report['project_export_probe']['status']=='PASS_INFRASTRUCTURE_SMOKE',
                'Actual isolated project target export failed after selected build')
        require(_source(repo,modules)==before and _packages(repo)==packages and git(repo,'rev-parse','HEAD')==report['checked_commit'],'Source changed during native preparation')
        report.update({'status':'PASS_NATIVE_PREPARED','worker':worker.to_dict(),'worker_environment':summary,
          'native_objects_sha256':file_hash(output/'native-objects.json'),'compiler':version,'worker_config_path':str(output/'worker.json')})
        (output/'worker.json').write_bytes(canonical_bytes(worker.to_dict())+b'\n');return report
    finally:(output/'result.json').write_bytes(canonical_bytes(report)+b'\n')


def atlas_driver(rows):
    modules=sorted({r['module'] for r in rows}|{'Zeta23.RHRC.OpicaRound3AtlasExport'})
    text='\n'.join('import '+lean_name(m) for m in modules)
    text+='\nset_option pp.fullNames true\nset_option pp.universes true\nrun_cmd do\n  Zeta23.RHRC.OpicaRound3AtlasExport.exportAtlas #[\n'
    text+=',\n'.join('    { declaration := '+lean_string(r['declaration'])+', moduleName := '+lean_string(r['module'])+' }' for r in rows)
    return text+'\n  ]\n'


def check_current_compatibility(repo,output,worker):
    worker=as_record(worker,WorkerConfig);repo=unlinked(repo).resolve();rows=frozen_atlas(repo)
    output=_external(repo,output,worker.production);before=_source(repo,{r['module'] for r in rows}|{'Zeta23.RHRC.OpicaRound3AtlasExport'})
    report={'schema':'OPICA_CURRENT_COMPATIBILITY_V1','status':'ENVIRONMENT_ERROR','batches':[],
      'checked_commit':git(repo,'rev-parse','HEAD'),'checked_tree':git(repo,'rev-parse','HEAD^{tree}'),
      'atlas_sha256':ATLAS_SHA256,'source_sha256':before,'RH':'OPEN','Step4':'OPEN','semantic_exhaustion':False}
    all_rows={};budget=SearchBudget(**worker.budget) if worker.budget else SearchBudget()
    native_export=output/'native-export.jsonl';native_export.write_bytes(b'')
    try:
        report['worker_version_command']=_worker_version(repo,output,worker)
        for index,start in enumerate(range(0,len(rows),16)):
            batch=rows[start:start+16];folder=output/('batch-'+str(index).zfill(3));folder.mkdir()
            source='AtlasBatch'+str(index).zfill(3)+'.lean';obj=source[:-5]+'.olean'
            (folder/source).write_text(atlas_driver(batch),encoding='utf-8',newline='\n')
            native=run_worker(worker,folder,source,obj,budget);report['batches'].append({'index':index,'declarations':[r['declaration'] for r in batch],'native':native})
            require(native['resource_status'] is None and native['exit_code']==0,'Fresh current atlas batch failed or exceeded resources')
            raw=(folder/(source+'.log')).read_bytes();require(len(raw)<8*1024*1024,'Current atlas batch log exceeds8MiB')
            wanted={r['declaration']:r for r in batch};seen=set()
            for line in raw.splitlines():
                if not line.startswith(b'OPICA3_ATLAS\t'):continue
                fact=load_bytes(line.split(b'\t',1)[1]);require(type(fact)is dict and set(fact)==ATLAS_FIELDS and fact['schema']=='OPICA3_ATLAS_COMPILER_ROW_V1','Malformed actual atlas compiler row')
                name=fact['declaration'];require(name in wanted and name not in seen and name not in all_rows,'Wrong/duplicate current atlas declaration')
                old=wanted[name];require(fact['module']==old['module'] and fact['kind']==old['kind'],'Current declaration source origin/kind changed')
                require(expression_hash(fact['type_expression'])==old['type_sha256'],'Current declaration exact type changed: '+name)
                require(fact['axioms']==old['statement']['axioms'] and set(fact['axioms'])<={'propext','Classical.choice','Quot.sound'},'Current declaration full axiom footprint changed')
                require(fact['universe_parameters']==old['statement']['universe_parameters'],'Current universe parameters changed')
                validate_telescope(fact['type_expression'],fact['outer_telescope'])
                with native_export.open('ab') as stream:stream.write(line+b'\n')
                seen.add(name);all_rows[name]={'declaration':name,'module':fact['module'],'type_sha256':old['type_sha256'],'axioms':fact['axioms']}
            require(seen==set(wanted),'Current atlas batch omitted required declarations')
            require((folder/obj).is_file(),'Fresh current atlas object absent')
            report['batches'][-1]['source_sha256']=file_hash(folder/source);report['batches'][-1]['object_sha256']=file_hash(folder/obj)
        require(len(all_rows)==462 and _source(repo,{r['module'] for r in rows}|{'Zeta23.RHRC.OpicaRound3AtlasExport'})==before,'Current atlas source changed during export')
        report.update({'status':'PASS_CURRENT_COMPATIBILITY' if worker.production else 'DEVELOPMENT_CURRENT_COMPATIBILITY',
          'declarations':462,'memberships':696,'required_root_memberships':221,'historical_contacts':185,
          'cohorts':COHORTS,'semantic_review_promotion':False,'compiler_rows':list(all_rows.values()),
          'native_export_path':str(native_export),'native_export_sha256':file_hash(native_export)})
        return report
    finally:(output/'result.json').write_bytes(canonical_bytes(report)+b'\n')


def _validate_mathematical_worker_receipts(result,output,worker):
    """A PASS label cannot substitute for the fixed isolated compiler recipe."""
    from ..opica_round4.math_gate import mathematical_budget,relative,SEMANTIC_MUTATIONS
    require(result.get('execution_mode')==('PRODUCTION_ISOLATED' if worker.production else 'DEVELOPMENT_ONLY') and
            result.get('authority')==('CURRENT_SOURCE_ISOLATED_NATIVE_SUPPORT' if worker.production else 'DEVELOPMENT_NATIVE_SUPPORT_ONLY'),
            'Mathematical support execution authority differs')
    budget=mathematical_budget(worker,600)
    require(result.get('worker')==worker.to_dict() and result.get('worker_budget')==budget.to_dict(),
            'Mathematical support worker/budget differs')
    rows=result.get('module_records')
    require(type(rows)is list and len(rows)==EXPECTED_MODULE_COUNT and
            {r.get('module') for r in rows}==set(MATHEMATICAL_MODULES),
            'Mathematical isolated module receipt inventory differs')
    isolated=replace(worker,lean_paths=[str(output/'lib'),*worker.lean_paths])
    def check(native,folder,source,code,log):
        require(type(native)is dict and native.get('recipe')==MATH_SUPPORT_RECIPE and
                native.get('capability')==('LINUX_ISOLATED' if worker.production else 'NATIVE_DEVELOPMENT_ONLY') and
                native.get('exit_code')==code and not native_resource_failure(native),
                'Mathematical isolated worker receipt missing or invalid')
        command,_=_recipe(isolated,folder,source,source[:-5]+'.olean',budget,mathematical_support=True)
        require(native.get('command')==command,'Mathematical isolated worker argv differs')
        require(native.get('log_sha256')==file_hash(folder/(source+'.log'))==file_hash(log),
                'Mathematical isolated worker log binding differs')
        scope=native.get('resource_scope',{})
        if worker.production:
            require(scope.get('mode')=='LINUX_CGROUP_V2_TMPFS' and
                    type(scope.get('address_space_bytes'))is int and scope['address_space_bytes']==LEAN_ADDRESS_SPACE_BYTES and
                    all(type(scope.get(key))is int and 0<scope[key]<=cap for key,cap in
                        (('memory_bytes',budget.memory_bytes),('processes',64),('disk_bytes',budget.disk_bytes))) and
                    type(scope.get('cgroup'))is str and scope['cgroup'].startswith('/'),
                    'Mathematical isolated worker resource scope differs')
        else:require(scope=={'mode':'NATIVE_DEVELOPMENT_ONLY'},'Development mathematical worker scope differs')
        expected_caps={'wall_seconds':budget.wall_seconds,'cpu_seconds_soft':budget.cpu_seconds,
          'cpu_seconds_hard':budget.cpu_seconds,'log_bytes':budget.log_bytes,'max_file_bytes':budget.max_file_bytes,
          'memory_bytes':scope.get('memory_bytes',budget.memory_bytes),'disk_bytes':scope.get('disk_bytes',budget.disk_bytes),
          'address_space_bytes':LEAN_ADDRESS_SPACE_BYTES,'os_limits_enforced':worker.production}
        caps=native.get('resource_caps')
        require(type(caps)is dict and caps==expected_caps and
                all(type(caps[key])is type(value) for key,value in expected_caps.items()),
                'Mathematical isolated worker resource caps differ')
        require(native.get('resource_reason') is None and
                native.get('failure_reason')==(None if code==0 else 'UNCLASSIFIED_WORKER_FAILURE'),
                'Mathematical isolated worker failure reason differs')
        child=native.get('child_status',{})
        require(type(child)is dict and type(child.get('return_code'))is int and
                child=={'schema':'OPICA_WORKER_WAIT_STATUS_V1','return_code':code,'signal':None,
                       'observation':'PYTHON_SUBPROCESS_WAIT','scope':'COMMAND_PROCESS_ONLY_WRAPPED_CHILD_UNKNOWN'},
                'Mathematical isolated worker wait status differs')
    for row in rows:
        module=row['module'];source=relative(module).as_posix();folder=output/'workers'/module
        require(row.get('worker_output')==str(folder) and row.get('argv')==row.get('native',{}).get('command') and
                row.get('exit_code')==0 and row.get('source_sha256')==file_hash(folder/source) and
                row.get('log_sha256')==file_hash(output/(module+'.log')),
                'Mathematical module source/receipt binding differs')
        check(row.get('native'),folder,source,0,output/(module+'.log'))
        products=row.get('products',{})
        required={relative(module,suffix).as_posix() for suffix in ('.olean','.ilean')}
        allowed=required|{relative(module,suffix).as_posix() for suffix in ('.olean.private','.olean.server')}
        require(type(products)is dict and required<=set(products)<=allowed and
                all(file_hash(folder/name)==expected==file_hash(output/'lib'/name) for name,expected in products.items()) and
                row.get('object_sha256')==products[relative(module,'.olean').as_posix()],
                'Mathematical module product binding differs')
    mutation=result.get('mutation',{});source='RejectedSemanticMutations.lean';folder=output/'workers'/'semantic-mutations'
    require(mutation.get('source_sha256')==hashlib.sha256(SEMANTIC_MUTATIONS.encode('utf-8')).hexdigest()==
            file_hash(output/source)==file_hash(folder/source) and mutation.get('exit_code')==1 and
            mutation.get('error_count')==9 and mutation.get('log_sha256')==file_hash(output/'semantic-mutations.log'),
            'Mathematical semantic mutation binding differs')
    check(mutation.get('native'),folder,source,1,output/'semantic-mutations.log')


def check_mathematical_support(repo,output,worker):
    from ..opica_round4.math_gate import load_worker_config
    worker=as_record(worker,WorkerConfig);repo=unlinked(repo).resolve();output=_external(repo,output,worker.production)
    gate=repo/'research/RHRC/integration/opica_round4/math_gate.py';require(gate.is_file(),'Actual mathematical support gate missing')
    version=_worker_version(repo,output,worker)
    report={'schema':'OPICA_MATHEMATICAL_SUPPORT_QUALIFICATION_V1','status':'ENVIRONMENT_ERROR',
      'gate_sha256':file_hash(gate),'RH':'OPEN','Step4':'OPEN'}
    report['worker_version_command']=version
    try:
        before=worker_environment(worker) if worker.production else None
        config=output/'worker-config.json';config.write_bytes(worker.to_bytes()+b'\n')
        config_hash=file_hash(config);report['worker_config_sha256']=config_hash
        command=[sys.executable,'-B',str(gate),'--repo',str(repo),'--output-dir',str(output/'native'),
          '--lean',worker.lean,'--lean-paths',os.pathsep.join(worker.lean_paths),'--timeout','600','--worker-config',str(config)]
        env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHONUTF8':'1'}
        record=_command(command,repo,env,output,'mathematical-support',7200);report['command']=record
        require(record['returncode']==0 and record['timeout'] is False,'Actual bounded mathematical support gate failed')
        checked_worker,checked_hash=load_worker_config(config)
        require(checked_hash==config_hash and checked_worker==worker,
                'Mathematical coordinator worker configuration changed')
        result=load_bytes((output/'native/result.json').read_bytes())
        require(result.get('worker_config_sha256')==config_hash,'Mathematical coordinator configuration binding differs')
        require(result.get('status')=='PASS' and result.get('module_count')==EXPECTED_MODULE_COUNT and
                result.get('declaration_count')==EXPECTED_DECLARATION_COUNT and
                result.get('baseline_module_count')==BASELINE_MODULE_COUNT==16 and
                result.get('baseline_declaration_count')==BASELINE_DECLARATION_COUNT==98 and
                result.get('semantic_mutation_count')==9,
                'Mathematical support gate incomplete or not actual native evidence')
        _validate_mathematical_worker_receipts(result,output/'native',worker)
        if worker.production:
            require(worker_environment(worker)==before,'Mathematical compiler/import environment changed')
            report['worker_environment']=before
        report.update({'status':'PASS_MATHEMATICAL_SUPPORT' if worker.production else 'DEVELOPMENT_MATHEMATICAL_SUPPORT',
          'native_result':result,'native_result_sha256':file_hash(output/'native/result.json')});return report
    finally:(output/'result.json').write_bytes(canonical_bytes(report)+b'\n')
