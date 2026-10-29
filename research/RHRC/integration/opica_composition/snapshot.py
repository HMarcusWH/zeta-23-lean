"""Source epochs bind complete reviewed bytes and reject links and drift."""
from __future__ import annotations
import hashlib, os, stat, subprocess
from contextlib import contextmanager
from pathlib import Path
from .canonical import require, digest, digest_text, validate_path_inventory, relative_path
from .contracts import ExperimentSpec, SnapshotIdentity, SearchBudget, as_record

def unlinked(path):
    path = Path(os.path.abspath(path))
    for part in (path, *path.parents):
        try: mode = os.lstat(part)
        except FileNotFoundError: continue
        require(not stat.S_ISLNK(mode.st_mode) and not (getattr(mode,"st_file_attributes",0) & 1024),
                "linked/reparse native path refused: "+str(part))
    return path

def file_hash(path):
    path=unlinked(path)
    require(path.is_file(), "regular source/evidence file required")
    with path.open("rb") as stream:
        return hashlib.file_digest(stream,"sha256").hexdigest()


def _evidence_identity(info):
    # Windows CRT fstat reports ctime differently from path stat; birthtime is
    # consistent while the no-delete/no-write native handles lock the identity.
    change=getattr(info,'st_birthtime_ns',info.st_ctime_ns) if os.name=='nt' else info.st_ctime_ns
    return (info.st_dev,info.st_ino,info.st_mode,info.st_size,info.st_mtime_ns,change)


def _require_evidence_identity(info,expected):
    require(_evidence_identity(info)[:len(expected)]==expected,'Evidence entry identity changed')


def _evidence_regular(info,*,directory=False):
    require((stat.S_ISDIR(info.st_mode) if directory else stat.S_ISREG(info.st_mode)) and
            not(getattr(info,'st_file_attributes',0)&1024),'Linked/reparse/nonregular evidence entry refused')


def _evidence_windows_handle(path,*,directory):
    """Lock every parent against rename; OPEN_REPARSE_POINT never opens its target."""
    import ctypes,msvcrt
    from ctypes import wintypes
    kernel=ctypes.WinDLL('kernel32',use_last_error=True)
    create=kernel.CreateFileW;create.restype=wintypes.HANDLE
    create.argtypes=[wintypes.LPCWSTR,wintypes.DWORD,wintypes.DWORD,wintypes.LPVOID,
                     wintypes.DWORD,wintypes.DWORD,wintypes.HANDLE]
    close=kernel.CloseHandle;close.argtypes=[wintypes.HANDLE]
    query=kernel.GetFileInformationByHandleEx
    query.argtypes=[wintypes.HANDLE,ctypes.c_int,wintypes.LPVOID,wintypes.DWORD]
    class AttributeTag(ctypes.Structure):
        _fields_=[('attributes',wintypes.DWORD),('tag',wintypes.DWORD)]
    flags=0x00200000|(0x02000000 if directory else 0x08000000)
    handle=create(str(path),0x80 if directory else 0x80000000,3 if directory else 1,None,3,flags,None)
    require(handle!=wintypes.HANDLE(-1).value,'No-follow evidence handle unavailable')
    retained=False
    try:
        tags=AttributeTag()
        require(query(handle,9,ctypes.byref(tags),ctypes.sizeof(tags)) and not(tags.attributes&1024) and
                bool(tags.attributes&16)==directory,'Evidence handle is reparse or wrong kind')
        if directory:retained=True;return handle,lambda:close(handle)
        fd=msvcrt.open_osfhandle(handle,os.O_RDONLY|os.O_BINARY);handle=None
        return fd,None
    finally:
        if handle is not None and not retained:close(handle)


@contextmanager
def _evidence_directory(root,relative='',identities=None):
    root=unlinked(root);parts=Path(relative).parts if relative else ();opened=[]
    try:
        if os.name!='nt':
            flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW
            fd=os.open(root.anchor,flags);opened.append((fd,lambda fd=fd:os.close(fd)))
            for part in root.parts[1:]:
                fd=os.open(part,flags,dir_fd=fd);opened.append((fd,lambda fd=fd:os.close(fd)))
            info=os.fstat(fd)
        else:
            current=Path(root.anchor)
            for part in ('',*root.parts[1:]):
                if part:current/=part
                handle,close=_evidence_windows_handle(current,directory=True);opened.append((handle,close))
            fd=None;info=os.lstat(root)
        _evidence_regular(info,directory=True)
        if identities is not None:_require_evidence_identity(info,identities[''])
        current=root;key=''
        for part in parts:
            current/=part;key=(key+'/' if key else '')+part
            if os.name!='nt':
                fd=os.open(part,flags,dir_fd=fd);opened.append((fd,lambda fd=fd:os.close(fd)));info=os.fstat(fd)
            else:
                handle,close=_evidence_windows_handle(current,directory=True);opened.append((handle,close));info=os.lstat(current)
            _evidence_regular(info,directory=True)
            if identities is not None:_require_evidence_identity(info,identities[key])
        yield fd,current
    finally:
        for _,close in reversed(opened):close()


@contextmanager
def _evidence_file(root,relative,identities=None):
    relative_path(relative);parent=Path(relative).parent.as_posix()
    with _evidence_directory(root,'' if parent=='.' else parent,identities) as (directory,path):
        if os.name!='nt':
            fd=os.open(Path(relative).name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=directory)
        else:fd,_=_evidence_windows_handle(path/Path(relative).name,directory=False)
        with os.fdopen(fd,'rb') as stream:
            info=os.fstat(stream.fileno());_evidence_regular(info)
            if identities is not None:_require_evidence_identity(info,identities[relative])
            yield stream,info
            after=os.fstat(stream.fileno());_evidence_regular(after)
            visible=os.stat(Path(relative).name,dir_fd=directory,follow_symlinks=False) if os.name!='nt' else os.lstat(path/Path(relative).name)
            _evidence_regular(visible)
            require(_evidence_identity(info)==_evidence_identity(after)==_evidence_identity(visible),
                    'Evidence file changed while reading')


def seal_evidence_tree(root,*,maximum_bytes=None):
    """Complete no-follow evidence inventory; physical identities stay private."""
    maximum_bytes=SearchBudget().disk_bytes if maximum_bytes is None else maximum_bytes
    require(type(maximum_bytes)is int and 0<maximum_bytes<=SearchBudget().disk_bytes,'Finite native evidence byte limit required')
    root=unlinked(root);identities={};directories=[];files=[];stack=[''];total=0
    while stack:
        relative=stack.pop()
        with _evidence_directory(root,relative,identities if identities else None) as (fd,path):
            before=os.fstat(fd) if fd is not None else os.lstat(path)
            identities[relative]=_evidence_identity(before)
            with os.scandir(fd if fd is not None else path) as entries:
                names=sorted(entry.name for entry in entries)
            for name in names:
                key=(relative+'/' if relative else '')+name;relative_path(key)
                info=os.stat(name,dir_fd=fd,follow_symlinks=False) if fd is not None else os.lstat(path/name)
                require(not stat.S_ISLNK(info.st_mode) and not(getattr(info,'st_file_attributes',0)&1024),
                        'Linked/reparse evidence entry refused: '+key)
                identities[key]=_evidence_identity(info)
                if stat.S_ISDIR(info.st_mode):directories.append(key);stack.append(key)
                else:
                    _evidence_regular(info)
                    total+=info.st_size
                    require(total<=maximum_bytes,'Complete native evidence logical bytes exceed hard disk cap')
                    with _evidence_file(root,key,identities) as (stream,opened):
                        hashed=hashlib.sha256();count=0
                        while True:
                            data=stream.read(min(1024*1024,opened.st_size-count+1))
                            if not data:break
                            count+=len(data);require(count<=opened.st_size,'Evidence grew during inventory hash')
                            hashed.update(data)
                        require(count==opened.st_size,'Evidence shrank during inventory hash')
                        value=hashed.hexdigest()
                    files.append({'path':key,'bytes':opened.st_size,'sha256':value})
            after=os.fstat(fd) if fd is not None else os.lstat(path)
            require(_evidence_identity(before)==_evidence_identity(after),'Evidence directory changed during inventory')
    paths=validate_path_inventory(row['path'] for row in files)
    all_paths=directories+list(paths)
    require(len({p.casefold() for p in all_paths})==len(all_paths),'Evidence case alias or file/directory collision')
    manifest={'schema':'OPICA_COMPLETE_NATIVE_EVIDENCE_V1','directories':sorted(directories),'total_bytes':total,
              'files':sorted(files,key=lambda row:row['path'])}
    # Reopen the named root as well as the descriptor tree: a renamed root is
    # never silently substituted with the tree retained by an old descriptor.
    with _evidence_directory(root,identities=identities):pass
    return manifest,identities


def verify_evidence_tree(root,manifest):
    actual,_=seal_evidence_tree(root)
    require(actual==manifest,'Complete native evidence inventory/content differs')
    return True


def evidence_bytes(root,relative,maximum):
    with _evidence_file(root,relative) as (stream,info):
        require(info.st_size<=maximum,'Evidence record byte budget exceeded')
        raw=stream.read(maximum+1)
        require(len(raw)==info.st_size and len(raw)<=maximum,'Evidence record size changed')
    return raw


def copy_evidence_tree(root,destination,sealed,*,maximum_bytes=None):
    """Copy the previously sealed whole tree, rejecting aliases and mutations."""
    root=unlinked(root);destination=unlinked(destination);manifest,identities=sealed
    require(not destination.exists() and not destination.is_relative_to(root) and not root.is_relative_to(destination),
            'Fresh disjoint evidence destination required')
    require(seal_evidence_tree(root,maximum_bytes=maximum_bytes)==sealed,'Native evidence changed after sealing')
    with _evidence_directory(destination.parent) as (fd,path):
        if fd is not None:os.mkdir(destination.name,dir_fd=fd)
        else:os.mkdir(path/destination.name)
    with _evidence_directory(destination) as (fd,path):
        copied={'':_evidence_identity(os.fstat(fd) if fd is not None else os.lstat(path))[:3]}
    for relative in sorted(manifest['directories'],key=lambda name:(len(Path(name).parts),name)):
        parent=Path(relative).parent.as_posix()
        with _evidence_directory(destination,'' if parent=='.' else parent,copied) as (fd,path):
            if fd is not None:os.mkdir(Path(relative).name,dir_fd=fd)
            else:os.mkdir(path/Path(relative).name)
            info=os.stat(Path(relative).name,dir_fd=fd,follow_symlinks=False) if fd is not None else os.lstat(path/Path(relative).name)
            _evidence_regular(info,directory=True);copied[relative]=_evidence_identity(info)[:3]
    for row in manifest['files']:
        relative=row['path'];parent=Path(relative).parent.as_posix()
        with _evidence_file(root,relative,identities) as (source,before), \
                _evidence_directory(destination,'' if parent=='.' else parent,copied) as (directory,path):
            flags=os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_BINARY',0)
            target=os.open(Path(relative).name,flags,0o600,dir_fd=directory) if directory is not None else os.open(path/Path(relative).name,flags,0o600)
            value=hashlib.sha256();count=0
            with os.fdopen(target,'wb') as stream:
                for data in iter(lambda:source.read(min(1024*1024,row['bytes']-count+1)),b''):
                    count+=len(data);require(count<=row['bytes'],'Native evidence grew during copy')
                    value.update(data);stream.write(data)
                stream.flush();info=os.fstat(stream.fileno());_evidence_regular(info)
            require(count==before.st_size==row['bytes'] and value.hexdigest()==row['sha256'],
                    'Native evidence bytes changed during copy')
            visible=os.stat(Path(relative).name,dir_fd=directory,follow_symlinks=False) if directory is not None else os.lstat(path/Path(relative).name)
            _evidence_regular(visible);_require_evidence_identity(visible,_evidence_identity(info)[:3])
            copied[relative]=_evidence_identity(visible)
    require(seal_evidence_tree(root,maximum_bytes=maximum_bytes)==sealed,'Native evidence changed during copy')
    actual,actual_ids=seal_evidence_tree(destination,maximum_bytes=maximum_bytes)
    require(actual==manifest and set(actual_ids)==set(copied),'Complete copied native evidence differs')
    for relative,identity in copied.items():
        require(actual_ids[relative][:len(identity)]==identity,'Copied evidence identity changed')
    return manifest

def hash_inventory(root,paths):
    """No-follow inventory read. Linux keeps directory descriptors open.

    Windows is development-only and performs reparse checks on every unique
    directory/leaf. It is not advertised as Linux namespace qualification.
    """
    root=unlinked(root); paths=validate_path_inventory(paths); result={}
    if os.name!="nt":
        descriptors={"":os.open(root,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)}
        try:
            def directory(parts):
                key="/".join(parts)
                if key not in descriptors:
                    parent=directory(parts[:-1])
                    descriptors[key]=os.open(parts[-1],os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=parent)
                return descriptors[key]
            for path in paths:
                parts=path.split("/"); parent=directory(parts[:-1])
                fd=os.open(parts[-1],os.O_RDONLY|os.O_NOFOLLOW,dir_fd=parent)
                with os.fdopen(fd,"rb") as stream:
                    before=os.fstat(stream.fileno()); require(stat.S_ISREG(before.st_mode),"regular file required")
                    result[path]=hashlib.file_digest(stream,"sha256").hexdigest()
                    after=os.fstat(stream.fileno())
                    require((before.st_ino,before.st_dev,before.st_size,before.st_mtime_ns)==
                            (after.st_ino,after.st_dev,after.st_size,after.st_mtime_ns),"file mutated while hashing")
        finally:
            for fd in descriptors.values(): os.close(fd)
    else:
        checked=set()
        for path in paths:
            p=root/path
            for parent in reversed(p.parents):
                if parent==root or parent.is_relative_to(root):
                    if parent not in checked:
                        info=os.lstat(parent)
                        require(not stat.S_ISLNK(info.st_mode) and not(getattr(info,"st_file_attributes",0)&1024),"reparse directory refused")
                        checked.add(parent)
            info=os.lstat(p)
            require(stat.S_ISREG(info.st_mode) and not(getattr(info,"st_file_attributes",0)&1024),"regular non-reparse file required")
            with p.open("rb") as stream: result[path]=hashlib.file_digest(stream,"sha256").hexdigest()
    return result

def git(repo,*args):
    env={"PATH":os.environ.get("PATH",""),"SYSTEMROOT":os.environ.get("SYSTEMROOT",""),
         "GIT_CONFIG_NOSYSTEM":"1","GIT_CONFIG_GLOBAL":os.devnull,"GIT_NO_LAZY_FETCH":"1","GIT_TERMINAL_PROMPT":"0"}
    return subprocess.check_output(["git","-C",str(repo),*args],env=env,text=True).strip()

def discover_source_paths(repo):
    repo=Path(repo)
    found=set()
    # Includes ignored/untracked source providers; Git's tracked inventory alone
    # cannot close the compiler/provider boundary.
    for root in (repo/"Zeta23",repo/".lake/packages",repo/"research/RHRC",repo/".github",repo/"scripts",repo/"tools"):
        if not root.exists(): continue
        unlinked(root)
        for directory,dirs,names in os.walk(root,followlinks=False):
            # Package-internal .lake is a generated dependency/cache alias;
            # selected packages are inventoried once at the host package root.
            dirs[:]=[d for d in dirs if d not in {".git","__pycache__","build",".lake"}]
            for d in dirs:
                info=os.lstat(Path(directory)/d)
                require(not stat.S_ISLNK(info.st_mode) and not(getattr(info,"st_file_attributes",0)&1024),"linked source directory refused: "+str(Path(directory)/d))
            for name in names:
                p=Path(directory)/name
                if p.suffix in {".lean",".py",".json",".yaml",".yml",".toml",".sh",".ps1"} or p.name.endswith(".lean.in"):
                    info=os.lstat(p)
                    require(stat.S_ISREG(info.st_mode) and not(getattr(info,"st_file_attributes",0)&1024),"linked source file refused: "+str(p))
                    found.add(p.relative_to(repo).as_posix())
    return found

def freeze_source_epoch(repo, approved):
    approved=as_record(approved,ExperimentSpec); repo=unlinked(repo).resolve()
    require(repo.is_dir(), "source root absent")
    require(approved.source_policy in {"DRAFT","REVIEWED_FROZEN"}, "unknown source policy")
    commit=git(repo,"rev-parse","HEAD"); tree=git(repo,"rev-parse","HEAD^{tree}")
    require(commit==approved.approved_commit,"approved commit differs")
    paths=validate_path_inventory(approved.source_files)
    # The evaluator's list cannot omit mathematical source from the host or packages.
    require(discover_source_paths(repo) <= set(paths),"complete project/package/checker source scope missing")
    require({"lean-toolchain","lake-manifest.json","lakefile.toml"} <= set(paths),"compiler/package pins absent")
    actual=hash_inventory(repo,paths)
    for p,want in approved.source_files.items():
        digest_text(want); require(actual[p]==want,"source bytes differ: "+p)
    source=digest(actual,domain="OPICA_SOURCE_FILES_V1")
    generation=digest({"source":source,"environment":approved.environment,"profile":approved.profile_id},
                      domain="OPICA_SOURCE_GENERATION_V1")
    return SnapshotIdentity(str(repo),commit,tree,source,generation,actual,approved.environment,
                            approved.profile_id,approved.source_policy)

def check_snapshot(snapshot):
    snapshot=as_record(snapshot,SnapshotIdentity)
    require(git(snapshot.repo,"rev-parse","HEAD")==snapshot.commit,"source commit changed")
    require(git(snapshot.repo,"rev-parse","HEAD^{tree}")==snapshot.tree,"source tree changed")
    require(discover_source_paths(snapshot.repo)<=set(snapshot.files),"new ignored/untracked source provider discovered")
    require(hash_inventory(snapshot.repo,snapshot.files)==snapshot.files,"source bytes changed")
    require(digest(snapshot.files,domain="OPICA_SOURCE_FILES_V1")==snapshot.source_digest,"source digest differs")
    require(digest({"source":snapshot.source_digest,"environment":snapshot.environment,"profile":snapshot.profile_id},
                   domain="OPICA_SOURCE_GENERATION_V1")==snapshot.generation,"source generation differs")
    return snapshot
