"""Source epochs bind complete reviewed bytes and reject links and drift."""
from __future__ import annotations
import hashlib, os, re, stat, struct, subprocess, zipfile
from contextlib import contextmanager
from pathlib import Path
from .canonical import (require, digest, digest_text, validate_path_inventory, relative_path,
                        closed_keys, canonical_bytes, load_bytes, MAX_BYTES)
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


def seal_evidence_tree(root,*,maximum_bytes=None,maximum_entries=None,maximum_depth=None):
    """Complete no-follow evidence inventory; physical identities stay private."""
    maximum_bytes=SearchBudget().disk_bytes if maximum_bytes is None else maximum_bytes
    require(type(maximum_bytes)is int and 0<maximum_bytes<=SearchBudget().disk_bytes,'Finite native evidence byte limit required')
    for bound in (maximum_entries,maximum_depth):
        require(bound is None or type(bound)is int and bound>0,'Finite evidence structural cap required')
    root=unlinked(root);identities={};directories=[];files=[];stack=[''];total=0;entry_count=0
    while stack:
        relative=stack.pop()
        with _evidence_directory(root,relative,identities if identities else None) as (fd,path):
            before=os.fstat(fd) if fd is not None else os.lstat(path)
            identities[relative]=_evidence_identity(before)
            with os.scandir(fd if fd is not None else path) as entries:
                names=[]
                for entry in entries:
                    entry_count+=1
                    require(maximum_entries is None or entry_count<=maximum_entries,'Evidence entry count budget exceeded')
                    names.append(entry.name)
                names.sort()
            for name in names:
                key=(relative+'/' if relative else '')+name;relative_path(key)
                require(maximum_depth is None or len(key.split('/'))<=maximum_depth,'Evidence path depth budget exceeded')
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


def verify_evidence_tree(root,manifest,*,maximum_entries=None,maximum_depth=None):
    actual,_=seal_evidence_tree(root,maximum_entries=maximum_entries,maximum_depth=maximum_depth)
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


# A transport is a closed additional envelope, never a replacement for lane or
# scientific verification. Explicit directory members survive artifact services
# which transport regular files only. ZIP metadata cannot grant permissions.
TRANSPORT_MAX_ENTRIES=20000
TRANSPORT_MAX_DEPTH=64
TRANSPORT_MAX_FILE_BYTES=128*1024*1024
TRANSPORT_MAX_BYTES=SearchBudget().disk_bytes
TRANSPORT_MAX_CONTAINER_BYTES=TRANSPORT_MAX_BYTES+64*1024*1024
TRANSPORT_NAMES=frozenset({'bundle.zip','transport.json'})


def _transport_identity(identity):
    closed_keys(identity,{'lane_id','experiment'})
    from .accept import ROUND4_LANES
    require(identity['lane_id'] in ROUND4_LANES,'Unknown transport lane')
    exp=closed_keys(identity['experiment'],{'run_id','attempt','requested_commit','requested_tree','profile_digest'})
    require(type(exp['run_id'])is str and re.fullmatch(r'[0-9]{1,32}',exp['run_id']) is not None and
            type(exp['attempt'])is int and 0<exp['attempt']<=1000000,'Exact workflow run/attempt required')
    for key in ('requested_commit','requested_tree'):
        require(type(exp[key])is str and re.fullmatch(r'[0-9a-f]{40}',exp[key]) is not None,
                'Exact requested transport source required')
    digest_text(exp['profile_digest'])
    return identity


def _transport_seal(root):
    return seal_evidence_tree(root,maximum_entries=TRANSPORT_MAX_ENTRIES,maximum_depth=TRANSPORT_MAX_DEPTH)


def _transport_manifest(manifest):
    closed_keys(manifest,{'schema','directories','total_bytes','files'})
    require(manifest['schema']=='OPICA_COMPLETE_NATIVE_EVIDENCE_V1','Transport content schema differs')
    directories=manifest['directories'];files=manifest['files']
    require(type(directories)is list and type(files)is list and files and
            len(directories)+len(files)<=TRANSPORT_MAX_ENTRIES,'Transport entry count budget exceeded')
    require(type(manifest['total_bytes'])is int and 0<=manifest['total_bytes']<=TRANSPORT_MAX_BYTES,
            'Transport logical byte budget exceeded')
    paths=[];total=0
    for row in files:
        closed_keys(row,{'path','bytes','sha256'});digest_text(row['sha256'])
        require(type(row['bytes'])is int and 0<=row['bytes']<=TRANSPORT_MAX_FILE_BYTES,
                'Transport member byte budget exceeded')
        paths.append(relative_path(row['path']));total+=row['bytes']
    require(files==sorted(files,key=lambda row:row['path']) and
            directories==sorted(directories),'Canonical transport inventory required')
    validate_path_inventory(paths)
    names=directories+paths
    require(len(names)==len(set(names))==len({name.casefold() for name in names}),
            'Duplicate/case-aliased transport entry')
    for name in names:
        relative_path(name)
        parts=name.split('/')
        require(len(parts)<=TRANSPORT_MAX_DEPTH,'Transport path depth budget exceeded')
        require(all('/'.join(parts[:end]) in directories for end in range(1,len(parts))),
                'Missing transport parent directory')
    require(total==manifest['total_bytes'],'Transport total logical bytes differ')
    return manifest


def _transport_new_directory(path):
    path=unlinked(path)
    require(not path.exists(),'Fresh owned transport destination required')
    with _evidence_directory(path.parent) as (fd,parent):
        if fd is None:os.mkdir(parent/path.name,0o700)
        else:os.mkdir(path.name,0o700,dir_fd=fd)
        info=os.lstat(parent/path.name) if fd is None else os.stat(path.name,dir_fd=fd,follow_symlinks=False)
        _evidence_regular(info,directory=True)
        identity=_evidence_identity(info)[:3]
    return {'':identity}


@contextmanager
def _transport_new_file(root,relative,identities):
    relative_path(relative);parent=Path(relative).parent.as_posix()
    with _evidence_directory(root,'' if parent=='.' else parent,identities) as (fd,path):
        flags=os.O_RDWR|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_BINARY',0)
        target=os.open(path/Path(relative).name,flags,0o600) if fd is None else os.open(Path(relative).name,flags,0o600,dir_fd=fd)
        with os.fdopen(target,'w+b') as stream:
            info=os.fstat(stream.fileno());_evidence_regular(info)
            yield stream
            stream.flush();after=os.fstat(stream.fileno());_evidence_regular(after)
            visible=os.lstat(path/Path(relative).name) if fd is None else os.stat(Path(relative).name,dir_fd=fd,follow_symlinks=False)
            _evidence_regular(visible)
            require(_evidence_identity(info)[:3]==_evidence_identity(after)[:3]==_evidence_identity(visible)[:3],
                    'Transport output identity changed')
            identities[relative]=_evidence_identity(after)


def _transport_hash(stream,maximum):
    stream.seek(0);value=hashlib.sha256();count=0
    while True:
        data=stream.read(min(1024*1024,maximum-count+1))
        if not data:break
        count+=len(data);require(count<=maximum,'Transport container byte budget exceeded');value.update(data)
    return {'bytes':count,'sha256':value.hexdigest()}


def pack_evidence_bundle(root,staging,identity,*,sealed=None):
    """Publish two transport files only after complete physical/content reseals."""
    _transport_identity(identity);root=unlinked(root);staging=unlinked(staging)
    require(not staging.is_relative_to(root) and not root.is_relative_to(staging),'Disjoint transport staging required')
    current=_transport_seal(root)
    require(sealed is None or current==sealed,'Evidence changed after transport preflight')
    sealed=current;manifest,source_ids=sealed;_transport_manifest(manifest)
    owned=_transport_new_directory(staging)
    with _transport_new_file(staging,'bundle.zip',owned) as container:
        with zipfile.ZipFile(container,'w',compression=zipfile.ZIP_STORED,allowZip64=True) as archive:
            def member(name,directory=False,size=0):
                info=zipfile.ZipInfo(name+('/' if directory else ''),(1980,1,1,0,0,0))
                info.create_system=3;info.external_attr=((stat.S_IFDIR|0o700) if directory else (stat.S_IFREG|0o600))<<16
                if directory:info.external_attr|=0x10
                info.file_size=size;return info
            for name in manifest['directories']:archive.writestr(member(name,True),b'')
            for row in manifest['files']:
                with _evidence_file(root,row['path'],source_ids) as (source,before), \
                        archive.open(member(row['path'],size=row['bytes']),'w') as target:
                    value=hashlib.sha256();count=0
                    while True:
                        data=source.read(min(1024*1024,row['bytes']-count+1))
                        if not data:break
                        count+=len(data);require(count<=row['bytes'],'Evidence grew during transport pack')
                        value.update(data);target.write(data)
                    require(count==before.st_size==row['bytes'] and value.hexdigest()==row['sha256'],
                            'Evidence changed during transport pack')
        require(_transport_seal(root)==sealed,'Evidence changed during transport pack')
        container.flush();container_record=_transport_hash(container,TRANSPORT_MAX_CONTAINER_BYTES)
        with _transport_zip_inventory(container,manifest,container_record['bytes']):pass
    envelope={'schema':'OPICA_EVIDENCE_TRANSPORT_V1',**identity,'container':container_record,'manifest':manifest}
    require(_transport_seal(root)==sealed,'Evidence changed before transport publication')
    raw=canonical_bytes(envelope)+b'\n'
    with _transport_new_file(staging,'transport.json',owned) as receipt:receipt.write(raw)
    # Reopen output names as well: retained descriptors cannot mask replacement.
    with _evidence_file(staging,'bundle.zip',owned):pass
    with _evidence_file(staging,'transport.json',owned):pass
    return envelope


def _transport_zip_inventory(stream,manifest,size):
    """Bound the central directory BEFORE zipfile allocates its member objects."""
    require(22<=size<=TRANSPORT_MAX_CONTAINER_BYTES,'Transport container size differs')
    stream.seek(size-22);end=stream.read(22)
    signature,disk,central_disk,disk_count,count,central_bytes,offset,comment=struct.unpack('<4s4H2LH',end)
    require(signature==b'PK\x05\x06' and disk==central_disk==comment==0 and disk_count==count and
            0<count<=TRANSPORT_MAX_ENTRIES and 0<central_bytes<=TRANSPORT_MAX_ENTRIES*1100,
            'Unsupported/bounded transport ZIP directory required')
    central_end=size-22
    if size>=98:
        stream.seek(size-42);locator=stream.read(20)
        if locator[:4]==b'PK\x06\x07':
            _,zip_disk,zip_offset,disks=struct.unpack('<4sLQL',locator)
            require(zip_disk==0 and disks==1 and zip_offset==size-98,'Unsupported ZIP64 locator')
            stream.seek(zip_offset);record=struct.unpack('<4sQ2H2L4Q',stream.read(56))
            require(record[:2]==(b'PK\x06\x06',44) and record[2:4]==(45,45) and record[4:6]==(0,0) and
                    record[6]==record[7]==count and record[8]==central_bytes and min(record[9],0xffffffff)==offset,
                    'Unsupported ZIP64 directory')
            central_end=zip_offset;offset=record[9]
    require(offset+central_bytes==central_end,'Transport ZIP trailing/prefix directory differs')
    expected={name+'/':None for name in manifest['directories']}
    expected.update({row['path']:row for row in manifest['files']})
    require(count==len(expected),'Transport ZIP member count differs')
    # EOCD's count is untrusted: zipfile parses until the central byte range
    # ends. Count actual fixed headers before permitting that allocation.
    stream.seek(offset);cursor=offset;seen=set()
    for _ in range(count):
        header=stream.read(46);require(len(header)==46 and header[:4]==b'PK\x01\x02','Transport ZIP central header differs')
        name_bytes,extra_bytes,comment_bytes=struct.unpack_from('<3H',header,28)
        require(0<name_bytes<=1025 and extra_bytes in (0,12) and comment_bytes==0 and header[34:36]==b'\0\0',
                'Transport ZIP central metadata budget exceeded')
        cursor+=46+name_bytes+extra_bytes
        require(cursor<=offset+central_bytes,'Transport ZIP central bytes exceeded')
        raw_name=stream.read(name_bytes)
        require(len(raw_name)==name_bytes and all(byte<128 for byte in raw_name),'Transport ZIP ASCII name required')
        name=raw_name.decode('ascii')
        require(name in expected and name not in seen,'Duplicate/unlisted transport ZIP central member')
        seen.add(name);require(len(stream.read(extra_bytes))==extra_bytes,'Truncated transport ZIP central metadata')
    require(cursor==offset+central_bytes and seen==set(expected),'Transport ZIP actual central count differs')
    stream.seek(0)
    archive=zipfile.ZipFile(stream,'r')
    try:
        require(archive.comment==b'' and len(archive.infolist())==count,'Transport ZIP metadata differs')
        names=[];next_offset=0
        for info in archive.infolist():
            names.append(info.filename);row=expected.get(info.filename)
            require(info.filename in expected,'Unlisted transport ZIP member')
            directory=info.filename.endswith('/');relative_path(info.filename[:-1] if directory else info.filename)
            size_expected=0 if directory else row['bytes']
            mode=((stat.S_IFDIR|0o700) if directory else (stat.S_IFREG|0o600))<<16
            extra=struct.pack('<HHQ',1,8,info.header_offset) if info.header_offset>zipfile.ZIP64_LIMIT else b''
            version=45 if extra else 20
            require(info.compress_type==zipfile.ZIP_STORED and info.flag_bits==0 and
                    info.create_system==3 and info.create_version==info.extract_version==version and info.reserved==0 and
                    info.external_attr==mode|(0x10 if directory else 0) and info.internal_attr==0 and
                    info.date_time==(1980,1,1,0,0,0) and info.comment==b'' and
                    info.file_size==info.compress_size==size_expected and info.header_offset==next_offset and
                    (not directory or info.CRC==0),
                    'Unsupported transport ZIP member metadata')
            require(info.extra==extra,
                    'Unsupported transport ZIP extra metadata')
            stream.seek(info.header_offset);header=stream.read(30)
            fields=struct.unpack('<4s5H3L2H',header)
            require(fields[0]==b'PK\x03\x04' and fields[1]==20 and fields[2:6]==(0,0,0,33) and
                    fields[6:9]==(info.CRC,size_expected,size_expected) and fields[9]==len(info.filename) and fields[10]==0,
                    'Transport ZIP local metadata differs')
            require(stream.read(fields[9])==info.filename.encode('ascii'),'Transport ZIP local name differs')
            next_offset=info.header_offset+30+fields[9]+size_expected
        require(len(names)==len(set(names)) and set(names)==set(expected) and next_offset==offset,
                'Duplicate/missing/overlapping transport ZIP members')
        return archive
    except BaseException:
        archive.close();raise


def unpack_evidence_bundle(staging,destination,identity):
    """Reconstruct an owned exact tree; callers must then run lane/science checks."""
    _transport_identity(identity);staging=unlinked(staging);destination=unlinked(destination)
    require(not destination.is_relative_to(staging) and not staging.is_relative_to(destination),
            'Disjoint transport extraction required')
    with _evidence_directory(staging) as (fd,path):
        with os.scandir(fd if fd is not None else path) as entries:names=[entry.name for entry in entries]
        require(set(names)==TRANSPORT_NAMES and len(names)==2,'Closed transport file set differs')
        staging_ids={'':_evidence_identity(os.fstat(fd) if fd is not None else os.lstat(path))}
        for name in names:
            info=os.lstat(path/name) if fd is None else os.stat(name,dir_fd=fd,follow_symlinks=False)
            _evidence_regular(info);staging_ids[name]=_evidence_identity(info)
    with _evidence_file(staging,'transport.json',staging_ids) as (receipt,info):
        require(info.st_size<=MAX_BYTES,'Transport envelope byte budget exceeded')
        envelope=load_bytes(receipt.read(MAX_BYTES+1))
    closed_keys(envelope,{'schema','lane_id','experiment','container','manifest'})
    require(envelope['schema']=='OPICA_EVIDENCE_TRANSPORT_V1' and
            {key:envelope[key] for key in identity}==identity,'Cross-lane/run/attempt/source transport refused')
    _transport_manifest(envelope['manifest'])
    container_record=closed_keys(envelope['container'],{'bytes','sha256'});digest_text(container_record['sha256'])
    require(type(container_record['bytes'])is int and 22<=container_record['bytes']<=TRANSPORT_MAX_CONTAINER_BYTES,
            'Transport container byte budget exceeded')
    with _evidence_file(staging,'bundle.zip',staging_ids) as (container,info):
        require(info.st_size==container_record['bytes'] and
                _transport_hash(container,TRANSPORT_MAX_CONTAINER_BYTES)==container_record,'Transport container content differs')
        with _transport_zip_inventory(container,envelope['manifest'],info.st_size) as archive:
            owned=_transport_new_directory(destination)
            for relative in sorted(envelope['manifest']['directories'],key=lambda name:(len(name.split('/')),name)):
                parent=Path(relative).parent.as_posix()
                with _evidence_directory(destination,'' if parent=='.' else parent,owned) as (fd,path):
                    name=Path(relative).name
                    if fd is None:os.mkdir(path/name,0o700)
                    else:os.mkdir(name,0o700,dir_fd=fd)
                    info=os.lstat(path/name) if fd is None else os.stat(name,dir_fd=fd,follow_symlinks=False)
                    _evidence_regular(info,directory=True);owned[relative]=_evidence_identity(info)[:3]
            for row in envelope['manifest']['files']:
                with archive.open(row['path'],'r') as source, _transport_new_file(destination,row['path'],owned) as target:
                    count=0;value=hashlib.sha256()
                    while True:
                        data=source.read(min(1024*1024,row['bytes']-count+1))
                        if not data:break
                        count+=len(data);require(count<=row['bytes'],'Extracted transport member grew')
                        value.update(data);target.write(data)
                    require(count==row['bytes'] and value.hexdigest()==row['sha256'],'Extracted transport content differs')
        require(_transport_hash(container,TRANSPORT_MAX_CONTAINER_BYTES)==container_record,'Transport changed while extracting')
    verify_evidence_tree(destination,envelope['manifest'],maximum_entries=TRANSPORT_MAX_ENTRIES,maximum_depth=TRANSPORT_MAX_DEPTH)
    actual,actual_ids=_transport_seal(destination)
    require(set(actual_ids)==set(owned),'Extracted transport physical inventory differs')
    for relative,expected in owned.items():_require_evidence_identity_value(actual_ids[relative],expected)
    return envelope


def _require_evidence_identity_value(actual,expected):
    require(actual[:len(expected)]==expected,'Extracted transport identity changed')

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
