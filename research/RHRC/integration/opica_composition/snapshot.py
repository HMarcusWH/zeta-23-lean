"""Source epochs bind complete reviewed bytes and reject links and drift."""
from __future__ import annotations
import hashlib, os, stat, subprocess
from pathlib import Path
from .canonical import require, digest, digest_text, validate_path_inventory
from .contracts import ExperimentSpec, SnapshotIdentity, as_record

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
                require(not stat.S_ISLNK(info.st_mode) and not(getattr(info,"st_file_attributes",0)&1024),"linked source directory refused")
            for name in names:
                p=Path(directory)/name
                if p.suffix in {".lean",".py",".json",".yaml",".yml",".toml",".sh",".ps1"} or p.name.endswith(".lean.in"):
                    info=os.lstat(p)
                    require(stat.S_ISREG(info.st_mode) and not(getattr(info,"st_file_attributes",0)&1024),"linked source file refused")
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
