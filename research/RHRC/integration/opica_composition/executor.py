"""Fixed offline Lean worker. Proposal JSON is data, never executable syntax.

Production requires Linux namespaces through bubblewrap plus process limits.
Native Windows mode is development evidence and cannot authorize publication.
"""
from __future__ import annotations
import hashlib, json, os, platform, re, signal, stat, subprocess, sys, time
from pathlib import Path
from .canonical import require, canonical_bytes, load_bytes, ContractError, digest
from .contracts import (CompositionProposal, TargetSpec, SnapshotIdentity, SearchBudget,
                        WorkerConfig, AttemptArtifacts, ApplicationReceipt, ObjectBinding, as_record)
from .snapshot import unlinked, file_hash, check_snapshot
from .proposals import validate_plan, used_constant_ids
from .inventory import expression_hash

LEAN_NAME=re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
DEFAULT_AXIOMS={"propext","Classical.choice","Quot.sound"}
CALIBRATION_GOLD={"Zeta23.OPICAComposition.cofinal_newborn_packet_calibration",
    "Zeta23.OPICAComposition.cofinal_schur_packet_calibration"}
VALIDATION_PREFIXES=("Zeta23.RHRC.OpicaComposition.Validation.","Zeta23.OPICARound3.Validation.",
                     "Zeta23.OPICARound4.Validation.")
FIXED_OUTPUT_FILES={"proposal.json","target.json","snapshot.json","constant-table.json","receipt.json",
    "application-receipt.json","import-objects-before.json","import-objects-after-summary.json",
    "consumer-imports-before-summary.json","consumer-imports-after-summary.json"} | {
    stem+suffix for stem in ("OpicaAttempt","OpicaConsumer") for suffix in
    (".lean",".lean.log",".olean",".olean.server",".olean.private",".ilean")}

def validate_output_inventory(output):
    """No new module root may shadow frozen checker imports in a consumer."""
    for path in Path(output).iterdir():
        require(path.name in FIXED_OUTPUT_FILES and path.is_file(),"unexpected worker output/module provider")
        unlinked(path)

def lean_name(name):
    require(type(name)is str and LEAN_NAME.fullmatch(name)is not None,"trusted Lean name invalid")
    return name

def lean_string(value):
    # JSON escapes used here are also Lean string escapes; reject controls that
    # would need JSON-only \u escaping. Input Unicode text is emitted literally.
    require(all(ord(c)>=32 or c in "\n\r\t" for c in value),"unsupported source control character")
    return json.dumps(value,ensure_ascii=False)

def _json_string(value): return lean_string(canonical_bytes(value).decode("utf-8"))

def _table(target,roles=None):
    roles=roles or {}
    rows=[]
    for cid,name in sorted(target.allowed_constants.items()):
        lean_name(name)
        # Constants are bound to actual defining modules, not their namespace.
        table=target.__dict__.get("constant_modules",{})
        module=table.get(cid)
        if module is None:
            # The frozen evaluator table supplies module origins via environment
            # below; this fallback is only for core Lean constants.
            module=("Init.Core" if name in {"Exists.intro","Eq.mp","Eq.mpr"} else
                    "Init.Prelude" if name in {"And.intro","And.left","And.right","True.intro","id"} else None)
        rows.append({"id":cid,"declaration":name,"module":module,"role":roles.get(cid,"constant")})
    return rows

def generate_source(proposal,target,constant_table):
    validate_plan(proposal.plan)
    require(set(used_constant_ids(proposal.plan))<=set(target.allowed_constants),"undeclared proposal constant")
    forbidden=set(target.forbidden_constants or [])|{target.declaration}
    forbidden |= CALIBRATION_GOLD
    require(not any(name.startswith(VALIDATION_PREFIXES) for name in target.allowed_constants.values()),
            "validation answer declaration in proposer table")
    require(not(set(target.allowed_constants.values())&forbidden),"answer/goal constant in proposer table")
    require({r["id"]:r["declaration"] for r in constant_table}==target.allowed_constants,"constant table substitution")
    for row in constant_table:
        require(set(row)=={"id","declaration","module","role"},"closed constant table required")
        lean_name(row["declaration"]); lean_name(row["module"])
        require(row["role"] in {"constant","projection","transport"},"unknown constant role")
    imports=list(dict.fromkeys([*target.imports,"Zeta23.RHRC.OpicaComposition.Audit"]))
    require(target.module in imports,"target module not imported")
    for name in imports: lean_name(name)
    require(set(target.allowed_axioms)<=DEFAULT_AXIOMS,"unapproved axiom policy")
    require(target.target_kind in {"value","type"},"target kind differs")
    return "\n".join("import "+n for n in imports)+"\n\nrun_cmd Zeta23.RHRC.OpicaComposition.runAttempt `"+lean_name(target.declaration)+" "+lean_string(target.target_kind)+" "+_json_string(proposal.plan)+" "+_json_string(constant_table)+" "+_json_string(target.allowed_axioms)+" "+_json_string(sorted(forbidden))+"\n"

def generate_consumer(target):
    return "import OpicaAttempt\nimport Zeta23.RHRC.OpicaComposition.Audit\n\nrun_cmd Zeta23.RHRC.OpicaComposition.runAudit `"+lean_name(target.declaration)+" "+lean_string(target.target_kind)+" "+_json_string(target.allowed_axioms)+" "+_json_string(sorted(set(target.forbidden_constants or [])|{target.declaration}))+"\n"

def _fresh_output(output,repo):
    output=unlinked(output).absolute(); repo=Path(repo).resolve()
    require(output.is_absolute() and not output.is_relative_to(repo),"fresh external output required")
    require(not output.exists(),"output directory already exists")
    output.mkdir(parents=True)
    return output

def worker_capability(worker):
    require(type(worker)is WorkerConfig,"trusted WorkerConfig required")
    for p in (worker.lean,worker.toolchain_root,*worker.lean_paths):
        require(Path(p).is_absolute(),"worker paths must be trusted absolute native paths")
        unlinked(p)
    require(Path(worker.lean).is_file() and Path(worker.toolchain_root).is_dir(),"native Lean toolchain absent")
    require(all(Path(p).is_dir() for p in worker.lean_paths),"native import path absent")
    if worker.production:
        require(platform.system()=="Linux","Linux production isolation unavailable")
        for p in (worker.bubblewrap,worker.prlimit):
            require(Path(p).is_absolute() and Path(p).is_file(),"isolation/limit executable unavailable")
        probe=[worker.bubblewrap,"--unshare-all","--die-with-parent","--new-session","--clearenv"]
        for p in ("/usr","/lib","/lib64"):
            if Path(p).exists(): probe += ["--ro-bind",p,p]
        probe += ["/usr/bin/true"]
        done=subprocess.run(probe,env={},capture_output=True,timeout=10)
        require(done.returncode==0,"actual Linux namespace isolation probe failed")
    return "LINUX_ISOLATED" if worker.production else "NATIVE_DEVELOPMENT_ONLY"

def _toolchain_file_record(path, root):
    """Hash a pinned toolchain file, including contained regular-file aliases.

    Directory links, reparse points, escapes and cycles remain forbidden. This
    exception never applies to project, package, import or evidence paths.
    """
    root=unlinked(root).absolute();current=Path(os.path.abspath(path));seen=set();links=[]
    require(current.is_relative_to(root),'Toolchain file is outside approved prefix')
    while True:
        unlinked(current.parent)
        info=os.lstat(current)
        require(not (getattr(info,'st_file_attributes',0)&1024),'Toolchain reparse point refused')
        if not stat.S_ISLNK(info.st_mode):
            require(stat.S_ISREG(info.st_mode),'Regular toolchain target required')
            break
        require(current not in seen and len(links)<40,'Cyclic or excessive toolchain file links')
        seen.add(current);target=os.readlink(current)
        resolved=Path(os.path.abspath(current.parent/target))
        require(resolved.is_relative_to(root),'Toolchain link escapes approved prefix')
        links.append({'path':current.relative_to(root).as_posix(),'target':target})
        current=resolved
    value=file_hash(current)
    # Bind both the exact chain and target bytes, and detect mutation while read.
    for row in links:
        alias=root/row['path']
        require(stat.S_ISLNK(os.lstat(alias).st_mode) and os.readlink(alias)==row['target'],
                'Toolchain link changed while hashing')
    return value,links


def worker_environment(worker,*,manifest_output=None):
    """Fingerprint every selected import object and the actual compiler bytes.

    A caller still needs independently reviewed source-to-object build receipts;
    hashing a stale cache is not fresh compilation of its source.
    """
    worker_capability(worker)
    objects={}; semantic_objects={}; toolchain_links={}
    for index,root in enumerate([worker.toolchain_root,*worker.lean_paths]):
        for path in Path(root).rglob("*"):
            linked=path.is_symlink()
            if linked and index!=0:
                unlinked(path)
            if linked or (path.is_file() and any(path.name.endswith(s) for s in
                    (".olean",".olean.server",".olean.private",".ir",".so",".dll",".exe",".bc"))):
                if index==0:
                    value,links=_toolchain_file_record(path,root)
                    if links:toolchain_links[path.relative_to(root).as_posix()]=links
                else:
                    value=file_hash(path)
                objects[str(path.absolute())]=value
                slot="TOOLCHAIN" if index==0 else "IMPORT_"+str(index-1)
                semantic_objects[slot+"/"+path.relative_to(root).as_posix()]=value
    version=subprocess.run([worker.lean,"--version"],env={"PATH":str(Path(worker.lean).parent),
        **({"SYSTEMROOT":os.environ["SYSTEMROOT"]} if "SYSTEMROOT" in os.environ else {})},
        capture_output=True,timeout=30,check=True).stdout
    raw=json.dumps(objects,ensure_ascii=False,sort_keys=True,separators=(",",":"),allow_nan=False).encode("utf-8")
    require(len(raw)<=128*1024*1024,"native object inventory exceeds host manifest cap")
    if manifest_output is not None:
        path=unlinked(manifest_output)
        require(not path.exists(),"fresh object manifest path required")
        path.write_bytes(raw)
    semantic_raw=json.dumps({'objects':semantic_objects,'toolchain_file_links':toolchain_links},
        ensure_ascii=False,sort_keys=True,separators=(",",":"),allow_nan=False).encode("utf-8")
    return {"compiler_sha256":file_hash(worker.lean),"version_sha256":hashlib.sha256(version).hexdigest(),
            "object_count":len(semantic_objects),"objects_digest":hashlib.sha256(b"OPICA_IMPORT_OBJECTS_V2\0"+semantic_raw).hexdigest(),
            "toolchain_file_links":toolchain_links}

MATH_SUPPORT_RECIPE="OPICA_MATHEMATICAL_LEAN_ISOLATED_V1"

def _recipe(worker,output,source,object_name,budget,*,mathematical_support=False):
    lean=Path(worker.lean); output=Path(output)
    require(type(mathematical_support)is bool,"closed mathematical recipe selector required")
    if mathematical_support:
        require(type(source)is str and (re.fullmatch(r"Zeta23(?:/[A-Za-z0-9_]+)+\.lean",source) or
                source=="RejectedSemanticMutations.lean") and object_name==source[:-5]+".olean",
                "fixed mathematical module source/object pairing required")
    def lean_argv(root):
        args=[str(lean),"-j2","--root="+root,"-DmaxHeartbeats="+str(budget.heartbeats),"-DmaxRecDepth=2048"]
        if mathematical_support:args += ["-DrelaxedAutoImplicit=false"]
        args += ["-o",root+"/"+object_name]
        if mathematical_support:args += ["-i",root+"/"+object_name[:-6]+".ilean"]
        return args+[root+"/"+source]
    if not worker.production:
        env={k:v for k,v in os.environ.items() if k.upper() in {"SYSTEMROOT","WINDIR","TEMP","TMP"}}
        imports=worker.lean_paths if mathematical_support else [str(output),*worker.lean_paths]
        env.update({"PATH":str(lean.parent),"LEAN_PATH":os.pathsep.join(imports),"LEAN_NUM_THREADS":"2"})
        if mathematical_support:return lean_argv(str(output)),env
        return [str(lean),"-j2","--root="+str(output),"-DmaxHeartbeats="+str(budget.heartbeats),
                "-DmaxRecDepth=2048","-o",str(output/object_name),str(output/source)],env
    # Every mounted path is evaluator-owned. No home, cloud credentials, sockets
    # or inherited environment is visible inside the unshared network namespace.
    cmd=[worker.prlimit,"--as="+str(budget.memory_bytes),"--cpu="+str(budget.wall_seconds),
         "--nproc=64","--fsize="+str(budget.output_bytes),"--",worker.bubblewrap,
         "--unshare-all","--die-with-parent","--new-session","--clearenv",
         "--proc","/proc","--dev","/dev","--tmpfs","/tmp"]
    mounts=[]
    for p in ("/usr","/lib","/lib64",worker.toolchain_root,*worker.lean_paths):
        if Path(p).exists() and p not in mounts:
            for parent in reversed(Path(p).parents):
                if str(parent) not in {"/","/usr","/lib","/lib64"}:
                    cmd += ["--dir",str(parent)]
            cmd += ["--ro-bind",p,p]; mounts.append(p)
    cmd += ["--bind",str(output),"/out","--chdir","/out",
            "--setenv","PATH",str(lean.parent),"--setenv","LEAN_NUM_THREADS","2",
            "--setenv","LEAN_PATH",":".join(worker.lean_paths if mathematical_support else ["/out",*worker.lean_paths])]
    if mathematical_support:return cmd+lean_argv("/out"),{}
    cmd += [
            str(lean),"-j2","--root=/out","-DmaxHeartbeats="+str(budget.heartbeats),
            "-DmaxRecDepth=2048","-o","/out/"+object_name,"/out/"+source]
    return cmd,{}

_FAILED_WORKER_LOG_TAIL_BYTES=16*1024
_FAILED_WORKER_LOG_TAIL_LINES=120

def _report_worker_failure(code,disposition,log,raw):
    """Preserve a bounded diagnostic in the parent log without changing evidence."""
    tail=raw[-_FAILED_WORKER_LOG_TAIL_BYTES:]
    lines=tail.decode("utf-8",errors="replace").splitlines()[-_FAILED_WORKER_LOG_TAIL_LINES:]
    messages=["OPICA_WORKER_DIAGNOSTIC_ONLY exit_code="+str(code)+
              " resource_status="+str(disposition)+" log_path="+json.dumps(str(log),ensure_ascii=True)+
              " log_bytes="+str(len(raw))+" tail_bytes="+str(len(tail))]
    for line in lines:
        # Prefix each line and escape terminal controls; untrusted compiler text
        # cannot become a GitHub Actions command or replace the diagnostic label.
        safe="".join(c if c=="\t" or (ord(c)>=32 and ord(c)!=127) else
                     "\\x"+format(ord(c),"02x") for c in line)
        messages.append("OPICA_WORKER_LOG_TAIL | "+safe)
    try:
        sys.stderr.write("\n".join(messages)+"\n")
        sys.stderr.flush()
    except (OSError,ValueError):
        pass  # Diagnostic transport must not change the worker's return status.

def run_worker(worker,output,source,object_name,budget,*,mathematical_support=False):
    capability=worker_capability(worker)
    resource_scope={"mode":"NATIVE_DEVELOPMENT_ONLY"}
    if worker.production:
        rows=Path("/proc/self/cgroup").read_text(encoding="utf-8").splitlines()
        groups=[line.split(":",2)[2] for line in rows if line.startswith("0::")]
        require(len(groups)==1,"actual cgroup-v2 scope required")
        group=Path("/sys/fs/cgroup")/groups[0].lstrip("/")
        def capped(name,maximum):
            value=(group/name).read_text(encoding="ascii").strip()
            require(value.isdecimal() and 0<int(value)<=maximum,"unbounded/oversized cgroup "+name)
            return int(value)
        memory=capped("memory.max",budget.memory_bytes); processes=capped("pids.max",64)
        # A trusted coordinator mounts this bounded writable volume before any
        # candidate dispatch. RLIMIT_FSIZE alone cannot cap many small files.
        output_path=Path(output).resolve(); mounts=[]
        def unescape(text):
            return re.sub(r"\\([0-7]{3})",lambda m:chr(int(m.group(1),8)),text)
        for line in Path("/proc/self/mountinfo").read_text(encoding="utf-8").splitlines():
            left,right=line.split(" - ",1); parts=left.split(); mount=Path(unescape(parts[4]))
            if output_path==mount or output_path.is_relative_to(mount):
                mounts.append((len(mount.parts),right.split()[0]))
        require(mounts and max(mounts)[1]=="tmpfs","bounded tmpfs output volume required")
        space=os.statvfs(output_path)
        require(0<space.f_blocks*space.f_frsize<=budget.disk_bytes,"output volume exceeds approved hard disk cap")
        resource_scope={"mode":"LINUX_CGROUP_V2_TMPFS","memory_bytes":memory,"processes":processes,
                        "disk_bytes":space.f_blocks*space.f_frsize,"cgroup":groups[0]}
    cmd,env=_recipe(worker,output,source,object_name,budget,mathematical_support=mathematical_support)
    log=Path(output)/(source+".log")
    start=time.monotonic(); disposition=None
    kwargs={"start_new_session":True} if os.name!="nt" else {"creationflags":subprocess.CREATE_NEW_PROCESS_GROUP}
    # The log's descriptor is owned before dispatch; no attacker-selected file.
    fd=os.open(log,os.O_WRONLY|os.O_CREAT|os.O_EXCL,getattr(stat,"S_IRUSR",256)|getattr(stat,"S_IWUSR",128))
    with os.fdopen(fd,"wb") as stream:
        proc=subprocess.Popen(cmd,cwd=output,env=env,stdout=stream,stderr=subprocess.STDOUT,**kwargs)
        while proc.poll() is None:
            if time.monotonic()-start>budget.wall_seconds or log.stat().st_size>budget.output_bytes:
                disposition="RESOURCE_EXHAUSTED"
                if os.name!="nt": os.killpg(proc.pid,signal.SIGKILL)
                else: proc.kill()
                break
            time.sleep(0.05)
        code=proc.wait()
    raw=log.read_bytes()
    if len(raw)>budget.output_bytes: disposition="RESOURCE_EXHAUSTED"
    if code!=0 or disposition is not None:
        _report_worker_failure(code,disposition,log,raw)
    return {"exit_code":code,"capability":capability,"recipe":MATH_SUPPORT_RECIPE if mathematical_support else "OPICA_LEAN_ISOLATED_V1",
            "elapsed_milliseconds":int((time.monotonic()-start)*1000),"resource_status":disposition,
            "log_sha256":file_hash(log),"command":cmd,"resource_scope":resource_scope}

def parse_native(log,marker):
    raw=Path(log).read_bytes()
    rows=[line.split(b"\t",1)[1] for line in raw.splitlines() if line.startswith(marker.encode()+b"\t")]
    require(len(rows)==1,"exact one complete native evidence row required")
    row=load_bytes(rows[0])
    require(set(row)=={"schema","declaration","type_expression","term_expression","context","axioms","constants","object_bindings"}
            and row["schema"]=="OPICA_NATIVE_CHECK_V1","native export shape differs")
    expression_hash(row["type_expression"]); expression_hash(row["term_expression"])
    for obj in row["object_bindings"]:
        require(type(obj)is dict and set(obj)=={"object_kind","scope_index","term_expression","type_expression"},"native object binding shape differs")
        require(type(obj["scope_index"])is int and 0<=obj["scope_index"]<=len(row["context"]),"native object scope differs")
        expression_hash(obj["term_expression"]); expression_hash(obj["type_expression"])
    return row

def execute_attempt(proposal,target,snapshot,output,*,worker=None,constant_table=None):
    proposal=as_record(proposal,CompositionProposal); target=as_record(target,TargetSpec)
    snapshot=check_snapshot(snapshot)
    require(proposal.target_id==target.target_id and proposal.source_generation==snapshot.generation,
            "proposal target/generation differs")
    budget=SearchBudget(**(worker.budget or {})) if worker else SearchBudget()
    validate_plan(proposal.plan,budget)
    output=_fresh_output(output,snapshot.repo)
    def result(status,native=None,reason="",export=None):
        context=export["context"] if export else []
        context_digest=digest(context,domain="OPICA_ORDERED_OBJECT_CONTEXT_V1")
        objects=[]
        if export:
            for obj in export["object_bindings"]:
                ctx=context[:obj["scope_index"]]
                objects.append(ObjectBinding(snapshot.source_digest,digest(ctx,domain="OPICA_ORDERED_OBJECT_CONTEXT_V1"),
                    obj["scope_index"],obj["object_kind"],obj["term_expression"],obj["type_expression"],ctx).to_dict())
        raw={p.name:file_hash(p) for p in output.iterdir() if p.is_file() and p.name not in {"receipt.json","application-receipt.json"}}
        used=[ObjectBinding.from_dict(objects[i]).digest for i,binder in enumerate(context)
              if binder["is_prop"] and binder["used_in_proof"]] if export else []
        application=ApplicationReceipt(proposal.proposal_id,snapshot.generation,target.digest,context_digest,status,used,[],raw,
            export["axioms"] if export else [],export["type_expression"] if export else None,
            export["term_expression"] if export else None,bool(export),objects)
        (output/"application-receipt.json").write_bytes(canonical_bytes(application.to_dict()))
        files={p.name:file_hash(p) for p in output.iterdir() if p.is_file() and p.name!="receipt.json"}
        row=AttemptArtifacts(status,target.digest,snapshot.digest,proposal.digest,str(output),files,native or {},reason)
        (output/"receipt.json").write_bytes(canonical_bytes(row.to_dict()))
        return row
    (output/"proposal.json").write_bytes(canonical_bytes(proposal.to_dict()))
    (output/"target.json").write_bytes(canonical_bytes(target.to_dict()))
    (output/"snapshot.json").write_bytes(canonical_bytes(snapshot.to_dict()))
    if worker is None: return result("ENVIRONMENT_ERROR",reason="trusted native worker configuration absent")
    try: worker_capability(worker)
    except (ContractError,OSError) as exc: return result("ENVIRONMENT_ERROR",reason=str(exc))
    if worker.production:
        expected_environment=snapshot.environment.get("worker_environment")
        require(expected_environment is not None,"frozen compiler/object environment binding absent")
        require(worker_environment(worker,manifest_output=output/"import-objects-before.json")==expected_environment,"compiler/import object inventory changed")
    table=constant_table if constant_table is not None else _table(target)
    source=generate_source(proposal,target,table)
    (output/"constant-table.json").write_bytes(canonical_bytes(table))
    (output/"OpicaAttempt.lean").write_text(source,encoding="utf-8",newline="\n")
    try:
        native=run_worker(worker,output,"OpicaAttempt.lean","OpicaAttempt.olean",budget)
    except (ContractError,OSError,subprocess.SubprocessError) as exc:
        return result("ENVIRONMENT_ERROR",reason=str(exc))
    check_snapshot(snapshot)
    if worker.production:
        after_environment=worker_environment(worker)
        (output/"import-objects-after-summary.json").write_bytes(canonical_bytes(after_environment))
        require(after_environment==snapshot.environment["worker_environment"],"compiler/import object bytes changed during attempt")
    if native["resource_status"]: return result("RESOURCE_EXHAUSTED",native,"native budget hit")
    if native["exit_code"]!=0:
        text=(output/"OpicaAttempt.lean.log").read_text(encoding="utf-8",errors="replace")
        if any(s in text for s in ("maximum number of heartbeats","out of memory","RESOURCE_EXHAUSTED")):
            return result("RESOURCE_EXHAUSTED",native,"native compiler budget hit")
        if any(s in text for s in ("UNRESOLVED","failed to synthesize","result contains metavariables")):
            return result("UNRESOLVED",native,"native elaboration obligations remain")
        semantic=any(s in text for s in ("TYPE_REJECTED_THIS_APPLICATION","application arity differs",
                     "lambda outside expected telescope","unknown restricted grammar tag","unauthorized local slot"))
        return result("TYPE_REJECTED_THIS_APPLICATION" if semantic else "ENVIRONMENT_ERROR",native,
                      "ordinary Lean rejected application" if semantic else "native compiler/environment failed; inspect raw output")
    validate_output_inventory(output)
    row=parse_native(output/"OpicaAttempt.lean.log","OPICA_NATIVE")
    require(expression_hash(row["type_expression"])==target.expected_type_hash,"frozen target expression differs")
    require(set(row["axioms"])<=set(target.allowed_axioms),"native axiom policy differs")
    require((output/"OpicaAttempt.olean").is_file(),"actual compiled attempt absent")
    return result("PROVED_CONDITIONAL",native,export=row)
