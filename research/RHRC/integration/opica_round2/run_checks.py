"""Explicit Round2 checks: compiler work, source plans and acceptance stay distinct."""
from __future__ import annotations
import argparse
import contextlib
import hashlib
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import uuid

try:
    from .certificate_io import InvalidCertificate, failure_envelope, load_strict_json, loads_strict_json
    from . import build_receipt as compiler, controls, dependency_delta, harvest_workflows
    from . import validate_contract as contract
except ImportError:
    from certificate_io import InvalidCertificate, failure_envelope, load_strict_json, loads_strict_json
    import build_receipt as compiler
    import controls
    import dependency_delta
    import harvest_workflows
    import validate_contract as contract

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise InvalidCertificate("run_checks", message)


def selected_targets(repo: Path, lane: str) -> list[str]:
    workflow = load_strict_json(repo/"research/RHRC/integration/opica_round2/WORKFLOW_CONTRACT.json")
    require(lane in workflow["formal_lane_targets"], "Unknown formal lane")
    targets = workflow["formal_lane_targets"][lane]
    require(type(targets) is list and targets and len(set(targets)) == len(targets)
            and all(type(t) is str and compiler.NAME.fullmatch(t)
                    and t.startswith("Zeta23.OPICARound2.") for t in targets), "Unsafe or duplicate formal target")
    for target in targets:
        require(contract.file_at(repo, target.replace(".", "/")+".lean").is_file(), "Formal target source is absent: "+target)
    return targets


def execute_formal(repo: Path, output: Path, lane: str, lake: str, timeout: int) -> dict:
    targets = selected_targets(repo, lane)
    sources = compiler.source_manifest(repo)
    identity = {"checked_commit": contract.git(repo,"rev-parse","HEAD"),
                "checked_tree": contract.git(repo,"rev-parse","HEAD^{tree}")}
    environment = compiler.validate_environment(repo)
    output.mkdir(parents=True)
    command = compiler.run_command(repo, [lake,"build",*targets],output,"formal-"+lane,identity["checked_tree"],timeout=timeout)
    require(command["returncode"] == 0, "Native formal lane failed; raw logs were preserved")
    require(compiler.source_manifest(repo) == sources, "Source changed while formal lane compiled")
    return {"schema":"OPICA2_NATIVE_LANE_BUILD_V1","status":"PASS_NATIVE_COMPILER_COMMAND_ONLY",
            **identity, **environment,"lane":lane,"targets":targets,"command":command,
            "source_manifest_sha256":compiler.canonical_sha256(sources),
            "object_cache":"EXISTING_PROJECT_AND_PINNED_PACKAGE_OBJECTS_ALLOWED",
            "complete_type_axiom_dependency_export":False,"independent_human_review":"NOT_ESTABLISHED",
            "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}


# Windows text transport is confined to this new Round2 runtime. Every frozen
# CLI stays byte-identical, including its resolver and empty-inventory guards.
_GENERATED_MATERIALIZE = "research/RHRC/tools/materialize_derived_state.py"
_GENERATED_CANDIDATE = "research/RHRC/integration/candidate_exactify.py"
_GENERATED_WORKER = "research/RHRC/integration/opica_round2/run_checks.py"
_GENERATED_INTERNAL_FLAG = "--_generated-lf-worker"
_GENERATED_LF_SCOPE = "EXACT_FROZEN_CANDIDATE_RUN_LEAN_UTF8_TEXT_TSV_OMITTED_NEWLINE_ONLY"
_GENERATED_ORIGINAL_RUN = subprocess.run


def _generated_windows_transport_required() -> bool:
    return os.name == "nt"


def _generated_frozen_cli_pin(repo: Path, relative: str, *, runner=None) -> dict:
    """Authenticate only the selected unchanged CLI against the frozen Git tree."""
    require(relative in {_GENERATED_MATERIALIZE, _GENERATED_CANDIDATE}, "Unknown frozen generated CLI")
    repo = repo.resolve()
    path = repo / relative
    require(path.is_file() and not path.is_symlink() and path.resolve() == path,
            "Frozen generated CLI is missing or aliased")
    runner = runner or _GENERATED_ORIGINAL_RUN
    argv = ["git", "-C", str(repo), "ls-tree", "-r", "--full-tree", "-z", contract.FROZEN_TREE, "--", relative]
    result = runner(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    require(type(result.returncode) is int and result.returncode == 0, "Frozen generated CLI tree lookup failed")
    rows = [row for row in result.stdout.split(b"\0") if row]
    require(len(rows) == 1, "Frozen generated CLI tree entry is missing or ambiguous")
    fields, name = rows[0].split(b"\t", 1)
    mode, kind, blob = fields.decode("ascii").split()
    require(name.decode("utf-8") == relative and kind == "blob" and mode in {"100644", "100755"},
            "Frozen generated CLI tree identity differs")
    raw = path.read_bytes()
    actual = hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest()
    require(actual == blob, "Protected generated CLI bytes differ from the frozen tree: " + relative)
    return {"path": relative, "frozen_tree": contract.FROZEN_TREE, "mode": mode, "git_blob": blob,
            "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def _generated_worker_argv(repo: Path, report: Path, worker_sha: str, run_id: str,
                           target: str, mode: str, *, python: str | None = None) -> list[str]:
    require(target in {"materialize", "candidate"} and mode in {"write", "check"}, "Unknown generated worker target/mode")
    return [python or sys.executable, "-B", str(repo / _GENERATED_WORKER), _GENERATED_INTERNAL_FLAG,
            "--repo", str(repo), "--expected-worker-sha256", worker_sha,
            "--transport-report", str(report), "--run-id", run_id, "--target", target, "--mode", mode]


def _generated_make_materialize_router(repo: Path, report: Path, worker_sha: str, run_id: str,
                                      *, runner=None, pin=None, emit=None):
    """Delegate all subprocesses exactly except one explicit frozen Python child."""
    runner = runner or _GENERATED_ORIGINAL_RUN
    pin = pin or _generated_frozen_cli_pin
    require(emit is not None, "Generated transport requires visible event recording")
    candidate = (repo / _GENERATED_CANDIDATE).resolve()
    count = [0]

    def routed(command, *positional, **kwargs):
        if not isinstance(command, (list, tuple)) or len(command) < 2 or not isinstance(command[1], str):
            return runner(command, *positional, **kwargs)
        path = Path(command[1])
        target = (path if path.is_absolute() else Path.cwd() / path).resolve()
        if target != candidate:
            return runner(command, *positional, **kwargs)
        require(not positional and len(command) == 3 and command[2] in {"--write", "--check"},
                "Unexpected frozen candidate command")
        require(Path(command[0]).resolve() == Path(sys.executable).resolve(), "Candidate interpreter changed")
        require(kwargs.get("shell") is None or kwargs.get("shell") is False, "Candidate command cannot use a shell")
        require(Path(kwargs.get("cwd", Path.cwd())).resolve() == repo, "Candidate repository cwd changed")
        require(count[0] == 0, "Frozen materializer invoked the candidate more than once")
        source_pin = pin(repo, _GENERATED_CANDIDATE)
        actual = _generated_worker_argv(repo, report, worker_sha, run_id, "candidate", command[2][2:], python=command[0])
        emit("ROUTE_CANDIDATE_SUBPROCESS", target="materialize", mode=command[2][2:],
             original_argv=list(command), actual_argv=actual, source_pin=source_pin)
        count[0] += 1
        return runner(actual, *positional, **kwargs)

    return routed, count


def _generated_make_tsv_factory(repo: Path, *, factory=None, pin=None, emit=None):
    """Select LF at creation; never rewrite a TSV payload or a compiler result."""
    factory = factory or tempfile.NamedTemporaryFile
    pin = pin or _generated_frozen_cli_pin
    require(emit is not None, "Generated transport requires visible event recording")
    candidate = (repo / _GENERATED_CANDIDATE).resolve()
    count = [0]

    def named(*args, **kwargs):
        caller = sys._getframe(1)
        filename = Path(caller.f_code.co_filename).resolve()
        mode = kwargs.get("mode", args[0] if args else "w+b")
        encoding = kwargs.get("encoding")
        utf8 = isinstance(encoding, str) and encoding.lower().replace("_", "-") in {"utf8", "utf-8"}
        selected = (filename == candidate and caller.f_code.co_name == "run_lean" and mode == "w" and utf8
                    and kwargs.get("suffix") == ".tsv" and "newline" not in kwargs)
        if not selected:
            return factory(*args, **kwargs)
        require(count[0] == 0, "Frozen candidate selected more than one query writer")
        source_pin = pin(repo, _GENERATED_CANDIDATE)
        emit("SELECT_EXPLICIT_LF_TSV_WRITER", target="candidate", source_pin=source_pin,
             caller_function="run_lean", suffix=".tsv", encoding=encoding,
             original_newline_argument="OMITTED", actual_newline_argument="LF")
        count[0] += 1
        return factory(*args, **dict(kwargs, newline="\n"))

    return named, count


@contextlib.contextmanager
def _generated_frozen_context(target: Path, mode: str):
    original_argv, original_path = sys.argv, sys.path
    try:
        sys.argv = [str(target), "--" + mode]
        sys.path = [str(target.parent), *original_path[1:]]
        yield
    finally:
        sys.argv, sys.path = original_argv, original_path


def _generated_execute_frozen(repo: Path, target: str, mode: str, report: Path,
                              worker_sha: str, run_id: str, *, emit, run_path=None, pin=None) -> None:
    pin = pin or _generated_frozen_cli_pin
    run_path = run_path or runpy.run_path
    relative = _GENERATED_MATERIALIZE if target == "materialize" else _GENERATED_CANDIDATE
    source_pin = pin(repo, relative)
    emit("WORKER_START", target=target, mode=mode, source_pin=source_pin,
         original_argv=[sys.executable, str(repo / relative), "--" + mode])
    original_run, original_factory = subprocess.run, tempfile.NamedTemporaryFile
    try:
        if target == "materialize":
            subprocess.run, count = _generated_make_materialize_router(repo, report, worker_sha, run_id, pin=pin, emit=emit)
        else:
            tempfile.NamedTemporaryFile, count = _generated_make_tsv_factory(repo, pin=pin, emit=emit)
        with _generated_frozen_context(repo / relative, mode):
            try:
                run_path(str(repo / relative), run_name="__main__")
            except SystemExit as error:
                # Only a genuine original success is equivalent to return.
                require(error.code is None or (type(error.code) is int and error.code == 0),
                        "Original frozen CLI returned a failure status")
        require(count[0] == 1, "Expected one exact candidate route/query-writer selection")
        require(pin(repo, relative) == source_pin, "Frozen CLI source changed while it executed")
        emit("WORKER_FINISH", target=target, mode=mode, source_pin=source_pin, selected_count=count[0],
             status="PASS_TRANSPORT_ONLY_ORIGINAL_EXIT_ZERO")
    finally:
        subprocess.run, tempfile.NamedTemporaryFile = original_run, original_factory


def _generated_transport_worker_main(argv: list[str]) -> int:
    """Internal Windows worker, deliberately absent from the eight public checks."""
    parser = argparse.ArgumentParser(description="Internal exact frozen generated-CLI LF transport")
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--expected-worker-sha256", required=True)
    parser.add_argument("--transport-report", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--target", choices=("materialize", "candidate"), required=True)
    parser.add_argument("--mode", choices=("write", "check"), required=True)
    args = parser.parse_args(argv)
    require(not args.transport_report.is_symlink(), "Generated transport report path cannot be a symlink")
    repo, report = args.repo.resolve(), args.transport_report.resolve()
    require(_generated_windows_transport_required(), "Internal LF transport is Windows-only")
    require(repo == REPO.resolve() and Path.cwd().resolve() == repo, "Generated worker requires its exact source checkout/cwd")
    worker = repo / _GENERATED_WORKER
    require(worker.is_file() and not worker.is_symlink() and Path(__file__).resolve() == worker,
            "Generated worker escaped its current source file")
    require(compiler.NAME.fullmatch("x" + args.run_id) and len(args.run_id) == 32
            and all(c in "0123456789abcdef" for c in args.run_id), "Unsafe generated transport run identity")
    worker_sha = contract.digest(worker)
    require(worker_sha == args.expected_worker_sha256, "Generated worker bytes changed")
    require(not report.is_relative_to(repo) and report.parent.is_dir() and not report.is_symlink(),
            "Generated transport report must be external and unaliased")
    if args.target == "materialize":
        require(not report.exists(), "Refuse to overwrite a prior generated transport observation")
    else:
        require(report.is_file() and report.stat().st_size <= 1024 * 1024, "Candidate transport lacks its parent observation")
        first = loads_strict_json(report.read_bytes().splitlines()[0], 1024 * 1024)
        require(first.get("event") == "WORKER_START" and first.get("target") == "materialize"
                and first.get("run_id") == args.run_id and first.get("worker_sha256") == worker_sha
                and first.get("repo") == str(repo) and first.get("mode") == args.mode, "Candidate transport parent identity differs")

    def emit(event, **fields):
        row = {"schema": "OPICA2_GENERATED_LF_TRANSPORT_EVENT_V1", "event": event,
               "run_id": args.run_id, "worker_sha256": worker_sha, "repo": str(repo),
               "normalization_scope": _GENERATED_LF_SCOPE, **fields}
        encoded = (json.dumps(row, sort_keys=True) + "\n").encode("utf-8")
        # Explicit report and visible logs; no process-wide import/environment injection.
        with report.open("ab") as stream:
            stream.write(encoded)
        print("OPICA2_GENERATED_LF_TRANSPORT " + encoded.decode("utf-8").rstrip("\n"), file=sys.stderr, flush=True)

    _generated_execute_frozen(repo, args.target, args.mode, report, worker_sha, args.run_id, emit=emit)
    require(contract.digest(worker) == worker_sha, "Generated worker source changed while it executed")
    return 0


def _generated_check_command(repo: Path, output: Path) -> tuple[list[str], dict]:
    original = [sys.executable, "-B", _GENERATED_MATERIALIZE, "--check"]
    if not _generated_windows_transport_required():
        return original, {"mode": "DIRECT_FROZEN_CLI_PLATFORM_DEFAULT_UNCHANGED", "original_argv": original}
    require(repo.resolve() == REPO.resolve(), "Windows generated transport requires the current source checkout")
    report, worker_sha, run_id = output / "windows-lf-transport.jsonl", contract.digest(repo / _GENERATED_WORKER), uuid.uuid4().hex
    require(not report.exists(), "Generated transport observation already exists")
    argv = _generated_worker_argv(repo, report, worker_sha, run_id, "materialize", "check")
    return argv, {"mode": "EXPLICIT_WINDOWS_FROZEN_CLI_LF_TRANSPORT", "original_argv": original,
                  "worker_sha256": worker_sha, "run_id": run_id, "report": report.name,
                  "normalization_scope": _GENERATED_LF_SCOPE, "full_release_authority": False}


def _generated_verify_transport(repo: Path, output: Path, transport: dict) -> dict:
    if transport["mode"] == "DIRECT_FROZEN_CLI_PLATFORM_DEFAULT_UNCHANGED":
        return transport
    require(transport["mode"] == "EXPLICIT_WINDOWS_FROZEN_CLI_LF_TRANSPORT", "Unknown generated transport mode")
    report = output / "windows-lf-transport.jsonl"
    require(report.is_file() and not report.is_symlink() and report.stat().st_size <= 1024 * 1024,
            "Missing or oversized explicit Windows transport observation")
    raw = report.read_bytes()
    require(raw.endswith(b"\n") and b"\r" not in raw, "Generated transport observations must use exact LF framing")
    rows = [loads_strict_json(line, 1024 * 1024) for line in raw.splitlines()]
    require(all(type(row) is dict for row in rows), "Generated transport events must be objects")
    expected = [("WORKER_START", "materialize"), ("ROUTE_CANDIDATE_SUBPROCESS", "materialize"),
                ("WORKER_START", "candidate"), ("SELECT_EXPLICIT_LF_TSV_WRITER", "candidate"),
                ("WORKER_FINISH", "candidate"), ("WORKER_FINISH", "materialize")]
    require([(row.get("event"), row.get("target")) for row in rows] == expected,
            "Generated transport lacks exactly one unchanged materializer/candidate execution")
    base_fields = {"schema", "event", "run_id", "worker_sha256", "repo", "normalization_scope"}
    event_fields = {
        "WORKER_START": {"target", "mode", "source_pin", "original_argv"},
        "ROUTE_CANDIDATE_SUBPROCESS": {"target", "mode", "source_pin", "original_argv", "actual_argv"},
        "SELECT_EXPLICIT_LF_TSV_WRITER": {"target", "source_pin", "caller_function", "suffix", "encoding",
                                          "original_newline_argument", "actual_newline_argument"},
        "WORKER_FINISH": {"target", "mode", "source_pin", "selected_count", "status"},
    }
    for row in rows:
        require(set(row) == base_fields | event_fields[row["event"]], "Unexpected generated transport event fields")
        require(row.get("schema") == "OPICA2_GENERATED_LF_TRANSPORT_EVENT_V1"
                and row.get("run_id") == transport["run_id"] and row.get("worker_sha256") == transport["worker_sha256"]
                and row.get("repo") == str(repo) and row.get("normalization_scope") == _GENERATED_LF_SCOPE,
                "Generated transport event identity/scope differs")
    materialize = _generated_frozen_cli_pin(repo, _GENERATED_MATERIALIZE)
    candidate = _generated_frozen_cli_pin(repo, _GENERATED_CANDIDATE)
    require(contract.digest(repo / _GENERATED_WORKER) == transport["worker_sha256"], "Generated worker source drift")
    for row, pin in zip(rows, [materialize, candidate, candidate, candidate, candidate, materialize]):
        require(row.get("source_pin") == pin, "Generated transport source pin differs")
    original_candidate = [sys.executable, str(repo / _GENERATED_CANDIDATE), "--check"]
    require(rows[0].get("original_argv") == [sys.executable, str(repo / _GENERATED_MATERIALIZE), "--check"]
            and rows[0].get("mode") == "check" and rows[1].get("mode") == "check"
            and rows[1].get("original_argv") == original_candidate
            and rows[1].get("actual_argv") == _generated_worker_argv(repo, report, transport["worker_sha256"], transport["run_id"], "candidate", "check")
            and rows[2].get("original_argv") == original_candidate and rows[2].get("mode") == "check",
            "Generated transport command or check-only mode differs")
    require(rows[3].get("caller_function") == "run_lean" and rows[3].get("suffix") == ".tsv"
            and rows[3].get("encoding") == "utf-8" and rows[3].get("original_newline_argument") == "OMITTED"
            and rows[3].get("actual_newline_argument") == "LF", "Generated transport selected a different writer")
    require(all(row.get("mode") == "check" and type(row.get("selected_count")) is int and row["selected_count"] == 1
                and row.get("status") == "PASS_TRANSPORT_ONLY_ORIGINAL_EXIT_ZERO" for row in rows[-2:]),
            "Generated transport original completion is missing")
    return {**transport, "report_sha256": hashlib.sha256(raw).hexdigest(), "event_count": len(rows),
            "frozen_source_pins": [materialize, candidate], "status": "PASS_EXPLICIT_LF_TRANSPORT_ONLY",
            "provider_authenticity_established_here": False, "independent_human_review": "NOT_ESTABLISHED"}




def execute_generated(repo: Path, output: Path, timeout: int) -> dict:
    manifest=load_strict_json(HERE/"BUILD_MANIFEST.json",8*1024*1024)
    paths=[r["path"] for r in manifest["generated"]]
    require(paths and len(set(paths))==len(paths),"Exact generated product inventory required")
    def snapshot():
        rows=[]
        for relative in paths:
            path=contract.file_at(repo,relative)
            require(path.is_file(),"Generated product missing before check: "+relative)
            rows.append({"path":relative,"bytes":path.stat().st_size,"sha256":contract.digest(path)})
        return rows
    before=snapshot()
    output.mkdir(parents=True)
    tree=contract.git(repo,"rev-parse","HEAD^{tree}")
    argv,transport=_generated_check_command(repo,output)
    command=compiler.run_command(repo,argv,output,"canonical-generated-check",tree,timeout=timeout)
    after=snapshot()
    require(command["returncode"]==0,"Canonical generated check failed; inputs were inspected before any regeneration")
    require(before==after,"Check-only generated validation changed a product")
    transport=_generated_verify_transport(repo,output,transport)
    return {"schema":"OPICA2_GENERATED_CHECK_V1","status":"PASS_CANONICAL_CHECK_WITHOUT_REWRITE",
            "before":before,"after":after,"command":command,"transport":transport,"full_core_accepted":False,
            "full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}




def execute_ancestry(repo: Path, output: Path, projection: Path, lake: str, timeout: int) -> dict:
    """Actually run frozen original CLIs and separate current76/100 exporters."""
    try:
        from . import capture_ancestor
    except ImportError:
        import capture_ancestor
    before=compiler.source_manifest(repo)
    head,tree=contract.git(repo,"rev-parse","HEAD"),contract.git(repo,"rev-parse","HEAD^{tree}")
    output.mkdir(parents=True)
    capture=capture_ancestor.capture(repo,projection,output/"baseline",populations=("76","100"),lake=lake,timeout=timeout)
    require(capture.get("status")=="LEGACY_RECEIPTS_PRODUCED_NOT_YET_INDEPENDENTLY_REPLAY_VERIFIED",
            "Frozen baseline compiler replay failed or was incomplete")
    paths={"baseline76":output/"baseline/original-76/compiler-receipt.json",
           "baseline100":output/"baseline/original-100/compiler-receipt.json"}
    for population in (76,100):
        target=output/("current"+str(population))
        dependency_delta.produce_current_export(repo,target,population=population,lake=lake,timeout=timeout)
        paths["current"+str(population)]=target/"current-compiler-receipt.json"
    exports=[];inputs=[]
    for role,population,commit,source_tree in (("baseline76",76,contract.FROZEN_COMMIT,contract.FROZEN_TREE),
        ("current76",76,head,tree),("baseline100",100,contract.FROZEN_COMMIT,contract.FROZEN_TREE),("current100",100,head,tree)):
        path=paths[role]
        verify=dependency_delta.verify_legacy if role.startswith("baseline") else dependency_delta.verify_current_export
        exports.append(verify(repo,path,path.parent,population=population,expected_commit=commit,expected_tree=source_tree))
        inputs.append({"role":role,"receipt":path.relative_to(output).as_posix(),"receipt_sha256":contract.digest(path)})
    comparison=dependency_delta.ancestry_report(*exports,current_commit=head,current_tree=tree)
    require(compiler.source_manifest(repo)==before and contract.git(repo,"rev-parse","HEAD")==head,
            "Current source changed during baseline/current ancestry compiler replay")
    return {"schema":"OPICA2_AUTHENTICATED_ANCESTRY_RUN_V1","status":"PASS_EXECUTED_BASELINE_AND_CURRENT_COMPILER_COMPARISON",
            "checked_commit":head,"checked_tree":tree,"inputs":inputs,"comparison":comparison,
            "source_manifest_sha256":compiler.canonical_sha256(before),"fresh_processes_executed_here":True,
            "provider_authenticity_established_here":False,"ancestor_baseline_replay":True,"ancestor_current_compatibility":True,
            "scope":"FROZEN_76_100_BASELINES_AND_CURRENT_SOURCE_BOUND_COMPILER_COMPATIBILITY",
            "full_core_accepted":False,"full_release_accepted":False,"human_review":"NOT_ESTABLISHED","RH":"OPEN","Step4":"OPEN"}


def compose_inputs(repo: Path, args, raw_path: Path, artifacts: Path) -> dict:
    required=(args.clause_evidence,args.control_evidence,args.optimized_control_evidence,args.ancestry_evidence)
    require(all(path is not None for path in required),
            "Composition requires exact clause metadata, both normal/optimized runtime controls and both baseline/current ancestry evidence")
    return compiler.compose_core_evidence(repo,raw_path,artifacts,load_strict_json(args.query_plan,32*1024*1024),
        clause_evidence=args.clause_evidence,control_evidence=args.control_evidence,
        optimized_control_evidence=args.optimized_control_evidence,ancestry_evidence=args.ancestry_evidence)


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check",choices=("contract","formal","controls","ancestry","aggregate","generated","harvest","acceptance"))
    parser.add_argument("--repo",type=Path,default=REPO)
    parser.add_argument("--lane",choices=("causal","filtered","gram","structural"))
    parser.add_argument("--scope",choices=("minimal","full-core"),default="full-core")
    parser.add_argument("--evidence-dir","--output-dir",dest="evidence_dir",type=Path)
    parser.add_argument("--query-plan",type=Path)
    parser.add_argument("--formal-receipt",type=Path)
    parser.add_argument("--formal-artifacts",type=Path)
    parser.add_argument("--ancestor-projection",type=Path)
    parser.add_argument("--clause-evidence",type=Path)
    parser.add_argument("--control-evidence",type=Path)
    parser.add_argument("--optimized-control-evidence",type=Path)
    parser.add_argument("--ancestry-evidence",type=Path)
    parser.add_argument("--classifications",type=Path)
    parser.add_argument("--snapshot",type=Path)
    parser.add_argument("--previous",type=Path)
    parser.add_argument("--snapshot-mode",choices=("in-workflow","post-run"),default="in-workflow")
    parser.add_argument("--lake",default="lake")
    parser.add_argument("--timeout",type=int,default=3600)
    parser.add_argument("--build-mode",choices=("warm","cold"),default="warm")
    for name in ("baseline76","current76","baseline100","current100"):
        parser.add_argument("--"+name,type=Path)
    args=parser.parse_args()
    repo=args.repo.resolve()
    root=args.evidence_dir or (Path(os.environ["OPICA2_OUTPUT_DIR"]) if os.environ.get("OPICA2_OUTPUT_DIR") else
        repo.parent/"opica2-check-evidence"/(datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")+"-"+uuid.uuid4().hex[:8]))
    output=root.resolve()/args.check
    output_existed=output.exists()
    try:
        require(not output.is_relative_to(repo),"Evidence must be external to the source checkout")
        require(not output.exists(),"Refuse to overwrite an earlier check observation")
        require(type(args.timeout) is int and args.timeout>0,"Positive execution timeout required")
        if args.check=="contract":
            output.mkdir(parents=True)
            result=contract.preflight(repo,repo/"research/RHRC/integration/opica_round2",scope=args.scope)
        elif args.check=="formal":
            require(args.lane is not None,"Formal execution needs an explicit lane")
            result=execute_formal(repo,output,args.lane,args.lake,args.timeout)
        elif args.check=="controls":
            output.mkdir(parents=True)
            result=controls.run_controls(registry_path=HERE/"CONTROL_REGISTRY.json",mapping_path=HERE/"PAPER_CROSSWALK.json",
                evidence_dir=output/"runtime",repo=repo,lake=args.lake,timeout=args.timeout)
        elif args.check=="aggregate":
            require(args.query_plan is not None,"Aggregate export needs independently reviewed exact root/query inventory")
            composition_inputs=(args.clause_evidence,args.control_evidence,args.optimized_control_evidence,args.ancestry_evidence)
            require(not any(path is not None for path in composition_inputs) or all(path is not None for path in composition_inputs),
                    "Partial evidence cannot silently produce full-core coverage")
            plan=load_strict_json(args.query_plan,32*1024*1024)
            receipt=compiler.produce_receipt(repo,output,compiler.compiler_plan_data(plan),lake=args.lake,
                build_mode=args.build_mode,timeout=args.timeout)
            if all(path is not None for path in composition_inputs):
                result=compose_inputs(repo,args,output/"compiler-receipt.json",output)
                (output/"composed-receipt.json").write_bytes((json.dumps(result["composed_receipt"],indent=2)+"\n").encode("utf-8"))
                (output/"core-composition.json").write_bytes((json.dumps(result,indent=2)+"\n").encode("utf-8"))
            else:
                result={"status":"PASS_SCOPED_COMPILER_EXPORT","receipt":receipt,
                        "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}
        elif args.check=="generated":
            result=execute_generated(repo,output,args.timeout)
        elif args.check=="ancestry":
            if args.ancestor_projection is not None:
                require(all(getattr(args,name) is None for name in ("baseline76","current76","baseline100","current100")),
                        "Fresh ancestry orchestration cannot mix separately supplied receipts")
                result=execute_ancestry(repo,output,args.ancestor_projection,args.lake,args.timeout)
            else:
                head,tree=contract.git(repo,"rev-parse","HEAD"),contract.git(repo,"rev-parse","HEAD^{tree}")
                inputs=[]
                for name,population,commit,source_tree in (("baseline76",76,contract.FROZEN_COMMIT,contract.FROZEN_TREE),
                    ("current76",76,head,tree),("baseline100",100,contract.FROZEN_COMMIT,contract.FROZEN_TREE),("current100",100,head,tree)):
                    path=getattr(args,name)
                    require(path is not None,"Both exact frozen and current76/100 compiler artifacts are mandatory: "+name)
                    verify=dependency_delta.verify_current_export if name.startswith("current") else dependency_delta.verify_legacy
                    inputs.append(verify(repo,path,path.parent,population=population,expected_commit=commit,expected_tree=source_tree))
                result=dependency_delta.ancestry_report(*inputs,current_commit=head,current_tree=tree)
                output.mkdir(parents=True)
        elif args.check=="harvest":
            require(args.classifications is not None,"Every workflow/job needs reviewed classification and scientific scope")
            head,tree=contract.git(repo,"rev-parse","HEAD"),contract.git(repo,"rev-parse","HEAD^{tree}")
            snapshot=load_strict_json(args.snapshot,64*1024*1024) if args.snapshot else harvest_workflows.collect(
                harvest_workflows.public_json,"HMarcusWH","zeta-23-lean",head)
            rules=load_strict_json(args.classifications)
            result=harvest_workflows.harvest(snapshot,head=head,tree=tree,classifications=rules,
                previous=load_strict_json(args.previous,64*1024*1024) if args.previous else None,
                snapshot_mode=args.snapshot_mode,required_jobs=rules.get("required_jobs"),
                current_run_id=int(os.environ["GITHUB_RUN_ID"]) if os.environ.get("GITHUB_RUN_ID") else None)
            output.mkdir(parents=True)
            (output/"provider-snapshot.json").write_text(json.dumps(snapshot,indent=2)+"\n",encoding="utf-8")
        else:
            require(args.formal_receipt is not None and args.query_plan is not None,
                    "Acceptance requires exact formal artifacts and independently reviewed query plan")
            artifacts=args.formal_artifacts or args.formal_receipt.parent
            composition=compose_inputs(repo,args,args.formal_receipt,artifacts)
            output.mkdir(parents=True)
            composed_path=output/"composed-receipt.json"
            composed_path.write_bytes((json.dumps(composition["composed_receipt"],indent=2)+"\n").encode("utf-8"))
            def reparse(receipt,source):
                return source.resolve()==repo and receipt==composition["composed_receipt"]
            result=contract.acceptance(repo,repo/"research/RHRC/integration/opica_round2",
                                       formal_receipt=composed_path,receipt_verifier=reparse)
            result["composition_sha256"]=compiler.canonical_sha256(composition)
            result["provider_authenticity_established_here"]=False
            result["fresh_compiler_replay"]=False
            (output/"core-composition.json").write_bytes((json.dumps(composition,indent=2)+"\n").encode("utf-8"))
    except (OSError,ValueError,TypeError,KeyError,subprocess.SubprocessError) as exc:
        result=failure_envelope("run_checks_"+args.check,exc)
        if output_existed:
            print(json.dumps(result,indent=2))
            return 1
        if not output.exists():
            output.mkdir(parents=True)
    (output/"result.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"check":args.check,"result":str(output/"result.json"),
        "status":result.get("status",result.get("outcome")),"RH":"OPEN","Step4":"OPEN"}))
    return 0 if result.get("status","").startswith("PASS_") or result.get("schema")=="OPICA2_WORKFLOW_HARVEST_V1" else 1


if __name__=="__main__":
    if sys.argv[1:2]==[_GENERATED_INTERNAL_FLAG]:
        raise SystemExit(_generated_transport_worker_main(sys.argv[2:]))
    raise SystemExit(main())
