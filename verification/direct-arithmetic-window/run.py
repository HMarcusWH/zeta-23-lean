#!/usr/bin/env python3
"""Run the direct-window gates in separate, reproducible source/checker scopes.

The full archive needs a large machine. This runner never treats a resource
refusal, a narrow build, a skipped checker, or an inherited receipt as success.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


stage_api, evidence = load("stage"), load("evidence")
LOCK = json.loads((HERE / "SOURCE_LOCK.json").read_text())


def require(ok, message):
    stage_api.require(ok, message)


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


class Run:
    def __init__(self, args):
        self.args = args
        self.out = args.out.resolve()
        self.out.mkdir(parents=True, exist_ok=True)
        require(not (self.out / "qualification.json").exists(), "output already qualified; use a new run directory")
        self.commands = []

    def command(self, argv, name, cwd=None, env=None, stdout=None):
        log = self.out / (name + ".log")
        require(not log.exists(), "command log already exists: " + str(log))
        start = time.monotonic()
        argv = [str(x) for x in argv]
        print("RUN", json.dumps(argv), flush=True)
        with log.open("wb") as handle:
            if stdout is None:
                proc = subprocess.Popen(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                for line in iter(proc.stdout.readline, b""):
                    handle.write(line); handle.flush()
                    sys.stdout.buffer.write(line); sys.stdout.buffer.flush()
                rc = proc.wait()
            else:
                require(not stdout.exists(), "fresh export destination already exists")
                with stdout.open("wb") as exported:
                    rc = subprocess.run(argv, cwd=cwd, env=env, stdout=exported, stderr=handle).returncode
        row = {"argv": argv, "cwd": str(cwd) if cwd else None, "exit_code": rc,
               "duration_seconds": time.monotonic() - start, "log": log.name,
               "log_sha256": evidence.digest(log)}
        if stdout is not None:
            row["stdout_path"] = str(stdout)
            row["stdout_sha256"] = evidence.digest(stdout)
            row["stdout_bytes"] = stdout.stat().st_size
        self.commands.append(row)
        write(self.out / "commands.json", self.commands)
        require(rc == 0, "command failed with exit " + str(rc) + ": " + " ".join(argv))
        return row

    def identity(self):
        require(self.args.stage and self.args.source, "--stage and --source required")
        source = stage_api.verify_stage(self.args.stage.resolve(), self.args.source.resolve())
        require(source["development_only"] is False, "acceptance runner requires committed source; development is not qualification")
        shutil.copyfile(self.args.source, self.out / "source.json")
        run_id = os.environ.get("GITHUB_RUN_ID") or os.environ.get("DIRECT_WINDOW_RUN_ID")
        attempt = os.environ.get("GITHUB_RUN_ATTEMPT") or os.environ.get("DIRECT_WINDOW_RUN_ATTEMPT")
        require(run_id and attempt, "set DIRECT_WINDOW_RUN_ID and DIRECT_WINDOW_RUN_ATTEMPT outside Actions")
        write(self.out / "context.json", {"head": source["head"], "tree": source["tree"],
              "run_id": run_id, "run_attempt": attempt})
        return source

    def finish(self, phase):
        self.command([sys.executable, "-B", HERE / "stage.py", "--verify-stage", "--stage", self.args.stage,
                      "--receipt", self.args.source], "source-after")
        write(self.out / "result.json", {"phase": phase, "status": "passed"})
        evidence.write(self.out, phase)


def source_env(prefix):
    return dict(os.environ, PATH=str(prefix / "bin") + os.pathsep + os.environ["PATH"],
                LEAN_ABORT_ON_PANIC="1", LAKE_ARTIFACT_CACHE="false",
                MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4")


def verify_packages(stage):
    manifest = json.loads((stage / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        require(package["type"] == "git", "unlocked package kind")
        path = stage / ".lake/packages" / package["name"]
        head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"]).decode().strip()
        require(head == package["rev"], "package commit drift: " + package["name"])
        require(not subprocess.check_output(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"]).strip(),
                "package source changed: " + package["name"])


def sandbox(stage, prefix, audit=None, writable=False, exporter=None, jobs=2):
    require(shutil.which("bwrap") is not None, "bubblewrap is required")
    stage, prefix = stage.resolve(), prefix.resolve()
    (stage / ".lake/build").mkdir(parents=True, exist_ok=True)
    # Hide home directories, credentials, and the independently judging toolchain.
    # Source, dependencies, and the source compiler are read-only. Build output,
    # an explicit audit directory, and private temporary storage are writable.
    cmd = ["bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--cap-drop", "ALL",
           "--ro-bind", "/", "/", "--tmpfs", "/tmp", "--tmpfs", "/home", "--tmpfs", "/root",
           "--tmpfs", "/opt", "--ro-bind", str(prefix), "/opt/direct-window-lean",
           "--ro-bind", str(stage), str(stage), "--proc", "/proc", "--dev", "/dev",
           "--chdir", str(stage), "--clearenv", "--setenv", "PATH", "/opt/direct-window-lean/bin:/usr/bin:/bin",
           "--setenv", "HOME", "/tmp", "--setenv", "LEAN_ABORT_ON_PANIC", "1",
           "--setenv", "LAKE_ARTIFACT_CACHE", "false", "--setenv", "LEAN_NUM_THREADS", str(jobs)]
    if writable:
        path = str(stage / ".lake/build"); cmd += ["--bind", path, path]
    if audit:
        audit.mkdir(parents=True, exist_ok=True)
        cmd += ["--bind", str(audit.resolve()), str(audit.resolve()),
                "--setenv", "DIRECT_WINDOW_AUDIT_DIR", str(audit.resolve())]
    if exporter:
        cmd += ["--ro-bind", str(exporter.resolve()), "/opt/direct-window-exporter"]
    return cmd + ["--"]


def resource_pilot(source, stage, out, full=False):
    info = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        key, value = line.split(":", 1)
        info[key] = int(value.strip().split()[0]) * 1024
    disk = shutil.disk_usage(stage)
    available = info["MemAvailable"]
    cgroup = None
    for limit_path, used_path in (("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory.current"),
                                 ("/sys/fs/cgroup/memory/memory.limit_in_bytes", "/sys/fs/cgroup/memory/memory.usage_in_bytes")):
        limit, used = Path(limit_path), Path(used_path)
        if limit.is_file() and used.is_file() and limit.read_text().strip().isdigit():
            maximum, current = int(limit.read_text()), int(used.read_text())
            if maximum < 2**60:
                cgroup = {"maximum_bytes": maximum, "current_bytes": current}
                available = min(available, max(0, maximum - current))
                break
    result = {"source_scope": source["scope"], "owner_counts": source["owner_counts"],
              "source_bytes": source["source_bytes"], "cpu_count": os.cpu_count(),
              "memory_available_bytes": available, "host_memory_available_bytes": info["MemAvailable"],
              "cgroup_memory": cgroup, "disk_available_bytes": disk.free,
              "full_run_requested": full,
              "full_guard_memory_bytes": 192 * 1024**3, "full_guard_disk_bytes": 300 * 1024**3,
              "guard_interpretation": "Conservative operational guard; not a proved minimum or guaranteed sufficient capacity."}
    write(out, result)
    if full:
        require(source["scope"] == "terminal", "full resource pilot needs the complete source closure")
        require(available >= result["full_guard_memory_bytes"] and disk.free >= result["full_guard_disk_bytes"],
                "full original supplier exceeds this runner's resource guard; select a sufficiently provisioned large runner")
    return result


def bootstrap_tools(run, work, source_prefix):
    work.mkdir(parents=True, exist_ok=True)
    exporter = work / "lean4export"
    require(not exporter.exists(), "exporter directory already exists; use a fresh tools directory")
    run.command(["git", "clone", "--no-checkout", LOCK["exporter"]["repository"], exporter], "clone-exporter")
    run.command(["git", "-C", exporter, "checkout", "--detach", LOCK["exporter"]["commit"]], "pin-exporter")
    (exporter / "lean-toolchain").write_text(LOCK["source_toolchain"] + "\n")
    run.command([source_prefix / "bin/lake", "build", "lean4export"], "build-exporter", exporter, source_env(source_prefix))
    binary = exporter / ".lake/build/bin/lean4export"
    require(binary.is_file(), "missing built exporter")
    write(run.out / "exporter.json", {"commit": LOCK["exporter"]["commit"],
          "source_toolchain": LOCK["source_toolchain"], "binary": str(binary), "sha256": evidence.digest(binary)})
    print("DIRECT_WINDOW_EXPORTER", binary)


def prepare_challenge(run, work, prefix, exporter):
    work.mkdir(parents=True, exist_ok=False)
    (work / "lean-toolchain").write_text(LOCK["source_toolchain"] + "\n")
    (work / "lakefile.toml").write_text('name = "DirectWindowChallenge"\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\nrev = "' + LOCK["mathlib"] + '"\n[[lean_lib]]\nname = "DirectWindowChallenge"\n')
    manifest = json.loads((HERE / "epoch-lean-4.33.1/lake-manifest.json").read_text())
    manifest["name"] = "DirectWindowChallenge"
    write(work / "lake-manifest.json", manifest)
    shutil.copyfile(HERE / "comparator/DirectWindowChallenge.lean", work / "DirectWindowChallenge.lean")
    run.command([prefix / "bin/lake", "exe", "mathlib/cache", "get"], "challenge-mathlib-cache", work, source_env(prefix))
    run.command(sandbox(work, prefix, writable=True, jobs=run.args.jobs) + ["lake", "build", "DirectWindowChallenge"], "build-challenge")
    target = run.out / "challenge.export"
    run.command(sandbox(work, prefix, exporter=exporter) + ["lake", "env", "/opt/direct-window-exporter", "DirectWindowChallenge", "--", "direct_window_rh", "propext", "Classical.choice", "Quot.sound"], "export-challenge", stdout=target)
    write(run.out / "challenge.json", {"sha256": evidence.digest(target), "bytes": target.stat().st_size,
          "source_toolchain": LOCK["source_toolchain"], "mathlib": LOCK["mathlib"],
          "source_sha256": evidence.digest(work / "DirectWindowChallenge.lean")})


def proof_phase(run, phase, source):
    prefix = run.args.source_prefix.resolve()
    stage = run.args.stage.resolve()
    verify_packages(stage)
    run.command([prefix / "bin/lean", "--version"], "source-compiler")
    require("version 4.33.1" in (run.out / "source-compiler.log").read_text(), "wrong source compiler")
    if phase in {"supplier-frontier", "common-terminal"}:
        resource_pilot(source, stage, run.out / "resource-pilot.json", full=True)
    audit = run.out / "audit"
    targets = {
        "supplier-frontier": ["Zeta23WindowArithmetic.PrincipalWindowSupply", "DirectWindowAudit.Core"],
        "native-frontier": ["Zeta23.RHReference.CofinalEnergyClosure", "Zeta23WindowArithmetic.PrincipalNormalization",
                            "Zeta23.RHReference.Step123MomentHandoffAudit", "DirectWindowAudit.Core"],
        "common-terminal": ["Zeta23.RHReference.DirectWindowAdapter", "DirectWindowSolution", "DirectWindowAudit.Core"],
    }[phase]
    cleanup_log = (run.out / "completed-setup-cleanup.log").open("w")
    cleanup = subprocess.Popen([sys.executable, "-B", HERE / "cleanup_completed.py", stage], stdout=cleanup_log, stderr=subprocess.STDOUT)
    try:
        run.command(sandbox(stage, prefix, audit, writable=True, jobs=run.args.jobs) + ["lake", "build", *targets], "build")
    finally:
        cleanup.terminate(); cleanup.wait(timeout=35); cleanup_log.close()
    module = {"supplier-frontier": "Supplier", "native-frontier": "Native", "common-terminal": "Terminal"}[phase]
    run.command(sandbox(stage, prefix, audit, jobs=run.args.jobs) + ["lake", "env", "lean", "DirectWindowAudit/" + module + ".lean"], "audit")
    if phase == "common-terminal":
        run.command(sandbox(stage, prefix, jobs=run.args.jobs) + ["lake", "env", "lean", "DirectWindowAudit/Expected.lean"], "expected-type")


def judge_exports(run, source):
    prefix, judge = run.args.source_prefix.resolve(), run.args.judge_prefix.resolve()
    require(run.args.exporter and run.args.challenge_export, "exporter and separately prepared challenge are required")
    require(source["scope"] == "terminal", "independent replay requires terminal scope")
    # The checker phase owns a new export and an empty judge working directory.
    exported = run.out / "solution.export"
    run.command(sandbox(run.args.stage, prefix, exporter=run.args.exporter) +
                ["lake", "env", "/opt/direct-window-exporter", "DirectWindowSolution", "--", "direct_window_rh", "propext", "Classical.choice", "Quot.sound"],
                "export-solution", stdout=exported)
    judge_work = run.out / "judge"; judge_work.mkdir()
    env = dict(os.environ, PATH=str(judge / "bin") + os.pathsep + os.environ["PATH"])
    run.command([judge / "bin/lean", "--version"], "judge-version", env=env)
    require("version 4.36.0" in (run.out / "judge-version.log").read_text(), "wrong independent judge")
    config = HERE / "comparator/config.json"
    run.command([judge / "bin/lake", "comparator", "--config", config,
                 "--challenge-from-export", run.args.challenge_export.resolve(), "--solution-from-export", exported],
                "comparator", judge_work, env)
    require("Your solution is okay!" in (run.out / "comparator.log").read_text(errors="replace"), "comparator did not accept")
    tools = {"source-lean": prefix / "bin/lean", "exporter": run.args.exporter,
             "judge-lean": judge / "bin/lean", "judge-lake": judge / "bin/lake",
             "lean-paranoid": judge / "bin/leanchecker-paranoid", "nanoda": judge / "bin/nanoda_bin"}
    check = {"judge_toolchain": LOCK["judge_toolchain"], "exporter_commit": LOCK["exporter"]["commit"],
             "config_sha256": evidence.digest(config), "solution_export_sha256": evidence.digest(exported),
             "solution_export_bytes": exported.stat().st_size,
             "challenge_export_sha256": evidence.digest(run.args.challenge_export),
             "tool_sha256": {name: evidence.digest(path) for name, path in tools.items()}, "exit_code": 0}
    write(run.out / "checker.json", check)
    # The huge export remains on the selected runner, outside the small evidence
    # bundle; moving it never substitutes a historical export for this fresh one.
    archive = run.args.export_directory.resolve()
    archive.mkdir(parents=True, exist_ok=True)
    context = json.loads((run.out / "context.json").read_text())
    destination = archive / (source["head"] + "-" + context["run_id"] + "-" + context["run_attempt"] + ".solution.export")
    require(not destination.exists(), "export archive already contains this candidate")
    exported.replace(destination)
    write(run.out / "export-location.json", {"path": str(destination), "sha256": check["solution_export_sha256"]})


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("phase", choices=[*evidence.PHASES, "resource-pilot", "bootstrap-tools", "prepare-challenge"])
    p.add_argument("--stage", type=Path)
    p.add_argument("--source", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--repo", type=Path, default=HERE.parents[1])
    p.add_argument("--work", type=Path)
    p.add_argument("--source-prefix", type=Path)
    p.add_argument("--judge-prefix", type=Path)
    p.add_argument("--exporter", type=Path)
    p.add_argument("--challenge-export", type=Path)
    p.add_argument("--export-directory", type=Path)
    p.add_argument("--independent-evidence", type=Path)
    p.add_argument("--jobs", type=int, default=2)
    p.add_argument("--full", action="store_true")
    a = p.parse_args()
    require(1 <= a.jobs <= 128, "jobs must be 1..128")
    run = Run(a)
    if a.phase == "bootstrap-tools":
        bootstrap_tools(run, a.work.resolve(), a.source_prefix.resolve()); return
    if a.phase == "prepare-challenge":
        prepare_challenge(run, a.work.resolve(), a.source_prefix.resolve(), a.exporter.resolve()); return
    if a.phase == "resource-pilot":
        source = stage_api.verify_stage(a.stage.resolve(), a.source.resolve())
        resource_pilot(source, a.stage.resolve(), run.out / "resource-pilot.json", a.full); return
    source = run.identity()
    if a.phase == "source-lock":
        run.command([sys.executable, "-B", HERE / "controls.py"], "source-controls")
        run.command([sys.executable, "-O", "-B", HERE / "controls.py"], "source-controls-optimized")
        resource_pilot(source, a.stage.resolve(), run.out / "resource-pilot.json")
    elif a.phase in {"supplier-frontier", "native-frontier", "common-terminal"}:
        proof_phase(run, a.phase, source)
    elif a.phase == "checker-preflight":
        run.command([sys.executable, "-B", HERE / "controls.py", "--audit", "--source-prefix", a.source_prefix,
                     "--work", a.work / "audit", "--out", run.out / "audit-controls"], "audit-controls")
        run.command([sys.executable, "-B", HERE / "controls.py", "--checker", "--source-prefix", a.source_prefix,
                     "--judge-prefix", a.judge_prefix, "--exporter", a.exporter,
                     "--work", a.work / "checker", "--out", run.out / "checker-controls"], "checker-controls")
        shutil.copyfile(run.out / "checker-controls/preflight.json", run.out / "preflight.json")
    elif a.phase == "independent-replay":
        require(a.export_directory is not None, "--export-directory required for large fresh export")
        judge_exports(run, source)
    elif a.phase == "alternate-checker":
        require(a.independent_evidence is not None, "--independent-evidence required")
        donor = evidence.verify(a.independent_evidence.resolve(), "independent-replay")
        context = json.loads((run.out / "context.json").read_text())
        require(all(donor[key] == context[key] for key in ("head", "tree", "run_id", "run_attempt")),
                "alternate-checker donor is from a different candidate/run/attempt")
        # Comparator is one invocation with three required kernels. The second
        # phase authenticates that same invocation/export, not an invented run.
        for name in ("checker.json", "comparator.log"):
            shutil.copyfile(a.independent_evidence / name, run.out / name)
        run.command([sys.executable, "-B", HERE / "evidence.py", "independent-replay",
                     a.independent_evidence, "--verify"], "authenticate-configured-kernels")
    elif a.phase == "check-generated":
        run.command([sys.executable, "-B", "research/RHRC/tools/materialize_derived_state.py", "--check"],
                    "canonical-generated-state", a.repo.resolve())
        run.command([sys.executable, "-B", "-m", "research.RHRC.integration.documentation_combined.direct_window_scope", "--check"],
                    "candidate-source-policy", a.repo.resolve())
    run.finish(a.phase)


if __name__ == "__main__":
    main()
