#!/usr/bin/env python3
"""Validate complete, same-candidate evidence; absence never means acceptance."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PHASES = ("source-lock", "checker-preflight", "supplier-frontier", "native-frontier",
          "common-terminal", "independent-replay", "alternate-checker", "check-generated")
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def inventory(path):
    return {p.relative_to(path).as_posix(): digest(p) for p in sorted(path.rglob("*"))
            if p.is_file() and p.name != "qualification.json"}


def validate_commands(path, phase):
    commands = read(path / "commands.json")
    require(commands and isinstance(commands, list), "missing actual command evidence")
    required = {
        "source-lock": {"source-controls", "source-controls-optimized"},
        "checker-preflight": {"audit-controls", "checker-controls"},
        "supplier-frontier": {"source-compiler", "build", "audit"},
        "native-frontier": {"source-compiler", "build", "audit"},
        "common-terminal": {"source-compiler", "build", "audit", "expected-type"},
        "independent-replay": {"export-solution", "judge-version", "comparator"},
        "alternate-checker": {"authenticate-configured-kernels"},
        "check-generated": {"canonical-generated-state", "candidate-source-policy"},
    }[phase] | {"source-after"}
    require(len(commands) == len(required) and {c["log"] for c in commands} == {n + ".log" for n in required},
            "missing, duplicate, or unexpected phase command")
    for command in commands:
        require(command["exit_code"] == 0 and command["argv"] and command["duration_seconds"] >= 0,
                "failed or unrecorded command")
        log = path / command["log"]
        require(log.is_file() and digest(log) == command["log_sha256"], "command log mismatch")
    return commands


def validate_audits(path, phase):
    specs = [r for r in read(HERE / "ROOTS.json")["roots"] if r["phase"] == phase]
    if not specs:
        return {}
    audit = path / "audit"
    require({p.stem for p in audit.glob("*.json")} == {s["name"] for s in specs},
            "wrong/missing audited root inventory")
    results = {}
    for spec in specs:
        row = read(audit / (spec["name"] + ".json"))
        require(row["schema"] == "DIRECT_WINDOW_AUDIT_V1" and row["root"] == spec["name"]
                and row["role"] == spec["role"] and row["complete_structural_edges"] is True,
                "audit root/policy mismatch")
        require(set(row["axioms"]) <= AXIOMS and len(set(row["axioms"])) == len(row["axioms"]),
                "forbidden or duplicate axiom")
        require(set(row["required"]) == set(spec["required"]) and row["type"] and row["type_expr"],
                "audit requirements/type missing")
        if spec["exact_type"]:
            require(row["type"] == spec["exact_type"], "wrong exact terminal statement")
        edges = audit / (spec["name"] + ".edges.jsonl")
        names = set()
        with edges.open() as f:
            for line in f:
                edge = json.loads(line)
                require(edge["name"] not in names and bool(edge["module"]), "duplicate/missing origin")
                names.add(edge["name"])
        require(len(names) == row["count"] and spec["name"] in names
                and set(spec["required"]) <= names, "incomplete dependency closure")
        with edges.open() as f:
            for line in f:
                edge = json.loads(line)
                for key in ("type_refs", "value_refs", "structural_refs"):
                    require(set(edge[key]) <= names, "dependency edge leaves inspected closure")
        results[spec["name"]] = digest(edges)
    return results


def validate(path, phase):
    require(phase in PHASES, "unknown phase")
    source = read(path / "source.json")
    lock = read(HERE / "SOURCE_LOCK.json")
    require(source["schema"] == "DIRECT_WINDOW_STAGE_V1" and source["development_only"] is False
            and source["fresh_project_objects"] is True,
            "development/unbound stage cannot be accepted")
    require(source["original_commit"] == lock["original"]["commit"] and
            source["source_toolchain"] == lock["source_toolchain"] and source["mathlib"] == lock["mathlib"],
            "source epoch mismatch")
    require(source["source_lock_sha256"] == digest(HERE / "SOURCE_LOCK.json") and
            source["ownership_sha256"] == digest(HERE / "OWNERSHIP.json") and
            source["compatibility_sha256"] == digest(HERE / "COMPATIBILITY.json"), "source policy mismatch")
    if phase in {"supplier-frontier", "common-terminal", "independent-replay", "alternate-checker"}:
        require(source["scope"] == "terminal", "narrow stage cannot qualify the full terminal")
    if phase == "native-frontier":
        require(source["scope"] in {"native", "terminal"}, "wrong native scope")
    commands = validate_commands(path, phase)
    context = read(path / "context.json")
    require(context["head"] == source["head"] and context["tree"] == source["tree"]
            and context["run_id"] and context["run_attempt"], "run/candidate context missing")
    require(read(path / "result.json") == {"phase": phase, "status": "passed"}, "phase not passed")
    if phase in {"independent-replay", "alternate-checker"}:
        check = read(path / "checker.json")
        require(check["judge_toolchain"] == lock["judge_toolchain"] and
                check["exporter_commit"] == lock["exporter"]["commit"] and
                check["config_sha256"] == digest(HERE / "comparator/config.json"), "checker identity drift")
        require(check["solution_export_sha256"] and check["challenge_export_sha256"] and
                check["exit_code"] == 0, "no completed independent check")
        text = (path / "comparator.log").read_text(errors="replace")
        require("Your solution is okay!" in text, "missing comparator acceptance")
        for kernel in ("Lean default", "Lean paranoid", "nanoda"):
            require(kernel + " kernel accepts the solution" in text, "missing kernel acceptance: " + kernel)
    if phase == "checker-preflight":
        controls = read(path / "preflight.json")
        config = read(HERE / "comparator/config.json")
        require(controls["accepted_clean"] is True and
                set(controls["rejected"]) == {"wrong-statement", "extra-axiom", "tampered-export"},
                "checker rejection controls incomplete")
        require("version 4.33.1" in controls["source_version"] and "version 4.36.0" in controls["judge_version"]
                and controls["exporter_commit"] == lock["exporter"]["commit"]
                and set(controls["permitted_axioms"]) == AXIOMS
                and controls["external_kernels"] == config["external_kernels"], "preflight checker configuration drift")
    return source, context, validate_audits(path, phase), commands


def write(path, phase):
    source, context, edges, _ = validate(path, phase)
    receipt = {"schema": "DIRECT_WINDOW_QUALIFICATION_V1", "phase": phase,
               "head": source["head"], "tree": source["tree"],
               "run_id": context["run_id"], "run_attempt": context["run_attempt"],
               "source_sha256": digest(path / "source.json"),
               "roots_sha256": digest(HERE / "ROOTS.json"), "edge_digests": edges,
               "files": inventory(path)}
    (path / "qualification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("DIRECT_WINDOW_PHASE_PASS", phase, source["head"])
    return receipt


def verify(path, phase):
    receipt = read(path / "qualification.json")
    source, context, edges, _ = validate(path, phase)
    require(receipt["schema"] == "DIRECT_WINDOW_QUALIFICATION_V1" and receipt["phase"] == phase and
            (receipt["head"], receipt["tree"], receipt["run_id"], receipt["run_attempt"]) ==
            (source["head"], source["tree"], context["run_id"], context["run_attempt"]), "receipt identity mismatch")
    require(receipt["source_sha256"] == digest(path / "source.json") and
            receipt["roots_sha256"] == digest(HERE / "ROOTS.json") and
            receipt["edge_digests"] == edges and receipt["files"] == inventory(path), "receipt bytes changed")
    return receipt


def aggregate(root, output):
    receipts = [verify(root / phase, phase) for phase in PHASES]
    identities = {(r["head"], r["tree"], r["run_id"], r["run_attempt"]) for r in receipts}
    require(len(identities) == 1, "mixed candidate/run/attempt evidence")
    independent = read(root / "independent-replay/checker.json")
    alternate = read(root / "alternate-checker/checker.json")
    require(independent == alternate, "independent kernels checked different exports or configuration")
    preflight = read(root / "checker-preflight/preflight.json")
    require(preflight["exporter_sha256"] and
            preflight["exporter_sha256"] == independent["tool_sha256"]["exporter"],
            "preflight and independent replay used different exporter binaries")
    head, tree, run, attempt = identities.pop()
    value = {"schema": "DIRECT_WINDOW_ACCEPTANCE_V1", "status": "accepted",
             "terminal": read(HERE / "SOURCE_LOCK.json")["terminal"], "exact_type": "RiemannHypothesis",
             "head": head, "tree": tree, "run_id": run, "run_attempt": attempt,
             "checker": independent, "receipts": {r["phase"]: digest(root / r["phase"] / "qualification.json")
                                                       for r in receipts}}
    output.write_text(json.dumps(value, indent=2) + "\n")
    print("DIRECT_WINDOW_TERMINAL_ACCEPTED", head)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("phase", choices=[*PHASES, "aggregate"])
    p.add_argument("path", type=Path)
    p.add_argument("--verify", action="store_true")
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    if a.phase == "aggregate":
        require(a.output is not None, "aggregate --output required")
        aggregate(a.path, a.output)
    elif a.verify:
        verify(a.path, a.phase)
    else:
        write(a.path, a.phase)
