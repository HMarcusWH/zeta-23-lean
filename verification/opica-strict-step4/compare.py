#!/usr/bin/env python3
"""Bind separate strict qualification jobs to one head, tree, and attempt."""

import hashlib
import json
import os
from pathlib import Path
import sys

ROLES = ("source", "perron", "native", "arithmetic", "common",
         "independent", "checker", "alternate")
ROOT = "Zeta23.RHReference.riemannHypothesis_compact_literal_ramp_candidate"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ROOT_FILES = {
    "audit/Zeta23.OPICATerminal.bothParityPowerComparison_proved.json",
    "audit/Zeta23.RHReference.native_literal_ramp_fixed_gap_transfer.json",
    "audit/Zeta23.RHReference.riemannHypothesis_of_c1_through_generated_pair.json",
    f"audit/{ROOT}.json",
    f"audit/{ROOT}.edges.jsonl",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            result.update(block)
    return result.hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def job_identity(source, run, attempt, head):
    require(source["schema"] == "STRICT_STEP4_STAGE_V1" and
            source["claim"] == "RH_OPEN" and source["head"] == head,
            "strict job source identity drift")
    return {"head": head, "tree": source["tree"], "run": run, "attempt": attempt}


def job_files(directory):
    return {file.relative_to(directory).as_posix(): digest(file)
            for file in sorted(directory.rglob("*"))
            if file.is_file() and file.name != "job.json"}


def receipt(role, directory):
    require(role in ROLES and not (directory / "job.json").exists(), "wrong or reused role")
    source = read(directory / "source.json")
    identity = job_identity(source, os.environ["GITHUB_RUN_ID"],
                            os.environ["GITHUB_RUN_ATTEMPT"], os.environ["GITHUB_SHA"])
    data = {"schema": "STRICT_STEP4_JOB_V1", "role": role, **identity, "result": "PASS",
            "files": job_files(directory)}
    (directory / "job.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def matching_job(job, role, identity):
    require(job["schema"] == "STRICT_STEP4_JOB_V1" and job["role"] == role and
            job["result"] == "PASS" and
            all(job[k] == v for k, v in identity.items()), "wrong job or attempt for " + role)


def proof_receipt(path):
    root = read(path)
    require(root["root"] == ROOT and root["exact_rh"] is True and root["has_edges"] is True
            and set(root["axioms"]) <= AXIOMS and root["count"] > 0, "wrong strict proof receipt")
    return root


def compare(directory, output):
    run = os.environ["GITHUB_RUN_ID"]
    attempt = os.environ["GITHUB_RUN_ATTEMPT"]
    head = os.environ["GITHUB_SHA"]
    dirs = {role: directory / f"strict-step4-{role}-{run}-{attempt}" for role in ROLES}
    source_file = dirs["source"] / "source.json"
    source = read(source_file)
    identity = job_identity(source, run, attempt, head)
    source_hash = digest(source_file)
    source_r7 = digest(dirs["source"] / "r7-source.json")
    jobs = {}
    for role, path in dirs.items():
        job = read(path / "job.json")
        matching_job(job, role, identity)
        require(job["files"] == job_files(path), "artifact bytes changed for " + role)
        require(job["files"]["source.json"] == source_hash, "strict source drift in " + role)
        require(job["files"]["r7-source.json"] == source_r7, "inherited source drift in " + role)
        jobs[role] = job
    for role in ("common", "independent"):
        require(ROOT_FILES <= jobs[role]["files"].keys(), "incomplete audit artifact for " + role)
        proof_receipt(dirs[role] / f"audit/{ROOT}.json")
    for p in ROOT_FILES:
        require(jobs["common"]["files"][p] == jobs["independent"]["files"][p],
                "independent proof receipt differs: " + p)
    require("STRICT_FRESH_KERNEL_PASS" in (dirs["independent"] / "fresh-kernel.log").read_text(),
            "missing fresh kernel replay")
    require("NATIVE_CHECKER_PREFLIGHT_PASS" in
            (dirs["checker"] / "checker-preflight-pass.txt").read_text(), "missing checker preflight")
    require((dirs["checker"] / "checker-environment.json").read_bytes() ==
            (dirs["alternate"] / "checker-environment.json").read_bytes(),
            "checker environment mismatch")
    alternate = (dirs["alternate"] / "alternate.log").read_text()
    require("Running nanoda kernel on solution" in alternate and "Your solution is okay!" in alternate,
            "missing alternate kernel acceptance")
    result = {"schema": "STRICT_STEP4_REVIEW_PACKET_V1", **identity, "claim": "RH_OPEN",
              "disposition": "READY_FOR_MANUAL_STRICT_CANDIDATE_REVIEW",
              "source_sha256": source_hash,
              "per_gate_receipts": {role: digest(path / "job.json") for role, path in dirs.items()},
              "strict_target": ROOT, "proof_sha256": jobs["common"]["files"][f"audit/{ROOT}.json"],
              "scope": "Compiler and checker receipts. Semantic review and canonical admission remain manual."}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["disposition"])


def self_test():
    ident = {"head": "commit", "tree": "tree", "run": "123", "attempt": "4"}
    job = {"schema": "STRICT_STEP4_JOB_V1", "role": "common", "result": "PASS", **ident}
    matching_job(job, "common", ident)
    for key, value in (("attempt", "3"), ("run", "122"), ("role", "native"),
                       ("result", "SKIPPED"), ("head", "other"), ("tree", "other")):
        try:
            matching_job({**job, key: value}, "common", ident)
        except ValueError:
            continue
        raise RuntimeError(f"strict receipt negative control accepted: {key}")
    print("STRICT_RECEIPT_CONTROLS_PASS", 6)


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        self_test()
    elif len(sys.argv) == 4 and sys.argv[1] == "receipt":
        receipt(sys.argv[2], Path(sys.argv[3]))
    elif len(sys.argv) == 4 and sys.argv[1] == "compare":
        compare(Path(sys.argv[2]), Path(sys.argv[3]))
    else:
        raise SystemExit("usage: compare.py [--self-test | receipt ROLE DIR | compare DIR OUTPUT]")
