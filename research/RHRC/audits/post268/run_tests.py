#!/usr/bin/env python3
"""Run all 44 audit checks, preserving failed processes and missing inputs.

Execution success is not scientific confirmation. In particular the post-222
independent checker consumes the SAME frozen schedule as its original workflow;
its producer must run successfully, and stale schedules are never reused.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
INVENTORY = HERE / "EXTENDED_TEST_INVENTORY.json"
POST222 = "check_post222_fb05_biregular_zero_shift_scalar_independent"
R003 = "research/RHRC/routes/R003_ccm_bridge"
SCHEDULE = "POST222_BIREGULAR_ZERO_SHIFT_SCALAR_SCHEDULE.json"


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def anchor() -> dict:
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()
    return {"commit": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
            "working_tree_dirty": bool(git("status", "--porcelain", "--untracked-files=no")),
            "inventory_sha256": digest(INVENTORY)}


def load_inventory() -> list[dict]:
    tests = json.loads(INVENTORY.read_text())["tests"]
    if len(tests) != 44 or len({r["id"] for r in tests}) != len(tests):
        raise ValueError("frozen inventory must contain 44 distinct checks")
    for test in tests:
        path = (REPO / test["path"]).resolve()
        if not path.is_relative_to(REPO) or not path.is_file():
            raise ValueError(f"missing or unsafe checker: {test['path']}")
        if test["timeout_seconds"] <= 0:
            raise ValueError("nonpositive timeout")
    return tests


def command_plan(test: dict, output: Path) -> list[list[str]]:
    checker = [sys.executable, str(REPO / test["path"])]
    if test["id"] == POST222:
        fixture = str(REPO / R003 / "fixtures/post222_fb05_biregular_zero_shift_scalar_v1.json")
        schedule = str(output / SCHEDULE)
        producer = [sys.executable, str(REPO / R003 / "probe_post222_fb05_biregular_zero_shift_scalar_scope.py"),
                    "--input", fixture, "--output", schedule]
        return [producer, checker + ["--input", fixture, "--schedule", schedule]]
    if test["id"] in ("check_ccm_weil_bridge", "check_diagonal_shift"):
        checker += ["--output", str(output / (test["id"] + ".json"))]
    return [checker]


def run_one(test: dict, output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    commands = command_plan(test, output)
    schedule = output / SCHEDULE
    if test["id"] == POST222:
        schedule.unlink(missing_ok=True)
    path = output / (test["id"] + ".log")
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1",
               RHRC_AUDIT_OUTPUT=str(output / "results"), PYTHONUNBUFFERED="1")
    start = time.monotonic()
    status, rc, steps = "FAIL", None, []
    with path.open("w", encoding="utf-8") as handle:
        for index, cmd in enumerate(commands):
            handle.write("$ " + " ".join(cmd) + "\n"); handle.flush()
            remaining = test["timeout_seconds"] - (time.monotonic() - start)
            if remaining <= 0:
                status, rc = "TIMEOUT", None
                handle.write("AUDIT_TIMEOUT: total pipeline budget exhausted.\n")
                break
            try:
                proc = subprocess.Popen(cmd, cwd=REPO, env=env, stdout=handle,
                                        stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    rc = proc.wait(timeout=remaining)
                    status = "PASS" if rc == 0 else "FAIL"
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    proc.wait()
                    status, rc = "TIMEOUT", None
                    handle.write("AUDIT_TIMEOUT: process group killed; no pass inferred.\n")
            except OSError as exc:
                status, rc = "FAIL", None
                handle.write(f"AUDIT_SPAWN_ERROR: {exc}\n")
            steps.append({"command": cmd, "returncode": rc, "execution_disposition": status})
            if status != "PASS":
                break
            if test["id"] == POST222 and index == 0 and not schedule.is_file():
                status, rc = "MISSING_GENERATED_INPUT", None
                handle.write("AUDIT_MISSING_INPUT: producer returned zero without a schedule.\n")
                break
    text = path.read_text(errors="replace")
    if status == "FAIL" and ("ModuleNotFoundError" in text or "No module named" in text):
        status = "ENVIRONMENT_BLOCKED"
    inputs = []
    if test["id"] == POST222 and schedule.is_file():
        inputs.append({"path": SCHEDULE, "sha256": digest(schedule)})
    old = test["baseline_disposition"]
    return {"id": test["id"], "path": test["path"], "command": commands[-1],
            "steps": steps, "generated_inputs": inputs, "returncode": rc,
            "execution_disposition": status, "baseline_disposition": old,
            "comparison": "UNCHANGED_EXECUTION_STATUS" if old == status else "CHANGED_REVIEW_LOG",
            "seconds": round(time.monotonic() - start, 3), "timeout_seconds": test["timeout_seconds"],
            "log": path.name, "log_sha256": digest(path), "tail": text[-5000:],
            "theorem_promotion": False}


def run_shard(shard: int, shards: int, output: Path) -> int:
    if not 0 <= shard < shards or shards < 1:
        raise ValueError("require 0 <= shard < shards")
    tests = load_inventory()
    selected = [r for i, r in enumerate(tests) if i % shards == shard]
    if not selected:
        raise ValueError("empty shard is not a valid success")
    output.mkdir(parents=True, exist_ok=True)
    result = {"schema": "POST268_EXECUTION_v2", "source": anchor(), "shard": shard, "shards": shards,
              "claim_cap": "CHECKER_EXECUTION_NOT_THEOREM_AUTHORITY", "terminal_claim": "RH_OPEN",
              "theorem_promotion": False, "expected_ids": [r["id"] for r in selected], "results": []}
    report = output / f"extended-{shard}.json"
    write_json(report, result)
    for test in selected:
        print("START", test["id"], flush=True)
        row = run_one(test, output)
        result["results"].append(row)
        write_json(report, result)
        print("END", test["id"], row["execution_disposition"], flush=True)
    result["source_after"] = anchor()
    result["all_executed_successfully"] = (
        result["source"] == result["source_after"] and not result["source"]["working_tree_dirty"]
        and all(r["execution_disposition"] == "PASS" for r in result["results"]))
    result["disposition_counts"] = dict(Counter(r["execution_disposition"] for r in result["results"]))
    write_json(report, result)
    return 0 if result["all_executed_successfully"] else 1


def verify_file(parent: Path, name: str, expected_hash: str) -> bool:
    path = (parent / name).resolve()
    return path.is_relative_to(parent.resolve()) and path.is_file() and digest(path) == expected_hash


def harvest(root: Path, output: Path) -> int:
    reports = sorted(root.rglob("extended-*.json"))
    inventory = load_inventory()
    expected = {r["id"]: r for r in inventory}
    current = anchor()
    errors, rows, shard_ids = [], [], []
    for path in reports:
        try:
            p = json.loads(path.read_text())
            if p["schema"] != "POST268_EXECUTION_v2":
                raise ValueError("missing pipeline-aware execution schema")
            if p["source"] != current or p["source_after"] != current or current["working_tree_dirty"]:
                errors.append(f"{path.name}: source identity mismatch or dirty tree")
            shard, shards = p["shard"], p["shards"]
            if not 0 <= shard < shards:
                raise ValueError("invalid shard identity")
            wanted = [r["id"] for i, r in enumerate(inventory) if i % shards == shard]
            if wanted != p["expected_ids"] or wanted != [r["id"] for r in p["results"]]:
                errors.append(f"{path.name}: incomplete or substituted membership")
            if p.get("terminal_claim") != "RH_OPEN" or p.get("theorem_promotion") is not False:
                errors.append(f"{path.name}: authority drift")
            for row in p["results"]:
                test = expected[row["id"]]
                if row.get("path") != test["path"] or row.get("timeout_seconds") != test["timeout_seconds"]:
                    errors.append(f"{row['id']}: checker identity drift")
                if not verify_file(path.parent, row["log"], row["log_sha256"]):
                    errors.append(f"{row['id']}: missing, unsafe or altered log")
                steps = row["steps"]
                if len(steps) != len(command_plan(test, path.parent)) or any(
                    s["returncode"] != 0 or s["execution_disposition"] != "PASS" for s in steps):
                    errors.append(f"{row['id']}: incomplete or failed pipeline")
                if row["id"] == POST222:
                    inputs = row["generated_inputs"]
                    if len(inputs) != 1 or inputs[0]["path"] != SCHEDULE or not verify_file(
                        path.parent, SCHEDULE, inputs[0]["sha256"]):
                        errors.append(f"{row['id']}: missing or altered generated schedule")
                if row.get("execution_disposition") != "PASS" or row.get("returncode") != 0:
                    errors.append(f"{row['id']}: execution did not pass")
                if row.get("theorem_promotion") is not False:
                    errors.append(f"{row['id']}: theorem promotion forbidden")
            rows.extend(p["results"]); shard_ids.append((shard, shards))
        except (KeyError, IndexError, TypeError, ValueError, OSError) as exc:
            errors.append(f"{path.name}: invalid report: {exc}")
    counts = Counter(r["id"] for r in rows)
    missing = sorted(set(expected) - set(counts))
    extra = sorted(set(counts) - set(expected))
    duplicates = sorted(k for k, v in counts.items() if v != 1)
    nsets = {n for _, n in shard_ids}
    complete = len(nsets) == 1 and sorted(i for i, _ in shard_ids) == list(range(next(iter(nsets))))
    passed = bool(reports) and not errors and not missing and not extra and not duplicates and complete
    result = {"schema": "POST268_EXTENDED_HARVEST_v2", "passed": passed, "source": current,
              "report_files": [str(p.relative_to(root)) for p in reports], "errors": errors,
              "missing": missing, "extra": extra, "duplicates": duplicates, "results": rows,
              "claim_cap": "EXECUTION_HARVEST; READ_EACH_SCIENTIFIC_DISPOSITION",
              "terminal_claim": "RH_OPEN", "theorem_promotion": False}
    write_json(output, result)
    print(json.dumps({k: v for k, v in result.items() if k != "results"}, indent=2))
    return 0 if passed else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--shards", type=int, default=1)
    ap.add_argument("--harvest", type=Path)
    args = ap.parse_args()
    return harvest(args.harvest, args.output) if args.harvest else run_shard(args.shard, args.shards, args.output)


if __name__ == "__main__":
    raise SystemExit(main())
