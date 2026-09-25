#!/usr/bin/env python3
"""Run and harvest the frozen 44-command audit inventory, failing closed.

A zero process exit means successful execution of that checker, not a proof
of its scientific conjecture. Logs and scientific dispositions remain part of
its result. Missing dependencies, timeouts, crashes and missing shards fail CI.
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


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def anchor() -> dict:
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()
    return {"commit":git("rev-parse","HEAD"),"tree":git("rev-parse","HEAD^{tree}"),
            "working_tree_dirty":bool(git("status","--porcelain","--untracked-files=no")),
            "inventory_sha256":hashlib.sha256(INVENTORY.read_bytes()).hexdigest()}


def load_inventory() -> list[dict]:
    tests = json.loads(INVENTORY.read_text())["tests"]
    if len(tests) != 44 or len({r["id"] for r in tests}) != len(tests):
        raise ValueError("frozen extended inventory is not 44 distinct checks")
    for test in tests:
        path = (REPO/test["path"]).resolve()
        if not path.is_relative_to(REPO) or not path.is_file():
            raise ValueError(f"missing or unsafe checker path: {test}")
        if test["timeout_seconds"] <= 0:
            raise ValueError("nonpositive timeout")
    return tests


def run_one(test: dict, output: Path) -> dict:
    cmd = [sys.executable, str(REPO/test["path"])]
    if test["id"] in ("check_ccm_weil_bridge", "check_diagonal_shift"):
        cmd += ["--output",str(output/(test["id"]+".json"))]
    path = output/(test["id"]+".log")
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1",
               RHRC_AUDIT_OUTPUT=str(output/"results"), PYTHONUNBUFFERED="1")
    start = time.monotonic()
    status, rc = "FAIL", None
    with path.open("w") as handle:
        handle.write("$ " + " ".join(cmd) + "\n"); handle.flush()
        proc = subprocess.Popen(cmd,cwd=REPO,env=env,stdout=handle,stderr=subprocess.STDOUT,
                                start_new_session=True)
        try:
            rc = proc.wait(timeout=test["timeout_seconds"])
            status = "PASS" if rc == 0 else "FAIL"
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            status = "TIMEOUT"
            handle.write("\nAUDIT_TIMEOUT: process group killed; no success inferred.\n")
    text = path.read_text(errors="replace")
    if rc not in (0,None) and ("ModuleNotFoundError" in text or "No module named" in text):
        status = "ENVIRONMENT_BLOCKED"
    old = test["baseline_disposition"]
    return {"id":test["id"],"path":test["path"],"command":cmd,"returncode":rc,
            "execution_disposition":status,"baseline_disposition":old,
            "comparison":"UNCHANGED_EXECUTION_STATUS" if old == status else "CHANGED_REVIEW_LOG",
            "seconds":round(time.monotonic()-start,3),"timeout_seconds":test["timeout_seconds"],
            "log":path.name,"log_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
            "tail":text[-5000:],"theorem_promotion":False}


def run_shard(shard: int, shards: int, output: Path) -> int:
    if not 0 <= shard < shards or shards < 1:
        raise ValueError("require 0 <= shard < shards")
    tests = load_inventory()
    selected = [r for i,r in enumerate(tests) if i % shards == shard]
    if not selected:
        raise ValueError("empty shard is not a valid success")
    output.mkdir(parents=True,exist_ok=True)
    result = {"schema":"POST268_EXECUTION_v1","source":anchor(),"shard":shard,"shards":shards,
              "claim_cap":"CHECKER_EXECUTION_NOT_THEOREM_AUTHORITY","terminal_claim":"RH_OPEN",
              "theorem_promotion":False,"expected_ids":[r["id"] for r in selected],"results":[]}
    report = output/f"extended-{shard}.json"
    write_json(report,result)
    for test in selected:
        print("START",test["id"],flush=True)
        row = run_one(test,output)
        result["results"].append(row)
        write_json(report,result)
        print("END",test["id"],row["execution_disposition"],flush=True)
    result["all_executed_successfully"] = all(r["execution_disposition"]=="PASS" for r in result["results"])
    result["disposition_counts"] = dict(Counter(r["execution_disposition"] for r in result["results"]))
    write_json(report,result)
    return 0 if result["all_executed_successfully"] else 1


def harvest(root: Path, output: Path) -> int:
    reports = sorted(root.rglob("extended-*.json"))
    inventory = load_inventory()
    expected = {r["id"]:r for r in inventory}
    current = anchor()
    errors, payloads, rows = [], [], []
    shard_ids = []
    for path in reports:
        try:
            p = json.loads(path.read_text())
            source = p["source"]
            for key in ("commit", "tree", "inventory_sha256"):
                if source.get(key) != current[key]:
                    errors.append(f"{path.name}: {key} is not this checkout")
            if source.get("working_tree_dirty") is not False:
                errors.append(f"{path.name}: dirty or unspecified source tree")
            shard, shards = p["shard"], p["shards"]
            if not 0 <= shard < shards:
                raise ValueError("invalid shard identity")
            wanted = [r["id"] for i,r in enumerate(inventory) if i % shards == shard]
            actual = [r["id"] for r in p["results"]]
            if wanted != p["expected_ids"] or wanted != actual:
                errors.append(f"{path.name}: incomplete or substituted shard membership")
            if p.get("terminal_claim") != "RH_OPEN" or p.get("theorem_promotion") is not False:
                errors.append(f"{path.name}: authority drift")
            for row in p["results"]:
                test = expected[row["id"]]
                if row.get("path") != test["path"] or row.get("timeout_seconds") != test["timeout_seconds"]:
                    errors.append(f"{row['id']}: checker identity drift")
                log = (path.parent/row["log"]).resolve()
                if not log.is_relative_to(path.parent.resolve()) or not log.is_file():
                    errors.append(f"{row['id']}: missing or unsafe log")
                elif hashlib.sha256(log.read_bytes()).hexdigest() != row.get("log_sha256"):
                    errors.append(f"{row['id']}: log hash mismatch")
                if row.get("execution_disposition") != "PASS" or row.get("returncode") != 0:
                    errors.append(f"{row['id']}: execution did not pass")
                if row.get("theorem_promotion") is not False:
                    errors.append(f"{row['id']}: theorem promotion forbidden")
            payloads.append(p); rows.extend(p["results"]); shard_ids.append((shard,shards))
        except (KeyError, TypeError, ValueError, OSError) as exc:
            errors.append(f"{path.name}: invalid report: {exc}")
    counts = Counter(r["id"] for r in rows)
    missing = sorted(set(expected)-set(counts))
    extra = sorted(set(counts)-set(expected))
    duplicates = sorted(k for k,v in counts.items() if v != 1)
    nsets = {n for _,n in shard_ids}
    complete_shards = len(nsets)==1 and sorted(i for i,_ in shard_ids)==list(range(next(iter(nsets))))
    passed = bool(reports) and not errors and not missing and not extra and not duplicates and complete_shards
    result = {"schema":"POST268_EXTENDED_HARVEST_v1","passed":passed,"source":current,
              "report_files":[str(p.relative_to(root)) for p in reports],"errors":errors,
              "missing":missing,"extra":extra,"duplicates":duplicates,"results":rows,
              "claim_cap":"EXECUTION_HARVEST; READ_EACH_SCIENTIFIC_DISPOSITION",
              "terminal_claim":"RH_OPEN","theorem_promotion":False}
    write_json(output,result)
    print(json.dumps({k:v for k,v in result.items() if k!="results"},indent=2))
    return 0 if passed else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,required=True)
    ap.add_argument("--shard",type=int,default=0)
    ap.add_argument("--shards",type=int,default=1)
    ap.add_argument("--harvest",type=Path)
    args = ap.parse_args()
    return harvest(args.harvest,args.output) if args.harvest else run_shard(args.shard,args.shards,args.output)


if __name__ == "__main__":
    raise SystemExit(main())
