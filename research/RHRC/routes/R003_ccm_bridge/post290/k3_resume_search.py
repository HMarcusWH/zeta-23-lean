#!/usr/bin/env python3
"""Execute both frozen SECOND passes, preserving unrun and unresolved coverage."""
from __future__ import annotations
import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from k3_resume_partition import HERE, OLD, digest, pair, rational, require_current, split, write


def run_job(job, resources, partition_hash, checkpoint=None):
    sys.path[:0] = [str(OLD), str(HERE.parent)]
    from flint import ctx
    import canonical_source_arb as C
    from wp4_k3_full_continuum import evaluate
    C.set_precision(resources["precision_bits"])
    ctx.prec = resources["precision_bits"]
    lo, hi = rational(job["left"]), rational(job["right"])
    start = time.monotonic()
    stack, accepted, unresolved, nodes, negative = [(lo, hi, 0)], [], [], 0, False
    while stack:
        l, r, depth = stack.pop()
        if checkpoint is not None:
            # Persist coverage BEFORE an expensive native enclosure. Hard interruption
            # preserves every earlier accepted leaf and identifies the in-flight tile.
            pending=[{"left":pair(a),"right":pair(b),"depth":d,"reason":"IN_FLIGHT_OR_QUEUED"} for a,b,d in [(l,r,depth),*stack]]
            write(checkpoint,{"schema":"post290.k3-search-job.v1","job":job,"partition_sha256":partition_hash,"resources":resources,"accepted":sorted(accepted,key=lambda t:rational(t["left"])),"unresolved":pending,"tested_nodes":nodes,"elapsed_seconds":time.monotonic()-start,"certified_negative_stop":negative,"status":"UNRESOLVED","terminal_claim":"RH_OPEN"})
        if nodes >= resources["max_nodes"] or time.monotonic()-start >= resources["seconds"]:
            reason = "NODE_LIMIT" if nodes >= resources["max_nodes"] else "WALL_LIMIT_BETWEEN_EVALUATIONS"
            unresolved += [{"left": pair(a), "right": pair(b), "depth": d, "reason": reason} for a,b,d in [(l,r,depth),*stack]]
            break
        nodes += 1
        try:
            result = evaluate((l,r),job["parity"],job["Q"],"SECOND")
        except Exception as exc:
            result = {"accepted": False, "method": "SECOND", "error": repr(exc)}
        tile = {"left": pair(l), "right": pair(r), "depth": depth}
        if result.get("certified_negative_centre"):
            negative = True
            unresolved.append({**tile,"candidate":result,"reason":"CERTIFIED_NEGATIVE_NATIVE_STOP"})
            unresolved += [{"left":pair(a),"right":pair(b),"depth":d,"reason":"NOT_TESTED_AFTER_NEGATIVE_STOP"} for a,b,d in stack]
            break
        if result["accepted"]:
            accepted.append({**tile,**result})
        elif depth >= resources["max_depth"]:
            unresolved.append({**tile,"candidate":result,"reason":"UNCERTIFIED_SIGN"})
        else:
            middle = (l+r)/2
            stack.extend([(middle,r,depth+1),(l,middle,depth+1)])
    accepted.sort(key=lambda x:rational(x["left"]))
    unresolved.sort(key=lambda x:rational(x["left"]))
    return {"schema":"post290.k3-search-job.v1","job":job,"partition_sha256":partition_hash,"resources":resources,"accepted":accepted,"unresolved":unresolved,"tested_nodes":nodes,"elapsed_seconds":time.monotonic()-start,"certified_negative_stop":negative,"status":"PASS" if not unresolved else "UNRESOLVED","terminal_claim":"RH_OPEN"}


def campaign(partition, directory):
    manifest = json.loads(partition.read_text())
    require_current(manifest)
    h = digest(partition)
    directory.mkdir(parents=True,exist_ok=True)
    # Process isolation is required: Arb precision is global, so threads are invalid.
    def execute(jobs, resources):
        results = []
        def isolated(job):
            specification=directory/(job["id"]+".input.json")
            output=directory/(job["id"]+".json")
            write(specification,{"job":job,"resources":resources,"partition_sha256":h})
            env=dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1")
            try:
                subprocess.run([sys.executable,str(Path(__file__).resolve()),"--worker",str(specification),"--out",str(output)],env=env,capture_output=True,text=True,timeout=resources["seconds"],check=True)
            except subprocess.TimeoutExpired:
                if output.exists():
                    checkpoint=json.loads(output.read_text())
                    for leaf in checkpoint["unresolved"]:
                        leaf["reason"]="HARD_WALL_TIMEOUT"
                    checkpoint["hard_wall_timeout"]=True
                    write(output,checkpoint)
                else:
                    raise RuntimeError("worker hit hard wall before initial coverage checkpoint")
            return json.loads(output.read_text())
        # Threads supervise independent child processes; no Arb arithmetic runs here.
        with concurrent.futures.ThreadPoolExecutor(max_workers=manifest["resources"]["max_concurrency"]) as pool:
            futures = {pool.submit(isolated, job): job for job in jobs}
            for future in concurrent.futures.as_completed(futures):
                job = futures[future]
                try:
                    result = future.result()
                except Exception as exc:
                    result = {"schema":"post290.k3-search-job.v1","job":job,"partition_sha256":h,"resources":resources,"accepted":[],"unresolved":[{"left":job["left"],"right":job["right"],"reason":"WORKER_FAILED","error":repr(exc)}],"status":"UNRESOLVED","terminal_claim":"RH_OPEN"}
                write(directory/(job["id"]+".json"),result)
                results.append(result)
                print(json.dumps({"job":job["id"],"pass":job["pass"],"status":result["status"],"accepted":len(result["accepted"]),"unresolved":len(result["unresolved"])}),flush=True)
        return results
    first = execute(manifest["jobs"],manifest["resources"]["first"])
    second_jobs, unrun = [], []
    ordered = sorted(((r["job"], t, i) for r in first for i,t in enumerate(r["unresolved"])), key=lambda x:(x[0]["Q"],x[0]["component"],rational(x[1]["left"])))
    # A certified negative is an investigation stop, never a second-pass candidate.
    negative = any(r.get("certified_negative_stop") for r in first)
    for parent,tile,index in ordered:
        for n,(lo,hi) in enumerate(split(rational(tile["left"]),rational(tile["right"]),4)):
            child={**parent,"id":parent["id"]+f"_R{index:05d}_P{n}","left":pair(lo),"right":pair(hi),"pass":2,"parent_job":parent["id"],"parent_leaf":index}
            if negative or len(second_jobs)>=manifest["resources"]["second_child_cap"]:
                unrun.append({**child,"reason":"NEGATIVE_INVESTIGATION_STOP" if negative else "SECOND_CHILD_CAP"})
            else:
                second_jobs.append(child)
    # Derived partition is persisted before evaluating any second-pass child.
    write(directory/"second-partition.json",{"partition_sha256":h,"jobs":second_jobs,"unrun":unrun,"rule":"all first-pass unresolved leaves into four children, first 256 by Q/component/left"})
    second=execute(second_jobs,manifest["resources"]["second"])
    require_current(manifest)
    summary={"schema":"post290.k3-search-campaign.v1","partition_sha256":h,"first_jobs":len(first),"second_jobs":len(second),"unrun":unrun,"unresolved_count":sum(len(r["unresolved"]) for r in second),"negative_investigation_stop":negative or any(r.get("certified_negative_stop") for r in second),"results":[{"file":r["job"]["id"]+".json","sha256":digest(directory/(r["job"]["id"]+".json"))} for r in first+second],"terminal_claim":"RH_OPEN"}
    summary["status"]="SEARCH_COMPLETE" if not unrun and not summary["unresolved_count"] and not summary["negative_investigation_stop"] else "UNRESOLVED"
    write(directory/"campaign.json",summary)
    return 0 if summary["status"]=="SEARCH_COMPLETE" else 2


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("partition",type=Path,nargs="?")
    p.add_argument("--worker",type=Path)
    p.add_argument("--out",type=Path,required=True)
    a=p.parse_args()
    if a.worker:
        data=json.loads(a.worker.read_text())
        write(a.out,run_job(data["job"],data["resources"],data["partition_sha256"],a.out))
        return 0
    if a.partition is None:
        p.error("partition required")
    return campaign(a.partition,a.out)


if __name__=="__main__":
    raise SystemExit(main())
