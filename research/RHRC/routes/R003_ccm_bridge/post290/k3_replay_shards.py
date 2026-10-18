#!/usr/bin/env python3
"""Freeze exact leaf-index checking shards; preserve all 30 layer unions."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from k3_resume_partition import digest, write, LAYERS, validate_layer, rational, seam_source_bindings, current_identity
from k3_source_revalidation import validate as validate_revalidation

MAX_LEAVES=512
CHUNK_SECONDS=1800
GROUPS=8


def target(directory,spec):
    path=Path(directory)/spec["file"]
    if path.name!=spec["file"] or digest(path)!=spec["sha256"]:
        raise ValueError("changed or illegal candidate layer")
    return json.loads(path.read_text())


def manifest(directory):
    result=json.loads((Path(directory)/"manifest.json").read_text())
    keys=[(r["cell"],r["parity"]) for r in result["records"]]
    if len(keys)!=30 or len(set(keys))!=30 or set(keys)!=LAYERS:
        raise ValueError("require all 30 unique candidate layers")
    return result


def freeze(candidate,partition,revalidation):
    data=manifest(candidate)
    if data["partition_sha256"]!=digest(partition):
        raise ValueError("candidate and original frozen partition differ")
    rev=validate_revalidation(revalidation,data["current_source"],data["partition_sha256"])
    chunks=[]
    for spec in sorted(data["records"],key=lambda r:(r["cell"],r["parity"])):
        raw=target(candidate,spec)
        validate_layer(spec,raw,"SECOND")
        size=len(raw["accepted"])
        for start in range(0,max(size,1),MAX_LEAVES):
            stop=min(size,start+MAX_LEAVES)
            q,parity=spec["cell"],spec["parity"]
            chunks.append({"id":f"Q{q:02d}_{parity}_{start:07d}_{stop:07d}","Q":q,"parity":parity,"parent_file":spec["file"],"parent_sha256":spec["sha256"],"start":start,"stop":stop,"group":len(chunks)%GROUPS})
    return {"schema":"post290.k3-fresh-check-shards.v1","protocol":"SECOND_FRESH_768_SHARDED_v1","candidate_manifest_sha256":digest(Path(candidate)/"manifest.json"),"original_partition_sha256":digest(partition),"source_revalidation_sha256":digest(revalidation),"producer_source":data["current_source"],"validation_source":rev["validation_source"],"resources":{"method":"SECOND","precision_bits":768,"max_leaves_per_chunk":MAX_LEAVES,"seconds_per_chunk":CHUNK_SECONDS,"concurrent_runner_groups":GROUPS},"chunks":chunks,"layers":data["records"],"terminal_claim":"RH_OPEN","fresh_all_leaves_required":True}


def validate_plan(plan,candidate,revalidation):
    data=json.loads(Path(plan).read_text())
    if data["schema"]!="post290.k3-fresh-check-shards.v1" or data["resources"]!={"method":"SECOND","precision_bits":768,"max_leaves_per_chunk":MAX_LEAVES,"seconds_per_chunk":CHUNK_SECONDS,"concurrent_runner_groups":GROUPS}:
        raise ValueError("altered checker partition protocol")
    if data["candidate_manifest_sha256"]!=digest(Path(candidate)/"manifest.json") or data["source_revalidation_sha256"]!=digest(revalidation):
        raise ValueError("stale candidate or source review")
    validate_revalidation(revalidation,data["producer_source"],data["original_partition_sha256"])
    if data["validation_source"]!=current_identity():
        raise ValueError("checker source changed after shard freeze")
    # Reconstruct the deterministic exact index partition independently.
    expected=[]
    source=manifest(candidate)
    if source["records"]!=data["layers"]:
        raise ValueError("shard manifest changes original layer specs")
    for spec in sorted(source["records"],key=lambda r:(r["cell"],r["parity"])):
        raw=target(candidate,spec)
        validate_layer(spec,raw,"SECOND")
        size=len(raw["accepted"])
        for start in range(0,max(size,1),MAX_LEAVES):
            stop=min(size,start+MAX_LEAVES);q,parity=spec["cell"],spec["parity"]
            expected.append({"id":f"Q{q:02d}_{parity}_{start:07d}_{stop:07d}","Q":q,"parity":parity,"parent_file":spec["file"],"parent_sha256":spec["sha256"],"start":start,"stop":stop,"group":len(expected)%GROUPS})
    if data["chunks"]!=expected:
        raise ValueError("checker leaf-index partition omitted, duplicated or reassigned a leaf")
    return data


def run_chunk(candidate,chunk,plan_hash,output):
    from flint import ctx
    import canonical_source_arb as C
    from k3_replay_all import independent_second
    C.set_precision(768);ctx.prec=768
    spec={"file":chunk["parent_file"],"sha256":chunk["parent_sha256"]}
    raw=target(candidate,spec)
    tiles=raw["accepted"]
    verified,failed=[],[];start=time.monotonic()
    def receipt(unverified):
        return {"schema":"post290.k3-fresh-check-chunk.v1","chunk":chunk,"plan_sha256":plan_hash,"precision_bits":768,"verified":verified,"failed":failed,"unverified":unverified,"complete":not failed and not unverified,"elapsed_seconds":time.monotonic()-start,"seam_source_bindings":seam_source_bindings(),"terminal_claim":"RH_OPEN"}
    for index in range(chunk["start"],chunk["stop"]):
        pending=[{"index":i,"left":tiles[i]["left"],"right":tiles[i]["right"],"reason":"IN_FLIGHT_OR_QUEUED"} for i in range(index,chunk["stop"])]
        write(output,receipt(pending))
        if time.monotonic()-start>=CHUNK_SECONDS:
            for row in pending:row["reason"]="CHECKER_WALL_LIMIT"
            write(output,receipt(pending));return
        tile=tiles[index]
        try:
            value=independent_second(tile,chunk["Q"],chunk["parity"])
        except Exception as exc:
            value={"accepted":False,"reason":"EVALUATION_ERROR","error":repr(exc)}
        entry={"index":index,"left":tile["left"],"right":tile["right"],**value}
        (verified if value["accepted"] else failed).append(entry)
    write(output,receipt([]))


def run_group(plan,candidate,revalidation,group,out):
    data=validate_plan(plan,candidate,revalidation)
    if group not in range(GROUPS):raise ValueError("invalid checker runner group")
    records=[]
    for chunk in data["chunks"]:
        if chunk["group"]!=group:continue
        job=out/(chunk["id"]+".input.json");output=out/(chunk["id"]+".json")
        write(job,chunk)
        command=[sys.executable,str(Path(__file__).resolve()),"worker",str(candidate),str(job),"--plan-sha256",digest(plan),"--out",str(output)]
        try:
            subprocess.run(command,env=dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1"),capture_output=True,text=True,check=True,timeout=CHUNK_SECONDS)
        except subprocess.TimeoutExpired:
            if output.exists():
                pending=json.loads(output.read_text())
                for row in pending["unverified"]:row["reason"]="HARD_CHECKER_WALL_TIMEOUT"
                write(output,pending)
            else:
                raise RuntimeError("checker timeout before initial coverage checkpoint")
        records.append({"file":output.name,"sha256":digest(output),"id":chunk["id"]})
        result=json.loads(output.read_text())
        print(json.dumps({"chunk":chunk["id"],"complete":result["complete"],"verified":len(result["verified"]),"unverified":len(result["unverified"])}),flush=True)
    validate_plan(plan,candidate,revalidation)
    write(out/f"group{group}.json",{"plan_sha256":digest(plan),"group":group,"records":records,"terminal_claim":"RH_OPEN"})


def run_selected(plan,candidate,revalidation,identifier,out):
    data=validate_plan(plan,candidate,revalidation)
    matches=[c for c in data["chunks"] if c["id"]==identifier]
    if len(matches)!=1:raise ValueError("unknown or duplicated checker shard ID")
    chunk=matches[0]
    job=out/(identifier+".input.json");output=out/(identifier+".json")
    write(job,chunk)
    command=[sys.executable,str(Path(__file__).resolve()),"worker",str(candidate),str(job),"--plan-sha256",digest(plan),"--out",str(output)]
    try:
        subprocess.run(command,env=dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1"),capture_output=True,text=True,check=True,timeout=CHUNK_SECONDS)
    except (subprocess.TimeoutExpired,subprocess.CalledProcessError) as exc:
        if output.exists():
            pending=json.loads(output.read_text())
            for row in pending["unverified"]:row["reason"]="HARD_CHECKER_WALL_TIMEOUT" if isinstance(exc,subprocess.TimeoutExpired) else "CHECKER_PROCESS_FAILED"
            write(output,pending)
        else:
            raw=target(candidate,{"file":chunk["parent_file"],"sha256":chunk["parent_sha256"]})
            unverified=[{"index":i,"left":raw["accepted"][i]["left"],"right":raw["accepted"][i]["right"],"reason":"PROCESS_FAILED_BEFORE_CHECKPOINT"} for i in range(chunk["start"],chunk["stop"])]
            write(output,{"schema":"post290.k3-fresh-check-chunk.v1","chunk":chunk,"plan_sha256":digest(plan),"precision_bits":768,"verified":[],"failed":[],"unverified":unverified,"complete":False,"seam_source_bindings":seam_source_bindings(),"terminal_claim":"RH_OPEN"})
    validate_plan(plan,candidate,revalidation)
    write(out/("shard_manifest_"+identifier+".json"),{"plan_sha256":digest(plan),"records":[{"file":output.name,"sha256":digest(output),"id":identifier}],"terminal_claim":"RH_OPEN"})
    result=json.loads(output.read_text())
    print(json.dumps({"chunk":identifier,"complete":result["complete"],"verified":len(result["verified"]),"unverified":len(result["unverified"])}),flush=True)


def assemble(plan,candidate,revalidation,chunks,out):
    from flint import arb,ctx
    from wp4_k3_full_continuum import interval_bounds
    ctx.prec=768
    data=validate_plan(plan,candidate,revalidation)
    plan_hash=digest(plan);results={}
    direct=sorted(chunks.glob("shard_manifest_*.json"))
    collection=direct if direct else sorted(chunks.glob("group*.json"))
    for file in collection:
        receipt=json.loads(file.read_text())
        if receipt["plan_sha256"]!=plan_hash:
            raise ValueError("wrong checker group parent")
        if direct:
            identifier=file.name[len("shard_manifest_"):-len(".json")]
            if identifier not in {c["id"] for c in data["chunks"]}:raise ValueError("unplanned checker shard receipt")
            expected={identifier}
        else:
            group=receipt["group"]
            expected={c["id"] for c in data["chunks"] if c["group"]==group}
        if {r["id"] for r in receipt["records"]}!=expected or len(receipt["records"])!=len(expected):
            raise ValueError("omitted or duplicated checker shard")
        for spec in receipt["records"]:
            path=chunks/spec["file"]
            if path.name!=spec["file"] or digest(path)!=spec["sha256"]:
                raise ValueError("changed checker shard bytes")
            result=json.loads(path.read_text())
            if spec["id"] in results or result["plan_sha256"]!=plan_hash or result["precision_bits"]!=768:
                raise ValueError("wrong or duplicated checker shard")
            results[spec["id"]]=result
    planned={c["id"] for c in data["chunks"]}
    if set(results)-planned:raise ValueError("extra unplanned checker shard")
    missing=sorted(planned-set(results))
    # A missing artifact is explicit unverified geometry, never accepted evidence.
    for chunk in data["chunks"]:
        if chunk["id"] not in missing:continue
        raw=target(candidate,{"file":chunk["parent_file"],"sha256":chunk["parent_sha256"]})
        pending=[{"index":i,"left":raw["accepted"][i]["left"],"right":raw["accepted"][i]["right"],"reason":"MISSING_CHECKER_SHARD_ARTIFACT"} for i in range(chunk["start"],chunk["stop"])]
        results[chunk["id"]]={"chunk":chunk,"plan_sha256":plan_hash,"precision_bits":768,"verified":[],"failed":[],"unverified":pending,"complete":False,"seam_source_bindings":seam_source_bindings(),"missing_artifact":True}
    layer_receipts=[]
    counts={"verified_tiles":0,"failed_tiles":0,"unverified_tiles":0,"unresolved_tiles":0,"complete_layers":0}
    for spec in data["layers"]:
        q,parity=spec["cell"],spec["parity"];raw=target(candidate,spec)
        bounds=interval_bounds(q);structure=validate_layer(spec,raw,"SECOND",bounds)
        qball=lambda f:arb(f.numerator)/f.denominator
        lower=arb(1)/512 if q==1 else arb(q).log()
        if not bool(qball(bounds[0])<=lower and qball(bounds[1])>=arb(q+1).log()):
            raise ValueError("physical seams not bracketed")
        verified=[];failed=[];unverified=[]
        for chunk in data["chunks"]:
            if (chunk["Q"],chunk["parity"])!=(q,parity):continue
            value=results[chunk["id"]]
            if value["chunk"]!=chunk or value.get("seam_source_bindings")!=seam_source_bindings() or type(value.get("complete")) is not bool:
                raise ValueError("checker shard lineage or disposition differs")
            seen=set()
            for category in ("verified","failed","unverified"):
                for tile in value[category]:
                    index=tile["index"]
                    if type(index) is not int or index in seen or not chunk["start"]<=index<chunk["stop"]:
                        raise ValueError("checker leaf omitted, duplicated or out of shard")
                    seen.add(index)
                    parent=raw["accepted"][index]
                    if tile["left"]!=parent["left"] or tile["right"]!=parent["right"]:
                        raise ValueError("checker widened or moved a raw leaf")
                    if category=="verified":
                        if tile.get("accepted") is not True:raise ValueError("unchecked shard leaf relabelled accepted")
                        for field in ("a_interval","delta_interval"):
                            exact=tile.get(field,{})
                            if exact.get("finite") is not True or not 0<rational(exact.get("lower"))<=rational(exact.get("upper")):
                                raise ValueError("nonfinite, unordered or nonpositive shard bound")
            if seen!=set(range(chunk["start"],chunk["stop"])) or value["complete"]!=(not value["failed"] and not value["unverified"] and not value.get("missing_artifact")):
                raise ValueError("checker shard coverage or complete flag disagrees")
            verified+=value["verified"];failed+=value["failed"];unverified+=value["unverified"]
        verified.sort(key=lambda t:t["index"]);failed.sort(key=lambda t:t["index"]);unverified.sort(key=lambda t:t["index"])
        complete=structure and not failed and not unverified
        layer={"schema":"post290.k3-layer-replay.v1","Q":q,"parity":parity,"candidate_sha256":spec["sha256"],"precision_bits":768,"verified":verified,"failed":failed,"unverified":unverified,"unresolved":raw["unresolved"],"seams_verified":True,"seam_source_bindings":seam_source_bindings(),"complete":complete,"checker_plan_sha256":plan_hash,"terminal_claim":"RH_OPEN"}
        name=f"replay_Q{q:02d}_{parity}.json";path=out.parent/"replay-layers"/name;write(path,layer)
        layer_receipts.append({"file":name,"sha256":digest(path),"Q":q,"parity":parity,"complete":complete})
        counts["verified_tiles"]+=len(verified);counts["failed_tiles"]+=len(failed);counts["unverified_tiles"]+=len(unverified);counts["unresolved_tiles"]+=len(raw["unresolved"]);counts["complete_layers"]+=int(complete)
    complete=counts["complete_layers"]==30 and not missing
    result={"schema":"post290.k3-independent-full-checker.v1","status":"PASS" if complete else "UNRESOLVED","claimed_scope":"K3_FULL" if complete else "FULL_TARGET_UNVERIFIED_REMAINDER","candidate_manifest_sha256":data["candidate_manifest_sha256"],"current_source":data["producer_source"],"producer_source":data["producer_source"],"validation_source":data["validation_source"],"source_revalidation_sha256":digest(revalidation),"checker_plan_sha256":plan_hash,"precision_bits":768,"layers":30,**counts,"seams_verified":True,"layer_receipts":layer_receipts,"terminal_claim":"RH_OPEN","not_a_lean_proof":True}
    result["missing_shards"]=missing
    write(out,result)
    return 0 if complete else 2


def main():
    p=argparse.ArgumentParser(description=__doc__);s=p.add_subparsers(dest="command",required=True)
    a=s.add_parser("freeze");a.add_argument("candidate",type=Path);a.add_argument("partition",type=Path);a.add_argument("revalidation",type=Path);a.add_argument("--out",type=Path,required=True)
    a=s.add_parser("group");a.add_argument("plan",type=Path);a.add_argument("candidate",type=Path);a.add_argument("revalidation",type=Path);a.add_argument("--group",type=int,required=True);a.add_argument("--out",type=Path,required=True)
    a=s.add_parser("single");a.add_argument("plan",type=Path);a.add_argument("candidate",type=Path);a.add_argument("revalidation",type=Path);a.add_argument("--id",required=True);a.add_argument("--out",type=Path,required=True)
    a=s.add_parser("assemble");a.add_argument("plan",type=Path);a.add_argument("candidate",type=Path);a.add_argument("revalidation",type=Path);a.add_argument("chunks",type=Path);a.add_argument("--out",type=Path,required=True)
    a=s.add_parser("worker");a.add_argument("candidate",type=Path);a.add_argument("chunk",type=Path);a.add_argument("--plan-sha256",required=True);a.add_argument("--out",type=Path,required=True)
    a=p.parse_args()
    if a.command=="freeze":
        if a.out.exists():raise ValueError("refuse to overwrite frozen checker shards")
        write(a.out,freeze(a.candidate,a.partition,a.revalidation))
    elif a.command=="group":run_group(a.plan,a.candidate,a.revalidation,a.group,a.out)
    elif a.command=="single":run_selected(a.plan,a.candidate,a.revalidation,a.id,a.out)
    elif a.command=="worker":run_chunk(a.candidate,json.loads(a.chunk.read_text()),a.plan_sha256,a.out)
    else:return assemble(a.plan,a.candidate,a.revalidation,a.chunks,a.out)
    return 0


if __name__=="__main__":raise SystemExit(main())
