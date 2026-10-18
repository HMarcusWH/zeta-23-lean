#!/usr/bin/env python3
"""Assemble inherited raw intervals plus continuation; accept only full fresh checking."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from k3_resume_partition import digest, intake, rational, require_current, write, LAYERS, validate_layer, seam_source_bindings


def assemble(partition, search, out):
    frozen=json.loads(partition.read_text())
    require_current(frozen)
    _, inherited, hashes=intake(frozen["historical_source"]["directory"])
    if hashes!=frozen["historical_source"]["hashes"]:
        raise ValueError("historical bytes changed after freeze")
    campaign=json.loads((search/"campaign.json").read_text())
    if campaign["partition_sha256"]!=digest(partition):
        raise ValueError("wrong continuation partition")
    jobs={}
    for spec in campaign["results"]:
        path=search/spec["file"]
        if path.name!=spec["file"] or digest(path)!=spec["sha256"]:
            raise ValueError("invalid or changed search result")
        result=json.loads(path.read_text())
        if result["partition_sha256"]!=digest(partition):
            raise ValueError("stale search result")
        if result["job"]["id"] in jobs:
            raise ValueError("duplicated continuation result")
        jobs[result["job"]["id"]]=result
    if {j["id"] for j in frozen["jobs"]}!={n for n,r in jobs.items() if r["job"]["pass"]==1}:
        raise ValueError("missing or additional first-pass job")
    second=json.loads((search/"second-partition.json").read_text())
    if {j["id"] for j in second["jobs"]}!={n for n,r in jobs.items() if r["job"]["pass"]==2}:
        raise ValueError("missing or additional second-pass job")
    records=[]
    for oldspec,data in inherited:
        q,parity=oldspec["cell"],oldspec["parity"]
        accepted=[{**tile,"ancestry":{"historical_file":oldspec["file"],"historical_sha256":oldspec["sha256"],"historical_accepted_index":i}} for i,tile in enumerate(data["accepted"])]
        unresolved=[]
        for result in jobs.values():
            job=result["job"]
            if (job["Q"],job["parity"])!=(q,parity):
                continue
            accepted.extend({**t,"ancestry":{"job":job["id"],"partition_sha256":digest(partition)}} for t in result["accepted"])
            if job["pass"]==2:
                unresolved.extend({**t,"ancestry":{"job":job["id"]}} for t in result["unresolved"])
        unresolved.extend({"left":j["left"],"right":j["right"],"reason":j["reason"],"unrun":True} for j in campaign["unrun"] if (j["Q"],j["parity"])==(q,parity))
        accepted.sort(key=lambda t:rational(t["left"]))
        unresolved.sort(key=lambda t:rational(t["left"]))
        record={"Q":q,"parity":parity,"left":data["left"],"right":data["right"],"accepted":accepted,"unresolved":unresolved,"status":"PASS" if not unresolved else "UNRESOLVED","candidate_only":True}
        path=out/oldspec["file"]
        spec={"cell":q,"parity":parity,"file":path.name,"status":record["status"],"intervals":len(accepted),"unresolved_count":len(unresolved)}
        validate_layer(spec,record,"SECOND")
        write(path,record)
        spec["sha256"]=digest(path)
        records.append(spec)
    complete=not any(r["unresolved_count"] for r in records) and not campaign["negative_investigation_stop"]
    manifest={"schema":"post290.k3-candidate.v1","partition_sha256":digest(partition),"current_source":frozen["current_source"],"historical_source":frozen["historical_source"],"method":"SECOND","status":"CANDIDATE_COMPLETE" if complete else "UNRESOLVED","records":records,"search_campaign_sha256":digest(search/"campaign.json"),"terminal_claim":"RH_OPEN","all_L_positivity_certified":False,"not_a_lean_proof":True}
    write(out/"manifest.json",manifest)
    return manifest


def final(candidate, replay, out, source_revalidation=None):
    from flint import ctx
    from wp4_k3_full_continuum import interval_bounds
    ctx.prec=768
    manifest=json.loads((candidate/"manifest.json").read_text())
    receipt=json.loads(replay.read_text())
    if receipt.get("candidate_manifest_sha256")!=digest(candidate/"manifest.json") or receipt.get("current_source")!=manifest["current_source"]:
        raise ValueError("stale independent checker receipt")
    if source_revalidation is None:
        require_current(manifest)
    else:
        from k3_source_revalidation import validate
        source_review=validate(source_revalidation,manifest["current_source"],manifest["partition_sha256"])
        if receipt.get("source_revalidation_sha256")!=digest(source_revalidation) or receipt.get("producer_source")!=manifest["current_source"] or receipt.get("validation_source")!=source_review["validation_source"]:
            raise ValueError("fresh checker lacks current source revalidation lineage")
    if len(manifest["records"])!=30 or {(r["cell"],r["parity"]) for r in manifest["records"]}!=LAYERS:
        raise ValueError("full D2 requires 30 distinct layers")
    specs={(s["cell"],s["parity"]):s for s in manifest["records"]}
    checked=set()
    derived_complete_layers = 0
    derived_verified = derived_failed = derived_unverified = derived_unresolved = 0
    derived_unrun=derived_nonfinite=0
    for layer in receipt.get("layer_receipts",[]):
        key=(layer["Q"],layer["parity"])
        if key in checked or key not in specs:
            raise ValueError("duplicate or invalid fresh-check layer")
        checked.add(key)
        path=replay.parent/"replay-layers"/layer["file"]
        if path.name!=layer["file"] or digest(path)!=layer["sha256"]:
            raise ValueError("changed layer checker receipt")
        data=json.loads(path.read_text())
        if type(data.get("Q")) is not int or (data.get("Q"),data.get("parity"))!=key:
            raise ValueError("layer checker payload has wrong Q/parity")
        if type(data.get("complete")) is not bool or type(layer.get("complete")) is not bool:
            raise ValueError("layer complete disposition must be Boolean")
        if data.get("seam_source_bindings")!=seam_source_bindings():
            raise ValueError("missing or stale physical-seam theorem source bindings")
        if data.get("candidate_sha256")!=specs[key]["sha256"] or data.get("precision_bits")!=768:
            raise ValueError("wrong fresh layer source/precision")
        raw=Path(candidate)/specs[key]["file"]
        if digest(raw)!=specs[key]["sha256"]:
            raise ValueError("candidate layer changed after replay")
        record=json.loads(raw.read_text())
        validate_layer(specs[key], record, "SECOND", interval_bounds(key[0]))
        derived_verified += len(data.get("verified",[]))
        derived_failed += len(data.get("failed",[]))
        derived_unverified += len(data.get("unverified",[]))
        derived_unresolved += len(data.get("unresolved",[]))
        derived_unrun+=sum(t.get("unrun") is True for t in record["unresolved"])
        derived_nonfinite+=sum(str(t.get("reason","")).startswith("NONFINITE") for t in data.get("failed",[]))
        if layer.get("complete") is not data.get("complete"):
            raise ValueError("layer summary contradicts checked payload")
        if data.get("complete"):
            derived_complete_layers += 1
            if data.get("seams_verified") is not True:
                raise ValueError("layer physical seam not verified")
            if data.get("unverified") or data.get("failed") or data.get("unresolved") or record["unresolved"]:
                raise ValueError("unchecked/unresolved leaf relabelled complete")
            verified=data.get("verified",[])
            if len(verified)!=len(record["accepted"]) or [v["index"] for v in verified]!=list(range(len(record["accepted"]))):
                raise ValueError("fresh layer checker omits or duplicates a tile")
            for tile,fresh in zip(record["accepted"],verified):
                if tile["left"]!=fresh["left"] or tile["right"]!=fresh["right"] or fresh.get("accepted") is not True:
                    raise ValueError("checker interval and accepted source interval differ")
                for field in ("a_interval","delta_interval"):
                    bounds=fresh.get(field,{})
                    if bounds.get("finite") is not True or "lower" not in bounds or "upper" not in bounds:
                        raise ValueError("missing or nonfinite exact fresh bound")
                    lower, upper = rational(bounds["lower"]), rational(bounds["upper"])
                    if not 0 < lower <= upper:
                        raise ValueError("fresh positive bound is unordered or nonpositive")
                # Typed rational endpoints establish positivity. Optional display
                # fields still have to render finite evidence honestly.
                for field in ("a","delta"):
                    display=fresh.get(field,{})
                    if isinstance(display,dict) and any(isinstance(value,str) and ("nan" in value.lower() or "inf" in value.lower()) for value in display.values()):
                        raise ValueError("nonfinite fresh-bound display violates evidence integrity")
    if checked!=LAYERS:
        raise ValueError("missing fresh-check layer receipt")
    for key, actual in (("complete_layers",derived_complete_layers),("verified_tiles",derived_verified),
                        ("failed_tiles",derived_failed),("unverified_tiles",derived_unverified),
                        ("unresolved_tiles",derived_unresolved)):
        if receipt.get(key) != actual:
            raise ValueError("checker summary disagrees with payload: " + key)
    # NON-PARTIAL gate is mandatory; partial process success is not certificate authority.
    complete=(manifest["status"]=="CANDIDATE_COMPLETE" and receipt.get("claimed_scope")=="K3_FULL" and receipt.get("status")=="PASS" and receipt.get("layers")==30 and receipt.get("complete_layers")==30 and receipt.get("unverified_tiles")==0 and receipt.get("failed_tiles")==0 and receipt.get("unresolved_tiles")==0 and receipt.get("precision_bits")==768 and receipt.get("seams_verified") is True and not receipt.get("missing_shards"))
    result={"schema":"post290.k3-complete.v1","status":"D2_COMPLETE" if complete else "D2_OPEN","terminal_claim":"RH_OPEN","candidate_manifest_sha256":digest(candidate/"manifest.json"),"independent_checker_sha256":digest(replay),"current_source":manifest["current_source"],"historical_source":manifest["historical_source"],"all_L_positivity_certified":complete,"not_a_lean_proof":True,"not_a_proof_of_RH":True,"authority":"CERTIFIED_FINITE" if complete else "UNRESOLVED_RESEARCH","checker_disposition":receipt.get("status"),"coverage":"both parities [1/512,log16]" if complete else "only separately freshly verified intervals"}
    result.update(complete_layers=derived_complete_layers,unresolved_tiles=derived_unresolved,unrun_tiles=derived_unrun,missing_artifacts=len(receipt.get("missing_shards",[])),unverified_tiles=derived_unverified,nonfinite_enclosures=derived_nonfinite,independent_nonpartial_verified=complete,both_parities=True,physical_seams_verified=receipt.get("seams_verified") is True)
    if source_revalidation is not None:
        result.update(producer_source=manifest["current_source"],validation_source=source_review["validation_source"],source_revalidation_sha256=digest(source_revalidation))
    result["source_tree"]=(source_review["validation_source"] if source_revalidation is not None else manifest["current_source"]).get("tree")
    write(out,result)
    if not complete:
        raise ValueError("NON-PARTIAL D2 gate failed: unresolved, unverified or missing coverage remains")
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    s=p.add_subparsers(dest="command",required=True)
    a=s.add_parser("candidates"); a.add_argument("partition",type=Path); a.add_argument("search",type=Path); a.add_argument("--out",type=Path,required=True)
    a=s.add_parser("final"); a.add_argument("candidate",type=Path); a.add_argument("replay",type=Path); a.add_argument("--out",type=Path,required=True)
    a.add_argument("--source-revalidation",type=Path)
    a=p.parse_args()
    result=assemble(a.partition,a.search,a.out) if a.command=="candidates" else final(a.candidate,a.replay,a.out,a.source_revalidation)
    print(json.dumps({"status":result["status"],"terminal_claim":"RH_OPEN"}))


if __name__=="__main__":
    main()
