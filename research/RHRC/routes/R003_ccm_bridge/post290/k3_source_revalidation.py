#!/usr/bin/env python3
"""Authorize fresh checking of old raw geometry without rewriting producer identity."""
from __future__ import annotations
import argparse
import ast
import json
import subprocess
from pathlib import Path
from k3_resume_partition import HERE, current_identity, digest, write, RESOURCES

BASE="research/RHRC/routes/R003_ccm_bridge/post290/"
ALLOWED_CHANGED={"k3_resume_partition.py","k3_replay_all.py","k3_assemble_complete.py"}
ALLOWED_NEW={"k3_source_revalidation.py","k3_replay_shards.py"}


def function_ast(text,name):
    tree=ast.parse(text)
    matches=[node for node in tree.body if isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef)) and node.name==name]
    if len(matches)!=1:
        raise ValueError("missing or duplicated mathematical function: "+name)
    return ast.dump(matches[0],include_attributes=False)


def literal_assignment(text,name):
    for node in ast.parse(text).body:
        if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in node.targets):
            return ast.literal_eval(node.value)
    raise ValueError("missing frozen mathematical constants: "+name)


def original_text(identity,name):
    commit=identity["commit"]
    if len(commit)!=40 or any(c not in "0123456789abcdef" for c in commit):
        raise ValueError("invalid producer commit")
    raw=subprocess.check_output(["git","show",commit+":"+BASE+name],cwd=HERE.parents[4])
    import hashlib
    if hashlib.sha256(raw).hexdigest()!=identity["continuation_source_digests"][name]:
        raise ValueError("producer frozen bytes do not match original Git object: "+name)
    return raw.decode("utf-8")


def compare(producer,validation):
    # Exact raw mathematical dependencies, basis, canonical evaluator and fixtures.
    if producer["source_digests"]!=validation["source_digests"]:
        raise ValueError("changed canonical SOURCE_INPUTS; integrity-only revalidation forbidden")
    prior,current=producer["continuation_source_digests"],validation["continuation_source_digests"]
    if set(prior)-set(current):
        raise ValueError("old continuation source disappeared")
    if set(current)-set(prior)-ALLOWED_NEW:
        raise ValueError("unregistered new continuation source")
    changes=[]
    for name,oldhash in prior.items():
        if oldhash!=current[name]:
            if name not in ALLOWED_CHANGED:
                raise ValueError("SECOND search changed after preregistration: "+name)
            changes.append({"path":BASE+name,"producer_sha256":oldhash,"validation_sha256":current[name]})
    old_partition=original_text(producer,"k3_resume_partition.py")
    new_partition=(HERE/"k3_resume_partition.py").read_text(encoding="utf-8")
    for name in ("RESOURCES","HISTORICAL_COMMIT","HISTORICAL_RUN","EXPECTED_UNRESOLVED"):
        if literal_assignment(old_partition,name)!=literal_assignment(new_partition,name):
            raise ValueError("frozen constants changed: "+name)
    if literal_assignment(old_partition,"RESOURCES")!=RESOURCES:
        raise ValueError("runtime resources differ from producer contract")
    for name in ("split","coalesce","intake"):
        if function_ast(old_partition,name)!=function_ast(new_partition,name):
            raise ValueError("historical partition semantics changed: "+name)
    old_replay=original_text(producer,"k3_replay_all.py")
    new_replay=(HERE/"k3_replay_all.py").read_text(encoding="utf-8")
    for name in ("independent_second","exact_ball_record"):
        if function_ast(old_replay,name)!=function_ast(new_replay,name):
            raise ValueError("SECOND validation mathematics changed: "+name)
    return changes


def make(partition):
    frozen=json.loads(Path(partition).read_text())
    producer=frozen["current_source"]
    validation=current_identity()
    changes=compare(producer,validation)
    return {"schema":"post290.k3-source-revalidation.v1","original_partition_sha256":digest(partition),
            "producer_source":producer,"validation_source":validation,"changes":changes,
            "new_files":[{"path":BASE+name,"sha256":validation["continuation_source_digests"][name]} for name in sorted(set(validation["continuation_source_digests"])-set(producer["continuation_source_digests"]))],
            "method":"SECOND","checker_precision_bits":768,"fresh_all_leaf_replay_required":True,
            "canonical_input_equality":"EXACT_RAW_SHA256_MAP_EQUALITY","mathematical_function_equality":"UNCHANGED_SEARCH_BYTES_AND_SECOND_AND_EXACT_ENDPOINT_AST",
            "terminal_claim":"RH_OPEN","authority":"SOURCE_INTEGRITY_ONLY"}


def validate(path,producer,partition_hash):
    receipt=json.loads(Path(path).read_text())
    actual=current_identity()
    if receipt.get("schema")!="post290.k3-source-revalidation.v1" or receipt.get("producer_source")!=producer or receipt.get("original_partition_sha256")!=partition_hash or receipt.get("validation_source")!=actual:
        raise ValueError("stale or mismatched source revalidation")
    if receipt.get("changes")!=compare(producer,actual) or receipt.get("fresh_all_leaf_replay_required") is not True:
        raise ValueError("unchecked source delta or attempted fresh-check bypass")
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("partition",type=Path);p.add_argument("--out",type=Path,required=True)
    a=p.parse_args()
    if a.out.exists():
        raise ValueError("refuse to overwrite source revalidation")
    value=make(a.partition);write(a.out,value)
    print(json.dumps({"status":"SOURCE_INTEGRITY_ONLY","changes":len(value["changes"]),"fresh_all_leaf_replay_required":True,"terminal_claim":"RH_OPEN"}))


if __name__=="__main__":
    main()
