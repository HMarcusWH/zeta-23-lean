#!/usr/bin/env python3
"""Mutate only an isolated staging directory; fail closed in both Python modes."""
import copy,json,pathlib,sys,tempfile
from epoch import verify_stage,require
P=pathlib.Path
work,receipt=map(P,sys.argv[1:3])
original=receipt.read_bytes()
r=json.loads(original)
def rejects(fn):
    try:fn()
    except (RuntimeError,ValueError,KeyError,FileNotFoundError):return
    raise RuntimeError("stage mutation accepted")
verify_stage(work,receipt)
with tempfile.TemporaryDirectory() as t:
    q=P(t)/"source.json"
    for key,value in (("claim","RH_PROVED"),("toolchain","leanprover/lean4:v4.33.0-rc2"),("mathlib","0"*40)):
        m=copy.deepcopy(r);m[key]=value;q.write_text(json.dumps(m))
        rejects(lambda:verify_stage(work,q))
    for key,value in (("schema","NATIVE_TERMINAL_REPAIR_EPOCH_V3"),("repair_baseline","cfc0e6bc92be1db226d4a84f9542ace9c4868e16")):
        m=copy.deepcopy(r);m[key]=value;q.write_text(json.dumps(m))
        rejects(lambda:verify_stage(work,q))
    m=copy.deepcopy(r);m["overlay"].pop();q.write_text(json.dumps(m))
    rejects(lambda:verify_stage(work,q))
    m=copy.deepcopy(r);m["files"][0]["sha256"]="0"*64;q.write_text(json.dumps(m))
    rejects(lambda:verify_stage(work,q))
    m=copy.deepcopy(r);m["overlay"][0]["replacement_git_blob"]="0"*40;q.write_text(json.dumps(m))
    rejects(lambda:verify_stage(work,q))
    p=work/"unexpected.olean"
    require(not p.exists(),"control path already exists")
    try:
        p.write_bytes(b"not a proof object")
        rejects(lambda:verify_stage(work,receipt))
    finally:p.unlink()
verify_stage(work,receipt)
print("NATIVE_R4_STAGE_CONTROLS_PASS 9")
