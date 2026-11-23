"""Independent selected closure at the native source pin; no historical-type promotion."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

def independent(repo, output, checker_work, checker_code, roots, lean_path):
    from check_candidate import need, PRIMITIVES, run
    sys.path.insert(0, str(checker_code))
    from common import (CHECKER_HEAD, RUNTIME_SHA, RUNTIME_BYTES, clean_env, clean_checkout,
                        file_inventory, verify_file_inventory, read_json, sha, git, run as bounded)
    from independent_38 import acceptance
    boot = read_json(checker_work/"BOOTSTRAP_RECEIPT.json")
    need(boot["status"] == "PASS" and boot["source_head"] == CHECKER_HEAD and
         boot["runtime_archive_sha256"] == RUNTIME_SHA and boot["runtime_archive_bytes"] == RUNTIME_BYTES,
         "Fresh independent checker bootstrap required")
    runtime = Path(boot["runtime"]).resolve()
    checker = Path(boot["source"]).resolve()
    binary = Path(boot["tools"]["con-leche"]["path"]).resolve()
    clean_checkout(checker, CHECKER_HEAD)
    need(binary == checker/".lake/build/bin/con-leche" and sha(binary) == boot["tools"]["con-leche"]["sha256"],
         "Checker binary identity differs")
    src = read_json(Path(boot["source_inventory"]))
    runtime_files = read_json(Path(boot["runtime_inventory"]))
    need(sha(Path(boot["source_inventory"])) == boot["source_inventory_sha256"] and
         sha(Path(boot["runtime_inventory"])) == boot["runtime_inventory_sha256"] and
         {n: sha(checker/n) for n in git(checker,"ls-files").splitlines()} == src,
         "Checker source inventory differs")
    verify_file_inventory(runtime, runtime_files)
    native_prefix = Path(run("lake", "env", "lean", "--print-prefix")).resolve()
    core = native_prefix/"lib/lean"
    paths = [Path(p).resolve() for p in lean_path.split(os.pathsep) if p]
    if core not in paths:
        paths.append(core)
    need(len(paths) == len(set(paths)) and all(p.is_dir() for p in paths), "Invalid native import root inventory")
    # Only the isolated audit module is added to the native proof import roots.
    audit_root = output/"audit-object"
    audit_root.mkdir()
    for source in output.glob("OPICASupportAudit.olean*"):
        (audit_root/source.name).write_bytes(source.read_bytes())
    need((audit_root/"OPICASupportAudit.olean").is_file(), "Audit module object absent")
    paths.insert(0,audit_root)
    manifests = {str(p): file_inventory(p) for p in paths}
    (output/"INDEPENDENT_OBJECT_INVENTORY.json").write_text(json.dumps(manifests, indent=2)+"\n")
    # Negative controls use the exact independent checker executable with its own pinned runtime.
    env=clean_env(runtime,1)
    fixture=output/"independent-fixture";fixture.mkdir()
    f=fixture/"ClosureControl.lean"
    f.write_text("namespace ClosureControl\naxiom uncheckedLeaf : False\ntheorem selectedRoot : False := uncheckedLeaf\ntheorem unrelatedRoot : True := True.intro\nend ClosureControl\n")
    bounded("fixture_compile",[runtime/"bin/lean","--root="+str(fixture),"-o",fixture/"ClosureControl.olean",f],
        cwd=fixture,env=env,output=output,timeout=120,memory_mib=2048)
    common=[binary,"--verified","--jobs=1","--progress=30s","--olean",
            "--search-path="+str(fixture)+os.pathsep+str(runtime/"lib/lean")]
    _, good=bounded("control_unused_axiom",[*common,"--constant=ClosureControl.unrelatedRoot","ClosureControl"],
        cwd=fixture,env=env,output=output,timeout=300,memory_mib=2048)
    acceptance(good,1)
    _, bad=bounded("control_transitive_axiom",[*common,"--constant=ClosureControl.selectedRoot","ClosureControl"],
        cwd=fixture,env=env,output=output,timeout=300,memory_mib=2048,expected=2)
    need("not implemented yet: non-standard axiom (ClosureControl.uncheckedLeaf)" in bad and "con-leche: accepted " not in bad, "Axiom negative control failed")
    _, bad=bounded("control_missing_root",[*common,"--constant=ClosureControl.absentRoot","ClosureControl"],
        cwd=fixture,env=env,output=output,timeout=300,memory_mib=2048,expected=3)
    need("the constant ClosureControl.absentRoot is not in the import closure" in bad and "con-leche: accepted " not in bad, "Missing root control failed")
    selected = list(PRIMITIVES)+list(roots)
    need(len(selected)==len(set(selected))==201, "Selected root inventory differs")
    _, log=bounded("independent_selected_201",[binary,"--verified","--jobs=1","--progress=30s","--olean",
        "--search-path="+os.pathsep.join(map(str,paths)),*["--constant="+n for n in selected],"OPICASupportAudit"],
        cwd=output,env=env,output=output,timeout=9000,memory_mib=10000)
    count=acceptance(log,len(selected),complete_prelude=True)
    need({str(p):file_inventory(p) for p in paths}==manifests, "Native input objects changed")
    verify_file_inventory(runtime,runtime_files)
    clean_checkout(checker,CHECKER_HEAD)
    need(sha(binary)==boot["tools"]["con-leche"]["sha256"] and
         {n:sha(checker/n) for n in git(checker,"ls-files").splitlines()}==src,"Checker changed")
    return {"status":"PASS_INDEPENDENT_SELECTED_NATIVE_CLOSURE_ONLY","selected_roots":selected,
            "accepted_declaration_records":count,"checker_head":CHECKER_HEAD,
            "checker_binary_sha256":sha(binary),"all_bound_inputs_rehashed":True,
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN",
            "historical_type_equivalence":"REVIEW_PENDING"}
