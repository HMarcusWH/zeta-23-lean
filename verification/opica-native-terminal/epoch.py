#!/usr/bin/env python3
"""Build only repository-committed native source under one stock Lake project.
No supplier clone, package dependency, prior project .olean, or source regeneration.
"""
import argparse, hashlib, io, json, pathlib, shutil, subprocess, tarfile
from port import verify_files, require, git, BASE, BASE_TREE, MATHLIB, HERE, PREFIX, sha
P=pathlib.Path
CONFIG='''name = "Zeta23"
version = "0.1.0"
defaultTargets = ["Zeta23Arithmetic", "Zeta23NativeTerminal"]
moreLeanArgs = ["--tstack=400000"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
maxHeartbeats = 800000

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "56a005855ea17e0b0958f73ec801ae140b0a1679"

[[lean_lib]]
name = "Zeta23"
roots = ["Zeta23"]
globs = ["Zeta23"]

[[lean_lib]]
name = "Zeta23Arithmetic"
roots = ["Zeta23Arithmetic"]
globs = ["Zeta23Arithmetic.+"]
leanOptions = { autoImplicit = false, relaxedAutoImplicit = false, maxSynthPendingDepth = 3, maxHeartbeats = 4000000, pp.unicode.fun = true }

[[lean_lib]]
name = "Zeta23NativeTerminal"
roots = ["Zeta23.OPICANativeTerminal.Terminal"]
globs = ["Zeta23.OPICANativeTerminal.Terminal"]
'''
def stage(repo,out,receipt,head):
    require(git(repo,"rev-parse","HEAD").decode().strip()==head,"checkout HEAD drift")
    require(git(repo,"rev-parse",BASE+"^{tree}").decode().strip()==BASE_TREE,"base tree drift")
    require(not git(repo,"status","--porcelain","--untracked-files=no").strip(),"dirty repository")
    manifest=verify_files(repo)
    require(not out.exists(),"epoch already exists")
    out.mkdir(parents=True)
    # All native pre-existing proof bytes are retained verbatim.
    changed=git(repo,"diff","--name-only",BASE,head,"--","Zeta23","Zeta23.lean").decode().splitlines()
    require(changed==["Zeta23/OPICANativeTerminal/Terminal.lean"],"preexisting native math modified: "+str(changed))
    data=git(repo,"archive",head,"Zeta23","Zeta23.lean",PREFIX)
    with tarfile.open(fileobj=io.BytesIO(data)) as t:t.extractall(out,filter="data")
    require(not (out/"supplier").exists() and not (out/"Lib").exists() and not (out/"New").exists(),"non-native layout")
    (out/"lakefile.toml").write_text(CONFIG)
    (out/"lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    m=json.loads((HERE/"MATHLIB_MANIFEST.json").read_text())
    require(next(p for p in m["packages"] if p["name"]=="mathlib")["rev"]==MATHLIB,"mathlib pin drift")
    require(all(p["type"]=="git" for p in m["packages"]),"nonstandard package dependency")
    m["name"]="Zeta23"
    (out/"lake-manifest.json").write_text(json.dumps(m,indent=2)+"\n")
    shutil.copy2(HERE/"Audit.lean",out/"AuditNativeTerminal.lean")
    files=[{"path":p.relative_to(out).as_posix(),"sha256":sha(p.read_bytes())} for p in sorted(out.rglob("*")) if p.is_file()]
    receipt.write_text(json.dumps({"schema":"NATIVE_TERMINAL_EPOCH_V1","head":head,
      "tree":git(repo,"rev-parse","HEAD^{tree}").decode().strip(),"native_base":BASE,"supplier_attribution":manifest["supplier_commit"],
      "package_count":1,"external_project_packages":0,"mathlib":MATHLIB,"files":files,"claim":"RH_OPEN"},indent=2)+"\n")
    print("NATIVE_COMMITTED_EPOCH_STAGE_PASS",head,len(files))
def pins(out):
    actual=json.loads((out/"lake-manifest.json").read_text())
    expected=json.loads((HERE/"MATHLIB_MANIFEST.json").read_text())
    p1={p["name"]:p["rev"] for p in actual["packages"]}
    p2={p["name"]:p["rev"] for p in expected["packages"]}
    require(p1==p2 and all(p["type"]=="git" for p in actual["packages"]),"unexpected package or pin")
    for n,r in p2.items():require(git(out/".lake/packages"/n,"rev-parse","HEAD").decode().strip()==r,"dependency drift "+n)
    require((out/"lean-toolchain").read_text().strip()=="leanprover/lean4:v4.35.0","toolchain drift")
    print("NATIVE_COMMON_PIN_PASS",p2)
if __name__=="__main__":
    a=argparse.ArgumentParser();a.add_argument("--repo",type=P);a.add_argument("--out",type=P,required=True);a.add_argument("--receipt",type=P);a.add_argument("--head");a.add_argument("--verify-pins",action="store_true")
    x=a.parse_args()
    if x.verify_pins:pins(x.out.resolve())
    else:stage(x.repo.resolve(),x.out.resolve(),x.receipt.resolve(),x.head)
