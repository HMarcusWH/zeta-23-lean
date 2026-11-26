#!/usr/bin/env python3
"""Stage one exact committed repair epoch. No supplier clone or project olean import."""
import argparse, copy, hashlib, io, json, pathlib, shutil, subprocess, tarfile
from port import verify_files, require, git, BASE, BASE_TREE, MATHLIB, HERE, PREFIX, sha, blob
P=pathlib.Path
REPAIR_PARENT="b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736"
REPAIR_PARENT_TREE="ad3dc3ced9a58dbd4619f8635600791a692bce34"
REPAIR_PATH="verification/opica-native-terminal/REPAIR_MANIFEST.json"
PORT_PATH="verification/opica-native-terminal/PORT_MANIFEST.json"
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
def object_at(repo,rev,path):
    r=subprocess.run(["git","-C",str(repo),"rev-parse","--verify",rev+":"+path],
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    return r.stdout.strip() if r.returncode==0 else None
def validate_scope(repo,head,m):
    require(m["schema"]=="OPICA_NATIVE_REPAIR_MANIFEST_V1","bad repair manifest schema")
    require(m["baseline_commit"]==REPAIR_PARENT and m["baseline_tree"]==REPAIR_PARENT_TREE,"repair baseline mismatch")
    require(git(repo,"rev-parse",REPAIR_PARENT+"^{tree}").decode().strip()==REPAIR_PARENT_TREE,"repair baseline tree drift")
    require(git(repo,"rev-parse",BASE+"^{tree}").decode().strip()==BASE_TREE,"native base tree drift")
    require(m["claim"]=="RH_OPEN","invalid claim promotion")
    rows=m["changes"]
    paths=[r["path"] for r in rows]
    require(len(paths)==len(set(paths)) and REPAIR_PATH not in paths,"duplicate/self-referential repair path")
    changed=set(git(repo,"diff","--name-only",REPAIR_PARENT,head).decode().splitlines())
    require(changed==set(paths)|{REPAIR_PATH},"repair scope drift: "+str(sorted(changed.symmetric_difference(set(paths)|{REPAIR_PATH}))))
    adapters={}
    for r in rows:
        p=r["path"]
        require(p.startswith(("Zeta23/","Zeta23Arithmetic/","verification/opica-native-terminal/",".github/workflows/opica-native-step4.yml")),"unexpected scope "+p)
        require(not p.startswith("Zeta23Arithmetic/") or p=="Zeta23Arithmetic/NativePrincipal.lean","frozen arithmetic edit "+p)
        require(p!=PORT_PATH,"original port manifest must remain frozen")
        require(object_at(repo,REPAIR_PARENT,p)==r["old_git_blob"],"baseline blob drift "+p)
        require(object_at(repo,head,p)==r["new_git_blob"] and r["new_git_blob"] is not None,"repaired blob drift "+p)
        require(blob((repo/p).read_bytes())==r["new_git_blob"],"working tree byte drift "+p)
        require(bool(r["reason"]) and r["statement_policy"] in {"PRESERVE","RETIRED_TACTIC_ENGINE","VERIFICATION_ONLY"},"unclassified repair "+p)
        if p in {"Zeta23Arithmetic/NativePrincipal.lean","Zeta23/OPICANativeTerminal/Terminal.lean"}:adapters[p]=r["new_git_blob"]
    require(git(repo,"show",REPAIR_PARENT+":"+PORT_PATH)==(repo/PORT_PATH).read_bytes(),"original port manifest modified")
    require(git(repo,"diff","--name-only",BASE,REPAIR_PARENT,"--","Zeta23","Zeta23.lean").decode().splitlines()==["Zeta23/OPICANativeTerminal/Terminal.lean"],"baseline native math drift")
    require((repo/"Zeta23Arithmetic/NativePrincipal.lean").read_bytes()==(HERE/"PrincipalStrip.lean").read_bytes(),"principal template drift")
    return adapters
def test_scope(repo,head):
    m=json.loads((repo/REPAIR_PATH).read_text())
    validate_scope(repo,head,m)
    mutations=[]
    a=copy.deepcopy(m);a["changes"].append(copy.deepcopy(a["changes"][0]));mutations.append(a)
    a=copy.deepcopy(m);a["changes"][0]["new_git_blob"]="0"*40;mutations.append(a)
    a=copy.deepcopy(m);a["changes"].pop();mutations.append(a)
    a=copy.deepcopy(m);a["baseline_tree"]="0"*40;mutations.append(a)
    a=copy.deepcopy(m);a["claim"]="RH_PROVED";mutations.append(a)
    for i,a in enumerate(mutations):
        try:validate_scope(repo,head,a)
        except (RuntimeError,ValueError,KeyError,subprocess.CalledProcessError):pass
        else:raise RuntimeError("scope negative control accepted "+str(i))
    print("NATIVE_REPAIR_SCOPE_CONTROLS_PASS",len(mutations),flush=True)
def stage(repo,out,receipt,head):
    require(git(repo,"rev-parse","HEAD").decode().strip()==head,"checkout HEAD drift")
    require(not git(repo,"status","--porcelain","--untracked-files=no").strip(),"dirty repository")
    m=json.loads((repo/REPAIR_PATH).read_text())
    adapters=validate_scope(repo,head,m)
    manifest=verify_files(repo,adapters)
    require(not out.exists(),"epoch already exists")
    out.mkdir(parents=True)
    data=git(repo,"archive",head,"Zeta23","Zeta23.lean",PREFIX)
    with tarfile.open(fileobj=io.BytesIO(data)) as t:t.extractall(out,filter="data")
    require(not any((out/p).exists() for p in ("supplier","Lib","New",".lake")),"non-native layout")
    (out/"lakefile.toml").write_text(CONFIG)
    (out/"lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    mlib=json.loads((HERE/"MATHLIB_MANIFEST.json").read_text())
    require(next(p for p in mlib["packages"] if p["name"]=="mathlib")["rev"]==MATHLIB,"mathlib pin drift")
    require(all(p["type"]=="git" for p in mlib["packages"]),"nonstandard package dependency")
    mlib["name"]="Zeta23"
    (out/"lake-manifest.json").write_text(json.dumps(mlib,indent=2)+"\n")
    for src,dst in (("Audit.lean","AuditNativeTerminal.lean"),("AuditSmoke.lean","AuditSmoke.lean"),
        ("AuditArithmetic.lean","AuditArithmetic.lean"),("AuditNativeFrontier.lean","AuditNativeFrontier.lean")):
        shutil.copy2(HERE/src,out/dst)
    files=[{"path":p.relative_to(out).as_posix(),"sha256":sha(p.read_bytes())} for p in sorted(out.rglob("*")) if p.is_file()]
    receipt.parent.mkdir(parents=True,exist_ok=True)
    receipt.write_text(json.dumps({"schema":"NATIVE_TERMINAL_REPAIR_EPOCH_V1","head":head,
      "tree":git(repo,"rev-parse","HEAD^{tree}").decode().strip(),"native_base":BASE,
      "repair_baseline":REPAIR_PARENT,"repair_manifest_sha256":sha((repo/REPAIR_PATH).read_bytes()),
      "original_port_manifest_sha256":sha((repo/PORT_PATH).read_bytes()),
      "supplier_attribution":manifest["supplier_commit"],"package_count":1,
      "external_project_packages":0,"mathlib":MATHLIB,"files":files,"claim":"RH_OPEN"},indent=2)+"\n")
    print("NATIVE_REPAIRED_EPOCH_STAGE_PASS",head,len(files),flush=True)
def pins(out):
    actual=json.loads((out/"lake-manifest.json").read_text())
    expected=json.loads((HERE/"MATHLIB_MANIFEST.json").read_text())
    p1={p["name"]:p["rev"] for p in actual["packages"]}
    p2={p["name"]:p["rev"] for p in expected["packages"]}
    require(p1==p2 and all(p["type"]=="git" for p in actual["packages"]),"unexpected package or pin")
    for n,r in p2.items():require(git(out/".lake/packages"/n,"rev-parse","HEAD").decode().strip()==r,"dependency drift "+n)
    require((out/"lean-toolchain").read_text().strip()=="leanprover/lean4:v4.35.0","toolchain drift")
    print("NATIVE_COMMON_PIN_PASS",p2,flush=True)
if __name__=="__main__":
    a=argparse.ArgumentParser();a.add_argument("--repo",type=P);a.add_argument("--out",type=P);a.add_argument("--receipt",type=P);a.add_argument("--head");a.add_argument("--verify-pins",action="store_true");a.add_argument("--self-test",action="store_true")
    x=a.parse_args()
    if x.verify_pins:pins(x.out.resolve())
    elif x.self_test:test_scope(x.repo.resolve(),x.head)
    else:stage(x.repo.resolve(),x.out.resolve(),x.receipt.resolve(),x.head)
