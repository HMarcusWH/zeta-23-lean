#!/usr/bin/env python3
"""Deterministic, attributed source port. NO Lean execution or claim promotion."""
import argparse, hashlib, json, pathlib, re, shutil, subprocess, sys
from extract_all import LOCK, CUTS, cut, imports, module, walk, blob, require, dump
P=pathlib.Path
HERE=P(__file__).resolve().parent
PREFIX="Zeta23Arithmetic"
BASE="2fe4a756e8576203cfb009314861616accdb6dde"
BASE_TREE="4571fe6cc82466115beae5bea5037071ebec3524"
CUT_SHA="c433d27ea109809ed7be4e75513714d3edc18bad9f0a578435644742aba5152e"
MATHLIB="56a005855ea17e0b0958f73ec801ae140b0a1679"
ROOT="New.ArithmeticOnly"
BANNED={"Main","Statements","Challenge","New.Main","New.Reduction.OneSidedBound"}
LOCKMAP={r["path"]:r for r in LOCK["blobs"]}
NOTICE='/-\nCopyright 2026 Anthropic, PBC. Apache License, Version 2.0.\nAdapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,\ncommit 72fead102f663d5c7a407964a13dc0cf9d977207.\nModified: relocated module imports into Zeta23Arithmetic; declarations and\nproof bodies retained. ArithmeticOnly additionally omits the final endpoints.\nOriginal license, notice, and attribution in this directory tree.\n-/\n'
IMP=re.compile(r"(?m)^import ((?:Lib|New)\.[A-Za-z0-9_.]+)(?=\s|$)")
REV=re.compile(r"(?m)^import Zeta23Arithmetic\.((?:Lib|New)\.[A-Za-z0-9_.]+)(?=\s|$)")
def sha(b):return hashlib.sha256(b).hexdigest()
def git(root,*args):return subprocess.check_output(["git","-C",str(root),*args])
def mapping(m):return PREFIX+"."+m if m.startswith(("Lib.","New.")) else m
def rewrite(t):
    z=NOTICE+IMP.sub(lambda m:"import "+PREFIX+"."+m.group(1),t)
    require(imports(z)==[mapping(m) for m in imports(t)],"unexpected import transform")
    require(undo(z)==t,"nonreversible source rewrite")
    return z
def undo(t):
    require(t.startswith(NOTICE),"missing source port notice")
    return REV.sub(lambda m:"import "+m.group(1),t[len(NOTICE):])
def write(path,b):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(b)
def module_path(m):return P(PREFIX)/P(*m.split(".")).with_suffix(".lean")
def verify_files(out):
    manifest=json.loads((out/"verification/opica-native-terminal/PORT_MANIFEST.json").read_text())
    require(manifest["supplier_commit"]==LOCK["commit"] and manifest["supplier_tree"]==LOCK["tree"],"supplier manifest drift")
    require(manifest["native_base"]==BASE and manifest["native_tree"]==BASE_TREE,"native manifest drift")
    rows=manifest["modules"]
    require(len(rows)==792 and len({r["module"] for r in rows})==792,"wrong module count")
    graph={}
    for r in rows:
        p=out/r["destination"]
        require(p==out/module_path(r["module"]),"destination drift")
        b=p.read_bytes()
        require(sha(b)==r["port_sha256"],"ported byte drift "+str(p))
        raw=undo(b.decode()).encode()
        require(sha(raw)==r["original_or_cut_sha256"],"inverse byte drift "+str(p))
        original="grh-compact/src/"+("New/Main.lean" if r["module"]==ROOT else r["module"].replace(".","/")+".lean")
        require(r["original_path"]==original and r["original_git_blob"]==LOCKMAP[original]["sha"],"original blob identity drift")
        if r["module"]==ROOT:
            require(sha(raw)==CUT_SHA,"arithmetic cut drift")
        else:
            require(blob(raw)==LOCKMAP[original]["sha"] and len(raw)==LOCKMAP[original]["size"],"proof body altered "+str(p))
        graph[mapping(r["module"])]=imports(b.decode())
    for p in (out/PREFIX).rglob("*.lean"):
        require(p==out/PREFIX/"NativePrincipal.lean" or p.relative_to(out).as_posix() in {r["destination"] for r in rows},"unexpected Lean source")
    require(not BANNED.intersection(r["module"] for r in rows),"terminal source included")
    order=walk(mapping(ROOT),graph)
    require(len(order)==792,"incomplete source import closure")
    for name in ("LICENSE","NOTICE","ATTRIBUTION.md","REFERENCES.md","GUIDE.md"):
        p=out/PREFIX/name
        origin="LICENSE" if name=="LICENSE" else "grh-compact/"+name
        require(blob(p.read_bytes())==LOCKMAP[origin]["sha"],"attribution drift "+name)
    for p in ("Zeta23Arithmetic/NativePrincipal.lean","Zeta23/OPICANativeTerminal/Terminal.lean"):
        require(sha((out/p).read_bytes())==manifest["new_source"][p],"new source drift "+p)
    require(imports((out/PREFIX/"NativePrincipal.lean").read_text())==[mapping(ROOT)],"principal import drift")
    require(imports((out/"Zeta23/OPICANativeTerminal/Terminal.lean").read_text())[0]==PREFIX+".NativePrincipal","terminal import drift")
    print("NATIVE_PORT_SOURCE_PASS",len(rows),"exact inverse proof body checks",flush=True)
    return manifest
def generate(original,out):
    require(git(original,"rev-parse","HEAD").decode().strip()==LOCK["commit"],"upstream commit drift")
    require(git(original,"rev-parse","HEAD^{tree}").decode().strip()==LOCK["tree"],"upstream tree drift")
    require(not git(original,"status","--porcelain","--untracked-files=no").strip(),"dirty source")
    for p,r in LOCKMAP.items():
        b=(original/p).read_bytes()
        require(len(b)==r["size"] and blob(b)==r["sha"],"source custody mismatch "+p)
    src=original/"grh-compact/src"
    files={module(p.relative_to(src).as_posix()):p for p in src.rglob("*.lean")}
    graph={m:imports(p.read_text(encoding="utf-8")) for m,p in files.items()}
    prefix=cut((src/"New/Main.lean").read_text(encoding="utf-8"),"grh-compact")
    require(sha(prefix.encode())==CUT_SHA,"frozen cut changed")
    graph[ROOT]=imports(prefix)
    order=walk(ROOT,graph)
    require(len(order)==792 and not BANNED.intersection(order),"wrong arithmetic cut")
    require(not out.exists(),"output exists")
    out.mkdir(parents=True)
    rows=[]
    for m in order:
        original_file=src/"New/Main.lean" if m==ROOT else files[m]
        raw=prefix if m==ROOT else original_file.read_text(encoding="utf-8")
        b=rewrite(raw).encode()
        destination=module_path(m)
        write(out/destination,b)
        rows.append({"module":m,"destination":destination.as_posix(),"original_path":original_file.relative_to(original).as_posix(),
          "original_git_blob":blob(original_file.read_bytes()),"original_or_cut_sha256":sha(raw.encode()),"port_sha256":sha(b)})
    for name in ("NOTICE","ATTRIBUTION.md","REFERENCES.md","GUIDE.md"):
        shutil.copy2(original/"grh-compact"/name,out/PREFIX/name)
    shutil.copy2(original/"LICENSE",out/PREFIX/"LICENSE")
    (out/PREFIX/"PORT_NOTICE.md").write_text(
       "# Native arithmetic source port\n\nAttributed source relocation of the compact arithmetic proof at "+LOCK["commit"]+
       ". The upstream final RH/GRH declarations are omitted. Proof bodies are unchanged except the exact arithmetic cut; imports are relocated. Declaration names are retained for proof compatibility. This is not an independent rediscovery of the arithmetic. All Apache notices and attribution preserved.\n")
    new={}
    for name,dest in (("PrincipalStrip.lean","Zeta23Arithmetic/NativePrincipal.lean"),("Terminal.lean","Zeta23/OPICANativeTerminal/Terminal.lean")):
        b=(HERE/name).read_bytes();write(out/dest,b);new[dest]=sha(b)
    manifest_path=out/"verification/opica-native-terminal/PORT_MANIFEST.json"
    manifest_path.parent.mkdir(parents=True,exist_ok=True)
    dump(manifest_path,{"schema":"NATIVE_COMPACT_SOURCE_PORT_V1","supplier_commit":LOCK["commit"],"supplier_tree":LOCK["tree"],
       "native_base":BASE,"native_tree":BASE_TREE,"modules":rows,"new_source":new,"claim":"RH_OPEN",
       "proof_body_policy":"reverse import relocation then verify exact original blob; arithmetic cut frozen SHA256",
       "proof_kernel":"NOT_RUN"})
    verify_files(out)
if __name__=="__main__":
    a=argparse.ArgumentParser()
    a.add_argument("--original",type=P)
    a.add_argument("--out",type=P,required=True)
    a.add_argument("--verify-only",action="store_true")
    args=a.parse_args()
    if args.verify_only:verify_files(args.out.resolve())
    else:
        require(args.original is not None,"original required for one-time source port")
        generate(args.original.resolve(),args.out.resolve())
