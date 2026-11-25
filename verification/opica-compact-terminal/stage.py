#!/usr/bin/env python3
"""Stage only pinned source. No old arithmetic, no .olean transfer."""
import argparse, hashlib, io, json, pathlib, re, shutil, subprocess, tarfile, tempfile
from extract_all import LOCK, CUTS, cut, imports, module, walk, blob, require, dump
P=pathlib.Path
HERE=P(__file__).resolve().parent
NATIVE="2fe4a756e8576203cfb009314861616accdb6dde"
NATIVE_TREE="4571fe6cc82466115beae5bea5037071ebec3524"
MATHLIB="56a005855ea17e0b0958f73ec801ae140b0a1679"
BANNED={"Main","Statements","Challenge","New.Main","New.Reduction.OneSidedBound"}
def git(root,*args):
    return subprocess.check_output(["git","-C",str(root),*args])
def file_sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def stage(native,original,out,receipt):
    require(LOCK["native"]["commit"]==NATIVE and LOCK["native"]["tree"]==NATIVE_TREE,"native lock metadata mismatch")
    require(git(native,"rev-parse",NATIVE+"^{tree}").decode().strip()==NATIVE_TREE,"native parent tree mismatch")
    require(git(original,"rev-parse","HEAD").decode().strip()==LOCK["commit"],"upstream commit mismatch")
    require(git(original,"rev-parse","HEAD^{tree}").decode().strip()==LOCK["tree"],"upstream tree mismatch")
    require(not git(original,"status","--porcelain","--untracked-files=no").strip(),"dirty supplier")
    require(not out.exists(),"staging output already exists")
    out.mkdir(parents=True)
    # Byte-authenticate all upstream tracked files, not just selected roots.
    rows=[]
    for r in LOCK["blobs"]:
        b=(original/r["path"]).read_bytes()
        require(len(b)==r["size"] and blob(b)==r["sha"],"upstream byte mismatch "+r["path"])
        rows.append({"path":r["path"],"git_blob":r["sha"],"sha256":hashlib.sha256(b).hexdigest()})
    base=original/"grh-compact"; src=base/"src"
    graph={}; bymod={}
    for p in sorted(src.rglob("*.lean")):
        m=module(p.relative_to(src).as_posix())
        bymod[m]=p; graph[m]=imports(p.read_text(encoding="utf-8"))
    old,new,_,_,_=CUTS["grh-compact"]
    prefix=cut((src/old).read_text(encoding="utf-8"),"grh-compact")
    root=module(new); graph[root]=imports(prefix)
    order=walk(root,graph)
    require(len(order)==792,"unexpected arithmetic source cone")
    require(not BANNED.intersection(order),"terminal source imported")
    supplier=out/"supplier"; (supplier/"src").mkdir(parents=True)
    for m in order:
        if m==root:continue
        f=bymod[m]; p=supplier/"src"/f.relative_to(src)
        p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,p)
    p=supplier/"src"/new;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(prefix,encoding="utf-8")
    shutil.copy2(HERE/"PrincipalStrip.lean",supplier/"src/New/PrincipalStrip.lean")
    for name in ("lean-toolchain","lake-manifest.json","NOTICE","ATTRIBUTION.md","REFERENCES.md","GUIDE.md"):
        shutil.copy2(base/name,supplier/name)
    shutil.copy2(original/"LICENSE",supplier/"LICENSE")
    config=(base/"lakefile.toml").read_text()
    config=re.sub(r'(?m)^defaultTargets\s*=.*$', 'defaultTargets = ["Lib", "New"]',config)
    config=config.split('\n[[lean_lib]]\nname = "Main"',1)[0].rstrip()+"\n"
    require('name = "Main"' not in config and 'name = "Challenge"' not in config,"terminal lake targets")
    (supplier/"lakefile.toml").write_text(config)
    (supplier/"OPICA_MODIFICATIONS.md").write_text(
       "Source slice of lsernau/grh-lean at "+LOCK["commit"]+". New.ArithmeticOnly cuts New.Main before the terminal declarations; import Statements replaced with Mathlib. New.PrincipalStrip is a new attributed fixed-exponent adapter. Copyright notices and Apache-2.0 retained. No upstream endpoint proof imported.\n")
    # All native bytes come from #316, not #317 or a moving PR head.
    data=git(native,"archive",NATIVE,"Zeta23","Zeta23.lean")
    with tarfile.open(fileobj=io.BytesIO(data)) as tar:tar.extractall(out,filter="data")
    require(not (out/"Zeta23/OPICATerminal").exists(),"old analytic ports present")
    native_rows=[]
    for record in git(native,"ls-tree","-rz","-l",NATIVE,"Zeta23","Zeta23.lean").split(b"\0"):
        if not record:continue
        meta,raw=record.split(b"\t",1); mode,typ,ident,size=meta.decode().split()
        path=raw.decode(); p=out/path
        require(typ=="blob" and p.is_file(),"unexpected native object "+path)
        b=p.read_bytes();require(blob(b)==ident and len(b)==int(size),"native blob mismatch "+path)
        native_rows.append({"path":path,"git_blob":ident,"sha256":hashlib.sha256(b).hexdigest()})
    dst=out/"Zeta23/OPICACompactTerminal";dst.mkdir()
    shutil.copy2(HERE/"Terminal.lean",dst/"Terminal.lean")
    shutil.copy2(HERE/"Audit.lean",out/"AuditCompactTerminal.lean")
    # Native package options kept separate from supplier options.
    (out/"lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (out/"lakefile.toml").write_text('''name = "Zeta23"
version = "0.1.0"
defaultTargets = ["Zeta23"]
moreLeanArgs = ["--tstack=400000"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
maxHeartbeats = 800000

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "56a005855ea17e0b0958f73ec801ae140b0a1679"

[[require]]
name = "GRH"
path = "supplier"

[[lean_lib]]
name = "Zeta23"
''')
    manifest=json.loads((base/"lake-manifest.json").read_text())
    require(next(p for p in manifest["packages"] if p["name"]=="mathlib")["rev"]==MATHLIB,"Mathlib pin mismatch")
    manifest["name"]="Zeta23"
    manifest["packages"].append({"type":"path","dir":"supplier","copy":False,"scope":"","name":"GRH",
      "configFile":"lakefile.toml","manifestFile":"lake-manifest.json","inherited":False})
    dump(out/"lake-manifest.json",manifest)
    dump(receipt,{"schema":"COMPACT_TERMINAL_SOURCE_V1","native_head":NATIVE,"native_tree":NATIVE_TREE,
      "supplier_head":LOCK["commit"],"supplier_tree":LOCK["tree"],"native_files":native_rows,
      "supplier_files":rows,"arithmetic_modules":order,"mathlib":MATHLIB,
      "staged_files":[{"path":p.relative_to(out).as_posix(),"sha256":file_sha(p)}
        for p in sorted(out.rglob("*")) if p.is_file()],
      "formal_status":"NOT_RUN","claim":"RH_OPEN"})
    print("COMPACT_SOURCE_STAGE_PASS",len(native_rows),len(rows),len(order),flush=True)

def verify_pins(work):
    m=json.loads((work/"lake-manifest.json").read_text())
    original=json.loads((work/"supplier/lake-manifest.json").read_text())
    expected={p["name"]:p["rev"] for p in original["packages"]}
    actual={p["name"]:p["rev"] for p in m["packages"] if p["type"]=="git"}
    require(expected==actual,"package set/pin drift")
    for name,rev in expected.items():
        p=work/".lake/packages"/name
        require(git(p,"rev-parse","HEAD").decode().strip()==rev,"checkout drift "+name)
    require((work/"lean-toolchain").read_text().strip()=="leanprover/lean4:v4.35.0","toolchain drift")
    require((work/"supplier/lean-toolchain").read_text().strip()=="leanprover/lean4:v4.35.0","supplier toolchain drift")
    print("COMPACT_COMMON_PIN_PASS",json.dumps(expected,sort_keys=True))

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--native",type=P);ap.add_argument("--original",type=P)
    ap.add_argument("--out",type=P);ap.add_argument("--receipt",type=P)
    ap.add_argument("--verify-pins",type=P)
    a=ap.parse_args()
    if a.verify_pins:verify_pins(a.verify_pins.resolve())
    else:
        require(all([a.native,a.original,a.out,a.receipt]),"missing source staging args")
        stage(a.native.resolve(),a.original.resolve(),a.out.resolve(),a.receipt.resolve())
