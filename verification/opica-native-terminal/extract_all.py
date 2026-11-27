#!/usr/bin/env python3
"""Exact source custody + lexical navigation + endpoint-free source cuts.
This is NOT a Lean parser, proof dependency exporter, or compiler receipt.
"""
import argparse, collections, csv, hashlib, io, json, pathlib, re, shutil, subprocess, tarfile
P = pathlib.Path
HERE = P(__file__).resolve().parent
LOCK = json.loads((HERE / "SOURCE_TREE_LOCK.json").read_text())
CUTS = {
    "grh-compact": ("New/Main.lean", "New/ArithmeticOnly.lean",
        "/-- The generalised Riemann hypothesis for Dirichlet L-functions, in half-plane form:",
        "198ed5bf26aa294898931e0649bc2b88f1389f65", False),
    "grh": ("New/Reduction/OneSidedBound.lean", "New/Reduction/ArithmeticOnly.lean",
        "/-- **Main theorem**, in half-plane form:",
        "99e5240de112527b739068b692e5007720d310c1", True),
}
EXPECTED = {"grh": (803, 30050271), "grh-compact": (794, 7420187)}
BANNED = {"Main", "Statements", "Challenge", "New.Main", "New.Reduction.OneSidedBound"}
EXTERNAL = {"Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq", "ProofWidgets",
    "Plausible", "LeanSearchClient", "ImportGraph", "Cli", "Lake"}
def require(ok, msg):
    if not ok: raise RuntimeError(msg)
def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])
def sha(b):
    return hashlib.sha256(b).hexdigest()
def blob(b):
    return hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
def dump(path, obj):
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
def jsonlines(path, rows):
    with path.open("w", encoding="utf-8") as f:
        for r in rows: f.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
def mask(text):
    """Mask nested Lean comments and strings while preserving lines and character positions.
    Character literals with quotes are handled conservatively; this is lexical navigation only."""
    out=list(text); i=0; depth=0; string=False
    while i<len(text):
        c=text[i]; n=text[i:i+2]
        if depth:
            if n=="/-": out[i:i+2]="  "; depth+=1; i+=2; continue
            if n=="-/": out[i:i+2]="  "; depth-=1; i+=2; continue
            if c!="\n": out[i]=" "
        elif string:
            if c=="\\" and i+1<len(text):
                out[i]=" "
                if text[i+1]!="\n": out[i+1]=" "
                i+=2; continue
            if c=='"': string=False
            if c!="\n": out[i]=" "
        elif n=="--":
            j=text.find("\n",i)
            if j<0:j=len(text)
            out[i:j]=" "*(j-i);i=j;continue
        elif n=="/-":
            out[i:i+2]="  ";depth=1;i+=2;continue
        elif c=='"':
            out[i]=" ";string=True
        elif c=="'" and (i==0 or not (text[i-1].isalnum() or text[i-1] in "_'")):
            m=re.match(r"'(?:\\.|[^'\\\n])'",text[i:])
            if m:
                j=i+len(m.group(0));out[i:j]=" "*(j-i);i=j;continue
        i+=1
    # Some syntax quotations may contain unusual literal forms; do not treat
    # the declaration index as complete. Header parser below is separate.
    return "".join(out)
IMPORT=re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+?)\s*$")
MOD=re.compile(r"[\w\u00a0-\U0010ffff][\w\u00a0-\U0010ffff'.]*\Z")
DECL=re.compile(r"^\s*(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped|public|meta|opaque)\s+)*(theorem|lemma|def|abbrev|opaque|axiom|constant|structure|class|inductive|instance|example)\b(?:\s+([^\s({\[:=]+))?")
def module(path):
    return path.removesuffix(".lean").replace("/", ".")
def imports(text):
    # Lean module header, not a whole-file regex: avoid imports inside quotation or example.
    found=[]
    for line in mask(text).splitlines():
        s=line.strip()
        if not s:continue
        if s in {"module","prelude"}:continue
        m=IMPORT.fullmatch(line)
        if not m:break
        names=m.group(1).split()
        require(all(MOD.fullmatch(n) for n in names), f"unrecognized import header: {line!r}")
        found.extend(names)
    return list(dict.fromkeys(found))
def anchors(text):
    # Name tokens are candidates, not Lean elaborated names. Never use to authorize promotion.
    return [{"line":i,"kind":m.group(1),"name_token":m.group(2) or "",
        "source_line":text.splitlines()[i-1].strip()}
        for i,line in enumerate(mask(text).splitlines(),1) if (m:=DECL.match(line))]
def walk(root, graph):
    done=set(); visiting=set(); order=[]
    def visit(m):
        if m in done:return
        require(m not in visiting, f"local import cycle: {m}")
        visiting.add(m)
        for n in graph[m]:
            if n in graph:visit(n)
            else: require(n.split(".")[0] in EXTERNAL, f"unknown external import: {m} -> {n}")
        visiting.remove(m);done.add(m);order.append(m)
    visit(root)
    return order
def cut(text, edition):
    original,dest,marker,expected,close=CUTS[edition]
    require(blob(text.encode())==expected, "cut blob mismatch")
    require(text.count(marker)==1, "ambiguous terminal boundary")
    prefix=text.split(marker,1)[0]
    require(prefix.count("import Statements")==1,"Statements import drift")
    prefix=prefix.replace("import Statements","import Mathlib",1)
    if close:prefix=prefix.rstrip()+"\n\nend New\n"
    for pat in (r"(?m)^\s*(?:lemma|theorem)\s+(?:New\.)?grh\b",
        r"(?m)^\s*(?:lemma|theorem)\s+(?:New\.)?(?:zeros_on_line|zeta_zeros_on_line)\b",
        r"(?m)^\s*(?:lemma|theorem)\s+riemannHypothesis\b"):
        require(not re.search(pat,mask(prefix)),"terminal declaration retained")
    return prefix
def tests():
    require(imports(' /- outer /- import Bad -/ -/\nimport Mathlib\nimport New.X -- fake\n/- import X -/\ndef a := "import Evil"\n')==["Mathlib","New.X"],"comment/header control")
    require(imports("module\npublic import all Mathlib\nimport New.X\n")==["Mathlib","New.X"],"module header control")
    require(walk("A",{"A":["B","Mathlib"],"B":[]})==["B","A"],"closure control")
    for g in ({"A":["B"]},{"A":["A"]}):
        try:walk("A",g)
        except RuntimeError:pass
        else:raise RuntimeError("bad graph accepted")
    require([r["name_token"] for r in anchors(' /- theorem nope : True -/\ntheorem yes : True := by trivial\n')]==["yes"],"anchor control")
    print("SOURCE_EXTRACTION_CONTROLS_PASS")
def run(root,out):
    require(git(root,"rev-parse","HEAD").decode().strip()==LOCK["commit"],"commit mismatch")
    require(git(root,"rev-parse","HEAD^{tree}").decode().strip()==LOCK["tree"],"tree mismatch")
    require(not git(root,"status","--porcelain","--untracked-files=no").strip(),"dirty tracked source")
    out.mkdir(parents=True,exist_ok=True)
    actual=git(root,"ls-tree","-rz","-l","HEAD").split(b"\0")
    gitrows={}
    for row in actual:
        if not row:continue
        meta,path=row.split(b"\t",1); mode,typ,ident,size=meta.decode().split()
        require(typ=="blob",f"nonblob leaf {path!r}")
        gitrows[path.decode()]=(mode,ident,int(size))
    expected={r["path"]:(r["mode"],r["sha"],r["size"]) for r in LOCK["blobs"]}
    require(gitrows==expected,"source lock does not match local Git tree")
    files=[]
    for path,(mode,ident,size) in sorted(gitrows.items()):
        b=(root/path).read_bytes()
        require(len(b)==size and blob(b)==ident,f"byte custody mismatch {path}")
        files.append(dict(path=path,mode=mode,git_blob=ident,bytes=size,sha256=sha(b)))
    dump(out/"SOURCE_BYTE_MANIFEST.json",files)
    with (out/"grh-lean-pinned-source.tar.gz").open("wb") as f:
        subprocess.run(["git","-C",str(root),"archive","--format=tar.gz","--prefix=grh-lean/",LOCK["commit"]],stdout=f,check=True)
    results={}
    for edition in EXPECTED:
        base=root/edition; dest=out/edition;dest.mkdir()
        graph={}; bymod={}; rows=[]; allanchors=[]
        for file in sorted((base/"src").rglob("*.lean")):
            rel=file.relative_to(base/"src").as_posix(); m=module(rel); b=file.read_bytes(); t=b.decode("utf-8"); dep=imports(t); graph[m]=dep;bymod[m]=file
            cleaned=mask(t)
            aa=anchors(t)
            for a in aa:allanchors.append(dict(module=m,path=rel,**a))
            rows.append(dict(module=m,path=rel,git_blob=blob(b),sha256=sha(b),bytes=len(b),
                physical_lines=len(t.splitlines()),nonblank_lines=sum(bool(x.strip()) for x in t.splitlines()),
                lexical_code_lines=sum(bool(x.strip()) for x in cleaned.splitlines()),
                imports=dep,lexical_declaration_candidates=len(aa)))
        require((len(rows),sum(r["bytes"] for r in rows))==EXPECTED[edition],f"{edition} count mismatch")
        for m in graph: walk(m,graph)
        dump(dest/"MODULES.json",rows);dump(dest/"IMPORT_GRAPH.json",graph)
        jsonlines(dest/"DECLARATION_CANDIDATES.jsonl",allanchors)
        # Copy and preserve every guide, reference, attribution, notice, and license.
        docs=dest/"documentation";docs.mkdir()
        for p in base.iterdir():
            if p.is_file() and (p.suffix==".md" or p.name in {"NOTICE","LICENSE","lean-toolchain","lake-manifest.json","lakefile.toml","comparator.json"}):
                shutil.copy2(p,docs/p.name)
        if (root/"LICENSE").is_file():shutil.copy2(root/"LICENSE",docs/"LICENSE")
        old,new,_,_,_=CUTS[edition]; prefix=cut((base/"src"/old).read_text(encoding="utf-8"),edition)
        cutmod=module(new); g=dict(graph);g[cutmod]=imports(prefix)
        order=walk(cutmod,g)
        require(not BANNED.intersection(order),"terminal module in arithmetic import closure")
        stage=dest/"arithmetic_source_slice";(stage/"src").mkdir(parents=True)
        for m in order:
            if m==cutmod:continue
            src=bymod[m];target=stage/"src"/src.relative_to(base/"src");target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,target)
        target=stage/"src"/new;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(prefix,encoding="utf-8")
        for name in ("lean-toolchain","lake-manifest.json","NOTICE","ATTRIBUTION.md","REFERENCES.md","GUIDE.md"):
            if (base/name).is_file():shutil.copy2(base/name,stage/name)
        shutil.copy2(root/"LICENSE",stage/"LICENSE")
        lake=(base/"lakefile.toml").read_text()
        lake=re.sub(r'(?m)^defaultTargets\s*=.*$', 'defaultTargets = ["Lib", "New"]',lake)
        lake=lake.split('\n[[lean_lib]]\nname = "Main"',1)[0].rstrip()+"\n"
        require('name = "Main"' not in lake and 'name = "Challenge"' not in lake, "terminal lake target")
        (stage/"lakefile.toml").write_text(lake)
        (stage/"EXTRACTION_NOTICE.md").write_text(
            "# Source-only arithmetic slice\n\nModified from the Anthropic/Alpöge/Claude rewrite at "+LOCK["commit"]+
            ". Terminal declarations removed; only the import of Statements replaced by Mathlib. "
            "Source closure is lexical, not kernel-certified. The original notices and attribution are retained. "
            "Run lake build in this directory after installing the pinned toolchain; then audit the exact roots. "
            "Do not claim RH from this extraction.\n")
        slice_rows=[]
        for p in sorted(stage.rglob("*")):
            if p.is_file():
                b=p.read_bytes();slice_rows.append({"path":p.relative_to(stage).as_posix(),"bytes":len(b),"sha256":sha(b)})
        dump(dest/"ARITHMETIC_SLICE_MANIFEST.json",{"root":cutmod,"source_cut_from":old,
            "original_git_blob":CUTS[edition][3],"cut_sha256":sha(prefix.encode()),"local_modules":order,
            "files":slice_rows,"terminal_modules_excluded":sorted(BANNED),"compiler":"NOT_RUN"})
        with tarfile.open(dest/"arithmetic-source-slice.tar.gz","w:gz") as z:z.add(stage,arcname=edition+"-arithmetic")
        shutil.rmtree(stage)
        with (dest/"READING_ORDER.txt").open("w",encoding="utf-8") as f:
            for m in order:f.write(m+"\n")
        results[edition]={"modules":len(rows),"source_bytes":sum(r["bytes"] for r in rows),
            "physical_lines":sum(r["physical_lines"] for r in rows),
            "nonblank_lines":sum(r["nonblank_lines"] for r in rows),
            "lexical_code_lines":sum(r["lexical_code_lines"] for r in rows),
            "lexical_declaration_candidates":len(allanchors),
            "arithmetic_slice_modules":len(order),"arithmetic_original_modules":len(order)-1,
            "arithmetic_slice_source_bytes":sum(bymod[m].stat().st_size for m in order if m!=cutmod)+len(prefix.encode()),
            "arithmetic_slice_excluded_original_modules":len(rows)-(len(order)-1),
            "arithmetic_slice_compiler":"NOT_RUN"}
        print(edition,json.dumps(results[edition],sort_keys=True),flush=True)
    receipt={"schema":"OPICA_COMPACT_FULL_SOURCE_EXTRACTION_V1","source_commit":LOCK["commit"],
        "source_tree":LOCK["tree"],"tracked_blobs_verified":len(files),"results":results,
        "source_byte_custody":"PASS","lexical_import_validation":"PASS","proof_value_dependencies":"NOT_RUN",
        "native_integration":"NOT_RUN","kernel":"NOT_RUN","independent_replay":"NOT_RUN","claim":"RH_OPEN"}
    dump(out/"RECEIPT.json",receipt)
    payload=[{"path":p.relative_to(out).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p.read_bytes())}
        for p in sorted(out.rglob("*")) if p.is_file()]
    dump(out/"ARTIFACT_SHA256.json",payload)
    print("FULL_SOURCE_EXTRACTION_PASS",json.dumps(receipt,sort_keys=True),flush=True)
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--source",type=P);p.add_argument("--out",type=P);p.add_argument("--test",action="store_true");a=p.parse_args();tests()
    if not a.test:
        require(a.source is not None and a.out is not None,"source/output required");run(a.source.resolve(),a.out.resolve())
