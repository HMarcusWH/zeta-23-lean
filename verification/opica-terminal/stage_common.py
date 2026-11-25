"""Prepare a fresh original-pin proof workspace; never import compiled objects.

This is candidate engineering, not a proof-acceptance receipt.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from lean_header import imports as lean_imports, rewrite_imports

ORIGINAL = "40e56bab026552e089d7afcfeff08d2defb9c005"
ORIGINAL_TREE = "e517b335d21898fd2506ad538a1e1775c0aaa4e4"
NATIVE_PARENT = "4f81c784d3b330395507f6dcd1c8b0010b3835cc"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
OLD = "Development.AutomorphicArithmetic.DedekindLFunctions."
NEW = "Zeta23.OPICATerminal.Analytic."
BASE = "Development/AutomorphicArithmetic/"
THIRD = BASE + "ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/"
BOX = BASE + "CharacterBoxes/"
FOCK = BASE + "ThetaCorrespondence/FockModels/"
DENIED = {"Main", "Statements", "Challenge", "Solution",
          (BOX + "MainConclusion").replace("/", "."),
          (BOX + "RiemannHypothesisOfEveryCharacter").replace("/", ".")}
EXTERNAL = {"Mathlib","Lean","Std","Init","Batteries","Aesop","Qq",
            "ProofWidgets","Plausible","ImportGraph","Cli","Lake","LeanSearchClient"}

def require(cond, msg):
    if not cond:
        raise RuntimeError(msg)

def git(repo, *args):
    return subprocess.check_output(["git","-C",str(repo),*args], text=True).strip()

def digest(b):
    return hashlib.sha256(b).hexdigest()

def exactly_remove(s, marker):
    require(s.count(marker) == 1, "source cut marker missing/ambiguous: " + marker)
    return s.replace(marker, "", 1)

def cut_between(s, start, end):
    require(s.count(start) == 1 and s.count(end) == 1, "nonunique source cut")
    a, b = s.index(start), s.index(end)
    require(a < b, "reversed source cut")
    return s[:a] + s[b:]

def trim(s, marker, suffix):
    require(s.count(marker) == 1 and s.endswith(suffix), "source cut shape changed")
    return s[:s.index(marker)] + suffix

def source_cuts(repo):
    edits = {}
    def edit(rel, fn):
        p = repo/"src"/rel
        require(p.is_file() and not p.is_symlink(), "bad source file: "+rel)
        orig = p.read_text(encoding="utf-8")
        # Match the original committed source, before any transformation.
        require(orig == subprocess.check_output(
            ["git","-C",str(repo),"show",ORIGINAL+":src/"+rel], text=True),
            "source modified before cut: "+rel)
        new = fn(orig)
        require(new != orig, "empty cut: "+rel)
        p.write_text(new, encoding="utf-8")
        edits[rel] = {"before":digest(orig.encode()), "after":digest(new.encode())}
    # Keep all source-producing arguments, remove only downstream terminal consumers.
    edit(BOX+"ZeroFreeAllOfTopG.lean", lambda s: trim(s,
        "\ntheorem zeroFreeAll_of_topG ", "\nend UpperTheory.Top\n\nend\n"))
    edit(BOX+"EveryCharacter.lean", lambda s: cut_between(s,
        "\ntheorem UpperTheory.Top.plugWin ", "\ndef UpperTheory.EveryCharacter ").split(
        "\ntheorem UpperTheory.Top.plugAll ",1)[0]+"\n")
    edit(FOCK+"EveryCharacterE.lean", lambda s: cut_between(s,
        "\ntheorem everyE₂ ", "\nstructure CovE "))
    edit(THIRD+"TopPlug.lean", lambda s: trim(s,
        "\ntheorem UpperTheory.Top.zero_free_all_of_green_v_win ", "\nend\n"))
    edit(THIRD+"SiegelEisensteinSecondTermHypotheses.lean", lambda s: trim(
        exactly_remove(s,"import "+(THIRD+"TopPlug").replace("/",".")+"\n"),
        "\ntheorem every_character_of_theta_integrals_local_matching ",
        "\nend UpperTheory.Lit\nend\nend\n"))
    edit(THIRD+"EveryCharacterOfLiteratureOfVWin.lean", lambda s: trim(
        exactly_remove(s,"import "+(BOX+"RiemannHypothesisOfEveryCharacter").replace("/",".")+"\n"),
        "\ntheorem UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ",
        "\nend\n"))
    return edits

def import_closure(root, roots):
    pending = [(m, "<root>", 0) for m in roots]
    seen = set()
    files = {}
    while pending:
        m, parent, line = pending.pop()
        if m in seen:
            continue
        location = f"{parent}:{line}"
        require(m not in DENIED, f"terminal module in source closure: {m} imported by {location}")
        seen.add(m)
        p = root / (m.replace(".","/")+".lean")
        require(not p.is_symlink(), "symlink source: "+m)
        if not p.is_file():
            require(m.split(".")[0] in EXTERNAL,
                    f"unresolved source import: {m} imported by {location}")
            continue
        data = p.read_bytes()
        files[m] = digest(data)
        pending += [(i.name, m, i.line) for i in lean_imports(data.decode("utf-8"), m)]
    return files

def stage(native, original, output):
    require(git(original,"rev-parse","HEAD")==ORIGINAL, "original commit mismatch")
    require(git(original,"rev-parse","HEAD^{tree}")==ORIGINAL_TREE, "original tree mismatch")
    require((original/"lean-toolchain").read_text().strip()==TOOLCHAIN, "wrong common Lean")
    manifest = json.loads((original/"lake-manifest.json").read_text())
    require(any(p["name"]=="mathlib" and p["rev"]==MATHLIB for p in manifest["packages"]),
            "wrong common Mathlib")
    subprocess.run(["git","-C",str(native),"merge-base","--is-ancestor",NATIVE_PARENT,"HEAD"],check=True)
    require(not git(native,"diff","--name-only","HEAD"), "native tracked worktree dirty")
    require(not git(original,"diff","--name-only","HEAD"), "original tracked worktree dirty")
    require(not (original/"src/Zeta23").exists(), "native namespace collision")
    # Verify that the standalone native analytic port has identical proof bodies.
    analytic = {}
    for p in sorted((native/"research/opica_terminal").glob("ANALYTIC_SOURCE_PART*.json")):
        for row in json.loads(p.read_text())["files"]:
            src = row["origin"]
            require(git(original,"rev-parse",ORIGINAL+":"+src)==row["blob"],
                    "original analytic blob mismatch")
            source = (original/src).read_text(encoding="utf-8")
            expected = rewrite_imports(source, OLD, NEW, src)
            require(expected==(native/row["path"]).read_text(encoding="utf-8"),
                    "analytic port not an import-only change: "+row["path"])
            analytic[row["path"]] = {"origin":src,"blob":row["blob"]}
    require(len(analytic)==27,"incomplete analytic source manifest")
    edits = source_cuts(original)
    # Common environment uses the identical ORIGINAL Deduction declarations;
    # do not load the separately namespaced-by-module native copies twice.
    staged = {}
    for rel in git(native,"ls-files","--","Zeta23","Zeta23.lean",
                   "verification/opica-terminal/OPICATerminalSupplier").splitlines():
        if not rel.endswith(".lean") or rel.startswith("Zeta23/OPICATerminal/Analytic/"):
            continue
        src = native/rel
        require(src.is_file() and not src.is_symlink(), "bad native source: "+rel)
        target = rel.removeprefix("verification/opica-terminal/")
        dst = original/"src"/target
        require(not dst.exists(), "source collision: "+target)
        dst.parent.mkdir(parents=True,exist_ok=True)
        text = src.read_text(encoding="utf-8")
        new = rewrite_imports(text, NEW, OLD, rel)
        dst.write_text(new,encoding="utf-8")
        staged[target] = {"tracked":rel,"before":digest(text.encode()),"after":digest(new.encode())}
    lake = original/"lakefile.toml"
    with lake.open("a",encoding="utf-8") as f:
        f.write('\n[[lean_lib]]\nname = "Zeta23"\nleanOptions = {autoImplicit = true, maxHeartbeats = 800000}\n')
        f.write('\n[[lean_lib]]\nname = "OPICATerminalSupplier"\nglobs = ["OPICATerminalSupplier.+"]\n')
    imports = import_closure(original/"src",["OPICATerminalSupplier.AuditTerminal",
                  "Zeta23.OPICATerminal.AuditNative"])
    out = {"schema":"OPICA_TERMINAL_COMMON_SOURCE_V1","status":"STAGED_NOT_COMPILED",
           "native_head":git(native,"rev-parse","HEAD"),"native_tree":git(native,"rev-parse","HEAD^{tree}"),
           "original_head":ORIGINAL,"original_tree":ORIGINAL_TREE,"toolchain":TOOLCHAIN,"mathlib":MATHLIB,
           "analytic_equivalence":analytic,"endpoint_source_cuts":edits,"staged_native":staged,
           "import_closure":imports,"lakefile_sha256":digest(lake.read_bytes()),
           "proof_acceptance":False,"RH":"OPEN"}
    output.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print("OPICA_TERMINAL_STAGED_NOT_COMPILED",len(imports),"source modules")

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--native",type=Path,required=True)
    parser.add_argument("--original",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    stage(args.native.resolve(),args.original.resolve(),args.output.resolve())
