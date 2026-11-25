"""Bind Lean declaration-level receipts to source and dependency pins.

No receipt is a release decision. Missing roots, types, origins or source
hashes fail closed. The independent replay compares the same common pin.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

PREFIX = "Zeta23.OPICATerminal."
NATIVE_ROOTS = {PREFIX+n for n in (
    "eventual_literalGEnergy_ge_rpow", "powerDetectorSupply_proved",
    "directEnergyToC1_proved", "riemannHypothesis_of_nativeEnergySubpower_direct")}
COMMON_ROOTS = NATIVE_ROOTS | {
    "OPICAR2Original.principal_host_from_source",
    "OPICATerminalSupplier.topG_from_original",
    "OPICATerminalSupplier.principal_ramp_windows_proved",
    PREFIX+"riemannHypothesis_step4_arithmetic_supplied",
    PREFIX+"riemannHypothesis_step4_direct_crosscheck"}
STOCK_ROOTS = {PREFIX+"riemannHypothesis_step4_arithmetic_supplied",
               PREFIX+"riemannHypothesis_step4_direct_crosscheck"}
ALLOWED_AX = {"propext", "Classical.choice", "Quot.sound"}
DENIED_MODULES = {"Main", "Statements", "Challenge", "Solution",
                  "Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion",
                  "Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter"}
DENIED_DECLS = {"UpperTheory.riemannHypothesis_of_everyCharacter",
                "UpperTheory.zeta_ne_zero_of_everyCharacter",
                "UpperTheory.Top.zeroFreeAll_of_topG", "UpperTheory.Top.plugWin",
                "UpperTheory.Top.plugAll", "UpperTheory.Top.zero_free_all_of_green_v_win",
                "UpperTheory.Top.every_character_of_green_v_win", "UpperTheory.Lit.everyE₂",
                "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
                "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin"}
REQUIRED = {
    PREFIX+"eventual_literalGEnergy_ge_rpow": {"Deduction.landau_window", "Deduction.poleData", PREFIX+"principalG_eq_literal", PREFIX+"nativeZero_mem_principal", PREFIX+"eventual_energy_growth_of_right_zero"},
    PREFIX+"powerDetectorSupply_proved": {PREFIX+"bothParityPowerComparison_proved", PREFIX+"eventual_literalGEnergy_ge_rpow"},
    PREFIX+"directEnergyToC1_proved": {PREFIX+"powerDetectorSupply_proved", "OPICAR2.directEnergyToC1_of_power_supply"},
    PREFIX+"riemannHypothesis_of_nativeEnergySubpower_direct": {PREFIX+"displacement_eq_zero_of_nativeEnergySubpower", PREFIX+"eventual_literalGEnergy_ge_rpow", PREFIX+"displacement_bound"},
    "OPICAR2Original.principal_host_from_source": {"OPICAR2Original.principal_vwin_from_source", "UpperTheory.One.vwin_of_row", "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"},
    "OPICATerminalSupplier.topG_from_original": {"OPICATerminalSupplier.literature_from_original", "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter", "UpperTheory.Zero.LLC.recTExists", "UpperTheory.LiteratureTheorems.published_results_eigen", "UpperTheory.LiteratureTheorems.published_results_first", "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt", "UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound", "GlobalTheory.Fc.forall_goal_of_shape_of_hyps"},
    "OPICATerminalSupplier.principal_ramp_windows_proved": {"OPICATerminalSupplier.topG_from_original", "OPICAR2Original.principal_host_from_source", "OPICAExtractionR1.principal_ramp_windows_of_connected"},
    PREFIX+"riemannHypothesis_step4_arithmetic_supplied": {"OPICATerminalSupplier.principal_ramp_windows_proved", PREFIX+"native_energy_subpower_arithmetic_supplied", PREFIX+"native_c1_arithmetic_supplied", PREFIX+"directEnergyToC1_proved", PREFIX+"powerDetectorSupply_proved", PREFIX+"eventual_literalGEnergy_ge_rpow", "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds"},
    PREFIX+"riemannHypothesis_step4_direct_crosscheck": {"OPICATerminalSupplier.principal_ramp_windows_proved", PREFIX+"native_energy_subpower_arithmetic_supplied", PREFIX+"riemannHypothesis_of_nativeEnergySubpower_direct", PREFIX+"eventual_literalGEnergy_ge_rpow"}}
DIRECT_ROOTS = {PREFIX+"riemannHypothesis_of_nativeEnergySubpower_direct",
                PREFIX+"riemannHypothesis_step4_direct_crosscheck"}
DIRECT_FORBIDDEN = {PREFIX+n for n in (
    "directEnergyToC1_proved", "powerDetectorSupply_proved", "bothParityPowerComparison_proved",
    "native_c1_arithmetic_supplied", "riemannHypothesis_step4_arithmetic_supplied")}
DIRECT_FORBIDDEN.add("Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds")

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(cwd, *args):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()

def git(cwd, *args):
    return run(cwd, "git", *args)

def load(p):
    return json.loads(p.read_text(encoding="utf-8"))

def dump(p, data):
    p.write_text(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False)+"\n", encoding="utf-8")

def validate_root(row, root, analytic, mode):
    require(row["schema"]=="OPICA_TERMINAL_DECLARATION_AUDIT_V2", "wrong audit schema")
    require(row["root"]==root and row["root_type"] and row["root_type_expr"], "missing root identity/type")
    require(row["native_only"]==(root in NATIVE_ROOTS), "incorrect native-only policy")
    require(set(row["axioms"]) <= ALLOWED_AX, "unapproved axioms: "+root)
    deps = {d["name"]:d["module"] for d in row["dependencies"]}
    require(len(deps)==len(row["dependencies"])==row["constants"] and root in deps,
            "incomplete or duplicate dependency inventory: "+root)
    require(REQUIRED[root] <= set(deps) and set(row["required"]) <= set(deps),
            "missing required proof dependency: "+root)
    require(not (set(row["excluded"]) & set(deps)), "excluded dependency present")
    if root in DIRECT_ROOTS:
        require(not (DIRECT_FORBIDDEN & set(deps)), "detector contamination in direct cross-check")
    if root in STOCK_ROOTS:
        require(row["root_type"].strip()=="RiemannHypothesis", "not exact stock RH: "+root)
        require("RiemannHypothesis" in row["root_type_expr"], "missing stock RH type expression")
    for name, module in deps.items():
        require(module and module not in DENIED_MODULES, "forbidden or missing origin: "+name)
        require(name != "sorryAx" and name not in DENIED_DECLS and not name.startswith("UpperTheory.FinalTheorems.")
                and not name.endswith("_of_riemannHypothesis")
                and not name.startswith("Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_"),
                "forbidden declaration: "+name)
        if root in NATIVE_ROOTS:
            require(name.split(".")[0] not in {"UpperTheory","Formalism","GlobalTheory","PositivityTheory",
                    "ReciprocityTheory","OPICATerminalSupplier","OPICAR2Original","SelfIntersectionVolumeEstimates"},
                    "supplier declaration in native closure: "+name)
            if module.startswith("Development."):
                require(mode=="common" and module in analytic, "nonanalytic original module in native closure: "+module)
            else:
                require(module.split(".")[0] in {"Zeta23","Mathlib","Lean","Std","Init","Batteries",
                        "Aesop","Qq","ProofWidgets","Plausible","ImportGraph","Cli","Lake","LeanSearchClient"},
                        "non-native origin: "+module)
    return {"root_type":row["root_type"],"root_type_expr":row["root_type_expr"],
            "axioms":sorted(row["axioms"]),"required":sorted(row["required"]),
            "excluded":sorted(row["excluded"]),"native_only":row["native_only"],
            "dependencies":dict(sorted(deps.items()))}

def verify(workspace, native, audit_dir, source, mode, out):
    common = mode=="common"
    manifest = load(source) if common else {}
    head, tree = git(native,"rev-parse","HEAD"), git(native,"rev-parse","HEAD^{tree}")
    require(not git(native,"diff","--name-only","HEAD"), "native worktree modified")
    pins = load(workspace/"lake-manifest.json")["packages"]
    packages = {}
    for p in pins:
        pkg = workspace/".lake/packages"/p["name"]
        require(git(pkg,"rev-parse","HEAD")==p["rev"], "package pin mismatch: "+p["name"])
        require(not git(pkg,"diff","--name-only","HEAD"), "modified package: "+p["name"])
        packages[p["name"]]=(pkg,p["rev"])
    toolchain = (workspace/"lean-toolchain").read_text().strip()
    expected_toolchain = "leanprover/lean4:v4.33.1" if common else "leanprover/lean4:v4.33.0-rc2"
    expected_mathlib = "0df444a360eaa60ab8c11dca51a86af692955474" if common else "51e6992efd06126df61a496bebf8f49482a4e129"
    require(toolchain==expected_toolchain and packages["mathlib"][1]==expected_mathlib, "wrong toolchain/mathlib pin")
    lean_prefix = Path(run(workspace,"lean","--print-prefix"))
    lean_version = run(workspace,"lean","--version")
    analytic = set()
    for f in sorted((native/"research/opica_terminal").glob("ANALYTIC_SOURCE_PART*.json")):
        for x in load(f)["files"]:
            analytic.add(x["origin"].removeprefix("src/").removesuffix(".lean").replace("/","."))
    require(len(analytic)==27, "incomplete analytic allowlist")
    if common:
        require(manifest["schema"]=="OPICA_TERMINAL_COMMON_SOURCE_V2" and manifest["status"]=="STAGED_NOT_COMPILED"
                and not manifest["source_census"]["violations"], "source gate not passed")
        require(manifest["native_head"]==head and manifest["native_tree"]==tree
                and manifest["original_head"]==git(workspace,"rev-parse","HEAD")
                and manifest["original_tree"]==git(workspace,"rev-parse","HEAD^{tree}"),
                "common source identity mismatch")
        require(sha(workspace/"lakefile.toml")==manifest["lakefile_sha256"], "staged lakefile changed")
    expected = COMMON_ROOTS if common else NATIVE_ROOTS
    actual = {p.stem for p in audit_dir.glob("*.json")}
    require(actual==expected, "audit root inventory differs: missing="+str(sorted(expected-actual))+" extra="+str(sorted(actual-expected)))
    roots = {root:validate_root(load(audit_dir/(root+".json")),root,analytic,mode)
             for root in sorted(expected)}
    modules = {m for row in roots.values() for m in row["dependencies"].values()}
    source_hashes = {}
    for m in sorted(modules):
        rel = m.replace(".","/")+".lean"
        local = (workspace/"src" if common else workspace)/rel
        if local.is_file():
            digest = sha(local)
            if common:
                require(manifest["import_closure"].get(m)==digest, "compiled local origin not in pinned staged closure: "+m)
            else:
                require(git(native,"ls-files","--",rel)==rel, "untracked native source origin: "+m)
            source_hashes[m]={"kind":"staged" if common else "native","path":rel,"sha256":digest}
            continue
        candidates = []
        for pkg,(base,rev) in packages.items():
            for parent in (base,base/"src"):
                f=parent/rel
                if f.is_file():
                    candidates.append((f,{"kind":"package","package":pkg,"revision":rev,"path":str(f.relative_to(base))}))
        for parent in (lean_prefix/"src/lean",lean_prefix/"src/lean/lake",lean_prefix/"src/lean/lean"):
            f=parent/rel
            if f.is_file():
                candidates.append((f,{"kind":"toolchain","revision":toolchain,"path":str(f.relative_to(lean_prefix))}))
        unique = {str(f.resolve()):(f,meta) for f,meta in candidates}
        require(len(unique)==1, "unresolved or ambiguous source origin: "+m)
        f,meta = next(iter(unique.values()))
        source_hashes[m]={**meta,"sha256":sha(f)}
    receipt = {"schema":"OPICA_TERMINAL_EVIDENCE_V2","status":"CANDIDATE_AUDIT_ONLY",
               "native_head":head,"native_tree":tree,"original_head":manifest.get("original_head"),
               "original_tree":manifest.get("original_tree"),"toolchain":toolchain,"lean_version":lean_version,
               "packages":{k:v[1] for k,v in sorted(packages.items())},
               "mode":mode,"roots":roots,"module_source_hashes":source_hashes,
               "proof_acceptance":False,"RH":"OPEN"}
    dump(out,receipt)
    print("OPICA_TERMINAL_EVIDENCE_V2",len(roots),"roots",len(modules),"source origins; CANDIDATE ONLY")

def compare(first, second, out):
    a,b=load(first),load(second)
    require(a["mode"]==b["mode"]=="common" and a["schema"]==b["schema"]=="OPICA_TERMINAL_EVIDENCE_V2",
            "comparison requires two common-pin receipts")
    for key in ("native_head","native_tree","original_head","original_tree","toolchain","lean_version","packages","roots","module_source_hashes"):
        require(a[key]==b[key],"independent replay mismatch: "+key)
    dump(out,{"schema":"OPICA_TERMINAL_INDEPENDENT_REPLAY_V1","status":"INDEPENDENT_REPLAY_MATCH_CANDIDATE_ONLY",
              "native_head":a["native_head"],"native_tree":a["native_tree"],
              "first_sha256":sha(first),"second_sha256":sha(second),"roots":sorted(a["roots"]),
              "proof_acceptance":False,"RH":"OPEN"})
    print("OPICA_TERMINAL_INDEPENDENT_REPLAY_MATCH_CANDIDATE_ONLY")

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    sub=parser.add_subparsers(dest="command",required=True)
    v=sub.add_parser("verify")
    for opt in ("workspace","native","audit-dir","output"):
        v.add_argument("--"+opt,type=Path,required=True)
    v.add_argument("--source",type=Path)
    v.add_argument("--mode",choices=["native","common"],required=True)
    c=sub.add_parser("compare")
    for opt in ("first","second","output"):
        c.add_argument("--"+opt,type=Path,required=True)
    a=parser.parse_args()
    if a.command=="verify":
        require(a.mode=="native" or a.source is not None,"common source receipt required")
        verify(a.workspace.resolve(),a.native.resolve(),a.audit_dir.resolve(),a.source,a.mode,a.output)
    else:
        compare(a.first,a.second,a.output)
