"""Exact historical-support source admission; never grants native/RH proof acceptance."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

BASE = "bb7c8184a135b2823c6296917c5ac893bebf2a71"
BASE_TREE = "2b19357e1b65cc500f3e3a5b5d4df14601b02062"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
POLICY = "research/RHRC/integration/opica_support_port/SEALED_PORT.json"
VALIDATOR = "research/RHRC/integration/opica_support_port/check_candidate.py"
POLICY_BLOB = "32e3360710cfb2d127e77f3d4c207a34a24360cc"
REVIEWED_OLD_HEAD = "983b6e78eccf9156ee7e2ec55f6772bd64cedccd"
REVIEWED_OLD_TREE = "23b527570280afd56f51376cf843e243e32b1b03"
FROZEN_PRODUCTS = frozenset((
    "research/RHRC/ffbbp/generated/history/RHKG_CANDIDATE_REDUCTION_ASSURANCE_v1_PR265.json",
    "research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl",
    "research/RHRC/ool/generated/history/RHKG_OOL_PHASE_ATLAS_v1_PR266.json",
    "research/RHRC/ool/generated/history/RHKG_OOL_ROUTE_CONTACTS_v1_PR266.jsonl"))
MANIFEST = "research/RHRC/integration/opica_round4/BUILD_MANIFEST.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PREFIXES = rb"OPICAStep4|FourierBridge|FourierEnergy|SamplingDensity|ParityRational|DensityCompatibility|ActualDensityEnergy|NativeParityRational|NativeParityActual|CofinalAperture|NativeSliceInterpolation|ApertureSlack"
PRIMITIVES = ("Quot", "Quot.mk", "Quot.lift", "Quot.ind", "propext", "Quot.sound",
    "Classical.choice", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
    "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String",
    "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam", "Empty")

class Reject(ValueError):
    pass

def need(condition, message):
    if not condition:
        raise Reject(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def oid(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest()

def run(*args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True, timeout=180).strip()

def git_tree(repo, ref):
    raw = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-rz", ref], timeout=180)
    result = {}
    for line in raw.split(b"\0"):
        if not line:
            continue
        meta, name = line.split(b"\t", 1)
        mode, kind, sha = meta.decode("ascii").split()
        p = name.decode("utf-8")
        need(p not in result, "Duplicate Git path")
        result[p] = {"mode": mode, "type": kind, "sha": sha}
    return result

def read_regular(repo, rel):
    p = repo / rel
    need(not p.is_symlink() and p.is_file() and p.resolve().is_relative_to(repo), "Unsafe source: " + rel)
    for parent in p.relative_to(repo).parents:
        need(not (repo / parent).is_symlink(), "Linked source directory")
    return p.read_bytes()

def delta(parent, current):
    need(set(parent) <= set(current), "Native parent deletion or rename")
    return {k: v for k, v in current.items() if parent.get(k) != v}

def verify_delta(parent, current, reviewed, policy_oid, validator_oid, active=()):
    actual = delta(parent, current)
    generated = set(actual) & set(active)
    need(all(p in parent and current[p]["mode"]==parent[p]["mode"]=="100644" and current[p]["type"]==parent[p]["type"]=="blob" for p in generated),"Invalid generated path/type")
    actual = {p:v for p,v in actual.items() if p not in generated}
    wanted = dict(reviewed)
    wanted[POLICY] = {"mode": "100644", "type": "blob", "sha": policy_oid}
    wanted[VALIDATOR] = {"mode": "100644", "type": "blob", "sha": validator_oid}
    need(actual == wanted, "Unexpected source path, mode or blob")
    need(all(v["mode"] == "100644" and v["type"] == "blob" for v in wanted.values()),
         "Nonregular candidate source")

def normalized_validator(raw):
    anchor = ('POLICY_BLOB = "' + POLICY_BLOB + '"\n').encode("ascii")
    need(raw.count(anchor) == 1, "Invalid policy anchor")
    return oid(raw.replace(anchor, b'POLICY_BLOB = "<policy-blob-oid>"\n'))

def axiom_reports(text, roots):
    found = {}
    need(not re.search(r"\bsorryAx\b|(?:^|\n).*?\berror:", text), "Compiler error or sorryAx")
    matches = list(re.finditer(r"(?m)^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)[ \t]*(?=\n|$)", text))
    for match in matches:
        name, raw = match.groups()
        need(name in roots and name not in found, "Unknown/duplicate named axiom report: " + name)
        values = [] if raw is None else [x.strip() for x in raw.split(",") if x.strip()]
        need(len(values) == len(set(values)) and set(values) <= ALLOWED, "Nonstandard axiom: " + name)
        found[name] = sorted(values)
    need(set(found) == set(roots), "Missing exact named axiom reports")
    return found

def generated_inventory(repo):
    need(run("git","rev-parse","HEAD:"+MANIFEST,cwd=repo)==run("git","rev-parse",BASE+":"+MANIFEST,cwd=repo),"Frozen generated manifest changed")
    all_paths=[r["path"] for r in json.loads(read_regular(repo,MANIFEST))["generated"]]
    need(len(all_paths)==len(set(all_paths))==81 and FROZEN_PRODUCTS<=set(all_paths),"81-product inventory")
    return set(all_paths)-FROZEN_PRODUCTS

def check(repo=ROOT):
    repo = Path(repo).resolve()
    head = run("git", "rev-parse", "HEAD", cwd=repo)
    tree = run("git", "rev-parse", "HEAD^{tree}", cwd=repo)
    need(run("git", "rev-parse", BASE+"^{tree}", cwd=repo) == BASE_TREE, "Wrong native base tree")
    need(run("git", "merge-base", BASE, "HEAD", cwd=repo) == BASE, "Wrong native ancestor")
    need(not run("git", "status", "--porcelain", "--untracked-files=all", cwd=repo), "Dirty checkout")
    parent, current = git_tree(repo, BASE), git_tree(repo, head)
    raw = read_regular(repo, POLICY)
    policy = json.loads(raw)
    need(set(policy) == {"schema", "base", "base_tree", "reviewed", "validator_template_oid", "proof_acceptance", "RH", "C1", "Step4"} and
         policy["schema"] == "OPICA_SUPPORT_SEALED_PORT_V3" and policy["base"] == BASE and policy["base_tree"] == BASE_TREE and
         policy["proof_acceptance"] is False and all(policy[k] == "OPEN" for k in ("RH", "C1", "Step4")), "Source policy scope differs")
    need(oid(raw) == POLICY_BLOB, "Sealed policy bytes differ")
    source = read_regular(repo, VALIDATOR)
    need(normalized_validator(source) == policy["validator_template_oid"], "Sealed validator differs")
    active=generated_inventory(repo)
    need(len(active)==77 and all(parent[p]==current[p] for p in FROZEN_PRODUCTS),"Frozen generated products differ")
    verify_delta(parent, current, policy["reviewed"], POLICY_BLOB, oid(source),active)
    for name, row in delta(parent, current).items():
        need(oid(read_regular(repo, name)) == row["sha"], "Working source differs: " + name)
    ignored = run("git", "ls-files", "--others", "--ignored", "--exclude-standard", cwd=repo)
    need(not any(s.startswith(("Zeta23/", "research/", ".github/", "docs/examples/")) and s.endswith((".lean", ".lean.in", ".py", ".yml", ".yaml", ".toml")) for s in ignored.splitlines()),
         "Ignored source provider")
    p = json.loads((repo/HERE.relative_to(ROOT)/"PORT_CONTRACT.json").read_text())
    registry = json.loads((repo/HERE.relative_to(ROOT)/"HISTORICAL_PACKAGE_REGISTRY.json").read_text())
    need(len(registry["packages"]) == len(p["historical_package_roots"]) == 16, "Package census differs")
    need((repo/"lean-toolchain").read_text().strip() == p["native_toolchain"], "Wrong native compiler")
    mathlib = [q for q in json.loads((repo/"lake-manifest.json").read_text())["packages"] if q["name"] == "mathlib"]
    need(len(mathlib) == 1 and mathlib[0]["rev"] == p["native_mathlib"], "Wrong native Mathlib")
    actual = set(run("git", "ls-files", "Zeta23/OPICASupport", cwd=repo).splitlines())
    expected = {r["path"] for r in p["candidate_modules"]}
    need(actual == expected and len(actual) == len(p["candidate_modules"]) == 24, "Authored module inventory differs")
    for row in p["candidate_modules"]:
        data = read_regular(repo, row["path"])
        need(digest(data) == row["ported_sha256"], "Ported source changed")
        orig = re.sub(rb"^import Zeta23\.OPICASupport\.(" + PREFIXES + rb")\.", rb"import \1.", data, flags=re.M)
        need(digest(orig) == row["original_sha256"] and len(orig) == row["original_bytes"], "Non-import-only edit")
    need(len(p["existing_native_modules"]) == 2, "Native dimension modules absent")
    for row in p["existing_native_modules"]:
        need(digest(read_regular(repo, row["path"])) == row["sha256"], "Existing native source changed")
    cp = p["compatibility_patch"]
    need(cp["status"] == "ARCHIVAL_ONLY_COMMON_PIN_NOT_APPLIED" and digest(read_regular(repo, cp["path"])) == cp["sha256"], "Common-pin compatibility boundary changed")
    roots = []
    for r, h in zip(registry["packages"], p["historical_package_roots"]):
        b = (repo/HERE.relative_to(ROOT)/"historical_receipts"/Path(r["bundle_receipt_path"]).name).read_bytes()
        need(digest(b) == r["receipt_sha256"], "Historical receipt changed")
        receipt = json.loads(b)
        names = h["receipt_roots"]
        available = receipt.get("transitive_axioms", receipt.get("axioms", {}))
        need(h["index"] == r["package_index"] and len(names) == r["public_roots"] and
             set(names) <= set(available) and all(set(available[n]) <= ALLOWED for n in names),
             "Historical named roots or axiom scope differs")
        roots.extend(names)
    need(len(roots) == len(set(roots)) == 167, "Exact 167 unique public roots required")
    need(head == run("git", "rev-parse", "HEAD", cwd=repo) and not run("git", "status", "--porcelain", "--untracked-files=all", cwd=repo), "Source changed during admission")
    return {"schema": "OPICA_SUPPORT_CANDIDATE_SOURCE_V3", "status": "PASS_SOURCE_SCOPE_ONLY",
            "checked_commit": head, "checked_tree": tree, "base": BASE, "base_tree": BASE_TREE,
            "source_port_families": 16, "source_port_modules": 24, "existing_native_modules": 2,
            "public_root_count": 167, "roots": roots, "proof_acceptance": False,
            "current_compiler_accepted": False, "full_round4_accepted": False,
            "historical_type_equivalence": "REVIEW_PENDING", "RH": "OPEN", "C1": "OPEN", "Step4": "OPEN",
            "canonical_product_count":len(active),"unchanged_historical_product_count":len(FROZEN_PRODUCTS),
            "delta":{"added":sorted(set(current)-set(parent)),
                     "edited":sorted(set(delta(parent,current))-set(active)-(set(current)-set(parent))),
                     "generated":sorted(set(delta(parent,current))&active),"deleted":[]},
            "path_policy_sha256":digest(raw),"manifest_sha256":digest(read_regular(repo,MANIFEST))}

def validate_descendant(repo=ROOT, *, require_clean=False):
    repo=Path(repo).resolve()
    if POLICY not in git_tree(repo,"HEAD"):
        from research.RHRC.integration.documentation_2026_11_21.source_scope import validate_descendant as historical
        return historical(repo,require_clean=require_clean)
    # The stricter clean check remains mandatory for this exact support epoch.
    return check(repo)

def check_classification(repo=ROOT):
    repo=Path(repo).resolve();r=check(repo)
    d=json.loads((repo/"research/RHRC/graph/FILE_CLASSES.json").read_text())
    for p in r["delta"]["added"]:
        hits=[q for q in d["rules"] if re.fullmatch(q["pattern"],p)]
        need(hits and hits[0]["file_class"] not in (d["unknown_class"],"UNKNOWN_FILE_CLASS") and hits[0]["trust_zone"] not in (d["unknown_trust_zone"],"UNKNOWN"),"Unclassified support path: "+p)
    p=json.loads((repo/HERE.relative_to(ROOT)/"PORT_CONTRACT.json").read_text())
    roles=json.loads((repo/"research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json").read_text())["standalone_module_roles"]
    need(all(roles.get(q["module"])=="OPICA_HISTORICAL_PORT_SUPPORT_CANDIDATE_ONLY" for q in p["candidate_modules"]),"Missing support module disposition")
    return {"status":"PASS_HISTORICAL_SUPPORT_CLASSIFICATION_ONLY","proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}

def canonical_candidate(output):
    source=check();check_classification();output=Path(output).resolve()
    need(not output.exists() and not output.is_relative_to(ROOT),"Fresh external candidate directory")
    output.mkdir(parents=True)
    active=generated_inventory(ROOT);paths=active|FROZEN_PRODUCTS
    receipt={"schema":"OPICA_CANONICAL_CANDIDATE_V3","status":"INCOMPLETE","source_head":source["checked_commit"],"source_tree":source["checked_tree"],"proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    def save():(output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    def hashes():return {p:digest(read_regular(ROOT,p)) for p in sorted(paths)}
    def changes():
        rows=run("git","diff","--name-status","--no-renames","HEAD").splitlines()
        need(all(x.startswith("M\t") and x[2:] in active for x in rows) and not run("git","ls-files","--others","--exclude-standard"),"Unexpected generated delta")
        need(run("git","rev-parse","HEAD")==source["checked_commit"] and run("git","rev-parse","HEAD^{tree}")==source["checked_tree"],"Source epoch changed")
        return sorted(x[2:] for x in rows)
    def command(label,args,timeout):
        receipt["phase"]=label;save()
        with (output/(label+".log")).open("xb") as f:
            subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=timeout,check=True)
    try:
        before=hashes();need(not changes(),"Dirty source")
        command("compiler-preparation",["lake","build","Zeta23.RHRC.DeclarationDependencyExport","Zeta23.RHRC.SourceCandidateResolution"],7200)
        need(not changes() and hashes()==before,"Compiler preparation changed products")
        command("write",[sys.executable,"-B","research/RHRC/tools/materialize_derived_state.py","--write"],10800)
        after=hashes();changed=changes()
        need(all(before[p]==after[p] for p in FROZEN_PRODUCTS) and set(changed)=={p for p in paths if before[p]!=after[p]},"Frozen/delta mismatch")
        coverage=json.loads((ROOT/"research/RHRC/graph/generated/REPOSITORY_COVERAGE.json").read_text())["declared_generated_products"]
        need(len(coverage)==77 and set(coverage)==active,"Generated coverage differs")
        command("check",[sys.executable,"-B","research/RHRC/tools/materialize_derived_state.py","--check"],10800)
        need(hashes()==after and changes()==changed,"Canonical check changed bytes")
        subprocess.run(["git","-C",str(ROOT),"diff","--check","HEAD"],check=True)
        patch=subprocess.check_output(["git","-C",str(ROOT),"diff","--binary","HEAD"]);(output/"generated-state.patch").write_bytes(patch)
        receipt.update(status="REVIEW_ONLY_GENERATED_STATE",phase="COMPLETE",active_count=77,frozen_count=4,total_count=81,before_sha256=before,after_write_sha256=after,after_check_sha256=after,frozen_git_oids={p:run("git","rev-parse",BASE+":"+p) for p in sorted(FROZEN_PRODUCTS)},changed_paths=changed,changed_count=len(changed),patch_sha256=digest(patch),logs_sha256={p.name:digest(p.read_bytes()) for p in sorted(output.glob("*.log"))})
        save();print(json.dumps({k:receipt[k] for k in ("status","source_head","changed_count","proof_acceptance")}))
    except BaseException as e:
        receipt.update(status="INCOMPLETE_NOT_ACCEPTED",error=str(e)[:1200]);save();raise

def build(output, *, checker_work=None, checker_code=None):
    report = check()
    spec = json.loads((HERE/"PORT_CONTRACT.json").read_text())
    output = output.resolve()
    need(not output.exists() and not output.is_relative_to(ROOT), "Fresh external output required")
    output.mkdir(parents=True)
    receipt = {**report, "status": "INCOMPLETE", "stages": [], "independent_full_closure": "NOT_RUN"}
    def save():
        (output/"receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    def command(label, argv, timeout=9000):
        with (output/(label+".log")).open("xb") as log:
            result = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
        need(result.returncode == 0, "Command failed: " + label)
    save()
    try:
        modules = [r["module"] for r in spec["candidate_modules"]+spec["existing_native_modules"]]
        command("build", ["lake", "build", *modules, "Zeta23.RHRC.OpicaComposition.Export"])
        receipt["stages"].append("FRESH_NATIVE_BUILD_PASS")
        for i, row in enumerate(spec["candidate_modules"]):
            command("strict_"+str(i), ["lake", "env", "lean", "-DwarningAsError=true", row["path"]], timeout=1800)
        receipt["stages"].append("STRICT_AUTHORED_MODULES_PASS")
        roots = report["roots"]
        audit = output/"OPICASupportAudit.lean"
        audit.write_text("\n".join("import "+m for m in modules+["Zeta23.RHRC.OpicaComposition.Export"]) +
            "\nset_option pp.fullNames true\nset_option pp.universes false\n" +
            "\n".join("#check @"+n+"\n#print axioms "+n+"\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget "+chr(96)+n+' "type"' for n in roots)+"\n", encoding="utf-8")
        command("root_audit", ["lake", "env", "lean", "--root="+str(output), "-DwarningAsError=true", "-o", str(output/"OPICASupportAudit.olean"), str(audit)])
        text = (output/"root_audit.log").read_text()
        receipt["axioms"] = axiom_reports(text, roots)
        expressions = [json.loads(line.split("\t", 1)[1]) for line in text.splitlines() if line.startswith("OPICA_TARGET\t")]
        need(len(expressions) == len(roots), "Missing compiler-derived theorem type DAGs")
        from research.RHRC.integration.opica_composition.inventory import expression_hash
        types = [{"name": n, "expression": t, "sha256": expression_hash(t)} for n, t in zip(roots, expressions)]
        (output/"NATIVE_TYPE_CANDIDATES.json").write_text(json.dumps(types, ensure_ascii=False, indent=2)+"\n")
        receipt["stages"].append("EXACT_NAMED_AXIOMS_AND_NATIVE_TYPE_EXPORT_PASS")
        # Fresh stock kernel replay is a separate gate, not a substitute for the independent checker.
        env = dict(os.environ)
        paths = run("lake", "env", "printenv", "LEAN_PATH")
        env["LEAN_PATH"] = str(output) + os.pathsep + paths
        checker = Path(run("lake", "env", "lean", "--print-prefix")) / "bin" / "leanchecker"
        need(checker.is_file(), "Pinned stock kernel checker unavailable")
        with (output/"stock_fresh.log").open("xb") as log:
            cp = subprocess.run([str(checker), "--fresh", "--verbose", "OPICASupportAudit"], cwd=ROOT, env=env,
                                stdout=log, stderr=subprocess.STDOUT, timeout=9000)
        need(cp.returncode == 0, "Fresh stock-kernel replay failed")
        receipt["stages"].append("FRESH_STOCK_KERNEL_REPLAY_PASS")
        receipt["status"] = "NATIVE_CANDIDATE_COMPILE_AXIOMS_STOCK_PASS"
        if checker_work:
            from independent_port import independent
            receipt["independent_full_closure"] = independent(ROOT, output, checker_work.resolve(), checker_code.resolve(), roots, paths)
            receipt["status"] = "NATIVE_CANDIDATE_INDEPENDENT_SELECTED_CLOSURE_PASS"
        need(check() == report, "Candidate source changed")
        return receipt
    except BaseException as exc:
        receipt.update(status="INCOMPLETE_OR_REJECTED", failure=str(exc)[:2000], exception_type=type(exc).__name__)
        raise
    finally:
        save()
        print(json.dumps({"status": receipt["status"], "proof_acceptance": False, "RH": "OPEN"}), flush=True)


HISTORICAL_HEAD = "7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9"
HISTORICAL_TREE = "9248b76d7aff60aab3bb775c4be9750dc6006003"
COMMON_LOCK_OID = "33038d620ce50e274683c0d939e128d7541b653e"
COMMON_MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
COMMON_TOOLCHAIN = "leanprover/lean4:v4.33.1"
COMPATIBILITY_PATHS = {
    "Zeta23/Taper/Norms.lean", "Zeta23/Taper/Decay.lean", "Zeta23/Taper/Fourier.lean",
    "Zeta23/PrimeSideA/Defs.lean", "Zeta23/PrimeSideA/EndsE1.lean", "Zeta23/MV/Spacing.lean",
}

def historical_checkout(repo):
    need(not repo.is_relative_to(ROOT) and repo != ROOT and
         run("git","rev-parse","HEAD",cwd=repo)==HISTORICAL_HEAD and
         run("git","rev-parse","HEAD^{tree}",cwd=repo)==HISTORICAL_TREE,
         "Historical replay must use separate exact common-pin worktree")

def historical_changes(repo, expected):
    modified=set(run("git","diff","--name-only","HEAD",cwd=repo).splitlines())
    untracked=set(run("git","ls-files","--others","--exclude-standard",cwd=repo).splitlines())
    need(modified|untracked==set(expected) and not (modified&untracked),
         "Unexpected historical worktree delta")
    for rel, sha in expected.items():
        need(digest(read_regular(repo,rel))==sha,"Historical replay input changed: "+rel)

def prepare_historical(repo, lock, evidence):
    # All edits are in a disposable pinned historical checkout; never native HEAD.
    source=check();spec=json.loads((HERE/"PORT_CONTRACT.json").read_text())
    repo,lock,evidence=repo.resolve(),lock.resolve(),evidence.resolve()
    historical_checkout(repo)
    need(not run("git","status","--porcelain","--untracked-files=all",cwd=repo),"Historical checkout dirty")
    need(not evidence.exists() and not evidence.is_relative_to(repo) and not evidence.is_relative_to(ROOT),
         "Fresh external historical input evidence required")
    raw=lock.read_bytes()
    need(oid(raw)==COMMON_LOCK_OID,"Historical common Mathlib lock bytes differ")
    packages=json.loads(raw)["packages"]
    need([x["rev"] for x in packages if x["name"]=="mathlib"]==[COMMON_MATHLIB],
         "Historical Mathlib pin differs")
    compat=ROOT/spec["compatibility_patch"]["path"]
    need(digest(compat.read_bytes())==spec["compatibility_patch"]["sha256"],"Historical patch differs")
    subprocess.run(["git","apply","--check","-p1",str(compat)],cwd=repo,check=True,timeout=120)
    subprocess.run(["git","apply","-p1",str(compat)],cwd=repo,check=True,timeout=120)
    need(set(run("git","diff","--name-only","HEAD",cwd=repo).splitlines())==COMPATIBILITY_PATHS,
         "Historical compatibility patch scope differs")
    paths=set(COMPATIBILITY_PATHS)
    module_names=[]
    for row in spec["candidate_modules"]:
        module=row["module"].removeprefix("Zeta23.OPICASupport.")
        rel=module.replace(".","/")+".lean"
        target=repo/rel
        need(not target.exists(),"Historical module would overwrite native source: "+rel)
        original=re.sub(rb"^import Zeta23\.OPICASupport\.("+PREFIXES+rb")\.",rb"import \1.",
                        (ROOT/row["path"]).read_bytes(),flags=re.M)
        need(digest(original)==row["original_sha256"] and len(original)==row["original_bytes"],
             "Historical original bytes differ")
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(original)
        paths.add(rel);module_names.append(module)
    for row in spec["existing_native_modules"]:
        need(digest(read_regular(repo,row["path"]))==row["sha256"],"Historical native root source differs")
        module_names.append(row["module"])
    lake=repo/"lakefile.toml";text=lake.read_text()
    old=spec["native_mathlib"]
    need(text.count(old)==1,"Historical Lake Mathlib declaration not unique")
    text=text.replace(old,COMMON_MATHLIB)
    for prefix in sorted({m.split(".")[0] for m in module_names if not m.startswith("Zeta23.")}):
        text+='\n[[lean_lib]]\nname = "'+prefix+'"\n'
    lake.write_text(text)
    (repo/"lake-manifest.json").write_bytes(raw)
    (repo/"lean-toolchain").write_text(COMMON_TOOLCHAIN+"\n")
    paths.update(("lakefile.toml","lake-manifest.json","lean-toolchain"))
    expected={rel:digest(read_regular(repo,rel)) for rel in sorted(paths)}
    historical_changes(repo,expected)
    record={"schema":"OPICA_SUPPORT_HISTORICAL_INPUT_V1","source":source,"historical_head":HISTORICAL_HEAD,
            "historical_tree":HISTORICAL_TREE,"common_mathlib":COMMON_MATHLIB,"common_toolchain":COMMON_TOOLCHAIN,
            "lock_git_blob":COMMON_LOCK_OID,"patch_sha256":spec["compatibility_patch"]["sha256"],
            "modules":module_names,"changed_files":expected,"proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    evidence.parent.mkdir(parents=True,exist_ok=True);evidence.write_text(json.dumps(record,indent=2)+"\n")
    return record

def type_rows(log, roots):
    expressions=[json.loads(line.split("\t",1)[1]) for line in log.splitlines() if line.startswith("OPICA_TARGET\t")]
    need(len(expressions)==len(roots),"Missing compiler-derived theorem type DAGs")
    from research.RHRC.integration.opica_composition.inventory import expression_hash
    return [{"name":n,"expression":t,"sha256":expression_hash(t)} for n,t in zip(roots,expressions)]

def historical_types(repo, evidence, output):
    repo,evidence,output=repo.resolve(),evidence.resolve(),output.resolve()
    source=check()
    record=json.loads(evidence.read_text())
    need(record.get("schema")=="OPICA_SUPPORT_HISTORICAL_INPUT_V1" and record.get("source")==source,
         "Historical replay source identity differs")
    historical_checkout(repo)
    historical_changes(repo,record["changed_files"])
    need(not output.exists() and not output.is_relative_to(repo) and not output.is_relative_to(ROOT),
         "Fresh historical type output required")
    output.mkdir(parents=True)
    result={"schema":"OPICA_SUPPORT_HISTORICAL_TYPES_V1","source":source,"historical_head":HISTORICAL_HEAD,
            "historical_tree":HISTORICAL_TREE,"status":"INCOMPLETE","proof_acceptance":False,
            "RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    def command(label,argv,timeout):
        with (output/(label+".log")).open("xb") as f:
            c=subprocess.run(argv,cwd=repo,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
        need(c.returncode==0,"Historical compiler command failed: "+label)
    def packages():
        return {x["name"]:run("git","rev-parse","HEAD",cwd=repo/".lake/packages"/x["name"])
                for x in json.loads((repo/"lake-manifest.json").read_text())["packages"]}
    try:
        need("version 4.33.1" in run("lake","env","lean","--version",cwd=repo),"Wrong common compiler version")
        expected_packages={x["name"]:x["rev"] for x in json.loads((repo/"lake-manifest.json").read_text())["packages"]}
        need(packages()==expected_packages,"Historical dependency checkout differs")
        roots=source["roots"];modules=record["modules"]
        command("historical_build",["lake","build",*modules,"Zeta23.RHRC.OpicaComposition.Export"],9000)
        driver=output/"HistoricalTypeAudit.lean"
        driver.write_text("\n".join("import "+m for m in modules+["Zeta23.RHRC.OpicaComposition.Export"]) +
            "\nset_option pp.fullNames true\nset_option pp.universes false\n"+
            "\n".join("#check @"+n+"\n#print axioms "+n+"\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget "+chr(96)+n+' "type"' for n in roots)+"\n")
        command("historical_root_types",["lake","env","lean","--root="+str(output),"-DwarningAsError=true",str(driver)],3600)
        log=(output/"historical_root_types.log").read_text()
        result["axioms"]=axiom_reports(log,roots)
        rows=type_rows(log,roots)
        (output/"HISTORICAL_TYPE_CANDIDATES.json").write_text(json.dumps(rows,ensure_ascii=False,indent=2)+"\n")
        historical_changes(repo,record["changed_files"])
        need(packages()==expected_packages and check()==source,"Historical input changed during replay")
        result.update(status="PASS_HISTORICAL_TYPE_EXPORT_ONLY",type_rows_sha256=digest((output/"HISTORICAL_TYPE_CANDIDATES.json").read_bytes()),
                      input_receipt_sha256=digest(evidence.read_bytes()),dependency_commits=expected_packages)
    except BaseException as exc:
        result.update(status="INCOMPLETE_OR_REJECTED",failure=str(exc)[:2000])
        raise
    finally:
        (output/"receipt.json").write_text(json.dumps(result,indent=2)+"\n")
    return result

def compare_type_rows(native, historical, roots):
    from research.RHRC.integration.opica_composition.inventory import expression_hash
    maps=[]
    for rows in (native,historical):
        need(type(rows) is list and len(rows)==len(roots),"Exact theorem type inventory required")
        index={}
        for row in rows:
            need(set(row)=={"name","expression","sha256"} and row["name"] in roots and row["name"] not in index and
                 expression_hash(row["expression"])==row["sha256"],"Invalid compiler expression row")
            index[row["name"]]=row
        need(set(index)==set(roots),"Missing named type root")
        maps.append(index)
    return [{"name":n,"native_type_sha256":maps[0][n]["sha256"],"historical_type_sha256":maps[1][n]["sha256"]}
            for n in roots if maps[0][n]["expression"]!=maps[1][n]["expression"] or
                                maps[0][n]["sha256"]!=maps[1][n]["sha256"]]

def name_parts(n):
    out=[]
    while n!=["anonymous"]:
        need(isinstance(n,list) and len(n)==3 and n[0] in ("str","num") and isinstance(n[2],str),"Malformed binder name")
        out.append((n[0],n[2]));n=n[1]
    return tuple(reversed(out))

def relocation_only(native_expr,historical_expr,modules):
    # No general alpha normalization, no definition unfolding. Keep all
    # expression edges, names of constants, universes and binder kinds exact.
    if set(native_expr)!=set(historical_expr) or any(native_expr[k]!=historical_expr[k] for k in native_expr if k!="nodes"):return None
    a,b=native_expr["nodes"],historical_expr["nodes"]
    if len(a)!=len(b):return None
    changes=[]
    for i,(n,h) in enumerate(zip(a,b)):
        if n==h:continue
        if len(n)!=5 or len(h)!=5 or n[0]!=h[0] or n[0] not in ("forall","lam") or n[2:]!=h[2:] or n[2]!="instImplicit":return None
        np,hp=name_parts(n[1]),name_parts(h[1])
        pre=(("str","inst"),("str","_@"))
        if hp[:2]!=pre or np!=hp[:2]+(("str","Zeta23"),("str","OPICASupport"))+hp[2:]:return None
        matches=[]
        for module in modules:
            old=module.removeprefix("Zeta23.OPICASupport.")
            q=tuple(("str",p) for p in old.split("."))
            if hp[2:2+len(q)]==q and len(hp)>2+len(q) and hp[2+len(q)][0]=="num":matches.append(module)
        if len(matches)!=1:return None
        changes.append({"node":i,"module":matches[0],"native_name":n[1],"historical_name":h[1]})
    return changes

def compare_historical(native, independent, historical, output, *, reviewed_old=False):
    controller=check();roots=controller["roots"];source=controller;output=output.resolve()
    need(not output.exists() and not output.is_relative_to(ROOT),"Fresh external comparison required")
    nr,ir,hr=[json.loads((p/"receipt.json").read_text()) for p in (native,independent,historical)]
    if reviewed_old:
        need(run("git","rev-parse",REVIEWED_OLD_HEAD+"^{tree}")==REVIEWED_OLD_TREE,"Old review tree identity")
        p=json.loads((HERE/"PORT_CONTRACT.json").read_text())
        immutable=[x["path"] for x in p["candidate_modules"]+p["existing_native_modules"]]+[str((HERE/n).relative_to(ROOT)) for n in ("PORT_CONTRACT.json","HISTORICAL_PACKAGE_REGISTRY.json")]+[str(f.relative_to(ROOT)) for f in sorted((HERE/"historical_receipts").glob("*.json"))]+["lean-toolchain","lake-manifest.json"]
        need(all(run("git","rev-parse","HEAD:"+p)==run("git","rev-parse",REVIEWED_OLD_HEAD+":"+p) for p in immutable),"Old mathematical source components changed")
        source=hr["source"]
        need(source["checked_commit"]==REVIEWED_OLD_HEAD and source["checked_tree"]==REVIEWED_OLD_TREE and source["roots"]==roots and source["proof_acceptance"] is False,"Old source receipt identity")
    for record in (nr,ir):
        need(record.get("checked_commit")==source["checked_commit"] and record.get("checked_tree")==source["checked_tree"] and
             record.get("proof_acceptance") is False,"Native receipt identity differs")
    need(nr["status"]=="NATIVE_CANDIDATE_COMPILE_AXIOMS_STOCK_PASS" and
         ir["status"]=="NATIVE_CANDIDATE_INDEPENDENT_SELECTED_CLOSURE_PASS" and
         hr["status"]=="PASS_HISTORICAL_TYPE_EXPORT_ONLY" and hr["source"]==source and
         hr["historical_head"]==HISTORICAL_HEAD and hr["historical_tree"]==HISTORICAL_TREE,
         "Full native, independent and historical type receipts required")
    n,i,h=[json.loads((p/file).read_text()) for p,file in (
        (native,"NATIVE_TYPE_CANDIDATES.json"),(independent,"NATIVE_TYPE_CANDIDATES.json"),
        (historical,"HISTORICAL_TYPE_CANDIDATES.json"))]
    need(not compare_type_rows(n,i,roots),"Independent native type export differs")
    need(hr["type_rows_sha256"]==digest((historical/"HISTORICAL_TYPE_CANDIDATES.json").read_bytes()),
         "Historical exported type bytes differ")
    raw_differences=compare_type_rows(n,h,roots)
    nm={r["name"]:r for r in n};hm={r["name"]:r for r in h}
    modules=[r["module"] for r in json.loads((HERE/"PORT_CONTRACT.json").read_text())["candidate_modules"]]
    differences=[];relocations=[]
    for row in raw_differences:
        name=row["name"]
        changes=relocation_only(nm[name]["expression"],hm[name]["expression"],modules)
        if changes:relocations.append({**row,"binder_relocations":changes})
        else:differences.append(row)
    axiom_differences=[name for name in roots if nr["axioms"][name]!=ir["axioms"][name] or
                                             nr["axioms"][name]!=hr["axioms"][name]]
    result={"schema":"OPICA_SUPPORT_CROSS_PIN_TYPE_COMPARISON_V2","source":source,"review_controller":controller,
            "reviewed_old_evidence":reviewed_old,
            "historical_head":HISTORICAL_HEAD,"historical_tree":HISTORICAL_TREE,
            "status":"PASS_RELOCATION_AWARE_ROOT_TYPE_DAGS_AND_AXIOMS_ONLY" if not differences and not axiom_differences else "TYPE_OR_AXIOM_DIFFERENCES_REQUIRE_REVIEW",
            "root_count":len(roots),"exact_type_matches":len(roots)-len(raw_differences),
            "relocation_type_matches":len(relocations),"normalized_type_matches":len(roots)-len(differences),
            "raw_type_differences":raw_differences,"relocation_matches":relocations,
            "type_differences":differences,"axiom_differences":axiom_differences,
            "cross_version_definition_equivalence":"NOT_ESTABLISHED_BY_TYPE_DAG_EQUALITY",
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,indent=2)+"\n")
    need(not differences and not axiom_differences,"Historical type or axiom differences require explicit review")
    return result

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--build", type=Path)
    parser.add_argument("--checker-work", type=Path)
    parser.add_argument("--checker-code", type=Path)
    parser.add_argument("--prepare-historical", nargs=3, type=Path, metavar=("CHECKOUT","LOCK","EVIDENCE"))
    parser.add_argument("--historical-types", nargs=3, type=Path, metavar=("CHECKOUT","EVIDENCE","OUTPUT"))
    parser.add_argument("--compare-types", nargs=4, type=Path, metavar=("NATIVE","INDEPENDENT","HISTORICAL","OUTPUT"))
    parser.add_argument("--compare-reviewed-old", nargs=4, type=Path, metavar=("NATIVE","INDEPENDENT","HISTORICAL","OUTPUT"))
    parser.add_argument("--check-classification",action="store_true")
    parser.add_argument("--canonical-candidate",type=Path)
    args = parser.parse_args()
    actions=[args.build,args.receipt,args.prepare_historical,args.historical_types,args.compare_types,args.compare_reviewed_old,args.check_classification or None,args.canonical_candidate]
    need(sum(v is not None for v in actions)<=1,"Select one operation")
    if args.prepare_historical:
        prepare_historical(*args.prepare_historical);return
    if args.historical_types:
        historical_types(*args.historical_types);return
    if args.compare_types:
        compare_historical(*args.compare_types);return
    if args.compare_reviewed_old:
        compare_historical(*args.compare_reviewed_old,reviewed_old=True);return
    if args.check_classification:
        print(json.dumps(check_classification()));return
    if args.canonical_candidate:
        canonical_candidate(args.canonical_candidate);return
    need(not args.build or not args.receipt, "Select one action")
    need(bool(args.checker_work) == bool(args.checker_code) and (not args.checker_work or args.build), "Explicit independent checker inputs required")
    if args.build:
        build(args.build, checker_work=args.checker_work, checker_code=args.checker_code)
    else:
        result = check()
        if args.receipt:
            path = args.receipt.resolve()
            need(not path.exists() and not path.is_relative_to(ROOT), "Fresh external receipt required")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(result, indent=2)+"\n")
        print("SOURCE_CONTRACT_PASS: 24 authored modules; 2 inherited native modules; 167 historical roots; no proof acceptance")

if __name__ == "__main__":
    # Make the repository importable for direct script invocation.
    sys.path.insert(0, str(ROOT))
    main()
