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
POLICY_BLOB = "ddec7217bbf3a227fc631d50d4edde9295f3cf84"
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

def verify_delta(parent, current, reviewed, policy_oid, validator_oid):
    actual = delta(parent, current)
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
         policy["schema"] == "OPICA_SUPPORT_SEALED_PORT_V2" and policy["base"] == BASE and policy["base_tree"] == BASE_TREE and
         policy["proof_acceptance"] is False and all(policy[k] == "OPEN" for k in ("RH", "C1", "Step4")), "Source policy scope differs")
    need(oid(raw) == POLICY_BLOB, "Sealed policy bytes differ")
    source = read_regular(repo, VALIDATOR)
    need(normalized_validator(source) == policy["validator_template_oid"], "Sealed validator differs")
    verify_delta(parent, current, policy["reviewed"], POLICY_BLOB, oid(source))
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
    return {"schema": "OPICA_SUPPORT_CANDIDATE_SOURCE_V2", "status": "PASS_SOURCE_SCOPE_ONLY",
            "checked_commit": head, "checked_tree": tree, "base": BASE, "base_tree": BASE_TREE,
            "source_port_families": 16, "source_port_modules": 24, "existing_native_modules": 2,
            "public_root_count": 167, "roots": roots, "proof_acceptance": False,
            "current_compiler_accepted": False, "full_round4_accepted": False,
            "historical_type_equivalence": "REVIEW_PENDING", "RH": "OPEN", "C1": "OPEN", "Step4": "OPEN"}

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

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--build", type=Path)
    parser.add_argument("--checker-work", type=Path)
    parser.add_argument("--checker-code", type=Path)
    args = parser.parse_args()
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
