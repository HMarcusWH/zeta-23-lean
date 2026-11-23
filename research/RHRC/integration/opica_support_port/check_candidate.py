"""Source-pinned historical candidate validation; never a proof promotion."""
from pathlib import Path
import hashlib, json, subprocess, sys, re

BASE = "bb7c8184a135b2823c6296917c5ac893bebf2a71"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def need(condition, message):
    if not condition:
        raise SystemExit(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def run(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()

def main():
    p = json.loads((HERE / "PORT_CONTRACT.json").read_text())
    registry = json.loads((HERE / "HISTORICAL_PACKAGE_REGISTRY.json").read_text())
    need(len(registry["packages"]) == 16, "Historical package census changed")
    need(run("git", "merge-base", BASE, "HEAD") == BASE, "Wrong native ancestor")
    need((ROOT / "lean-toolchain").read_text().strip() == p["native_toolchain"], "Native toolchain changed")
    need(json.loads((ROOT / "lake-manifest.json").read_text())["packages"] != [], "Missing manifest")
    mathlib = [q for q in json.loads((ROOT / "lake-manifest.json").read_text())["packages"] if q["name"] == "mathlib"]
    need(len(mathlib) == 1 and mathlib[0]["rev"] == p["native_mathlib"], "Wrong Mathlib revision")
    need(run("git", "status", "--porcelain", "--untracked-files=all") == "", "Dirty checkout")
    actual = set(run("git", "ls-files", "Zeta23/OPICASupport").splitlines())
    expected = {r["path"] for r in p["candidate_modules"]}
    need(actual == expected and len(actual) == 13, "Unreviewed module inventory")
    for r in p["candidate_modules"]:
        raw = (ROOT / r["path"]).read_bytes()
        need(digest(raw) == r["ported_sha256"], "Changed source " + r["path"])
        original = re.sub(rb"^import Zeta23\.OPICASupport\.(OPICAStep4|FourierBridge|FourierEnergy|SamplingDensity|ParityRational)\.", rb"import \1.", raw, flags=re.M)
        need(digest(original) == r["original_sha256"] and len(original) == r["original_bytes"], "Not import-only relocation " + r["path"])
    for r in registry["packages"]:
        b = (HERE / "historical_receipts" / Path(r["bundle_receipt_path"]).name).read_bytes()
        need(digest(b) == r["receipt_sha256"], "Historical receipt changed")
    roots = [n for r in p["historical_package_roots"] if r["index"] <= 8 for n in r["receipt_roots"]]
    need(len(roots) == 72 and len(set(roots)) == 72, "Public root inventory differs")
    if len(sys.argv) == 1:
        print("SOURCE_CONTRACT_PASS: 13 candidates, 72 historical root names, 16 archived receipt records; native proof acceptance pending")
        return
    output = Path(sys.argv[1]).resolve()
    need(output != ROOT and ROOT not in output.parents, "Output must remain outside checkout")
    output.mkdir(parents=True, exist_ok=True)
    modules = [r["module"] for r in p["candidate_modules"]]
    audit = output / "Audit.lean"
    audit.write_text("\n".join("import " + m for m in modules) + "\nset_option pp.fullNames true\nset_option pp.universes false\n" + "\n".join("#check @" + n + "\n#print axioms " + n for n in roots) + "\n")
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "build", *modules], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (output / "root_audit.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(audit)], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    s = (output / "root_audit.log").read_text()
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    found = {}
    for line in s.splitlines():
        m = re.match(r"^'(.+)' depends on axioms: \[(.*)\]$", line)
        if m:
            name, raw = m.groups()
            need(name in roots and name not in found, "Unknown or duplicate axiom report " + name)
            names = {x.strip() for x in raw.split(",") if x.strip()}
            need(names <= allowed, "Nonstandard axiom " + name)
            found[name] = sorted(names)
        else:
            m = re.match(r"^'(.+)' does not depend on any axioms$", line)
            if m:
                name = m.group(1)
                need(name in roots and name not in found, "Unknown or duplicate axiom report")
                found[name] = []
    need(set(found) == set(roots), "Incomplete root axiom reports")
    need(run("git", "status", "--porcelain", "--untracked-files=all") == "", "Source boundary changed")
    result = {"status":"NATIVE_CANDIDATE_COMPILE_AND_AXIOM_PASS", "head":run("git","rev-parse","HEAD"), "tree":run("git","rev-parse","HEAD^{tree}"), "roots":found, "independent_full_closure":"NOT_RUN", "exact_historical_type_equivalence":"REVIEW_PENDING", "proof_acceptance":False, "RH":"OPEN", "C1":"OPEN", "Step4":"OPEN"}
    (output / "receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])

if __name__ == "__main__":
    main()
