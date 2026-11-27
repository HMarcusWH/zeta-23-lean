"""Run one source-locked cumulative R7 public-type diagnostic at the common pin."""
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

import operator_audit

BASE = "42184bcd5018ad1bfec7f2a83af1dcd6cbd8b15f"
TREE = "badbdee500034ef10617499d4d3817c190c8b6d2"
HIST_ARCHIVE = "ce693f712de136f1595322e670277ddd9de1cbed098f74d1f064262b431b81d4"
HIST_EXPORT = "c2268e6b5d31255a7364b8fa9e97d402da097cdf935c100ea19f5133e574b255"
OLD_COMPARISON = "27a159604ab498e8bff13107d426a7824c2659a7879eaf306450c968ccd97497"
OLD_COMMON = "08e3e26e3e385e39b2bfca7e60a7e82c3ab1ac7342b0cdfb7b050e3e5491ad2e"
FIRST_TRIAL = "23436c2abcac5c92850aabbe55330f1b1a3d09a1"
FIRST_TREE = "719f8f4eca8b6835a0ac30d6594129e6f08b6a5d"
PREVIOUS_TRIAL = "50593c3d0a9174c9f809a3b9b8e87ba404f23286"
PREVIOUS_TREE = "b15e6008cc273c64ea8e7ec9f6e8377d2bb16391"
R7 = Path("verification/opica-native-terminal")
OVERLAYS = R7 / "compatibility/lean-4.35.0"
HELPER = "Zeta23/OPICACompatibility/ContinuousENorm.lean"
HELPER_SOURCE = {"repository": "leanprover-community/mathlib4",
                "commit": "51e6992efd06126df61a496bebf8f49482a4e129",
                "path": "Mathlib/Analysis/Normed/Group/Continuity.lean",
                "blob": "062cd64a5c88bf2303d8a24bc2b486ca3cf2d427",
                "declaration": "SeminormedGroup.toContinuousENorm"}
TRIAL = Path("verification/opica-native-surface-trial/trial.py")
WORKFLOW = Path(".github/workflows/opica-native-surface-trial.yml")
MANIFEST = TRIAL.with_name("R8_TRIAL_SOURCES.json")
OPERATOR_AUDIT = TRIAL.with_name("operator_audit.py")
REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / R7))
from compare_type_surfaces import comparison, expected_modules
from epoch import staged_files
from receipts import digest, require


def git(*args):
    return subprocess.check_output(["git", "-C", REPO, *map(str, args)], text=True).strip()


def save(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def source_plan(head):
    manifest = json.loads(git("show", f"{head}:{MANIFEST}"))
    require(manifest["schema"] == "R8_CUMULATIVE_SURFACE_SOURCES_V1" and manifest["r7"] == BASE
            and manifest["first_trial"] == FIRST_TRIAL, "incorrect diagnostic source baseline")
    rows = manifest["sources"]
    names = [r["destination"] for r in rows]
    require(bool(names) and names == sorted(set(names)), "duplicate or unsorted source paths")
    inventory = json.loads(git("show", f"{BASE}:{OVERLAYS}/OVERLAY_MANIFEST.json"))
    permitted = {r["destination"]: r["replacement_git_blob"] for r in inventory["replacements"]
                 if r["destination"].removesuffix(".lean").replace("/", ".") in expected_modules()}
    require("Zeta23/FromPNTPlus/StrongPNTPrefix.lean" in names, "original diagnostic module missing")
    producers = {n.replace(".", "/") + ".lean" for n in operator_audit.PRODUCERS.values()}
    for row in rows:
        path = row["destination"]
        require(path in permitted or path == HELPER or path in producers, "unexpected mathematical source: " + path)
        source = OVERLAYS / path
        require(git("ls-tree", head, source).startswith("100644 blob "), "unexpected source mode: " + path)
        actual = git("rev-parse", f"{head}:{source}")
        require(actual == row["postimage"] and actual != row["preimage"], "trial postimage mismatch: " + path)
        if path == HELPER:
            require(row["preimage"] is None and not git("ls-tree", BASE, source)
                    and not git("ls-tree", BASE, path), "unexpected existing helper")
            require(row.get("attribution") == HELPER_SOURCE, "compatibility helper origin mismatch")
        elif path in producers:
            require(not git("ls-tree", BASE, source) and row["preimage"] == git("rev-parse", f"{BASE}:{path}"),
                    "additional producer baseline preimage mismatch")
            expected = row["common_pin_inventory"]
            require(isinstance(expected["count"], int) and expected["count"] > 0 and
                    expected["changed"] == sorted(set(expected["changed"])) and
                    all(re.fullmatch(r"[0-9a-f]{64}", expected[key])
                        for key in ("baseline_inventory_sha256", "candidate_inventory_sha256")), "invalid additional producer scope")
        else:
            require(row["preimage"] == permitted[path] == git("rev-parse", f"{BASE}:{source}"),
                    "R7 source preimage mismatch: " + path)
    allowed = {str(p) for p in (TRIAL, WORKFLOW, MANIFEST, OPERATOR_AUDIT)} | {str(OVERLAYS / name) for name in names}
    paths = set(git("diff", "--no-renames", "--name-only", BASE, head).splitlines())
    require(paths == allowed, "cumulative diff disagrees with the bounded source manifest")
    return rows


def stage(work, out):
    head = os.environ["GITHUB_SHA"]
    require(git("rev-parse", "HEAD") == head, "trial checkout head mismatch")
    subprocess.run(["git", "-C", REPO, "merge-base", "--is-ancestor", PREVIOUS_TRIAL, head], check=True)
    require(git("rev-parse", BASE + "^{tree}") == TREE and git("rev-parse", FIRST_TRIAL + "^{tree}") == FIRST_TREE
            and git("rev-parse", PREVIOUS_TRIAL + "^{tree}") == PREVIOUS_TREE,
            "baseline tree mismatch")
    require(not git("status", "--porcelain", "--untracked-files=no"), "dirty checkout")
    plan = source_plan(head)
    out.mkdir(parents=True, exist_ok=True)
    parent = out.parent / "r7-source"
    subprocess.run(["git", "-C", REPO, "worktree", "add", "--detach", parent, BASE], check=True)
    receipt = out / "r7-source.json"
    subprocess.run([sys.executable, "-B", parent / R7 / "epoch.py", "--repo", parent,
                    "--out", work, "--receipt", receipt, "--head", BASE], check=True)
    baseline = json.loads(receipt.read_text())
    require(baseline["head"] == BASE and baseline["tree"] == TREE, "wrong reconstructed source")
    expected = {r["path"]: r["sha256"] for r in baseline["files"]}
    for row in plan:
        path = row["destination"]
        destination = work / path
        if row["preimage"] is None:
            require(not destination.exists() and path not in expected, "helper already present in baseline")
        else:
            require(git("hash-object", destination) == row["preimage"], "stage preimage mismatch: " + path)
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("wb") as dest:
            subprocess.run(["git", "-C", REPO, "cat-file", "blob", row["postimage"]], stdout=dest, check=True)
        expected[path] = digest(destination)
    actual = staged_files(work)
    require(len(actual) == len(expected) and {r["path"]: r["sha256"] for r in actual} == expected,
            "unmanifested effective source change")
    save(out / "trial-source.json", {"schema": "R8_CUMULATIVE_DIAGNOSTIC", "claim": "RH_OPEN",
         "head": head, "tree": git("rev-parse", "HEAD^{tree}"), "baseline": BASE, "baseline_tree": TREE,
         "first_trial": FIRST_TRIAL, "run_id": os.environ["GITHUB_RUN_ID"], "attempt": os.environ["GITHUB_RUN_ATTEMPT"],
         "sources": plan, "r7_receipt_sha256": digest(receipt), "manifest_sha256": digest(REPO / MANIFEST),
         "files": actual})


def run_compiler(work, out):
    receipt = json.loads((out / "trial-source.json").read_text())
    require(receipt["head"] == git("rev-parse", "HEAD") == os.environ["GITHUB_SHA"], "trial head mismatch")
    parent_epoch = out.parent / "r7-source" / R7 / "epoch.py"
    def verify():
        subprocess.run([sys.executable, "-B", parent_epoch, "--out", work, "--verify-pins"], check=True)
        require(staged_files(work) == receipt["files"], "effective trial source drift")
    verify()
    require(not any((work / ".lake/build").rglob("*.olean")), "pre-existing project object")
    modules = [line.split()[1] for line in (work / "TypeSurface.lean").read_text().splitlines()
               if line.startswith("import Zeta23.")]
    require(len(modules) == 20 and set(modules) == expected_modules() | {"Zeta23.FromPNTPlus.Tactic.AdditiveCombination"},
            "exporter import inventory changed")
    if any(r["destination"] == "Zeta23/CCM/DictionaryTentArchLimit.lean" for r in receipt["sources"]):
        bridge = "Zeta23.CCM.DictionaryZeroSideBridge"
        subprocess.run(["lake", "build", bridge], cwd=work, check=True)
        chain = [operator_audit.PRODUCERS["tent"], "Zeta23.CCM.DictionaryTentEFExtension", bridge]
        with (out / "companion-bridge-kernel.log").open("w") as log:
            for module in chain:
                subprocess.run(["lake", "env", "leanchecker", "--verbose", module], cwd=work,
                               stdout=log, stderr=subprocess.STDOUT, check=True)
        save(out / "companion-bridge.json", {"head": receipt["head"], "tree": receipt["tree"],
             "compiled": bridge, "stock_kernel_replays": chain, "claim": "RH_OPEN"})
    subprocess.run(["lake", "build", *modules], cwd=work, check=True)
    env = dict(os.environ, OPICA_NATIVE_TYPE_SURFACE=str(out / "public-types.json"))
    subprocess.run(["lake", "env", "lean", "TypeSurface.lean"], cwd=work, env=env, check=True)
    verify()


def audit_producer(work, out, role):
    receipt = json.loads((out / "trial-source.json").read_text())
    require(receipt["head"] == git("rev-parse", "HEAD") == os.environ["GITHUB_SHA"], "trial head mismatch")
    destination = operator_audit.PRODUCERS[role].replace(".", "/") + ".lean"
    rows = [r for r in receipt["sources"] if r["destination"] == destination]
    if rows:
        require(staged_files(work) == receipt["files"], "operator trial source drift")
        operator_audit.run(work, out, REPO, BASE, rows[0]["common_pin_inventory"], role)


def compare(out, historical_archive, comparison_archive):
    require(digest(historical_archive) == HIST_ARCHIVE and digest(comparison_archive) == OLD_COMPARISON,
            "frozen R7 artifact archive digest mismatch")
    historical = out.parent / "historical-public-types.json"
    with zipfile.ZipFile(historical_archive) as z:
        meta = json.loads(z.read("historical.json"))
        require((meta["head"], meta["tree"], meta["status"]) == (BASE, TREE, "PASS"), "historical identity drift")
        with z.open("public-types.json") as source, historical.open("wb") as target:
            shutil.copyfileobj(source, target, 2**20)
    require(digest(historical) == HIST_EXPORT, "historical compiler export digest mismatch")
    with zipfile.ZipFile(comparison_archive) as z:
        prior = json.loads(z.read("type-comparison.json"))
    require(prior["common_sha256"] == OLD_COMMON and prior["historical_sha256"] == HIST_EXPORT and
            not prior["missing"] and not prior["extra"] and len(prior["changed"]) == 94,
            "original comparison receipt drift")
    report = comparison(historical, out / "public-types.json")
    require(report["historical_count"] == 355, "unexpected historical declaration count")
    save(out / "r7-comparison.json", report)
    before, after = (set(map(tuple, x["changed"])) for x in (prior, report))
    missing = set(map(tuple, report["missing"]))
    source = json.loads((out / "trial-source.json").read_text())
    per_module = {}
    for module in report["modules"]:
        old = {name for m, name in before if m == module}
        now = {name for m, name in after if m == module}
        lost = {name for m, name in missing if m == module}
        per_module[module] = {"previously_changed": len(old), "changed": len(now),
                              "restored": sorted(old - now - lost), "regressed": sorted(now - old),
                              "missing": sorted(lost), "extra": sorted(n for m, n in report["extra"] if m == module)}
    delta = {"schema": "R8_PUBLIC_TYPE_DIAGNOSTIC_ONLY", "claim": "RH_OPEN", "head": source["head"],
             "tree": source["tree"], "run_id": source["run_id"], "attempt": source["attempt"],
             "trial_source_sha256": digest(out / "trial-source.json"), "r7_run": 45907849844, "r7_attempt": 1,
             "historical_artifact": 15161592519, "comparison_artifact": 15164550350,
             "old_changed": len(before), "new_changed": len(after), "restored": sorted(before - after - missing),
             "regressed": sorted(after - before), "missing": report["missing"], "extra": report["extra"],
             "per_module": per_module, "comparison_sha256": digest(out / "r7-comparison.json"), "exact_surface": report["status"]}
    save(out / "trial-result.json", delta)
    print(json.dumps(delta), flush=True)
    require(report["common_count"] == 355 and report["status"] == "PASS", "full public surface still differs")


if __name__ == "__main__":
    mode = sys.argv[1]
    argv = [Path(arg).resolve() for arg in sys.argv[2:]]
    if mode in operator_audit.PRODUCERS:
        audit_producer(*argv, role=mode)
    else:
        {"stage": stage, "compile": run_compiler, "compare": compare}[mode](*argv)
