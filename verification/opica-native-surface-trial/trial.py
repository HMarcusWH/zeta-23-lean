"""Run a diagnostic on one R7 overlay at the original common pin."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

BASE = "42184bcd5018ad1bfec7f2a83af1dcd6cbd8b15f"
TREE = "badbdee500034ef10617499d4d3817c190c8b6d2"
HIST_ARCHIVE = "ce693f712de136f1595322e670277ddd9de1cbed098f74d1f064262b431b81d4"
HIST_EXPORT = "c2268e6b5d31255a7364b8fa9e97d402da097cdf935c100ea19f5133e574b255"
OLD_COMPARISON = "27a159604ab498e8bff13107d426a7824c2659a7879eaf306450c968ccd97497"
OLD_COMMON = "08e3e26e3e385e39b2bfca7e60a7e82c3ab1ac7342b0cdfb7b050e3e5491ad2e"
DEST = Path("Zeta23/FromPNTPlus/StrongPNTPrefix.lean")
R7 = Path("verification/opica-native-terminal")
OVERLAY = R7 / "compatibility/lean-4.35.0" / DEST
TRIAL = Path("verification/opica-native-surface-trial/trial.py")
WORKFLOW = Path(".github/workflows/opica-native-surface-trial.yml")
REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / R7))
from compare_type_surfaces import comparison, expected_modules
from epoch import staged_files
from receipts import digest, require


def git(*args):
    return subprocess.check_output(["git", "-C", REPO, *map(str, args)], text=True).strip()


def save(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def stage(work, out):
    head = os.environ["GITHUB_SHA"]
    require(git("rev-parse", "HEAD") == head, "trial checkout head mismatch")
    subprocess.run(["git", "-C", REPO, "merge-base", "--is-ancestor", BASE, head], check=True)
    require(git("rev-parse", BASE + "^{tree}") == TREE, "baseline tree mismatch")
    paths = set(git("diff", "--no-renames", "--name-only", BASE, head).splitlines())
    require(paths == set(map(str, (OVERLAY, TRIAL, WORKFLOW))), "unexpected trial source paths")
    require(not git("status", "--porcelain", "--untracked-files=no"), "dirty checkout")
    out.mkdir(parents=True, exist_ok=True)
    parent = out.parent / "r7-source"
    subprocess.run(["git", "-C", REPO, "worktree", "add", "--detach", parent, BASE], check=True)
    receipt = out / "r7-source.json"
    subprocess.run([sys.executable, "-B", parent / R7 / "epoch.py", "--repo", parent,
                    "--out", work, "--receipt", receipt, "--head", BASE], check=True)
    baseline = json.loads(receipt.read_text())
    require(baseline["head"] == BASE and baseline["tree"] == TREE, "wrong reconstructed source")
    rows = {r["destination"]: r for r in baseline["overlay"]}
    destination = work / DEST
    require(git("ls-tree", head, OVERLAY).startswith("100644 blob "), "unexpected trial source file mode")
    old_blob = git("hash-object", destination)
    require(old_blob == rows[str(DEST)]["replacement_git_blob"] == git("rev-parse", f"{BASE}:{OVERLAY}"),
            "trial source preimage drift")
    replacement_blob = git("rev-parse", f"{head}:{OVERLAY}")
    require(old_blob != replacement_blob, "trial must test a changed source")
    destination.write_bytes(subprocess.check_output(["git", "-C", REPO, "cat-file", "blob", replacement_blob]))
    changed = {"path": str(DEST), "sha256": digest(destination)}
    expected = [changed if row["path"] == str(DEST) else row for row in baseline["files"]]
    require(staged_files(work) == expected, "trial changed more than the expected source")
    save(out / "trial-source.json", {"schema": "R8_SINGLE_OVERLAY_DIAGNOSTIC", "claim": "RH_OPEN",
         "head": head, "tree": git("rev-parse", "HEAD^{tree}"), "baseline": BASE, "baseline_tree": TREE,
         "run_id": os.environ["GITHUB_RUN_ID"], "attempt": os.environ["GITHUB_RUN_ATTEMPT"],
         "destination": str(DEST), "preimage": old_blob, "postimage": replacement_blob,
         "r7_receipt_sha256": digest(receipt), "files": expected})


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
    subprocess.run(["lake", "build", *modules], cwd=work, check=True)
    env = dict(os.environ, OPICA_NATIVE_TYPE_SURFACE=str(out / "public-types.json"))
    subprocess.run(["lake", "env", "lean", "TypeSurface.lean"], cwd=work, env=env, check=True)
    verify()


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
    delta = {"schema": "R8_PUBLIC_TYPE_DIAGNOSTIC_ONLY", "claim": "RH_OPEN", "head": source["head"],
             "tree": source["tree"], "run_id": source["run_id"], "attempt": source["attempt"],
             "trial_source_sha256": digest(out / "trial-source.json"), "r7_run": 45907849844, "r7_attempt": 1,
             "historical_artifact": 15161592519, "comparison_artifact": 15164550350,
             "old_changed": len(before), "new_changed": len(after), "restored": sorted(before - after - missing),
             "regressed": sorted(after - before), "missing": report["missing"], "extra": report["extra"],
             "comparison_sha256": digest(out / "r7-comparison.json"), "exact_surface": report["status"]}
    save(out / "trial-result.json", delta)
    print(json.dumps(delta), flush=True)
    require(report["common_count"] == 355 and report["status"] == "PASS", "full public surface still differs")


if __name__ == "__main__":
    mode = sys.argv[1]
    argv = [Path(arg).resolve() for arg in sys.argv[2:]]
    {"stage": stage, "compile": run_compiler, "compare": compare}[mode](*argv)
