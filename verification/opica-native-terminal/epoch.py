#!/usr/bin/env python3
"""Reconstruct the exact committed R4 source overlay, never mutate the historical checkout."""
import argparse, copy, io, json, os, pathlib, re, subprocess, tarfile
from port import verify_files, require, git, BASE, BASE_TREE, MATHLIB, HERE, PREFIX, sha, blob

P = pathlib.Path
V = "verification/opica-native-terminal/"
R0 = "b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736"
R0_TREE = "ad3dc3ced9a58dbd4619f8635600791a692bce34"
R1 = "c109fb02385bd4f7a00890594478e3bf664cbd14"
R1_TREE = "855dfc4d6f9126be4b7078e0772e2b7c1bda3b4d"
R2 = "cfc0e6bc92be1db226d4a84f9542ace9c4868e16"
R2_TREE = "1732a82a22c6d48230a865c81249aa090b428afe"
R3 = "176e582916156e1df90252aeb7746dd904f24983"
R3_TREE = "11ebe592671e8e604d86ab851dc39dabdef7f02c"
REPAIR_PATH = V + "REPAIR_MANIFEST.json"
R1_PATH = V + "history/R1_REPAIR_MANIFEST.json"
R2_PATH = V + "history/R2_REPAIR_MANIFEST.json"
R3_PATH = V + "history/R3_REPAIR_MANIFEST.json"
PORT_PATH = V + "PORT_MANIFEST.json"
OVERLAY_DIR = V + "compatibility/lean-4.35.0/"
OVERLAY_PATH = OVERLAY_DIR + "OVERLAY_MANIFEST.json"
TOOLCHAIN = "leanprover/lean4:v4.35.0"
TERMINAL = "Zeta23/OPICANativeTerminal/Terminal.lean"
TERMINAL_BLOB = "7f1e2cc138279c91e6972d1046d5528c5d9536a6"
ADAPTER = "Zeta23Arithmetic/NativePrincipal.lean"
ADAPTER_BLOB = "310daf8dce577ab1fb3dcbb454f3e1af00f8204a"
WORKFLOW = ".github/workflows/opica-native-step4.yml"
R4_NEW_DESTINATIONS = {
    "Zeta23/CCM/UniversalSincSourceCharacteristic.lean",
    "Zeta23/Analytic/RectangleLogDeriv.lean",
    "Zeta23/WeilEF/Landau.lean",
    "Zeta23/ThmE/IntMuChi.lean",
}
R4_SCOPE = {
    ".github/workflows/opica-native-step4.yml",
    "verification/opica-native-terminal/epoch.py",
    "verification/opica-native-terminal/run.sh",
    "verification/opica-native-terminal/receipts.py",
    "verification/opica-native-terminal/compare.py",
    "verification/opica-native-terminal/compare_type_surfaces.py",
    "verification/opica-native-terminal/TypeSurface.lean",
    "verification/opica-native-terminal/historical.sh",
    "verification/opica-native-terminal/stage_controls.py",
    "verification/opica-native-terminal/checker-preflight.sh",
    "verification/opica-native-terminal/admission.py",
    "verification/opica-native-terminal/README.md",
    "verification/opica-native-terminal/compatibility/lean-4.35.0/OVERLAY_MANIFEST.json",
    "verification/opica-native-terminal/history/R3_REPAIR_MANIFEST.json",
    "verification/opica-native-terminal/compatibility/lean-4.35.0/Zeta23/CCM/UniversalSincSourceCharacteristic.lean",
    "verification/opica-native-terminal/compatibility/lean-4.35.0/Zeta23/Analytic/RectangleLogDeriv.lean",
    "verification/opica-native-terminal/compatibility/lean-4.35.0/Zeta23/WeilEF/Landau.lean",
    "verification/opica-native-terminal/compatibility/lean-4.35.0/Zeta23/ThmE/IntMuChi.lean",
}
CONFIG = '''name = "Zeta23"
version = "0.1.0"
defaultTargets = ["Zeta23Arithmetic", "Zeta23NativeTerminal"]
moreLeanArgs = ["--tstack=400000"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
maxHeartbeats = 800000

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "56a005855ea17e0b0958f73ec801ae140b0a1679"

[[lean_lib]]
name = "Zeta23"
roots = ["Zeta23"]
globs = ["Zeta23"]

[[lean_lib]]
name = "Zeta23Arithmetic"
roots = ["Zeta23Arithmetic"]
globs = ["Zeta23Arithmetic.+"]
leanOptions = { autoImplicit = false, relaxedAutoImplicit = false, maxSynthPendingDepth = 3, maxHeartbeats = 4000000, pp.unicode.fun = true }

[[lean_lib]]
name = "Zeta23NativeTerminal"
roots = ["Zeta23.OPICANativeTerminal.Terminal"]
globs = ["Zeta23.OPICANativeTerminal.Terminal"]

[[lean_lib]]
name = "AuditSmokeFixtures"
roots = ["AuditSmokeFixtures"]
globs = ["AuditSmokeFixtures"]

[[lean_lib]]
name = "Challenge"
srcDir = "comparator"
roots = ["Challenge.NativeRH"]
globs = ["Challenge.NativeRH"]

[[lean_lib]]
name = "Solution"
srcDir = "comparator"
roots = ["Solution.NativeRH"]
globs = ["Solution.NativeRH"]
'''

def object_at(repo, rev, path):
    r = subprocess.run(["git", "-C", str(repo), "rev-parse", "--verify", rev + ":" + path],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    return r.stdout.strip() if r.returncode == 0 else None

def committed(repo, head, path):
    return git(repo, "show", head + ":" + path)

def safe_path(path):
    q = pathlib.PurePosixPath(path)
    require(bool(path) and not q.is_absolute() and ".." not in q.parts and
            q.as_posix() == path and "\\" not in path, "unsafe path " + path)
    return q

def validate_overlay(repo, head, overlay):
    prior = json.loads(committed(repo, R3, OVERLAY_PATH))
    require(prior["version"] == "R3" and len(prior["replacements"]) == 10,
            "R3 overlay identity drift")
    previous = {r["destination"]: r for r in prior["replacements"]}
    require(len(previous) == 10 and not set(previous) & R4_NEW_DESTINATIONS,
            "R3 overlay inventory drift")
    require(overlay["version"] == "R4" and
            {k: v for k, v in overlay.items() if k not in {"version", "replacements"}} ==
            {k: v for k, v in prior.items() if k not in {"version", "replacements"}} and
            overlay["schema"] == "OPICA_NATIVE_COMPATIBILITY_OVERLAY_V1" and
            overlay["native_base"] == R0 and overlay["toolchain"] == TOOLCHAIN and
            overlay["mathlib"] == MATHLIB, "overlay identity drift")
    expected = set(previous) | R4_NEW_DESTINATIONS
    rows = overlay["replacements"]
    dests = [r["destination"] for r in rows]
    require(len(dests) == len(set(dests)) == 14 and set(dests) == expected,
            "overlay destinations incomplete or unexpected")
    physical = set(git(repo, "ls-tree", "-r", "--name-only", head, "--", OVERLAY_DIR)
                   .decode().splitlines())
    require(physical == {OVERLAY_PATH} | {OVERLAY_DIR + p for p in expected},
            "unlisted or missing overlay file")
    history = json.loads(committed(repo, R1, REPAIR_PATH))
    r1 = {r["path"]: r for r in history["changes"]
          if r["path"].startswith("Zeta23/") and r["old_git_blob"]}
    require(set(r1) == set(previous), "R1 mathematical repair inventory drift")
    for r in rows:
        p, repl = r["destination"], r["replacement_path"]
        safe_path(p); safe_path(repl)
        require(repl == OVERLAY_DIR + p and p != TERMINAL and
                not p.startswith(PREFIX + "/") and
                r["statement_policy"] == (previous[p]["statement_policy"] if p in previous else "PRESERVE") and
                bool(r["reason"]), "overlay destination/policy drift " + p)
        original = r["historical_git_blob"]
        for rev in (BASE, R0, R2, R3, head):
            require(object_at(repo, rev, p) == original, "historical blob drift " + p)
        if p in previous:
            require(r == previous[p] and
                    object_at(repo, R3, repl) == r["replacement_git_blob"] and
                    original == r1[p]["old_git_blob"] and
                    r["r1_replacement_git_blob"] == r1[p]["new_git_blob"] and
                    object_at(repo, R1, p) == r1[p]["new_git_blob"],
                    "frozen overlay/ancestry drift " + p)
        else:
            require(set(r) == {"destination", "historical_git_blob", "replacement_path",
                               "replacement_git_blob", "introduced_in", "statement_policy", "reason"} and
                    r["introduced_in"] == "R4" and object_at(repo, R1, p) == original and
                    object_at(repo, R3, repl) is None and r["replacement_git_blob"] != original,
                    "new R4 overlay ancestry drift " + p)
        require(object_at(repo, head, repl) == r["replacement_git_blob"] and
                blob(committed(repo, head, repl)) == r["replacement_git_blob"] and
                blob((repo / repl).read_bytes()) == r["replacement_git_blob"],
                "replacement blob drift " + p)
    return rows

def validate_scope(repo, head, m):
    require(m["schema"] == "OPICA_NATIVE_REPAIR_MANIFEST_V4" and m["version"] == "R4",
            "bad repair manifest schema")
    require(m["baseline_commit"] == R3 and m["baseline_tree"] == R3_TREE and
            m["acquisition_commit"] == R0 and m["acquisition_tree"] == R0_TREE and
            m["native_base"] == BASE, "repair baseline mismatch")
    for rev, tree in ((BASE, BASE_TREE), (R0, R0_TREE), (R1, R1_TREE), (R2, R2_TREE), (R3, R3_TREE)):
        require(git(repo, "rev-parse", rev + "^{tree}").decode().strip() == tree,
                "baseline tree drift " + rev)
    require(m["claim"] == "RH_OPEN", "invalid claim promotion")
    for prior_base, prior_tree, rev, archive, version in (
            (R0, R0_TREE, R1, R1_PATH, "R1"),
            (R1, R1_TREE, R2, R2_PATH, "R2"),
            (R2, R2_TREE, R3, R3_PATH, "R3")):
        require(committed(repo, head, archive) == committed(repo, rev, REPAIR_PATH),
                version + " manifest history drift")
        prior = json.loads(committed(repo, rev, REPAIR_PATH))
        require(prior["version"] == version and prior["baseline_commit"] == prior_base and
                prior["baseline_tree"] == prior_tree and prior["claim"] == "RH_OPEN",
                version + " history identity drift")
        prior_paths = [r["path"] for r in prior["changes"]]
        require(len(prior_paths) == len(set(prior_paths)) and REPAIR_PATH not in prior_paths and
                set(git(repo, "diff", "--name-only", prior_base, rev).decode().splitlines()) ==
                    set(prior_paths) | {REPAIR_PATH}, version + " historical scope drift")
        for row in prior["changes"]:
            p = row["path"]; safe_path(p)
            require(object_at(repo, prior_base, p) == row["old_git_blob"] and
                    object_at(repo, rev, p) == row["new_git_blob"], version + " historical blob drift " + p)
    require(committed(repo, head, PORT_PATH) == committed(repo, R0, PORT_PATH),
            "original port manifest modified")
    rows = validate_overlay(repo, head, json.loads(committed(repo, head, OVERLAY_PATH)))
    changes = m["changes"]
    paths = [r["path"] for r in changes]
    require(len(paths) == len(set(paths)) and set(paths) == R4_SCOPE,
            "unexpected R4 repair inventory")
    changed = set(git(repo, "diff", "--name-only", R3, head).decode().splitlines())
    require(changed == set(paths) | {REPAIR_PATH},
            "repair scope drift: " + str(sorted(changed.symmetric_difference(set(paths) | {REPAIR_PATH}))))
    for r in changes:
        p = r["path"]; safe_path(p)
        require(p in R4_SCOPE and p != PORT_PATH and p != TERMINAL,
                "frozen or unapproved path " + p)
        require(object_at(repo, R3, p) == r["old_git_blob"] and
                object_at(repo, head, p) == r["new_git_blob"] and
                r["new_git_blob"] is not None and r["old_git_blob"] != r["new_git_blob"],
                "repair blob drift " + p)
        require(blob((repo / p).read_bytes()) == r["new_git_blob"], "working tree drift " + p)
        policy = "PRESERVE" if p in {OVERLAY_DIR + d for d in R4_NEW_DESTINATIONS} else "VERIFICATION_ONLY"
        require(bool(r["reason"]) and r["statement_policy"] == policy, "unclassified repair " + p)
    native_delta = set(git(repo, "diff", "--name-only", BASE, head, "--", "Zeta23", "Zeta23.lean")
                       .decode().splitlines())
    require(native_delta == {TERMINAL, "Zeta23/OPICANativeTerminal/AuditCore.lean"},
            "historical native tree drift " + str(native_delta))
    require(not git(repo, "diff", "--name-only", R3, head, "--", PREFIX).strip(),
            "arithmetic source changed")
    require(object_at(repo, head, TERMINAL) == TERMINAL_BLOB, "terminal changed")
    require(object_at(repo, head, ADAPTER) == ADAPTER_BLOB, "R1 principal adapter changed")
    require(committed(repo, head, ADAPTER) == committed(repo, head, V + "PrincipalStrip.lean"),
            "principal template drift")
    return rows

def reject(fn, description):
    try:
        fn()
    except (RuntimeError, ValueError, KeyError, subprocess.CalledProcessError, FileNotFoundError):
        return
    raise RuntimeError("negative control accepted: " + description)

def test_scope(repo, head):
    m = json.loads(committed(repo, head, REPAIR_PATH))
    validate_scope(repo, head, m)
    mutations = []
    a = copy.deepcopy(m); a["changes"].append(copy.deepcopy(a["changes"][0])); mutations.append(a)
    a = copy.deepcopy(m); a["changes"][0]["new_git_blob"] = "0" * 40; mutations.append(a)
    a = copy.deepcopy(m); a["changes"].pop(); mutations.append(a)
    a = copy.deepcopy(m); a["baseline_tree"] = "0" * 40; mutations.append(a)
    a = copy.deepcopy(m); a["claim"] = "RH_PROVED"; mutations.append(a)
    a = copy.deepcopy(m); a["baseline_commit"] = R2; mutations.append(a)
    a = copy.deepcopy(m); a["changes"][0]["path"] = TERMINAL; mutations.append(a)
    a = copy.deepcopy(m); a["changes"][0]["old_git_blob"] = "0" * 40; mutations.append(a)
    for i, a in enumerate(mutations):
        reject(lambda a=a: validate_scope(repo, head, a), "manifest " + str(i))
    overlay = json.loads(committed(repo, head, OVERLAY_PATH))
    om = []
    a = copy.deepcopy(overlay); a["replacements"].pop(); om.append(a)
    a = copy.deepcopy(overlay); a["replacements"].append(copy.deepcopy(a["replacements"][0])); om.append(a)
    for key, value in (("destination", TERMINAL), ("destination", ADAPTER),
                       ("replacement_path", "../escape"), ("replacement_git_blob", "0" * 40),
                       ("historical_git_blob", "0" * 40)):
        a = copy.deepcopy(overlay); a["replacements"][0][key] = value; om.append(a)
    a = copy.deepcopy(overlay); a["toolchain"] = "leanprover/lean4:v4.33.0-rc2"; om.append(a)
    a = copy.deepcopy(overlay); a["mathlib"] = "0" * 40; om.append(a)
    untouched = next(i for i, row in enumerate(overlay["replacements"])
                     if row["destination"] not in R4_NEW_DESTINATIONS)
    a = copy.deepcopy(overlay); a["replacements"][untouched]["reason"] += " (unauthorized)"; om.append(a)
    repaired = next(i for i, row in enumerate(overlay["replacements"])
                    if row["destination"] in R4_NEW_DESTINATIONS)
    a = copy.deepcopy(overlay); a["replacements"][repaired]["introduced_in"] = "R1"; om.append(a)
    a = copy.deepcopy(overlay); a["replacements"][repaired]["r1_replacement_git_blob"] = "0" * 40; om.append(a)
    a = copy.deepcopy(overlay); a["replacements"][repaired]["historical_git_blob"] = "0" * 40; om.append(a)
    a = json.loads(committed(repo, R3, OVERLAY_PATH)); om.append(a)
    for i, a in enumerate(om):
        reject(lambda a=a: validate_overlay(repo, head, a), "overlay " + str(i))
    print("NATIVE_R4_SCOPE_CONTROLS_PASS", len(mutations) + len(om), flush=True)

def staged_files(out):
    paths = []
    for root, dirs, files in os.walk(out):
        dirs[:] = sorted(d for d in dirs if d != ".lake")
        for d in dirs:
            require(not (P(root) / d).is_symlink(), "symlink in staged source")
        for f in files:
            p = P(root) / f
            require(not p.is_symlink(), "symlink in staged source")
            paths.append(p)
    return [{"path": p.relative_to(out).as_posix(), "sha256": sha(p.read_bytes())}
            for p in sorted(paths)]

def verify_stage(out, receipt):
    r = json.loads(receipt.read_text())
    require(r["schema"] == "NATIVE_TERMINAL_REPAIR_EPOCH_V4" and
            r["claim"] == "RH_OPEN" and r["toolchain"] == TOOLCHAIN and
            r["mathlib"] == MATHLIB and r["repair_baseline"] == R3 and
            r["acquisition_commit"] == R0 and r["native_base"] == BASE and
            len(r["overlay"]) == 14, "source receipt schema drift")
    require(staged_files(out) == r["files"], "effective staged source drift")
    require(blob((out / TERMINAL).read_bytes()) == TERMINAL_BLOB, "effective terminal changed")
    require(blob((out / ADAPTER).read_bytes()) == ADAPTER_BLOB, "effective adapter changed")
    for row in r["overlay"]:
        require(blob((out / row["destination"]).read_bytes()) == row["replacement_git_blob"],
                "effective overlay drift " + row["destination"])
    print("NATIVE_R4_EFFECTIVE_SOURCE_PASS", r["head"], len(r["files"]), flush=True)

def stage(repo, out, receipt, head):
    require(git(repo, "rev-parse", "HEAD").decode().strip() == head, "checkout HEAD drift")
    require(not git(repo, "status", "--porcelain", "--untracked-files=no").strip(), "dirty repository")
    m = json.loads(committed(repo, head, REPAIR_PATH))
    overlay = validate_scope(repo, head, m)
    manifest = verify_files(repo, {ADAPTER: ADAPTER_BLOB})
    require(not out.exists(), "epoch already exists")
    out.mkdir(parents=True)
    data = git(repo, "archive", head, "Zeta23", "Zeta23.lean", PREFIX)
    with tarfile.open(fileobj=io.BytesIO(data)) as t:
        t.extractall(out, filter="data")
    require(not any((out / p).exists() for p in ("supplier", "Lib", "New", ".lake")),
            "non-native layout")
    require(not any(p.suffix in {".olean", ".ilean", ".so", ".dll", ".a"} for p in out.rglob("*") if p.is_file()),
            "precompiled object in staged source")
    for row in overlay:
        dst = out / row["destination"]
        require(blob(dst.read_bytes()) == row["historical_git_blob"], "overlay input mismatch")
        dst.write_bytes(committed(repo, head, row["replacement_path"]))
        require(blob(dst.read_bytes()) == row["replacement_git_blob"], "overlay output mismatch")
    (out / "lakefile.toml").write_text(CONFIG)
    (out / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    mlib = json.loads(committed(repo, head, V + "MATHLIB_MANIFEST.json"))
    require(next(p for p in mlib["packages"] if p["name"] == "mathlib")["rev"] == MATHLIB,
            "mathlib pin drift")
    require(all(p["type"] == "git" for p in mlib["packages"]), "nonstandard dependency")
    mlib["name"] = "Zeta23"
    (out / "lake-manifest.json").write_text(json.dumps(mlib, indent=2) + "\n")
    for src, dst in (("Audit.lean", "AuditNativeTerminal.lean"),
                     ("AuditSmoke.lean", "AuditSmoke.lean"),
                     ("AuditSmokeFixtures.lean", "AuditSmokeFixtures.lean"),
                     ("AuditArithmetic.lean", "AuditArithmetic.lean"),
                     ("AuditNativeFrontier.lean", "AuditNativeFrontier.lean"),
                     ("TypeSurface.lean", "TypeSurface.lean"),
                     ("comparator/Challenge/NativeRH.lean", "comparator/Challenge/NativeRH.lean"),
                     ("comparator/Solution/NativeRH.lean", "comparator/Solution/NativeRH.lean"),
                     ("comparator/PrintAxioms/NativeRH.lean", "comparator/PrintAxioms/NativeRH.lean"),
                     ("comparator/config-native-rh.json", "comparator/config-native-rh.json")):
        dest = out / dst
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(committed(repo, head, V + src))
    receipt.parent.mkdir(parents=True, exist_ok=True)
    receipt.write_text(json.dumps({"schema": "NATIVE_TERMINAL_REPAIR_EPOCH_V4", "head": head,
      "tree": git(repo, "rev-parse", head + "^{tree}").decode().strip(), "native_base": BASE,
      "repair_baseline": R3, "acquisition_commit": R0,
      "repair_manifest_sha256": sha(committed(repo, head, REPAIR_PATH)),
      "overlay_manifest_sha256": sha(committed(repo, head, OVERLAY_PATH)),
      "original_port_manifest_sha256": sha(committed(repo, head, PORT_PATH)),
      "supplier_attribution": manifest["supplier_commit"], "package_count": 1,
      "external_project_packages": 0, "mathlib": MATHLIB, "toolchain": TOOLCHAIN,
      "overlay": overlay, "files": staged_files(out), "claim": "RH_OPEN"}, indent=2) + "\n")
    verify_stage(out, receipt)
    print("NATIVE_R4_EPOCH_STAGE_PASS", head, flush=True)

def pins(out):
    actual = json.loads((out / "lake-manifest.json").read_text())
    expected = json.loads((HERE / "MATHLIB_MANIFEST.json").read_text())
    p1 = {p["name"]: p["rev"] for p in actual["packages"]}
    p2 = {p["name"]: p["rev"] for p in expected["packages"]}
    require(p1 == p2 and len(p1) == len(actual["packages"]) and
            all(p["type"] == "git" for p in actual["packages"]), "unexpected package or pin")
    for name, rev in p2.items():
        dep = out / ".lake/packages" / name
        require(git(dep, "rev-parse", "HEAD").decode().strip() == rev, "dependency drift " + name)
        require(not git(dep, "status", "--porcelain", "--untracked-files=no").strip(),
                "dirty tracked dependency " + name)
    require((out / "lean-toolchain").read_text().strip() == TOOLCHAIN, "toolchain drift")
    version = subprocess.check_output(["lean", "--version"], cwd=out, text=True).strip()
    require(re.search(r"\bversion 4\.35\.0(?:,|\s|$)", version) is not None,
            "actual compiler drift: " + version)
    print("NATIVE_COMMON_PIN_PASS", version, p2, flush=True)

if __name__ == "__main__":
    a = argparse.ArgumentParser()
    a.add_argument("--repo", type=P); a.add_argument("--out", type=P)
    a.add_argument("--receipt", type=P); a.add_argument("--head")
    a.add_argument("--verify-pins", action="store_true")
    a.add_argument("--verify-stage", action="store_true")
    a.add_argument("--self-test", action="store_true")
    x = a.parse_args()
    if x.verify_pins: pins(x.out.resolve())
    elif x.verify_stage: verify_stage(x.out.resolve(), x.receipt.resolve())
    elif x.self_test: test_scope(x.repo.resolve(), x.head)
    else: stage(x.repo.resolve(), x.out.resolve(), x.receipt.resolve(), x.head)
