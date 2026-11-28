#!/usr/bin/env python3
"""Stage the selected direct-window import closure at its original source epoch.

No upstream proof is vendored into Git. Every copied byte is bound to either the
candidate commit, the external source commit, or a reviewed compatibility file.
Only explicitly mapped duplicate modules become import-only shims. A development
stage may use working-tree bytes; it can never produce an acceptance receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import Counter, deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOTS = {
    "supplier": ["Zeta23WindowArithmetic.PrincipalWindowSupply"],
    "native": ["Zeta23.RHReference.CofinalEnergyClosure", "Zeta23WindowArithmetic.PrincipalNormalization"],
    "terminal": ["Zeta23.RHReference.DirectWindowAdapter"],
    "controls": [],
}
EXTERNAL = {"Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq",
            "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli", "Lake"}
AUDITS = {"AuditCore": "Core", "AuditSupplier": "Supplier", "AuditNative": "Native",
          "AuditTerminal": "Terminal", "Expected": "Expected", "SmokeFixtures": "SmokeFixtures",
          "AuditSmoke": "Smoke"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def safe(path):
    require(isinstance(path, str) and path and not path.startswith("/") and
            "\\" not in path and all(p not in {"", ".", ".."} for p in path.split("/")),
            "unsafe relative path: " + repr(path))
    return path


def strip_comments(source):
    """Keep newlines; respect nested Lean comments and quoted strings."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif source.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if source[i] == "\n" else " "); i += 1
        elif quoted:
            out.append("\n" if source[i] == "\n" else " ")
            if source[i] == "\\" and i + 1 < len(source):
                i += 1; out.append("\n" if source[i] == "\n" else " ")
            elif source[i] == '"':
                quoted = False
            i += 1
        elif source.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif source.startswith("--", i):
            stop = source.find("\n", i)
            if stop < 0: stop = len(source)
            out.extend(" " * (stop - i)); i = stop
        else:
            quoted = source[i] == '"'
            out.append(source[i]); i += 1
    require(depth == 0, "unterminated Lean block comment")
    return "".join(out)


def imports(raw):
    text = strip_comments(raw.decode("utf-8"))
    result = []
    for line in text.splitlines():
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$", line)
        if match:
            for name in match.group(1).split():
                require(all(c not in name for c in '/\\;"'), "invalid import: " + name)
                result.append(name)
    return result


def module_path(name):
    return safe(name.replace(".", "/") + ".lean")


def tree(repo, revision):
    result = {}
    for row in git(repo, "ls-tree", "-r", "-z", revision).split(b"\0"):
        if row:
            info, path = row.split(b"\t", 1)
            mode, kind, oid = info.decode().split()
            if kind == "blob":
                result[path.decode()] = (mode, oid)
    return result


def exact_bytes(repo, path, inventory, development=False):
    path = safe(path)
    target = repo / path
    require(target.is_file() and not target.is_symlink(), "missing or symlink source " + path)
    raw = target.read_bytes()
    if not development:
        require(path in inventory and inventory[path][0] == "100644" and
                inventory[path][1] == blob(raw), "source differs from pinned commit: " + path)
    return raw


def owner_map(repo, original, native_tree, original_tree, development):
    data = read_json(HERE / "OWNERSHIP.json")
    require(data["schema"] == "DIRECT_WINDOW_OWNERSHIP_V1", "ownership schema")
    owners = {}
    for row in data["owners"]:
        n, o = row["native_module"], row["original_module"]
        require(n not in owners and n.startswith("Zeta23.OPICATerminal.Analytic."), "duplicate/unexpected shim")
        nr = exact_bytes(repo, module_path(n), native_tree, development)
        op = "src/" + module_path(o)
        ore = exact_bytes(original, op, original_tree)
        require(sha(nr) == row["native_sha256"] and sha(ore) == row["original_sha256"],
                "ownership preimage changed: " + n)
        require(row["relation"] in {"identical_modulo_imports", "original_superset"}
                and bool(row["reason"]), "unreviewed ownership relation")
        owners[n] = row
    native_analytic = {str(p.relative_to(repo)).removesuffix(".lean").replace("/", ".")
                       for p in (repo / "Zeta23/OPICATerminal/Analytic").rglob("*.lean")}
    require(set(owners) == native_analytic, "incomplete native analytic ownership map")
    return owners


def staged_files(stage):
    return {p.relative_to(stage).as_posix(): sha(p.read_bytes())
            for p in sorted(stage.rglob("*")) if p.is_file()
            and p.relative_to(stage).parts[0] not in {".lake", ".git"}}


def project_cache_is_fresh(stage):
    """Only pinned dependency caches may predate a production stage."""
    cache = stage / ".lake"
    require(not cache.is_symlink(), "symlink project cache: .lake")
    require(not (cache / "build").is_symlink(), "symlink project cache: .lake/build")
    if not cache.exists():
        return True
    require(cache.is_dir(), "project cache is not a directory")
    fresh = True
    for entry in cache.iterdir():
        require(not entry.is_symlink(), "symlink project cache: " + str(entry))
        if entry.name == "packages":
            require(entry.is_dir(), "dependency cache is not a directory")
            continue
        for artifact in [entry, *entry.rglob("*")]:
            require(not artifact.is_symlink(), "symlink project cache: " + str(artifact))
            if not artifact.is_dir():
                fresh = False
    return fresh


def verify_stage(stage, receipt):
    data = read_json(receipt)
    require(data["schema"] == "DIRECT_WINDOW_STAGE_V1", "stage receipt schema")
    expected = {r["path"]: r["sha256"] for r in data["files"]}
    require(expected == staged_files(stage), "effective staged source changed")
    require((stage / "lean-toolchain").read_text().strip() == data["source_toolchain"], "compiler pin changed")
    manifest = read_json(stage / "lake-manifest.json")
    require([p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"] == [data["mathlib"]],
            "Mathlib pin changed")
    print("DIRECT_WINDOW_EFFECTIVE_SOURCE_PASS", data["head"], len(expected))
    return data


def stage_sources(repo, original, stage, receipt, head, development=False, restage=False, scope="terminal"):
    lock = read_json(HERE / "SOURCE_LOCK.json")
    head = git(repo, "rev-parse", head + "^{commit}").decode().strip()
    require(git(original, "rev-parse", "HEAD").decode().strip() == lock["original"]["commit"],
            "wrong external source commit")
    native_tree, original_tree = tree(repo, head), tree(original, lock["original"]["commit"])
    for name, digest in lock["original_config_sha256"].items():
        require(sha(exact_bytes(original, name, original_tree)) == digest, "original config drift: " + name)
    if not development:
        require(git(repo, "rev-parse", "HEAD").decode().strip() == head, "checkout is not candidate head")
        require(not git(repo, "status", "--porcelain", "--untracked-files=all").strip(), "candidate checkout is dirty")
    owners = owner_map(repo, original, native_tree, original_tree, development)
    compatibility = read_json(HERE / "COMPATIBILITY.json")
    require(compatibility["schema"] == "DIRECT_WINDOW_COMPATIBILITY_V1", "compatibility schema")
    overlays = {}
    for row in compatibility["overlays"]:
        path = safe(row["path"])
        require(path.startswith("Zeta23/") and path not in overlays, "invalid compatibility path")
        require(path.removesuffix(".lean").replace("/", ".") not in owners, "overlay duplicates original owner")
        before = exact_bytes(repo, path, native_tree, development)
        after = exact_bytes(repo, safe(row["overlay_path"]), native_tree, development)
        require(sha(before) == row["original_sha256"] and sha(after) == row["replacement_sha256"]
                and row["reason"], "compatibility preimage/replacement changed")
        overlays[path] = (row, before, after)
    fresh_project_objects = project_cache_is_fresh(stage)
    require(development or fresh_project_objects, "production staging must start without project cache artifacts")
    if restage:
        old = verify_stage(stage, receipt)
        for row in old["files"]:
            (stage / safe(row["path"])).unlink()
    elif stage.exists():
        require(not staged_files(stage), "stage contains untracked source; use an empty directory")
    stage.mkdir(parents=True, exist_ok=True)
    rows, contents, graph = {}, {}, {}

    def add(path, raw, origin, source_path, original_raw=None):
        path = safe(path)
        require(path not in contents, "duplicate staged path: " + path)
        contents[path] = raw
        rows[path] = {"path": path, "owner": origin, "source_path": source_path,
                      "sha256": sha(raw), "git_blob": blob(raw), "bytes": len(raw)}
        if original_raw is not None:
            rows[path]["preimage_sha256"] = sha(original_raw)

    audit_names = {"terminal": list(AUDITS), "supplier": ["AuditCore", "AuditSupplier"],
                   "native": ["AuditCore", "AuditNative"],
                   "controls": ["AuditCore", "SmokeFixtures", "AuditSmoke"]}[scope]
    for src in audit_names:
        dest = AUDITS[src]
        path = "verification/direct-arithmetic-window/" + src + ".lean"
        raw = exact_bytes(repo, path, native_tree, development)
        add("DirectWindowAudit/" + dest + ".lean", raw, "verification", path)
    starts = [*ROOTS[scope], *["DirectWindowAudit." + AUDITS[x] for x in audit_names]]
    if scope == "terminal":
        sol_path = "verification/direct-arithmetic-window/comparator/DirectWindowSolution.lean"
        add("DirectWindowSolution.lean", exact_bytes(repo, sol_path, native_tree, development), "verification", sol_path)
        starts.append("DirectWindowSolution")
    queue = deque(starts)
    seen, external = set(), set()
    while queue:
        name = queue.popleft()
        if name in seen: continue
        seen.add(name)
        if name.split(".")[0] in EXTERNAL:
            external.add(name); continue
        path = module_path(name)
        if path in contents:
            raw = contents[path]
        elif name in owners:
            owner = owners[name]
            nr = exact_bytes(repo, path, native_tree, development)
            raw = ("-- Original source owns these declarations; see OWNERSHIP.json.\nimport " +
                   owner["original_module"] + "\n").encode()
            add(path, raw, "original-owner-shim", path, nr)
        elif path in overlays:
            row, before, raw = overlays[path]
            add(path, raw, "compatibility", row["overlay_path"], before)
        elif (repo / path).is_file():
            require(name.startswith(("Zeta23.", "Zeta23WindowArithmetic.")), "unapproved native module " + name)
            require(not name.startswith("Zeta23.RHReference.Perron.") and
                    name not in {"Zeta23.RHReference.CompactEnergyAdapter", "Zeta23.RHReference.CompactEnergyClosure"},
                    "old energy supplier entered import closure: " + name)
            raw = exact_bytes(repo, path, native_tree, development)
            add(path, raw, "native", path)
        else:
            op = "src/" + path
            raw = exact_bytes(original, op, original_tree)
            add(path, raw, "original", op)
        graph[name] = imports(raw)
        queue.extend(graph[name])
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        path = "verification/direct-arithmetic-window/epoch-lean-4.33.1/" + name
        add(name, exact_bytes(repo, path, native_tree, development), "epoch", path)
    for path, raw in contents.items():
        target = stage / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
    def reachable(roots):
        todo, visited = list(roots), set()
        while todo:
            n = todo.pop()
            if n in visited or n not in graph: continue
            visited.add(n); todo.extend(graph[n])
        return sorted(visited)
    counts = dict(Counter(r["owner"] for r in rows.values()))
    data = {"schema": "DIRECT_WINDOW_STAGE_V1", "development_only": development, "scope": scope,
            "fresh_project_objects": fresh_project_objects,
            "entry_modules": starts,
            "head": head, "tree": git(repo, "rev-parse", head + "^{tree}").decode().strip(),
            "original_commit": lock["original"]["commit"],
            "source_toolchain": lock["source_toolchain"], "mathlib": lock["mathlib"],
            "source_lock_sha256": sha((HERE / "SOURCE_LOCK.json").read_bytes()),
            "ownership_sha256": sha((HERE / "OWNERSHIP.json").read_bytes()),
            "compatibility_sha256": sha((HERE / "COMPATIBILITY.json").read_bytes()),
            "files": [rows[k] for k in sorted(rows)], "owner_counts": counts,
            "source_bytes": sum(r["bytes"] for r in rows.values()),
            "root_import_closures": {k: reachable(v) for k, v in ROOTS.items()},
            "external_imports": sorted(external)}
    receipt.parent.mkdir(parents=True, exist_ok=True)
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    verify_stage(stage, receipt)
    print("DIRECT_WINDOW_SOURCE_COUNTS", json.dumps(counts, sort_keys=True))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path)
    p.add_argument("--original", type=Path)
    p.add_argument("--stage", type=Path, required=True)
    p.add_argument("--receipt", type=Path, required=True)
    p.add_argument("--head", default="HEAD")
    p.add_argument("--scope", choices=list(ROOTS), default="terminal")
    p.add_argument("--allow-dirty", action="store_true", help="development only, never acceptable evidence")
    p.add_argument("--restage", action="store_true", help="replace authenticated staged source; preserve .lake")
    p.add_argument("--verify-stage", action="store_true")
    a = p.parse_args()
    if a.verify_stage:
        verify_stage(a.stage.resolve(), a.receipt.resolve())
    else:
        require(a.repo is not None and a.original is not None, "--repo and --original are required")
        stage_sources(a.repo.resolve(), a.original.resolve(), a.stage.resolve(), a.receipt.resolve(),
                      a.head, a.allow_dirty, a.restage, a.scope)


if __name__ == "__main__":
    main()
