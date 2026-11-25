"""Exhaustive diagnostic census of the parseable, non-denied source frontier.

Visit each allowed source module once and give a shortest path from every
reachable root to each bad edge. Never follow or admit denied modules.
External package imports are checked by the pinned Lean build.
"""
from collections import deque
import hashlib
from lean_header import imports as lean_imports

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def git_blob_sha(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()

def reviewed_cut(rel, original, transform, reviews):
    if rel not in reviews:
        raise RuntimeError("unreviewed source cut: "+rel)
    expected, retained = reviews[rel]
    if git_blob_sha(original.encode()) != expected:
        raise RuntimeError("changed original source blob: "+rel)
    new = transform(original)
    if new == original:
        raise RuntimeError("empty cut: "+rel)
    for marker in retained:
        if original.count(marker) != 1 or new.count(marker) != 1:
            raise RuntimeError("reviewed retained declaration missing or ambiguous: "+rel+": "+marker)
    return new

def scan_imports(root, roots, denied, external, edits=None, staged=None):
    edits, staged = edits or {}, staged or {}
    files, graph, bad, external_imports = {}, {}, {}, set()
    loaded = set()
    pending = deque(roots)
    def source_path(m):
        return m.replace(".", "/")+".lean"
    def issue(kind, parent, line, target, detail):
        key = (kind, parent, line, target)
        if key not in bad:
            rel = source_path(parent)
            review = edits.get(rel)
            prior = (review or staged.get(rel) or {}).get("before", files.get(parent))
            bad[key] = {"kind":kind, "importer":parent, "line":line,
                        "target":target, "detail":detail, "importer_sha256":files.get(parent),
                        "original_sha256":prior, "reviewed_cut":review, "paths":[]}
    while pending:
        m = pending.popleft()
        if m in loaded:
            continue
        loaded.add(m)
        graph[m] = []
        p = root/source_path(m)
        if m in denied:
            issue("forbidden", "<root>", 0, m, "terminal root forbidden")
            continue
        if p.is_symlink():
            issue("symlink", m, 0, m, "symlink source")
            continue
        if not p.is_file():
            if m.split(".")[0] in external:
                external_imports.add(m)
            else:
                issue("unresolved", "<root>", 0, m, "missing root source")
            continue
        try:
            data = p.read_bytes()
            files[m] = sha256(data)
            imports = lean_imports(data.decode("utf-8"), m)
        except (RuntimeError, UnicodeError, OSError) as exc:
            issue("malformed", m, 0, m, str(exc))
            continue
        for i in imports:
            target = i.name
            dst = root/source_path(target)
            if target in denied:
                issue("forbidden", m, i.line, target, "terminal module in source closure")
            elif dst.is_symlink():
                issue("symlink", m, i.line, target, "symlink source")
            elif not dst.is_file():
                if target.split(".")[0] in external:
                    external_imports.add(target)
                else:
                    issue("unresolved", m, i.line, target, "unresolved source import")
            else:
                graph[m].append(target)
                pending.append(target)
    for start in roots:
        prev = {start: None}
        q = deque([start])
        while q:
            m = q.popleft()
            for target in graph.get(m, []):
                if target not in prev:
                    prev[target] = m
                    q.append(target)
        for row in bad.values():
            parent, target = row["importer"], row["target"]
            if parent == "<root>":
                if target == start:
                    row["paths"].append([start])
                continue
            if parent not in prev:
                continue
            path, cursor = [], parent
            while cursor is not None:
                path.append(cursor)
                cursor = prev[cursor]
            path.reverse()
            if target != parent:
                path.append(target)
            row["paths"].append(path)
    return {"roots":list(roots), "files":files, "external_imports":sorted(external_imports),
            "violations":sorted(bad.values(), key=lambda x:(x["importer"],x["line"],x["target"],x["kind"])),
            "coverage":"all reachable parseable non-denied local modules; denied or malformed frontier not traversed"}

def require_clean(census):
    if census["violations"]:
        row = census["violations"][0]
        raise RuntimeError(f'{len(census["violations"])} source closure violation(s); '
                           f'{row["detail"]}: {row["target"]} imported by {row["importer"]}:{row["line"]}')
