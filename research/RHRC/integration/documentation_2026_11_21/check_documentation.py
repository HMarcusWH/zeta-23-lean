"""Check local links/anchors in the current reader guides; no external requests.

Historical records remain immutable and are not silently rewritten. The policy's
exact documentation path list defines this check's scope. Git's complete tracked
inventory is used so a sparse clone does not misreport archived PDFs as absent.
"""
from __future__ import annotations

import html
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
from urllib.parse import unquote, urlsplit

from .source_scope import POLICY, REPO


def without_fences(text: str) -> str:
    result, marker = [], None
    for line in text.splitlines():
        fence = re.match(r"^\s*(`{3,}|~{3,})", line)
        if fence:
            token = fence.group(1)
            if marker is None:
                marker = token
            elif token[0] == marker[0] and len(token) >= len(marker):
                marker = None
            result.append("")
        else:
            result.append(line if marker is None else "")
    return "\n".join(result)


def anchors(text: str) -> set[str]:
    body = without_fences(text)
    found = set(re.findall(r'<(?:a|h[1-6])\s+[^>]*id=[\"\']([^\"\']+)', body))
    used: set[str] = set()
    for match in re.finditer(r"^ {0,3}#{1,6}\s+(.+?)(?:\s+#+)?\s*$", body, re.M):
        title = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", match.group(1))
        title = html.unescape(re.sub(r"<[^>]+>", "", title)).lower()
        # GitHub-style heading anchors: retain Unicode letters, digits, spaces,
        # underscores and hyphens; formatting/punctuation is removed.
        title = "".join(c for c in title if c.isalnum() or c in " _-").replace(" ", "-")
        slug, number = title, 0
        while slug in used:
            number += 1
            slug = title + "-" + str(number)
        used.add(slug)
    return found | used


def main() -> int:
    root = REPO
    policy = json.loads((root / POLICY).read_text(encoding="utf-8"))
    paths = sorted(p for p in {*policy["added"], *policy["edited"]} if p.endswith(".md"))
    raw = subprocess.check_output(["git", "-C", str(root), "ls-files", "-z", "--cached", "--others", "--exclude-standard"])
    files = {p.decode() for p in raw.split(b"\0") if p}
    directories = {parent.as_posix() for p in files for parent in PurePosixPath(p).parents}
    errors, checked = [], 0
    cache: dict[str, set[str]] = {}
    link_pattern = re.compile(r"\[[^\]\n]*\]\((<[^>\n]+>|[^\s)]+)(?:\s+[\"'][^\n]*[\"'])?\)")
    for name in paths:
        text = without_fences((root / name).read_text(encoding="utf-8"))
        for match in link_pattern.finditer(text):
            target = html.unescape(match.group(1).strip("<>"))
            parsed = urlsplit(target)
            if parsed.scheme or parsed.netloc:
                continue
            checked += 1
            path = unquote(parsed.path)
            resolved = (root / path.lstrip("/")) if path.startswith("/") else (root / name).parent / path
            if not path:
                resolved = root / name
            try:
                relative = resolved.resolve().relative_to(root.resolve()).as_posix()
            except ValueError:
                errors.append(f"{name}: link escapes repository: {target}")
                continue
            if relative not in files and relative not in directories:
                errors.append(f"{name}: missing target: {target}")
                continue
            if parsed.fragment and relative.endswith(".md") and (root / relative).is_file():
                if relative not in cache:
                    cache[relative] = anchors((root / relative).read_text(encoding="utf-8"))
                if unquote(parsed.fragment) not in cache[relative]:
                    errors.append(f"{name}: missing anchor: {target}")
    if errors:
        print("\n".join(errors))
        return 1
    print(f"PASS: {len(paths)} reader documents, {checked} local links; Markdown anchors checked where present")
    print("Scope: policy-listed reader documents only; external URLs and historical receipt links are not network-checked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
