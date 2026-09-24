"""Deterministic source-surface helpers for the RHKG final closure pass.

This layer is deliberately weaker than Lean compiler authority.  It indexes named
source commands so that declarations outside registered theorem dependency
closures remain discoverable.  It never creates theorem authority and never
replaces LEAN_ENV_EXACT compiler dependency edges.
"""

from __future__ import annotations

import hashlib
import re
from collections import Counter
from pathlib import Path

DECLARATION_RE = re.compile(
    r"""(?mx)
    ^[ \t]*
    (?:(?:private|protected|noncomputable|unsafe|scoped|local|partial)\s+)*
    (?P<kind>theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive)\s+
    (?P<name>[^\s(:={\[]+)
    """
)

NAMED_INSTANCE_RE = re.compile(
    r"""(?mx)
    ^[ \t]*
    (?:(?:private|protected|noncomputable|unsafe|scoped|local)\s+)*
    instance\s+(?P<name>[^\s:({\[]+)\s*(?:\([^\n]*?\)\s*)*:
    """
)


def _stable_source_decl_id(path: str, ordinal: int, kind: str, name: str) -> str:
    digest = hashlib.sha256(
        f"{path}|{ordinal}|{kind}|{name}".encode("utf-8")
    ).hexdigest()
    return "rh:source-decl:" + digest


def scan_named_source_declarations(
    *,
    path: str,
    module: str,
    trust_zone: str,
    source_locator: dict,
    text: str,
    strip_comments,
) -> list[dict]:
    """Index named Lean declaration commands from source text.

    The result is a source-navigation surface, not a compiler declaration
    census.  Anonymous instances, generated recursors/constructors and macro
    expansions are intentionally outside this layer.
    """
    clean = strip_comments(text)
    matches: list[tuple[int, int, str, str]] = []
    for match in DECLARATION_RE.finditer(clean):
        matches.append((match.start(), match.start(), match.group("kind"), match.group("name")))
    for match in NAMED_INSTANCE_RE.finditer(clean):
        matches.append((match.start(), match.start(), "instance", match.group("name")))
    matches.sort(key=lambda row: row[0])

    rows: list[dict] = []
    seen_at: set[tuple[int, str, str]] = set()
    for ordinal, (_, start, kind, name) in enumerate(matches, start=1):
        line = clean.count("\n", 0, start) + 1
        key = (line, kind, name)
        if key in seen_at:
            continue
        seen_at.add(key)
        locator = dict(source_locator)
        locator["line"] = line
        rows.append(
            {
                "id": _stable_source_decl_id(path, ordinal, kind, name),
                "type": "LeanSourceDeclaration",
                "path": path,
                "file_id": "rh:file:" + path,
                "module": module,
                "module_id": "rh:module:" + module,
                "declared_name": name,
                "command_kind": kind.upper(),
                "line": line,
                "ordinal": ordinal,
                "trust_zone": trust_zone,
                "authority_role": "SOURCE_DISCOVERY_ONLY",
                "source_locator": locator,
            }
        )
    return rows


def exact_token_mentions(text: str, tokens: set[str]) -> list[str]:
    """Return exact identifier-like token mentions, sorted deterministically."""
    found: list[str] = []
    for token in sorted(tokens):
        pattern = rf"(?<![A-Za-z0-9_]){re.escape(token)}(?![A-Za-z0-9_])"
        if re.search(pattern, text):
            found.append(token)
    return found


def module_semantic_closure_view(
    *,
    local_modules: list[dict],
    reachability: dict,
    source_declarations: list[dict],
    compiler_declarations: list[dict],
    standalone_roles: dict[str, str],
) -> dict:
    source_counts = Counter(row["module"] for row in source_declarations)
    compiler_counts = Counter(
        row["module"]
        for row in compiler_declarations
        if row.get("repository_scope") == "LOCAL" and row.get("module")
    )
    registered_counts = Counter(
        row["module"]
        for row in compiler_declarations
        if row.get("graph_role") == "REGISTERED_CLAIM_ROOT" and row.get("module")
    )
    root_sets = {
        "Zeta23": set(reachability["reachable_from_Zeta23_root"]),
        "Zeta23.CCM": set(reachability["reachable_from_CCM_root"]),
        "Zeta23.ExceptionalZero": set(reachability["reachable_from_ExceptionalZero_root"]),
        "comparator": set(reachability["reachable_from_comparator_roots"]),
    }
    standalone = set(reachability["standalone_or_auxiliary"])
    entries: list[dict] = []
    for module in sorted(local_modules, key=lambda row: row["module"]):
        name = module["module"]
        roots = sorted(root for root, members in root_sets.items() if name in members)
        entries.append(
            {
                "module": name,
                "module_id": module["id"],
                "path": module["path"],
                "file_id": module["file_id"],
                "trust_zone": module["trust_zone"],
                "reachability": "STANDALONE_OR_AUXILIARY" if name in standalone else "ENTRYPOINT_REACHABLE",
                "reachable_from": roots,
                "standalone_role": standalone_roles.get(name),
                "named_source_declaration_count": source_counts[name],
                "compiler_dependency_surface_declaration_count": compiler_counts[name],
                "registered_root_count": registered_counts[name],
            }
        )
    return {
        "schema_version": "RHKG-final-module-closure-1.0",
        "scope": "ALL_LOCAL_LEAN_MODULES",
        "entry_count": len(entries),
        "entries": entries,
        "source_surface_semantics": (
            "named_source_declaration_count is a deterministic source-navigation census; "
            "it is not compiler theorem authority."
        ),
        "compiler_surface_semantics": (
            "compiler_dependency_surface_declaration_count remains the exact registered-root "
            "dependency receipt surface."
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }


def document_semantic_closure_view(
    *,
    document_nodes: list[dict],
    claim_ids: set[str],
    route_ids: set[str],
    repo_root: Path,
) -> dict:
    entries: list[dict] = []
    for node in sorted(document_nodes, key=lambda row: row["path"]):
        text = (repo_root / node["path"]).read_text(encoding="utf-8")
        entries.append(
            {
                "path": node["path"],
                "document_id": node["id"],
                "file_id": node["file_id"],
                "file_class": node["file_class"],
                "document_role": node["document_role"],
                "claim_mentions": exact_token_mentions(text, claim_ids),
                "route_mentions": exact_token_mentions(text, route_ids),
                "heading_count": sum(
                    1 for line in text.splitlines() if re.match(r"^#{1,6}\s+", line)
                ),
            }
        )
    return {
        "schema_version": "RHKG-final-document-closure-1.0",
        "scope": "ALL_DOCUMENTATION_AND_LIVING_SSOT_FILES",
        "entry_count": len(entries),
        "entries": entries,
        "mention_semantics": (
            "claim_mentions and route_mentions are exact textual-token navigation hints only; "
            "they do not establish support, implication, supersession, or theorem authority."
        ),
        "terminal_claim": "RH_OPEN",
        "graph_theorem_promotion": False,
    }
