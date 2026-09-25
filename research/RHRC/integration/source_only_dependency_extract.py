from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
SOURCE_ONLY = RHRC / "integration" / "generated" / "RH_CORE_SOURCE_ONLY_THEOREMS.jsonl"
SUMMARY = RHRC / "integration" / "generated" / "SOURCE_CANDIDATE_SUMMARY.json"
RECEIPT = RHRC / "integration" / "generated" / "SOURCE_ONLY_CANDIDATE_DEPENDENCIES.jsonl"
SCHEMA_VERSION = "RHRC-source-only-candidate-dependencies-1.0"


def fail(message: str) -> None:
    raise SystemExit("source_only_dependency_extract: " + message)


def load_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def load_roots() -> list[dict]:
    rows = load_jsonl(SOURCE_ONLY)
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary.get("terminal_claim") != "RH_OPEN":
        fail("candidate summary does not preserve RH_OPEN")
    if len(rows) != summary.get("source_only_public_theorem_count"):
        fail("source-only receipt/count drift")
    if any(row.get("visibility_class") != "SOURCE_ONLY_PUBLIC_THEOREM" for row in rows):
        fail("non-source-only row entered source-only dependency extraction")
    if any(row.get("registered_claim_id") is not None for row in rows):
        fail("source-only root unexpectedly carries a registered claim")
    names = [row.get("resolved_full_name") for row in rows]
    if any(not isinstance(name, str) or not name for name in names):
        fail("source-only root lacks exact Lean declaration identity")
    if len(set(names)) != len(names):
        fail("duplicate exact Lean declaration among source-only roots")
    return sorted(rows, key=lambda row: row["resolved_full_name"])


def render_driver(roots: list[dict]) -> str:
    tick2 = chr(96) * 2
    root_names = ",\n    ".join(tick2 + row["resolved_full_name"] for row in roots)
    modules = sorted({row["module"] for row in roots})
    imports = "\n".join(
        ["import Zeta23.RHRC.DeclarationDependencyExport", *[f"import {module}" for module in modules]]
    )
    return (
        imports + "\n\n"
        "open Lean\n"
        "open Lean.Elab Command\n\n"
        "run_cmd do\n"
        "  Zeta23.RHRC.exportDependencies #[\n"
        f"    {root_names}\n"
        "  ]\n"
    )


def run_lean(roots: list[dict]) -> str:
    driver = render_driver(roots)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", encoding="utf-8", delete=False
    ) as handle:
        handle.write(driver)
        driver_path = Path(handle.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(driver_path)],
            cwd=REPO,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    finally:
        driver_path.unlink(missing_ok=True)
    if proc.returncode != 0:
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=os.sys.stderr)
        fail(f"Lean exporter failed with exit code {proc.returncode}")
    return proc.stdout


def is_local_module(module: str | None) -> bool:
    return module == "Zeta23" or (module is not None and module.startswith("Zeta23."))


def parse_output(stdout: str, roots: list[dict]) -> list[dict]:
    declarations: dict[str, dict] = {}
    edge_channels_by_source: dict[str, dict[str, set[str]]] = {}

    for raw in stdout.splitlines():
        if raw.startswith("RHKG_DEP_DECL\t"):
            parts = raw.split("\t")
            if len(parts) != 5:
                fail(f"malformed declaration line: {raw!r}")
            _, name, module_raw, kind, internal_raw = parts
            module = None if module_raw == "-" else module_raw
            row = {
                "declaration": name,
                "module": module,
                "declaration_kind": kind,
                "private_or_internal": internal_raw == "1",
            }
            prior = declarations.get(name)
            if prior is not None and prior != row:
                fail(f"inconsistent duplicate declaration metadata for {name}")
            declarations[name] = row
        elif raw.startswith("RHKG_DEP_EDGE\t"):
            parts = raw.split("\t")
            if len(parts) != 4:
                fail(f"malformed dependency edge: {raw!r}")
            _, source, target, channel = parts
            if channel not in {"TYPE", "VALUE", "STRUCTURE"}:
                fail(f"unknown dependency channel {channel!r}")
            edge_channels_by_source.setdefault(source, {}).setdefault(target, set()).add(channel)
        elif raw.startswith("RHKG_DEP_CHANNEL\t"):
            parts = raw.split("\t")
            if len(parts) < 3:
                fail(f"malformed dependency channel line: {raw!r}")
            _, source, channel, *targets = parts
            if channel not in {"TYPE", "VALUE", "STRUCTURE"}:
                fail(f"unknown dependency channel {channel!r}")
            target_map = edge_channels_by_source.setdefault(source, {})
            for target in targets:
                if not target:
                    fail(f"empty dependency target in channel line: {raw!r}")
                target_map.setdefault(target, set()).add(channel)

    root_by_name = {row["resolved_full_name"]: row for row in roots}
    missing_roots = sorted(set(root_by_name) - set(declarations))
    if missing_roots:
        fail(f"compiler output omitted source-only roots: {missing_roots[:10]}")

    for source, targets in edge_channels_by_source.items():
        if source not in declarations:
            fail(f"dependency source lacks declaration metadata: {source}")
        for target in targets:
            if target not in declarations:
                fail(f"dependency target lacks declaration metadata: {target}")

    result: list[dict] = []
    for name in sorted(declarations):
        meta = declarations[name]
        module = meta["module"]
        if name in root_by_name:
            graph_role = "SOURCE_ONLY_ROOT"
        elif is_local_module(module):
            graph_role = "LOCAL_DEPENDENCY"
        else:
            graph_role = "EXTERNAL_BOUNDARY"

        deps = [
            {
                "constant": target,
                "used_in_type": "TYPE" in channels,
                "used_in_value": "VALUE" in channels,
                "used_in_structure": "STRUCTURE" in channels,
            }
            for target, channels in sorted(edge_channels_by_source.get(name, {}).items())
        ]
        row = {
            "schema_version": SCHEMA_VERSION,
            "declaration": name,
            "module": module,
            "repository_scope": "LOCAL" if is_local_module(module) else "EXTERNAL",
            "graph_role": graph_role,
            "declaration_kind": meta["declaration_kind"],
            "private_or_internal": meta["private_or_internal"],
            "dependencies": deps,
            "claim_cap": "DISCOVERY_ONLY",
            "terminal_claim": "RH_OPEN",
            "theorem_promotion": False,
        }
        if graph_role == "SOURCE_ONLY_ROOT":
            row["source_candidate_id"] = root_by_name[name]["source_declaration_id"]
        result.append(row)

    root_rows = [row for row in result if row["graph_role"] == "SOURCE_ONLY_ROOT"]
    if len(root_rows) != len(roots):
        fail("source-only root count drift after compiler export")
    return result


def render(rows: list[dict]) -> bytes:
    return "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"
        for row in rows
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract/check compiler dependency closure for source-only RH candidates"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    roots = load_roots()
    rows = parse_output(run_lean(roots), roots)
    payload = render(rows)

    if args.write:
        RECEIPT.parent.mkdir(parents=True, exist_ok=True)
        RECEIPT.write_bytes(payload)
        print(
            "source_only_dependency_extract: WROTE "
            f"{len(rows)} declarations from {len(roots)} source-only roots"
        )
        return 0

    current = RECEIPT.read_bytes() if RECEIPT.exists() else None
    if current != payload:
        fail("checked-in source-only compiler dependency receipt is stale or missing")
    print(
        "source_only_dependency_extract: PASS "
        f"({len(rows)} declarations; {len(roots)} source-only roots)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
