from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
MANIFEST = ROOT / "REGISTERED_THEOREM_BINDINGS.json"
RECEIPT = ROOT / "graph" / "compiler" / "REGISTERED_DECLARATION_DEPENDENCIES.jsonl"
SCHEMA_VERSION = "RHKG-phase2b-compiler-dependencies-0.4"


def fail(message: str) -> None:
    raise SystemExit("lean_dependency_extract: " + message)


def load_roots() -> list[dict]:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("scope") != "ALL_PROVED_UNCONDITIONAL_REGISTERED_CLAIMS":
        fail(f"unexpected manifest scope {data.get('scope')!r}")
    if data.get("terminal_claim") != "RH_OPEN":
        fail("manifest does not preserve RH_OPEN")
    rows = data["bindings"]
    if len({row["id"] for row in rows}) != len(rows):
        fail("duplicate claim IDs in registered theorem manifest")
    if len({row["theorem"] for row in rows}) != len(rows):
        fail("duplicate theorem names in registered theorem manifest")
    return sorted(rows, key=lambda row: row["id"])


def render_driver(roots: list[dict]) -> str:
    tick2 = chr(96) * 2
    root_names = ",\n    ".join(tick2 + row["theorem"] for row in roots)
    return (
        "import Zeta23.RHRC.DeclarationDependencyExport\n\n"
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
    # Index dependency channels by source while parsing. The previous
    # representation stored one global edge map and rescanned every edge for
    # every declaration when rendering rows, making receipt construction
    # O(declarations * edges). This adjacency index makes it O(edges).
    edge_channels_by_source: dict[str, dict[str, set[str]]] = {}

    for raw in stdout.splitlines():
        if raw.startswith("RHKG_DEP_DECL\t"):
            parts = raw.split("\t")
            if len(parts) != 5:
                fail(f"malformed declaration line: {raw!r}")
            _, name, module_raw, kind, internal_raw = parts
            if internal_raw not in {"0", "1"}:
                fail(f"invalid private/internal flag for {name}: {internal_raw!r}")
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
            # Backward-compatible parser support for the original one-edge-per-line
            # protocol. Current Lean emits RHKG_DEP_CHANNEL records instead.
            parts = raw.split("\t")
            if len(parts) != 4:
                fail(f"malformed dependency line: {raw!r}")
            _, source, target, channel = parts
            if channel not in {"TYPE", "VALUE", "STRUCTURE"}:
                fail(f"unknown dependency channel {channel!r}")
            edge_channels_by_source.setdefault(source, {}).setdefault(
                target, set()
            ).add(channel)
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

    root_by_theorem = {row["theorem"]: row for row in roots}
    missing_roots = sorted(set(root_by_theorem) - set(declarations))
    if missing_roots:
        fail(f"compiler output omitted registered roots: {missing_roots}")

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
        if name in root_by_theorem:
            graph_role = "REGISTERED_CLAIM_ROOT"
            claim_id = root_by_theorem[name]["id"]
        elif is_local_module(module):
            graph_role = "LOCAL_DEPENDENCY"
            claim_id = None
        else:
            graph_role = "EXTERNAL_BOUNDARY"
            claim_id = None

        deps = []
        for target, channels in sorted(edge_channels_by_source.get(name, {}).items()):
            deps.append(
                {
                    "constant": target,
                    "used_in_type": "TYPE" in channels,
                    "used_in_value": "VALUE" in channels,
                    "used_in_structure": "STRUCTURE" in channels,
                }
            )

        row = {
            "schema_version": SCHEMA_VERSION,
            "declaration": name,
            "module": module,
            "repository_scope": "LOCAL" if is_local_module(module) else "EXTERNAL",
            "graph_role": graph_role,
            "declaration_kind": meta["declaration_kind"],
            "private_or_internal": meta["private_or_internal"],
            "dependencies": deps,
        }
        if claim_id is not None:
            row["registered_claim_id"] = claim_id
        result.append(row)

    root_rows = [row for row in result if row["graph_role"] == "REGISTERED_CLAIM_ROOT"]
    if {row["declaration"] for row in root_rows} != set(root_by_theorem):
        fail("registered-root declaration set drift")
    if {row["registered_claim_id"] for row in root_rows} != {row["id"] for row in roots}:
        fail("registered-root claim-id set drift")
    root_claim_map = {
        row["declaration"]: row["registered_claim_id"] for row in root_rows
    }
    expected_claim_map = {
        row["theorem"]: row["id"] for row in roots
    }
    if root_claim_map != expected_claim_map:
        fail("registered-root theorem/claim mapping drift")
    return result


def render_receipt(rows: list[dict]) -> bytes:
    return "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"
        for row in rows
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract/check compiler-derived Lean declaration dependencies"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    roots = load_roots()
    print(
        f"lean_dependency_extract: extracting from {len(roots)} registered roots",
        flush=True,
    )
    started = time.monotonic()
    stdout = run_lean(roots)
    lean_elapsed = time.monotonic() - started
    print(
        "lean_dependency_extract: Lean exporter completed "
        f"in {lean_elapsed:.2f}s ({stdout.count(chr(10))} protocol lines)",
        flush=True,
    )

    parse_started = time.monotonic()
    rows = parse_output(stdout, roots)
    parse_elapsed = time.monotonic() - parse_started
    rendered = render_receipt(rows)
    dependency_count = sum(len(row["dependencies"]) for row in rows)
    print(
        "lean_dependency_extract: parsed "
        f"{len(rows)} declarations / {dependency_count} dependencies "
        f"in {parse_elapsed:.2f}s; receipt={len(rendered)} bytes",
        flush=True,
    )
    current = RECEIPT.read_bytes() if RECEIPT.exists() else None

    if args.write:
        RECEIPT.parent.mkdir(parents=True, exist_ok=True)
        RECEIPT.write_bytes(rendered)
        print(
            "lean_dependency_extract: WROTE "
            f"{len(rows)} declarations from {len(roots)} registered roots"
        )
        return 0

    if current != rendered:
        fail("checked-in compiler dependency receipt is stale or missing")

    print(
        "lean_dependency_extract: PASS "
        f"({len(rows)} declarations; {len(roots)} registered roots)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
