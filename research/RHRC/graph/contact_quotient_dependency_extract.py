from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
CONFIG = RHRC / "graph" / "CONTACT_QUOTIENT_CONFIG.json"
RECEIPT = RHRC / "graph" / "generated" / "CONTACT_QUOTIENT_DECLARATION_DEPENDENCIES.jsonl"
SCHEMA = "RHRC-contact-quotient-dependencies-1.0"


def fail(message: str) -> None:
    raise SystemExit("contact_quotient_dependency_extract: " + message)


def roots_from_config() -> list[dict]:
    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    if config.get("terminal_claim") != "RH_OPEN" or config.get("theorem_promotion") is not False:
        fail("config authority firewall drift")
    roots = []
    seen = set()
    for family in config.get("interface_families", []):
        for anchor in family.get("anchors", []):
            name = anchor.get("declaration")
            module = anchor.get("module")
            if not isinstance(name, str) or not name or not isinstance(module, str) or not module:
                fail("malformed anchor")
            if name not in seen:
                roots.append({"declaration": name, "module": module})
                seen.add(name)
    if not roots:
        fail("no contact-quotient roots")
    return sorted(roots, key=lambda r: r["declaration"])


def render_driver(roots: list[dict]) -> str:
    ticks = chr(96) * 2
    root_names = ",\n    ".join(ticks + row["declaration"] for row in roots)
    modules = sorted({row["module"] for row in roots})
    imports = "\n".join(
        ["import Zeta23.RHRC.DeclarationDependencyExport", *[f"import {m}" for m in modules]]
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
    modules = sorted({row["module"] for row in roots})
    build = subprocess.run(
        ["lake", "build", *modules],
        cwd=REPO,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if build.returncode != 0:
        print(build.stdout, end="")
        print(build.stderr, end="", file=os.sys.stderr)
        fail(f"root module build failed with exit code {build.returncode}")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", encoding="utf-8", delete=False) as h:
        h.write(render_driver(roots))
        path = Path(h.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=REPO,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    finally:
        path.unlink(missing_ok=True)
    if proc.returncode != 0:
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=os.sys.stderr)
        fail(f"Lean exporter failed with exit code {proc.returncode}")
    return proc.stdout


def is_local_module(module: str | None) -> bool:
    return module == "Zeta23" or (module is not None and module.startswith("Zeta23."))


def parse(stdout: str, roots: list[dict]) -> list[dict]:
    declarations: dict[str, dict] = {}
    edges: dict[str, dict[str, set[str]]] = {}
    for raw in stdout.splitlines():
        if raw.startswith("RHKG_DEP_DECL\t"):
            parts = raw.split("\t")
            if len(parts) != 5:
                fail(f"malformed declaration line: {raw!r}")
            _, name, module_raw, kind, internal_raw = parts
            declarations[name] = {
                "declaration": name,
                "module": None if module_raw == "-" else module_raw,
                "declaration_kind": kind,
                "private_or_internal": internal_raw == "1",
            }
        elif raw.startswith("RHKG_DEP_EDGE\t"):
            parts = raw.split("\t")
            if len(parts) != 4:
                fail(f"malformed edge line: {raw!r}")
            _, source, target, channel = parts
            edges.setdefault(source, {}).setdefault(target, set()).add(channel)
        elif raw.startswith("RHKG_DEP_CHANNEL\t"):
            parts = raw.split("\t")
            if len(parts) < 3:
                fail(f"malformed channel line: {raw!r}")
            _, source, channel, *targets = parts
            for target in targets:
                if target:
                    edges.setdefault(source, {}).setdefault(target, set()).add(channel)

    root_names = {row["declaration"] for row in roots}
    missing = sorted(root_names - set(declarations))
    if missing:
        fail(f"compiler output omitted roots: {missing}")

    rows = []
    for name in sorted(declarations):
        meta = declarations[name]
        deps = [
            {
                "constant": target,
                "used_in_type": "TYPE" in channels,
                "used_in_value": "VALUE" in channels,
                "used_in_structure": "STRUCTURE" in channels,
            }
            for target, channels in sorted(edges.get(name, {}).items())
        ]
        rows.append({
            "schema_version": SCHEMA,
            "declaration": name,
            "module": meta["module"],
            "repository_scope": "LOCAL" if is_local_module(meta["module"]) else "EXTERNAL",
            "graph_role": "CONTACT_QUOTIENT_ROOT" if name in root_names else (
                "LOCAL_DEPENDENCY" if is_local_module(meta["module"]) else "EXTERNAL_BOUNDARY"
            ),
            "declaration_kind": meta["declaration_kind"],
            "private_or_internal": meta["private_or_internal"],
            "dependencies": deps,
            "claim_cap": "DISCOVERY_ONLY",
            "terminal_claim": "RH_OPEN",
            "theorem_promotion": False,
        })
    return rows


def render(rows: list[dict]) -> bytes:
    return "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"
        for row in rows
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    roots = roots_from_config()
    payload = render(parse(run_lean(roots), roots))
    if args.write:
        RECEIPT.parent.mkdir(parents=True, exist_ok=True)
        RECEIPT.write_bytes(payload)
        print(f"contact_quotient_dependency_extract: WROTE {len(payload)} bytes")
        return 0
    current = RECEIPT.read_bytes() if RECEIPT.exists() else None
    if current != payload:
        fail("checked-in/generated contact quotient dependency receipt is stale or missing")
    print("contact_quotient_dependency_extract: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
