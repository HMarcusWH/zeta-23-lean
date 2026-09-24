from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
from pathlib import Path

from contracts import LeanCandidateReceipt, RepositoryAnchor
from source_candidates import classify_visibility, select_rh_core_theorem_sources, summarize

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
SOURCE_DECLARATIONS = RHRC / "graph" / "generated" / "lean_source_declarations.jsonl"
COMPILER_RECEIPT = (
    RHRC / "graph" / "compiler" / "REGISTERED_DECLARATION_DEPENDENCIES.jsonl"
)
STATE = RHRC / "integration" / "INTEGRATION_STATE.json"
GENERATED = RHRC / "integration" / "generated"
RESOLUTION = GENERATED / "SOURCE_CANDIDATE_RESOLUTION.jsonl"
SOURCE_ONLY = GENERATED / "RH_CORE_SOURCE_ONLY_THEOREMS.jsonl"
SUMMARY = GENERATED / "SOURCE_CANDIDATE_SUMMARY.json"

SCHEMA_VERSION = "RHRC-lean-candidate-receipt-1.0"
PROTOCOL_PREFIX = "RHRC_CANDIDATE_RESULT\t"


def fail(message: str) -> None:
    raise SystemExit("candidate_exactify: " + message)


def load_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def render_driver(candidates: list[dict]) -> str:
    modules = sorted({row["module"] for row in candidates})
    imports = "\n".join(
        ["import Zeta23.RHRC.SourceCandidateResolution"]
        + [f"import {module}" for module in modules]
    )
    entries = []
    for row in candidates:
        entries.append(
            "    { sourceId := "
            + lean_string(row["id"])
            + ", moduleName := "
            + lean_string(row["module"])
            + ", shortName := "
            + lean_string(row["declared_name"])
            + ", sourceKind := "
            + lean_string(row["command_kind"])
            + " }"
        )
    joined = ",\n".join(entries)
    return (
        imports
        + "\n\nopen Zeta23.RHRC\n\nrun_cmd do\n"
        + "  Zeta23.RHRC.resolveSourceCandidates #[\n"
        + joined
        + "\n  ]\n"
    )


def run_lean(candidates: list[dict]) -> str:
    driver = render_driver(candidates)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", encoding="utf-8", delete=False
    ) as handle:
        handle.write(driver)
        path = Path(handle.name)
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
        fail(f"Lean candidate resolver failed with exit code {proc.returncode}")
    return proc.stdout


def parse_output(stdout: str, candidates: list[dict]) -> dict[str, dict]:
    by_id = {row["id"]: row for row in candidates}
    out: dict[str, dict] = {}
    for raw in stdout.splitlines():
        if not raw.startswith(PROTOCOL_PREFIX):
            continue
        parts = raw.split("\t", 9)
        if len(parts) != 10:
            fail(f"malformed resolver protocol line: {raw!r}")
        (
            _prefix,
            source_id,
            status,
            match_count_raw,
            full_name,
            module,
            compiler_kind,
            private_raw,
            type_text,
            ambiguous_names,
        ) = parts
        if source_id not in by_id:
            fail(f"resolver emitted unknown source id {source_id!r}")
        if source_id in out:
            fail(f"resolver emitted duplicate source id {source_id!r}")
        try:
            match_count = int(match_count_raw)
        except ValueError:
            fail(f"invalid match count for {source_id}: {match_count_raw!r}")
        out[source_id] = {
            "resolution_status": status,
            "match_count": match_count,
            "resolved_full_name": None if full_name == "-" else full_name,
            "resolved_module": None if module == "-" else module,
            "compiler_kind": None if compiler_kind == "-" else compiler_kind,
            "private_or_internal": (
                None if private_raw == "-" else private_raw == "1"
            ),
            "exact_type_text": None if type_text == "-" else type_text,
            "ambiguous_names": (
                [] if ambiguous_names == "-" else ambiguous_names.split(",")
            ),
        }
    missing = sorted(set(by_id) - set(out))
    if missing:
        fail(f"resolver omitted {len(missing)} candidates; first={missing[:5]}")
    return out


def build_receipts() -> list[dict]:
    state = json.loads(STATE.read_text(encoding="utf-8"))
    if state.get("terminal_claim") != "RH_OPEN":
        fail("integration state does not preserve RH_OPEN")
    source_rows = load_jsonl(SOURCE_DECLARATIONS)
    candidates = select_rh_core_theorem_sources(source_rows)
    if not candidates:
        fail("RH_FORMAL_CORE theorem/lemma candidate population is empty")

    compiler_rows = load_jsonl(COMPILER_RECEIPT)
    compiler_by_name = {row["declaration"]: row for row in compiler_rows}
    resolver = parse_output(run_lean(candidates), candidates)

    graph = state["repository_graph_authority"]
    anchor = RepositoryAnchor(
        pr=int(graph["pr"]),
        merge_commit=str(graph["merge_commit"]),
        tree=str(graph["tree"]),
        status=str(graph["status"]),
    )

    receipts: list[dict] = []
    for source in candidates:
        resolved = resolver[source["id"]]
        visibility, claim_id = classify_visibility(resolved, compiler_by_name)
        type_text = resolved["exact_type_text"]
        type_digest = (
            hashlib.sha256(type_text.encode("utf-8")).hexdigest()
            if type_text is not None
            else None
        )
        receipt = LeanCandidateReceipt(
            schema_version=SCHEMA_VERSION,
            repository_graph_authority=anchor,
            source_declaration_id=source["id"],
            path=source["path"],
            line=int(source["line"]),
            module=source["module"],
            declared_name=source["declared_name"],
            source_command_kind=source["command_kind"],
            trust_zone=source["trust_zone"],
            resolution_status=resolved["resolution_status"],
            visibility_class=visibility,
            resolved_full_name=resolved["resolved_full_name"],
            compiler_kind=resolved["compiler_kind"],
            private_or_internal=resolved["private_or_internal"],
            exact_type_text=type_text,
            exact_type_sha256=type_digest,
            registered_claim_id=claim_id,
        ).to_dict()
        receipt["match_count"] = resolved["match_count"]
        receipt["ambiguous_names"] = resolved["ambiguous_names"]
        receipts.append(receipt)
    return receipts


def render_jsonl(rows: list[dict]) -> bytes:
    return "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
        for row in rows
    ).encode("utf-8")


def render_summary(rows: list[dict]) -> bytes:
    return (
        json.dumps(summarize(rows), sort_keys=True, indent=2, ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def outputs(rows: list[dict]) -> dict[Path, bytes]:
    source_only = [
        row
        for row in rows
        if row["visibility_class"] == "SOURCE_ONLY_PUBLIC_THEOREM"
    ]
    return {
        RESOLUTION: render_jsonl(rows),
        SOURCE_ONLY: render_jsonl(source_only),
        SUMMARY: render_summary(rows),
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Exactify RH_FORMAL_CORE source theorem/lemma candidates in Lean"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    rows = build_receipts()
    products = outputs(rows)

    if args.write:
        GENERATED.mkdir(parents=True, exist_ok=True)
        for path, payload in products.items():
            path.write_bytes(payload)
        summary = json.loads(products[SUMMARY])
        print(
            "candidate_exactify: WROTE "
            f"{summary['candidate_count']} candidates; "
            f"{summary['source_only_public_theorem_count']} source-only public theorem/lemmas"
        )
        return 0

    stale = []
    for path, payload in products.items():
        if not path.exists() or path.read_bytes() != payload:
            stale.append(str(path.relative_to(REPO)))
    if stale:
        fail(f"checked-in candidate products are stale: {stale}")

    summary = json.loads(products[SUMMARY])
    print(
        "candidate_exactify: PASS "
        f"({summary['candidate_count']} candidates; "
        f"{summary['source_only_public_theorem_count']} source-only public theorem/lemmas)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
