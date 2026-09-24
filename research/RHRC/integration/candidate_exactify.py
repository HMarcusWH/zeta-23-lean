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
LEAN_TOOLCHAIN = REPO / "lean-toolchain"

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


def validate_candidate_modules(candidates: list[dict]) -> None:
    modules = sorted({row["module"] for row in candidates})
    unsupported = [
        module
        for module in modules
        if not (
            module == "Zeta23.CCM"
            or module.startswith("Zeta23.CCM.")
            or module == "Zeta23.ExceptionalZero"
            or module.startswith("Zeta23.ExceptionalZero.")
        )
    ]
    if unsupported:
        fail(
            "RH_FORMAL_CORE candidate scope escaped the audited CCM/ExceptionalZero "
            f"aggregators: {unsupported[:10]}"
        )


def render_query_tsv(candidates: list[dict]) -> str:
    lines = []
    for row in candidates:
        fields = [
            row["id"],
            row["module"],
            row["declared_name"],
            row["command_kind"],
        ]
        if any("\t" in value or "\n" in value or "\r" in value for value in fields):
            fail(f"candidate contains invalid TSV control characters: {row['id']}")
        lines.append("\t".join(fields))
    return "\n".join(lines) + "\n"


def render_driver(query_path: Path) -> str:
    return (
        "import Zeta23.RHRC.SourceCandidateResolution\n"
        "import Zeta23.CCM\n"
        "import Zeta23.ExceptionalZero\n\n"
        "run_cmd do\n"
        "  Zeta23.RHRC.resolveSourceCandidatesFile "
        + lean_string(str(query_path))
        + "\n"
    )


def run_lean(candidates: list[dict]) -> str:
    validate_candidate_modules(candidates)
    query_path: Path | None = None
    driver_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".tsv", encoding="utf-8", delete=False
        ) as query_handle:
            query_handle.write(render_query_tsv(candidates))
            query_path = Path(query_handle.name)
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", encoding="utf-8", delete=False
        ) as driver_handle:
            driver_handle.write(render_driver(query_path))
            driver_path = Path(driver_handle.name)
        proc = subprocess.run(
            ["lake", "env", "lean", str(driver_path)],
            cwd=REPO,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    finally:
        if driver_path is not None:
            driver_path.unlink(missing_ok=True)
        if query_path is not None:
            query_path.unlink(missing_ok=True)
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
            "compiler_type_text": None if type_text == "-" else type_text,
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
    source_surface_bytes = SOURCE_DECLARATIONS.read_bytes()
    compiler_receipt_bytes = COMPILER_RECEIPT.read_bytes()
    source_surface_sha256 = hashlib.sha256(source_surface_bytes).hexdigest()
    compiler_receipt_sha256 = hashlib.sha256(compiler_receipt_bytes).hexdigest()
    lean_toolchain = LEAN_TOOLCHAIN.read_text(encoding="utf-8").strip()

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
        type_text = resolved["compiler_type_text"]
        type_digest = (
            hashlib.sha256(type_text.encode("utf-8")).hexdigest()
            if type_text is not None
            else None
        )
        receipt = LeanCandidateReceipt(
            schema_version=SCHEMA_VERSION,
            repository_graph_authority=anchor,
            source_surface_sha256=source_surface_sha256,
            registered_compiler_receipt_sha256=compiler_receipt_sha256,
            lean_toolchain=lean_toolchain,
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
            compiler_type_text=type_text,
            compiler_type_sha256=type_digest,
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
    data = summarize(rows)
    if rows:
        data["source_surface_sha256"] = rows[0]["source_surface_sha256"]
        data["registered_compiler_receipt_sha256"] = rows[0][
            "registered_compiler_receipt_sha256"
        ]
        data["lean_toolchain"] = rows[0]["lean_toolchain"]
    return (
        json.dumps(data, sort_keys=True, indent=2, ensure_ascii=False)
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
