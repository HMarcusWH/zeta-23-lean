from __future__ import annotations

import argparse
import json
from pathlib import Path


def relation_kind(row: dict) -> str:
    for key in ("relation", "relation_type", "edge_type", "kind", "type"):
        value = row.get(key)
        if isinstance(value, str):
            return value.upper()
    return ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--obligations",
        default="research/RHRC/closure_batch/OBLIGATIONS.json",
    )
    ap.add_argument(
        "--relations",
        default="research/RHRC/graph/generated/relations",
        help="relation shard directory (relations-<hex>.jsonl) or a single JSONL file",
    )
    args = ap.parse_args()

    obligations = json.loads(Path(args.obligations).read_text(encoding="utf-8"))
    open_ids = {
        row["id"] for row in obligations["obligations"]
        if row["status"] in {"OPEN", "INTERFACE"}
    }

    path = Path(args.relations)
    if path.is_dir():
        files = sorted(path.glob("relations-*.jsonl"))
    elif path.is_file():
        files = [path]
    else:
        files = []
    if not files:
        raise SystemExit(f"missing generated relation graph: {path}")

    bad: list[str] = []
    for file in files:
        for lineno, line in enumerate(file.read_text(encoding="utf-8").splitlines(), 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if relation_kind(row) != "PROVES":
                continue
            serialized = json.dumps(row, sort_keys=True)
            touched = sorted(oid for oid in open_ids if oid in serialized)
            if touched:
                bad.append(f"{file}:{lineno}: PROVES touches open obligation(s) {touched}")

    if bad:
        raise SystemExit(
            "RHRC OBLIGATION GRAPH FIREWALL: FAIL\n" + "\n".join(bad)
        )
    print(
        "RHRC OBLIGATION GRAPH FIREWALL: PASS "
        f"({len(open_ids)} open/interface obligations checked)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
