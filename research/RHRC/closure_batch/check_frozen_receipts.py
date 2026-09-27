from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PLAN = HERE / "PLAN.json"

EXPECTED = (
    "track_a.json",
    "track_b.json",
    "track_c.json",
    "track_d.json",
    "HARVEST.json",
    "diagnostic_a_small_aperture.json",
    "diagnostic_b_schur_arb.json",
    "diagnostic_c_characteristic.json",
    "diagnostic_d_r002.json",
)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def disposition(row: dict) -> tuple:
    return (
        row.get("schema_version"),
        row.get("classification"),
        row.get("research_disposition"),
        row.get("terminal_claim"),
        row.get("theorem_promotion"),
        row.get("rh_claim"),
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--receipt-dir", required=True)
    ap.add_argument("--replay-dir")
    args = ap.parse_args()

    root = Path(args.receipt_dir)
    manifest = load(root / "MANIFEST.json")
    if manifest.get("schema_version") != "RHRC-PR274-CLOSURE-RECEIPT-MANIFEST-1.0":
        raise SystemExit("manifest schema drift")
    if manifest.get("terminal_claim") != "RH_OPEN":
        raise SystemExit("manifest attempted terminal promotion")
    if manifest.get("plan_sha256") != sha256(PLAN):
        raise SystemExit("plan digest mismatch")

    if set(manifest.get("files", {})) != set(EXPECTED):
        raise SystemExit("receipt file-set mismatch")
    for name in EXPECTED:
        path = root / name
        spec = manifest["files"][name]
        if not path.is_file():
            raise SystemExit(f"missing frozen receipt: {name}")
        if path.stat().st_size != spec["bytes"] or sha256(path) != spec["sha256"]:
            raise SystemExit(f"frozen receipt digest mismatch: {name}")
        row = load(path)
        if row.get("terminal_claim") != "RH_OPEN":
            raise SystemExit(f"{name}: terminal claim drift")

    harvest = load(root / "HARVEST.json")
    if harvest.get("execution_status") != "SUCCESS" or harvest.get("integrity_status") != "PASS":
        raise SystemExit("campaign harvest is not successful/integrity PASS")
    if harvest.get("research_disposition") != "NO_RH_CLOSURE_ALL_PARALLEL_TRACKS_HARVESTED":
        raise SystemExit("unexpected campaign terminal disposition")

    if args.replay_dir:
        replay = Path(args.replay_dir)
        for name in EXPECTED:
            live = load(replay / name)
            frozen = load(root / name)
            if disposition(live) != disposition(frozen):
                raise SystemExit(
                    f"replay disposition drift in {name}: "
                    f"{disposition(frozen)} -> {disposition(live)}"
                )
            if name == "diagnostic_b_schur_arb.json":
                keys = (
                    "selected_classification_counts",
                    "scope_classification_counts",
                    "certified_bad_interval_count",
                )
                for key in keys:
                    if live.get(key) != frozen.get(key):
                        raise SystemExit(f"{name}: replay drift in {key}")
            if name == "diagnostic_a_small_aperture.json":
                if [r.get("K") for r in live.get("rows", [])] != [
                    r.get("K") for r in frozen.get("rows", [])
                ]:
                    raise SystemExit(f"{name}: K-scope drift")
        print("PR274 CLOSURE RECEIPT REPLAY: PASS")
    else:
        print("PR274 CLOSURE FROZEN RECEIPTS: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
