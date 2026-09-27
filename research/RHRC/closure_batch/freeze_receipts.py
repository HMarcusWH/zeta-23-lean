from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil

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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", required=True)
    ap.add_argument("--destination", required=True)
    ap.add_argument("--source-commit", required=True)
    ap.add_argument("--source-tree", required=True)
    args = ap.parse_args()

    src = Path(args.results)
    dst = Path(args.destination)
    if len(args.source_commit) != 40 or len(args.source_tree) != 40:
        raise SystemExit("source commit/tree must be full Git SHAs")
    missing = [name for name in EXPECTED if not (src / name).is_file()]
    if missing:
        raise SystemExit(f"missing campaign outputs: {missing}")

    dst.mkdir(parents=True, exist_ok=True)
    for old in dst.glob("*.json"):
        old.unlink()
    for name in EXPECTED:
        shutil.copyfile(src / name, dst / name)

    manifest = {
        "schema_version": "RHRC-PR274-CLOSURE-RECEIPT-MANIFEST-1.0",
        "source_commit": args.source_commit,
        "source_tree": args.source_tree,
        "plan_sha256": sha256(PLAN),
        "terminal_claim": "RH_OPEN",
        "files": {
            name: {"sha256": sha256(dst / name), "bytes": (dst / name).stat().st_size}
            for name in EXPECTED
        },
    }
    (dst / "MANIFEST.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
