from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent


def run(cmd: list[str]) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, check=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(HERE.parents[2]))
    ap.add_argument("--output-dir", required=True)
    args = ap.parse_args()
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)
    py = sys.executable
    run([py, str(HERE / "source_jet_oracle.py"), "--repo", args.repo, "--output", str(out / "track_a.json")])
    run([py, str(HERE / "canonical_schur_search.py"), "--output", str(out / "track_b.json")])
    run([py, str(HERE / "canonical_schur_verify.py"), "--input", str(out / "track_b.json")])
    run([py, str(HERE / "independent_mp_oracle.py"), "--output", str(out / "track_c.json")])
    run([py, str(HERE / "detector_family_audit.py"), "--output", str(out / "track_d.json")])
    run([py, str(HERE / "harvest.py"), "--results", str(out), "--output", str(out / "HARVEST.json")])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
