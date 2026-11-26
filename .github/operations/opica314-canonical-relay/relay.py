"""Relay one authenticated public canonical artifact as a verified metadata receipt."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path


REPOSITORY = "HMarcusWH/zeta-23-lean"
ARCHIVE_BYTES_LIMIT = 5 * 1024 * 1024


def need(value: bool, reason: str) -> None:
    if not value:
        raise ValueError(reason)


def api(path: str) -> dict:
    return json.loads(subprocess.check_output(["gh", "api", path]))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", required=True, type=int)
    parser.add_argument("--attempt", required=True, type=int)
    parser.add_argument("--artifact", required=True, type=int)
    parser.add_argument("--sha256", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--tree", required=True)
    parser.add_argument("--base", required=True, type=Path)
    parser.add_argument("--census", required=True, type=Path)
    parser.add_argument("--consumer", required=True, type=Path)
    args = parser.parse_args()

    run_path = f"repos/{REPOSITORY}/actions/runs/{args.run}/attempts/{args.attempt}"
    run = api(run_path)
    need(run["id"] == args.run and run["run_attempt"] == args.attempt
         and run["head_sha"] == args.head and run["repository"]["full_name"] == REPOSITORY
         and run["path"].split("@", 1)[0] == ".github/workflows/opica-dispatch-registration-review.yml",
         "Exact integrated workflow attempt differs")

    all_jobs = api(run_path + "/jobs?per_page=100")
    need(all_jobs["total_count"] == len(all_jobs["jobs"]), "Incomplete job listing")
    jobs = [job for job in all_jobs["jobs"] if job["name"] == "canonical-candidate"]
    need(len(jobs) == 1 and jobs[0]["conclusion"] == "success", "Canonical job not passed")

    artifact_path = f"repos/{REPOSITORY}/actions/artifacts/{args.artifact}"
    metadata = api(artifact_path)
    need(metadata["id"] == args.artifact and metadata["expired"] is False
         and metadata["workflow_run"]["id"] == args.run
         and metadata["name"] == f"registration-canonical-{args.head}-{args.run}-{args.attempt}"
         and metadata["digest"] == "sha256:" + args.sha256
         and 0 < metadata["size_in_bytes"] <= ARCHIVE_BYTES_LIMIT,
         "Exact canonical artifact descriptor differs")

    with tempfile.TemporaryDirectory(prefix="canonical-evidence-transport-") as directory:
        folder = Path(directory)
        archive = folder / "canonical.zip"
        with archive.open("xb") as payload:
            subprocess.run(["gh", "api", artifact_path + "/zip"], stdout=payload, check=True)
        need(archive.stat().st_size == metadata["size_in_bytes"], "Artifact size differs")

        review = folder / "verified.json"
        subprocess.run([
            sys.executable, "-B", str(args.consumer), "--archive", str(archive),
            "--archive-sha256", args.sha256, "--census", str(args.census),
            "--expected-head", args.head, "--expected-tree", args.tree,
            "--repo", str(args.base), "--output", str(review)
        ], check=True)
        print("RH_CANONICAL_ARCHIVE_VERIFIED " +
              json.dumps(json.loads(review.read_bytes()), separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
