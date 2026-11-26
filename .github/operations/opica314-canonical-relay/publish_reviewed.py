"""Relay one authenticated public canonical artifact as a verified metadata receipt."""

from __future__ import annotations

import argparse
import hashlib
import os
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


def publish(base: Path, archive: Path, verified: dict) -> str:
    from zipfile import ZipFile

    expected_tree = os.environ["REVIEWED_RESULT_TREE"]
    expected_patch = os.environ["REVIEWED_PATCH_SHA256"]
    expected_paths = json.loads(os.environ["REVIEWED_CHANGED_PATHS"])
    need(verified["result_tree"] == expected_tree
         and verified["generated_patch_sha256"] == expected_patch
         and verified["changed_paths"] == expected_paths,
         "Exact scoped review does not match this replay")
    target = "refs/heads/workmode/opica314-reviewed-generated"
    head = verified["source_head"]

    def checked_git(*args: str) -> str:
        return subprocess.check_output(["git", "-C", str(base), *args], text=True).strip()

    need(not checked_git("status", "--porcelain", "--untracked-files=all"),
         "Candidate source checkout is dirty")
    need(checked_git("rev-parse", "HEAD") == head, "Candidate source HEAD changed")
    subprocess.run(["gh", "auth", "setup-git"], check=True)
    need(checked_git("ls-remote", "origin", target) == f"{head}\t{target}",
         "Review ref moved from its exact expected parent")

    with ZipFile(archive) as bundle:
        patch = bundle.read("generated-state.patch")
    need(hashlib.sha256(patch).hexdigest() == expected_patch,
         "Patch changed after verification")
    subprocess.run(["git", "-C", str(base), "apply", "--index",
                    "--whitespace=error-all", "-"], input=patch, check=True)
    need(checked_git("write-tree") == expected_tree, "Applied Git tree differs")

    checked_git("-c", "user.name=github-actions[bot]",
                "-c", "user.email=41898282+github-actions[bot]@users.noreply.github.com",
                "commit", "-m", "Apply independently reviewed dispatch registration graph products")
    candidate = checked_git("rev-parse", "HEAD")
    need(checked_git("rev-parse", "HEAD^{tree}") == expected_tree
         and checked_git("show", "-s", "--format=%P", candidate) == head
         and not checked_git("status", "--porcelain", "--untracked-files=all"),
         "Publication commit scope differs")
    checked_git("push", "origin", f"{candidate}:{target}")
    need(checked_git("ls-remote", "origin", target) == f"{candidate}\t{target}",
         "Publication ref did not read back")
    return candidate


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
        verified = json.loads(review.read_bytes())
        verified["candidate_commit"] = publish(args.base, archive, verified)
        print("RH_CANONICAL_ARCHIVE_STAGED " +
              json.dumps(verified, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
