"""Complete paginated workflow observations with explicit scientific dispositions.

Provider execution, reviewed classification, artifact evidence and mathematical
authority remain separate. A running workflow cannot harvest its own final result.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
from typing import Any, Callable, Mapping
from urllib.parse import urlencode, urlsplit
from urllib.request import Request, urlopen

try:
    from .certificate_io import InvalidCertificate, failure_envelope, load_strict_json, loads_strict_json, validate_schema
    from . import validate_contract as contract
except ImportError:
    from certificate_io import InvalidCertificate, failure_envelope, load_strict_json, loads_strict_json, validate_schema
    import validate_contract as contract

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
CLASSES = {"FORMAL_VALIDITY_GATE", "REGRESSION_GATE", "RESEARCH_PRODUCING_CHECK", "RELEASE_GATE", "AGGREGATION_GATE"}
PENDING = {"queued", "in_progress", "waiting", "pending", "requested"}
CONCLUSIONS = {"success", "failure", "cancelled", "timed_out", "skipped"}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise InvalidCertificate("workflow_evidence", message)


def complete_pages(pages: list[dict[str, Any]], field: str) -> list[dict[str, Any]]:
    require(type(pages) is list and pages, "Missing provider pages")
    totals = [p.get("total_count") for p in pages]
    require(all(type(n) is int and n >= 0 for n in totals) and len(set(totals)) == 1,
            "Changing or invalid provider total")
    require(all(type(p.get(field)) is list for p in pages), "Missing provider collection")
    rows = [r for p in pages for r in p[field]]
    require(len(rows) == totals[0] and all(type(r) is dict for r in rows), "Incomplete or excess provider pages")
    ids = [r.get("id") for r in rows]
    require(all(type(i) is int and i > 0 for i in ids) and len(set(ids)) == len(ids), "Duplicate or invalid provider IDs")
    return rows


def fetch_pages(fetch: Callable[[str], dict], url: str, field: str) -> list[dict[str, Any]]:
    pages, seen = [], 0
    for page in range(1, 1001):
        separator = "&" if "?" in url else "?"
        payload = fetch(url + separator + urlencode({"per_page": 100, "page": page}))
        require(type(payload) is dict and type(payload.get("total_count")) is int
                and payload["total_count"] >= 0 and type(payload.get(field)) is list, "Malformed provider pagination")
        require(not pages or payload["total_count"] == pages[0]["total_count"], "Provider total changed while collecting")
        pages.append(payload)
        seen += len(payload[field])
        require(seen <= payload["total_count"], "Provider returned excess records")
        if seen == payload["total_count"]:
            complete_pages(pages, field)
            return pages
        require(payload[field], "Empty page before the provider total")
    raise InvalidCertificate("workflow_page_limit", "Provider pagination resource limit reached")


def collect(fetch: Callable[[str], dict], owner: str, repository: str, head: str) -> dict[str, Any]:
    require(all(type(x) is str and x and all(c.isalnum() or c in "-_." for c in x)
                for x in (owner, repository)), "Invalid repository identity")
    require(type(head) is str and len(head) == 40 and all(c in "0123456789abcdef" for c in head), "Invalid requested head")
    base = "https://api.github.com/repos/" + owner + "/" + repository
    run_pages = fetch_pages(fetch, base+"/actions/runs?"+urlencode({"head_sha":head}), "workflow_runs")
    runs = complete_pages(run_pages, "workflow_runs")
    require(all(r.get("head_sha") == head for r in runs), "Provider run does not match the queried head")
    jobs = []
    for run in runs:
        attempt = run.get("run_attempt")
        require(type(attempt) is int and attempt >= 1, "Missing exact workflow attempt")
        for observed_attempt in range(1, attempt+1):
            url = base + "/actions/runs/" + str(run["id"]) + "/attempts/" + str(observed_attempt) + "/jobs"
            jobs.append({"run_id": run["id"], "attempt": observed_attempt, "pages": fetch_pages(fetch, url, "jobs")})
    return {"schema": "OPICA2_PROVIDER_ACTIONS_SNAPSHOT_V1", "head": head,
            "observed_at_utc": datetime.now(timezone.utc).isoformat(), "run_pages": run_pages, "job_collections": jobs}


def execution(job: Mapping[str, Any]) -> str:
    status, conclusion = job.get("status"), job.get("conclusion")
    if status in PENDING:
        require(conclusion is None, "Pending job has an inconsistent completed conclusion")
        return "in_progress" if status == "in_progress" else "queued"
    require(status == "completed", "Unknown provider job execution status")
    if conclusion in {"action_required", "startup_failure", "stale", "neutral"}:
        return "failure"  # Raw provider conclusion remains in the saved snapshot.
    require(conclusion in CONCLUSIONS, "Unknown or missing completed provider conclusion")
    return conclusion


def classification_index(mapping: Mapping[str, Any]) -> dict[tuple[str, str], dict[str, Any]]:
    require(type(mapping) is dict and type(mapping.get("jobs")) is list, "Reviewed job classification inventory required")
    indexed = {}
    for row in mapping["jobs"]:
        require(type(row) is dict and row.get("classification") in CLASSES
                and type(row.get("evidence_scope")) is str and row["evidence_scope"], "Missing reviewed job scope/classification")
        key = row.get("workflow_path"), row.get("name")
        require(all(type(x) is str and x for x in key) and key not in indexed, "Invalid or duplicate job classification")
        require(type(row.get("on_success")) is str and row["on_success"]
                and type(row.get("on_failure")) is str and row["on_failure"], "Exact scientific dispositions are required")
        indexed[key] = row
    return indexed


def harvest(snapshot: Mapping[str, Any], *, head: str, tree: str, classifications: Mapping[str, Any],
            previous: Mapping[str, Any] | None = None, snapshot_mode: str = "in-workflow",
            current_run_id: int | None = None, required_jobs: list[dict[str, str]] | None = None,
            artifact_evidence: Mapping[str, Any] | None = None,
            artifact_verifier: Callable[[dict, dict, dict], bool] | None = None) -> dict[str, Any]:
    require(snapshot.get("schema") == "OPICA2_PROVIDER_ACTIONS_SNAPSHOT_V1" and snapshot.get("head") == head,
            "Provider snapshot schema/head differs")
    require(snapshot_mode in {"in-workflow", "post-run"}, "Unknown workflow observation mode")
    rules = classification_index(classifications)
    runs = complete_pages(snapshot["run_pages"], "workflow_runs")
    require(all(r.get("head_sha") == head for r in runs), "Mixed source heads in workflow runs")
    collections = {(r["run_id"], r["attempt"]): r for r in snapshot["job_collections"]}
    require(all(type(r.get("run_attempt")) is int and 1 <= r["run_attempt"] <= 1000 for r in runs),
            "Invalid or excessive workflow attempt inventory")
    expected_collections = {(r["id"], attempt) for r in runs for attempt in range(1,r["run_attempt"]+1)}
    require(len(collections) == len(snapshot["job_collections"]) and set(collections) == expected_collections,
            "Missing/duplicate workflow attempt job collection")
    runs = [{**r,"run_attempt":attempt} for r in runs for attempt in range(1,r["run_attempt"]+1)]
    old = {}
    if previous is not None:
        validate_schema(previous, load_strict_json(HERE/"schemas/workflow_harvest.schema.json"))
        for row in previous["jobs"]:
            key = row["workflow_path"], row["event"], row["name"]
            if key not in old or (row["run_id"],row["attempt"],row["job_id"] or 0) > (
                    old[key]["run_id"],old[key]["attempt"],old[key]["job_id"] or 0):
                old[key] = row
    evidence = artifact_evidence or {}
    rows, ids = [], set()
    pending = False
    for run in runs:
        require(type(run.get("run_attempt")) is int and run["run_attempt"] >= 1
                and type(run.get("path")) is str and type(run.get("event")) is str, "Incomplete workflow identity")
        workflow_path = run["path"].split("@", 1)[0]
        key = (run["id"], run["run_attempt"])
        require(key in collections, "No exact attempt job collection")
        jobs = complete_pages(collections[key]["pages"], "jobs")
        seen_names = set()
        for job in jobs:
            require(job.get("run_id") == run["id"] and job.get("head_sha", head) == head,
                    "Job belongs to another run/head")
            require(job["id"] not in ids and type(job.get("name")) is str and job["name"], "Duplicate job or missing name")
            ids.add(job["id"]); seen_names.add(job["name"])
            disposition = execution(job)
            pending = pending or disposition in {"queued", "in_progress"}
            rule = rules.get((workflow_path, job["name"]))
            require(rule is not None, "Unreviewed workflow/job classification: " + workflow_path + " / " + job["name"])
            science = rule["on_success"] if disposition == "success" else rule["on_failure"]
            if disposition in {"queued", "in_progress"}:
                science = "PENDING: no completed scientific disposition"
            elif disposition == "skipped":
                science = "SKIPPED: no execution evidence or new mathematical authority"
            prior = old.get((workflow_path, run["event"], job["name"]))
            comparison = "NO_REVIEWED_PRIOR_RESULT" if prior is None else (
                "UNCHANGED_EXECUTION; mathematical implications require review against the new theorem state"
                if prior["execution"] == disposition else "CHANGED_EXECUTION; investigate source-pinned logs and mathematical disposition")
            proof = evidence.get(str(job["id"]))
            hashes = []
            if proof is not None:
                require(artifact_verifier is not None and artifact_verifier(proof,job,run) is True,
                        "Scientific artifact disposition needs independent source-pinned revalidation")
                require(proof.get("head") == head and proof.get("run_id") == run["id"]
                        and proof.get("attempt") == run["run_attempt"]
                        and type(proof.get("artifact_hashes")) is list,
                        "Artifact evidence has stale or incomplete workflow identity")
                hashes = proof["artifact_hashes"]
                if proof.get("scientific_disposition") is not None:
                    require(type(proof["scientific_disposition"]) is str and proof["scientific_disposition"],
                            "Invalid reviewed scientific artifact disposition")
                    science = proof["scientific_disposition"]
            elif disposition == "success":
                science += "; PROVIDER_SUCCESS_ONLY: artifacts/log claims not revalidated by this harvest"
            rows.append({"head":head,"workflow_path":workflow_path,"event":run["event"],
                "run_id":run["id"],"attempt":run["run_attempt"],"job_id":job["id"],"name":job["name"],
                "execution":disposition,"classification":rule["classification"],"scientific_disposition":science,
                "evidence_scope":rule["evidence_scope"],"prior_result":None if prior is None else prior["scientific_disposition"],
                "comparison":comparison,"artifact_hashes":hashes,"source_url":job.get("html_url",run.get("html_url",""))})
        for expected in required_jobs or []:
            if expected["workflow_path"] != workflow_path or expected["name"] in seen_names:
                continue
            rule = rules.get((workflow_path, expected["name"]))
            require(rule is not None, "Missing classification for not-yet-instantiated required job")
            pending = True
            rows.append({"head":head,"workflow_path":workflow_path,"event":run["event"],
                "run_id":run["id"],"attempt":run["run_attempt"],"job_id":None,"name":expected["name"],
                "execution":"NOT_YET_INSTANTIATED","classification":rule["classification"],
                "scientific_disposition":"PENDING: required job has not been instantiated; no PASS inferred",
                "evidence_scope":rule["evidence_scope"],"prior_result":None,"comparison":"NO_COMPLETED_RESULT",
                "artifact_hashes":[],"source_url":run.get("html_url","")})
        if run.get("status") != "completed":
            pending = True
    expected_workflows={r["workflow_path"] for r in required_jobs or []}
    require(not expected_workflows or expected_workflows <= {r["path"].split("@",1)[0] for r in runs},
            "A required workflow has not been instantiated; its unknown run ID cannot be invented")
    final = bool(runs and rows) and snapshot_mode == "post-run" and not pending and current_run_id not in {r["id"] for r in runs}
    require(snapshot_mode != "post-run" or final, "Post-run snapshot still has pending/self workflow evidence")
    report = {"schema":"OPICA2_WORKFLOW_HARVEST_V1","head":head,"tree":tree,
        "observed_at_utc":snapshot["observed_at_utc"],"all_pages_read":True,
        "is_final_post_run_snapshot":final,"jobs":rows,"RH":"OPEN","Step4":"OPEN"}
    validate_schema(report, load_strict_json(HERE/"schemas/workflow_harvest.schema.json"))
    return report


def public_json(url: str) -> dict:
    parsed = urlsplit(url)
    require(parsed.scheme == "https" and parsed.hostname == "api.github.com" and parsed.username is None,
            "Only GitHub's HTTPS read API is permitted")
    headers = {"Accept":"application/vnd.github+json","X-GitHub-Api-Version":"2022-11-28",
               "User-Agent":"opica-round2-evidence-harvester"}
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token:
        headers["Authorization"] = "Bearer " + token
    request = Request(url, headers=headers, method="GET")
    with urlopen(request, timeout=60) as response:
        require(urlsplit(response.url).hostname == "api.github.com", "Unexpected provider redirect")
        return loads_strict_json(response.read(32*1024*1024+1), 32*1024*1024)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo",type=Path,default=REPO)
    parser.add_argument("--owner",default="HMarcusWH")
    parser.add_argument("--repository",default="zeta-23-lean")
    parser.add_argument("--head")
    parser.add_argument("--snapshot",type=Path)
    parser.add_argument("--classifications",type=Path,required=True)
    parser.add_argument("--previous",type=Path)
    parser.add_argument("--snapshot-mode",choices=("in-workflow","post-run"),default="in-workflow")
    parser.add_argument("--output-dir",type=Path,required=True)
    args = parser.parse_args()
    output_existed=args.output_dir.exists()
    try:
        head = args.head or contract.git(args.repo,"rev-parse","HEAD")
        tree = contract.git(args.repo,"rev-parse",head+"^{tree}")
        require(not args.output_dir.exists(), "Use a new harvest directory; prior observations are immutable")
        args.output_dir.mkdir(parents=True)
        snapshot = load_strict_json(args.snapshot,64*1024*1024) if args.snapshot else collect(public_json,args.owner,args.repository,head)
        (args.output_dir/"provider-snapshot.json").write_text(json.dumps(snapshot,indent=2)+"\n",encoding="utf-8")
        classifications=load_strict_json(args.classifications)
        result=harvest(snapshot,head=head,tree=tree,classifications=classifications,
            previous=load_strict_json(args.previous,64*1024*1024) if args.previous else None,
            snapshot_mode=args.snapshot_mode,current_run_id=int(os.environ["GITHUB_RUN_ID"]) if os.environ.get("GITHUB_RUN_ID") else None,
            required_jobs=classifications.get("required_jobs"))
        (args.output_dir/"workflow-harvest.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    except (OSError,ValueError,TypeError,KeyError) as exc:
        result=failure_envelope("workflow_harvest",exc)
        if not output_existed and args.output_dir.is_dir() and not (args.output_dir/"failure.json").exists():
            (args.output_dir/"failure.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))
    return 0 if result.get("schema")=="OPICA2_WORKFLOW_HARVEST_V1" else 1


if __name__=="__main__":
    raise SystemExit(main())
