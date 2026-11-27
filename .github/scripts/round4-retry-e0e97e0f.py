"""Retry only the configured Round4 attempt when the whole failure is a runner feed outage."""
import argparse
import json
import os
import re
import signal
import subprocess
import sys
import urllib.request
from urllib.parse import urlencode

REPO = "HMarcusWH/zeta-23-lean"
REPO_ID = 1339954300
RUN = 46068027549
WORKFLOW = 399701040
PATH = ".github/workflows/rhrc_opica_composition.yml"
HEAD = "e0e97e0f53f20fb8c5b34404c697b0950d3ef46d"
BASE = "d4c7fc7114e5f1b61b90ea9037890969358ff0cc"
BRANCH = "review/paper-320-combined-source"
API = "/repos/" + REPO + "/"
LANES = {
    "SEMANTIC_NEGATIVES": 140737966801, "REPLAY_CAMPAIGN": 140737967027,
    "PROVIDER_SELECTED": 140737967071, "CONTRACT": 140737967083,
    "GENERATED_STATE": 140737967090, "COMPOSITION_FORMAL": 140737967093,
    "FRAMEWORK_ADAPTERS": 140737967123, "CURRENT_COMPATIBILITY": 140737967125,
    "PARENT_REGRESSION": 140737967138, "MATHEMATICAL_SUPPORT": 140737967133,
    "SOURCE_NUMERICS": 140737967142,
}
HIST = "POST299_HISTORICAL_15_OF_15_REGRESSION_NOT_REPLAY"
INDEPENDENT = {"INDEPENDENT_" + n for n in ("AUXILIARY", "CORE", "CANONICAL")}
RUNTIME = "Run ./host/.github/actions/opica4-runtime"
LANE = "Execute exact source-bound lane in a bounded cgroup"
IGUARD = "Require every matrix job to succeed"
AGUARD = "Require every producer and independent group to succeed"
CHECKOUT = "Run actions/checkout@11d5960a326750d5838078e36cf38b85af677262"
SIGNATURE = re.compile(r"E: Failed to fetch https://packages\.microsoft\.com/ubuntu/24\.04/prod/dists/noble/InRelease\s+403\s+Forbidden(?: \[IP: [a-fA-F0-9.:]+ 443\])?$")
SIGNING = "E: The repository 'https://packages.microsoft.com/ubuntu/24.04/prod noble InRelease' is no longer signed."
NO_HOST = "##[error]An error occurred trying to start process '/usr/bin/bash' with working directory '/home/runner/work/zeta-23-lean/zeta-23-lean/host'. No such file or directory"

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def gh(*args):
    return subprocess.check_output(["gh", "api", "--hostname", "github.com", *args], timeout=25)

def read(path, *, log=False):
    # gh handles tokens and signed log redirects without passing secrets to untrusted scripts.
    if os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN"):
        data = gh(API + path)
    else:
        request = urllib.request.Request("https://api.github.com" + API + path,
                                         headers={"Accept": "application/vnd.github+json", "User-Agent": "round4-retry-readback"})
        with urllib.request.urlopen(request, timeout=20) as response:
            data = response.read(16_000_001)
    require(len(data) <= 16_000_000, "unexpectedly large response")
    return data.decode("utf-8-sig") if log else json.loads(data)

def anchors():
    run = read(f"actions/runs/{RUN}")
    reqs = run["pull_requests"]
    require((run["id"],run["workflow_id"],run["path"],run["run_attempt"],run["event"],run["head_branch"],run["head_sha"]) ==
            (RUN,WORKFLOW,PATH,1,"pull_request",BRANCH,HEAD), "run identity or attempt changed")
    for r in (run["repository"],run["head_repository"]):
        require((r["full_name"],r["id"]) == (REPO,REPO_ID), "run repository changed")
    require(len(reqs) == 1 and reqs[0]["id"] == 5530754949 and reqs[0]["number"] == 321, "run PR changed")
    pr = read("pulls/321")
    require(pr["state"] == "open" and not pr["merged"] and pr["number"] == 321 and pr["id"] == 5530754949, "PR state changed")
    for context in (pr,reqs[0]):
        for k, ref, commit in (("head",BRANCH,HEAD),("base","main",BASE)):
            r = context[k]
            require((r["ref"],r["sha"],r["repo"]["id"]) == (ref,commit,REPO_ID), "PR source or base changed")
    for ref,commit in ((BRANCH,HEAD),("main",BASE)):
        r = read("git/ref/heads/" + ref)
        require((r["ref"],r["object"]["type"],r["object"]["sha"]) == ("refs/heads/"+ref,"commit",commit), "advertised ref moved")
    require((run["status"],run["conclusion"]) == ("completed","failure"),
            f"attempt 1 is {run['status']}/{run['conclusion']}; retry is ineligible")

def no_other_run():
    # The workflow uses cancel-in-progress, keyed on the head branch. Do not displace another run.
    query = urlencode({"branch": BRANCH,"per_page":100})
    found = read(f"actions/workflows/{WORKFLOW}/runs?{query}")
    runs = found["workflow_runs"]
    require(len(runs) == found["total_count"] and any(x["id"] == RUN for x in runs), "incomplete branch run census")
    require(not any(x["id"] != RUN and x["status"] != "completed" for x in runs), "another Round4 run is active for this branch")
    require(not any(x["id"] > RUN and x["event"] == "pull_request" for x in runs), "a newer PR run supersedes this one")

def stripped_log(raw):
    return [re.sub(r"^\d{4}-\d\d-\d\dT[0-9:.]+Z ", "", x).strip() for x in raw.splitlines()]

def check_feed(raw):
    lines = stripped_log(raw)
    errors = [line for line in lines if line.startswith(("E:", "##[error]"))]
    require(len(errors) == 3 and SIGNATURE.fullmatch(errors[0]) and errors[1:] == [SIGNING,"##[error]Process completed with exit code 100."], "bootstrap cause differs from the authenticated Microsoft 403")

def check_upstream(raw, independent):
    lines = stripped_log(raw)
    err = [x for x in lines if x.startswith("##[error]")]
    expected = ["##[error]Process completed with exit code 1."]
    # A skipped checkout also prevents the optional, continue-on-error diagnostic from starting.
    require(err == expected or (independent and err == expected + [NO_HOST]), "downstream error differs from upstream gate")
    before_failure = lines[:lines.index(expected[0])]
    needed = {"UPSTREAM: failure"} if independent else {"PRODUCERS: failure","INDEPENDENT: failure"}
    require(needed <= set(before_failure), "downstream prerequisite evidence missing")

def check_jobs(result, logs):
    rows = result["jobs"]
    require(result["total_count"] == len(rows) == 16, "expected all 16 attempt-1 jobs")
    expected = set(LANES) | INDEPENDENT | {"ACCEPTANCE",HIST}
    names = [j["name"].removeprefix("Round4 / ") for j in rows]
    require(set(names)==expected and len({j['id'] for j in rows})==16, "unexpected job role or duplicate")
    causes = {}
    for name,j in zip(names,rows):
        require(j["name"]=="Round4 / "+name and (j["run_id"],j["run_attempt"],j["head_sha"],j["head_branch"],j["status"])==
                (RUN,1,HEAD,BRANCH,"completed"), "job identity or status mismatch")
        if name == HIST:
            require(j["id"] == 140737968313 and j["conclusion"]=="skipped", "PR 300/301 historic lane changed")
            continue
        if name in LANES:
            require(j["id"]==LANES[name], "producer job ID differs")
            if j["conclusion"] == "success":
                require(name!="FRAMEWORK_ADAPTERS", "known failed adapter unexpectedly passed")
                success={s["name"] for s in j["steps"] if s["status"]=="completed" and s["conclusion"]=="success"}
                require({CHECKOUT, RUNTIME, LANE, "Seal directory-preserving evidence transport",
                         "Run actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02"} <= success, "incomplete successful lane")
                continue
        require(j["conclusion"] == "failure", "non-success disposition is outside this retry")
        steps = j["steps"]
        require(all(s["status"]=="completed" and s["conclusion"] in {"success","skipped","failure"} for s in steps), "unexpected step disposition")
        def at(step,conclusion):
            return any(s["name"]==step and s["conclusion"]==conclusion for s in steps)
        failed=[s for s in steps if s["conclusion"]=="failure"]
        require(len(failed)==1,"additional failed step")
        if name in LANES:
            require(failed[0]["name"]==RUNTIME and at(CHECKOUT,"success") and at(LANE,"skipped") and
                    at("Seal directory-preserving evidence transport","skipped"), "source or non-bootstrap producer failure")
            check_feed(logs(j["id"]))
            causes[name]="Microsoft Ubuntu 24.04 noble InRelease HTTP 403"
        else:
            indep=name in INDEPENDENT
            target = "Reconstruct eleven complete bundles and run the fixed independent group" if indep else "Reconstruct and bind every producer and independent group"
            require(failed[0]["name"]==(IGUARD if indep else AGUARD) and at(CHECKOUT,"skipped") and at(target,"skipped"), "downstream execution or unexpected cause")
            check_upstream(logs(j["id"]),indep)
            causes[name]="producer prerequisite failed"
    require("FRAMEWORK_ADAPTERS" in causes,"known adapter failure missing")
    return causes

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--retry",action="store_true",help="after live checks, make one full same-run retry request")
    args=p.parse_args()
    anchors()
    out=check_jobs(read(f"actions/runs/{RUN}/attempts/1/jobs?per_page=100"),lambda i:read(f"actions/jobs/{i}/logs",log=True))
    no_other_run()
    print(json.dumps({"run":RUN,"attempt":1,"source":HEAD,"base":BASE,"causes":out}))
    if args.retry:
        require(os.environ.get("GITHUB_REPOSITORY")==REPO and os.environ.get("GITHUB_REF")=="refs/heads/workmode/paper-320-reviewed-generated-publish", "activation is restricted to the existing paper helper")
        require(bool(os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")), "Actions-write credential required")
        helper=read("git/ref/heads/workmode/paper-320-reviewed-generated-publish")
        require(helper["ref"]==os.environ["GITHUB_REF"] and helper["object"]["type"]=="commit" and
                helper["object"]["sha"]==os.environ.get("GITHUB_SHA"), "shared helper moved")
        anchors()
        no_other_run()
        # No retries, content writes, cancellation, or endpoint selected by caller. Read next attempt separately.
        response=gh("--include","--method","POST",API+f"actions/runs/{RUN}/rerun")
        require(re.match(rb"HTTP/\S+ 201\b",response), "unexpected POST result; read back attempt before further action")
        print("Full retry accepted. Read back attempt 2 and all original receipts.")
    else:
        print("Read-only qualification passed.")

if __name__=="__main__":
    try:
        signal.alarm(150)
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as exc:
        sys.exit(f"BLOCKED: {exc}")
