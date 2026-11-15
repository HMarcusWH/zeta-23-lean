"""Non-self-authorizing successor composite acceptance candidate.

V1 historical acceptance and V2 independent numerical evidence are different
claims, even when both pass. The report is NEVER approval of the revised
source policy and cannot set merge_ready. Independent human review is external.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

FROZEN_HEAD = "df914f38f26bdc4109aeaa13f48b3896c3bc61b1"
FROZEN_TREE = "5fc2aa4793b658c58dd89c1d36b0ceee756d400d"
HIST_RUN = 43299302582
CASE_IDS = (
    "K4_Q3_FIVE_FOURTHS", "K5_Q5_SEVEN_FOURTHS",
    "K5_LOG4_SEAM", "K5_Q4_MODIFIED_Q2_HALF",
    "K4_Q2_ENTERING_Q2", "K4_Q4_ENTERING_Q4",
)
EXPECTED_AX = frozenset(("propext","Classical.choice","Quot.sound"))
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
HIST_JOBS = frozenset(f"Round4 / {x}" for x in (
    "CONTRACT","PARENT_REGRESSION","CURRENT_COMPATIBILITY",
    "MATHEMATICAL_SUPPORT","SOURCE_NUMERICS","PROVIDER_SELECTED",
    "GENERATED_STATE","FRAMEWORK_ADAPTERS","REPLAY_CAMPAIGN",
    "SEMANTIC_NEGATIVES","COMPOSITION_FORMAL","INDEPENDENT_CORE",
    "INDEPENDENT_AUXILIARY","INDEPENDENT_CANONICAL","ACCEPTANCE",
))

def require(predicate: bool, message: str):
    if not predicate:
        raise ValueError(message)

def strict_json(path: Path):
    def no_repeat(pairs):
        value={}
        for k,v in pairs:
            require(k not in value,"Duplicate evidence field "+k)
            value[k]=v
        return value
    return json.loads(path.read_bytes(),object_pairs_hook=no_repeat,
                      parse_constant=lambda x:(_ for _ in ()).throw(ValueError("Non-finite JSON")))

def source_check(x: dict, sha: str, tree: str):
    require(type(x) is dict, "Missing current source record")
    require(x.get("schema") in (
        "OPICA5_POST299_SUCCESSOR_SOURCE_INSPECTION_V2",
        "OPICA5_POST299_SUCCESSOR_SOURCE_INSPECTION_V3"),"Unknown reviewed-source policy version")
    require(x.get("status")=="PASS_SOURCE_SCOPE_ONLY","Current source scope did not pass")
    require(x.get("checked_commit")==sha and x.get("checked_tree")==tree,
            "Current source receipt is for another head/tree")
    require(x.get("base")==FROZEN_HEAD and x.get("base_tree")==FROZEN_TREE,
            "Wrong immutable parent")
    require(x.get("successor_human_review")=="PENDING" and x.get("full_round4_accepted") is False,
            "Current source receipt improperly claims release authority")
    require(type(x.get("path_policy")) is str and SHA256.fullmatch(x["path_policy"]),
            "No precise successor source-policy digest")
    delta=x.get("delta")
    require(type(delta) is dict and delta.get("deleted")==[],
            "Source delta includes deletions")
    for field in ("added","edited","generated"):
        require(type(delta.get(field)) is list and len(delta[field])==len(set(delta[field])),
                "Duplicate or malformed source delta: "+field)
    require(x.get("RH")=="OPEN" and x.get("Step4")=="OPEN","Source report escalated an open claim")

def baseline_check(x: dict):
    require(type(x) is dict,"Missing #299 baseline evidence")
    require(x.get("schema")=="OPICA4_POST299_ACCEPTED_V1_HISTORICAL_RECEIPT_V1" and
            x.get("status")=="PASS_FROZEN_V1_PREVIOUSLY_ACCEPTED" and
            x.get("authority")=="REGRESSION_ONLY_NO_CURRENT_HEAD_ACCEPTANCE",
            "Historical V1 evidence mislabeled or incomplete")
    require(x.get("run_id")==HIST_RUN and x.get("run_attempt")==1,
            "Historical baseline was substituted")
    require(x.get("merge")==FROZEN_HEAD and x.get("tree")==FROZEN_TREE,
            "Wrong historical source")
    require(type(x.get("jobs")) is list and len(x["jobs"])==15
            and set(x["jobs"])==HIST_JOBS,"Not the full V1 fifteen-job acceptance")
    require(x.get("RH")=="OPEN" and x.get("Step4")=="OPEN","Historical RH escalation")

def numerical_check(x: dict):
    require(type(x) is dict, "Missing independent 512-bit evidence")
    require(x.get("schema")=="OPICA4_SOURCE_NUMERICS_LANE_V2_CANDIDATE" and
            x.get("status")=="CANDIDATE_V2_RECOMPUTED_FINITE_SOURCE_NOT_RELEASE" and
            x.get("authority")=="CANDIDATE_V2_FINITE_INTERVAL_EVIDENCE_NOT_RELEASE",
            "Wrong V2 numerical claim authority")
    require(x.get("acceptance_eligible") is False and
            x.get("kernel_or_cell_authority") is False and
            x.get("is_zero_generated_detector") is False,"Numerical evidence escalated authority")
    require(x.get("checked_commit")==FROZEN_HEAD and x.get("checked_tree")==FROZEN_TREE,
            "V2 replay did not verify frozen exact source")
    require(x.get("modes")==["normal","optimized"] and
            x.get("case_ids")==list(CASE_IDS),"Incomplete producer mode or case inventory")
    require(type(x.get("independently_recomputed_cases")) is int and
            x["independently_recomputed_cases"]==6 and
            type(x.get("contained_interval_comparisons")) is int and
            x["contained_interval_comparisons"]>=10000,"Insufficient fresh independent evidence")
    hashes=x.get("direct_case_sha256")
    require(type(hashes) is dict and set(hashes)==set(CASE_IDS) and
            all(type(v) is str and SHA256.fullmatch(v) for v in hashes.values()),
            "Direct worker result digests incomplete")
    disp=x.get("dispositions")
    require(type(disp) is dict and set(disp)==set(CASE_IDS),"Missing research dispositions")
    require(all(type(v) is dict and v.get("status")=="CERTIFIED_FINITE_POINT_FALSIFICATION_CONTROL"
                and "FINITE_POINT_ONLY" in v.get("scope","") for v in disp.values()),
            "Incorrect scientific finite-source disposition")
    identity=x.get("source_identity")
    require(type(identity) is dict and identity.get("head")==FROZEN_HEAD and
            identity.get("tree")==FROZEN_TREE and identity.get("clean") is True,
            "V2 source identity is not clean and frozen")

def formal_axioms(text: str):
    rows=re.findall(r"depends on axioms: \[([^\]]+)\]",text)
    require(len(rows)>=4,"Missing Lean theorem-specific #print axioms transcript")
    for row in rows:
        names=frozenset(x.strip() for x in row.split(","))
        require(names <= EXPECTED_AX,"Lean theorem introduced an unexpected axiom")
    require(any("fixedMomentParityShortExact" in line for line in text.splitlines()),
            "Missing exact short-sequence theorem axiom output")

def current_repo(root: Path, expected_head: str, expected_tree: str):
    def git(*args):
        return subprocess.check_output(["git","-C",str(root),*args],text=True).strip()
    require(git("rev-parse","HEAD")==expected_head and
            git("rev-parse","HEAD^{tree}")==expected_tree,
            "Composite evidence not checked on exact expected successor commit/tree")
    require(not git("status","--porcelain","--untracked-files=all"),
            "Successor checkout dirty at composite acceptance")
    require(git("rev-parse",FROZEN_HEAD+"^{tree}")==FROZEN_TREE,
            "Accepted frozen #299 tree changed")

def assemble(root: Path, source: dict, baseline: dict, numeric: dict,
             axioms: str, head: str, tree: str, run_id: str, attempt: str) -> dict:
    current_repo(root,head,tree)
    source_check(source,head,tree)
    baseline_check(baseline)
    numerical_check(numeric)
    formal_axioms(axioms)
    require(run_id.isdecimal() and attempt.isdecimal() and int(attempt)>0,
            "Missing current workflow run/attempt")
    return {
        "schema":"OPICA5_POST299_COMPOSITE_EVIDENCE_CANDIDATE_V1",
        "status":"PASS_COMPOSITE_EVIDENCE_PENDING_INDEPENDENT_REVIEW",
        "authority":"HISTORICAL_FULL_V1_REGRESSION_PLUS_NEW_V2_NUMERICS_PLUS_CURRENT_LEAN_ONLY",
        "current_head":head,"current_tree":tree,
        "workflow_run_id":run_id,"workflow_attempt":int(attempt),
        "frozen_subject":FROZEN_HEAD,"frozen_tree":FROZEN_TREE,
        "full_historical_v1_jobs":15,
        "independent_source_cases":numeric["independently_recomputed_cases"],
        "direct_interval_containments":numeric["contained_interval_comparisons"],
        "current_source_policy_digest":source["path_policy"],
        "source_policy_schema":source["schema"],
        "case_digests":numeric["direct_case_sha256"],
        "independent_release_review":"PENDING",
        "generated_state_release_check":"SEPARATE_REQUIRED_GATE",
        "merge_ready":False,"RH":"OPEN","Step4":"OPEN",
    }

def _selftest():
    sample={"schema":"OPICA4_SOURCE_NUMERICS_LANE_V2_CANDIDATE",
      "status":"CANDIDATE_V2_RECOMPUTED_FINITE_SOURCE_NOT_RELEASE",
      "authority":"CANDIDATE_V2_FINITE_INTERVAL_EVIDENCE_NOT_RELEASE",
      "checked_commit":FROZEN_HEAD,"checked_tree":FROZEN_TREE,
      "source_identity":{"head":FROZEN_HEAD,"tree":FROZEN_TREE,"clean":True},
      "modes":["normal","optimized"],"case_ids":list(CASE_IDS),
      "independently_recomputed_cases":6,"contained_interval_comparisons":10012,
      "direct_case_sha256":{k:"a"*64 for k in CASE_IDS},
      "dispositions":{k:{"status":"CERTIFIED_FINITE_POINT_FALSIFICATION_CONTROL",
                      "scope":"FINITE_POINT_ONLY"} for k in CASE_IDS},
      "acceptance_eligible":False,"kernel_or_cell_authority":False,
      "is_zero_generated_detector":False}
    numerical_check(sample)
    for key, value in [
        ("acceptance_eligible",True),
        ("contained_interval_comparisons",0),
        ("modes",["normal"]),
        ("case_ids",list(CASE_IDS[:-1])),
        ("checked_commit","0"*40),
        ("status","PASS_NEW_RH"),
    ]:
        mutation={**sample,key:value}
        try:numerical_check(mutation)
        except ValueError:pass
        else:raise AssertionError("Nonaccepting composite admitted a bad numerical report: "+key)
    formal_axioms("fixedMomentParityShortExact depends on axioms: [propext, Classical.choice, Quot.sound]\n"*4)
    try: formal_axioms("fixedMomentParityShortExact depends on axioms: [unsound_custom]\n"*4)
    except ValueError:pass
    else:raise AssertionError("Unexpected project axiom accepted")
    print("Composite candidate evidence and negative controls: PASS")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--selftest",action="store_true")
    p.add_argument("--repo",type=Path)
    p.add_argument("--baseline",type=Path)
    p.add_argument("--current-source",type=Path)
    p.add_argument("--independent-source",type=Path)
    p.add_argument("--axioms",type=Path)
    p.add_argument("--head");p.add_argument("--tree")
    p.add_argument("--run-id");p.add_argument("--attempt")
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    if args.selftest:return _selftest()
    for key in ("repo","baseline","current_source","independent_source","axioms",
                "head","tree","run_id","attempt","output"):
        require(getattr(args,key) is not None,"Missing mandatory input: "+key)
    result=assemble(args.repo.resolve(strict=True),
        strict_json(args.current_source),strict_json(args.baseline),
        strict_json(args.independent_source),args.axioms.read_text(),
        args.head,args.tree,args.run_id,args.attempt)
    require(not args.output.exists(),"Refuse to overwrite versioned evidence report")
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":result["status"],"cases":result["independent_source_cases"],
           "containments":result["direct_interval_containments"],
           "merge_ready":False,"RH":"OPEN","Step4":"OPEN"}))

if __name__=="__main__":main()
