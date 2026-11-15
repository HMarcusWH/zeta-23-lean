"""Historical V1 15-job acceptance verifier; never a current-head approval."""
import json, os, subprocess
from pathlib import Path
from urllib.request import Request,urlopen
HEAD="4b123cb4ebc3ec587ee7c6e361674caef47e2ad4"
MERGE="df914f38f26bdc4109aeaa13f48b3896c3bc61b1"
TREE="5fc2aa4793b658c58dd89c1d36b0ceee756d400d"
RUN=43299302582
JOBS={f"Round4 / {x}" for x in (
 "CONTRACT","PARENT_REGRESSION","CURRENT_COMPATIBILITY","MATHEMATICAL_SUPPORT",
 "SOURCE_NUMERICS","PROVIDER_SELECTED","GENERATED_STATE","FRAMEWORK_ADAPTERS",
 "REPLAY_CAMPAIGN","SEMANTIC_NEGATIVES","COMPOSITION_FORMAL","INDEPENDENT_CORE",
 "INDEPENDENT_AUXILIARY","INDEPENDENT_CANONICAL","ACCEPTANCE")}
def load(path):
 token=os.environ.get("GITHUB_TOKEN")
 if not token: raise RuntimeError("GitHub Actions token missing")
 req=Request("https://api.github.com/repos/HMarcusWH/zeta-23-lean"+path,
  headers={"Accept":"application/vnd.github+json",
  "Authorization":"Bearer "+token,"X-GitHub-Api-Version":"2022-11-28"})
 with urlopen(req,timeout=20) as res:return json.load(res)
def audit(root):
 def git(*args):return subprocess.check_output(["git","-C",str(root),*args],text=True).strip()
 if git("rev-parse",HEAD+"^{tree}")!=TREE or git("rev-parse",MERGE+"^{tree}")!=TREE:
  raise RuntimeError("Original full-V1 acceptance tree differs from merged tree")
 run=load("/actions/runs/"+str(RUN))
 if any((run.get(k)!=v) for k,v in {
  "id":RUN,"head_sha":HEAD,"run_attempt":1,"status":"completed",
  "conclusion":"success","event":"pull_request"}.items()):
  raise RuntimeError("Wrong frozen #299 run identity or result")
 rows=load("/actions/runs/"+str(RUN)+"/jobs?per_page=100&filter=latest")["jobs"]
 if len(rows)!=15 or {r["name"] for r in rows}!=JOBS or any(
   r.get("conclusion")!="success" or r.get("status")!="completed" or r.get("run_id")!=RUN
   for r in rows):
  raise RuntimeError("Frozen #299 15-job acceptance is not completely green")
 return {"schema":"OPICA4_POST299_ACCEPTED_V1_HISTORICAL_RECEIPT_V1",
  "status":"PASS_FROZEN_V1_PREVIOUSLY_ACCEPTED","authority":"REGRESSION_ONLY_NO_CURRENT_HEAD_ACCEPTANCE",
  "run_id":RUN,"run_attempt":1,"head":HEAD,"merge":MERGE,"tree":TREE,
  "jobs":sorted(JOBS),"successor_human_review":"PENDING","RH":"OPEN","Step4":"OPEN"}
if __name__=="__main__":
 import argparse
 p=argparse.ArgumentParser();p.add_argument("--repo",type=Path,required=True)
 p.add_argument("--output",type=Path,required=True)
 a=p.parse_args(); result=audit(a.repo.resolve(strict=True))
 if a.output.exists():raise RuntimeError("Refuse historical receipt overwrite")
 a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
 print(json.dumps({"status":result["status"],"jobs":15,"RH":"OPEN","Step4":"OPEN"}))
