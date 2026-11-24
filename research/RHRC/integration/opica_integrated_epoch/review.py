"""Non-promoting integrated epoch: exact donor blobs, no copied acceptance."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
REL=HERE.relative_to(ROOT).as_posix()+"/"
WORKFLOW=".github/workflows/opica-integrated-epoch.yml"
FC="research/RHRC/graph/FILE_CLASSES.json"
SEM="research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json"
CLAIMS={"proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
ALLOWED={"propext","Classical.choice","Quot.sound"}

def need(ok, msg):
    if not ok:
        raise RuntimeError(msg)

def run(*args):
    return subprocess.check_output(args,cwd=ROOT,text=True).strip()

def git(*args):
    return run("git",*args)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def load(p):
    return json.loads(p.read_text())

def save(p,d):
    p.write_text(json.dumps(d,indent=2,sort_keys=True)+"\n")

def check_delta(actual, additions, edits):
    expected={**{p:"A" for p in additions},**{p:"M" for p in edits}}
    need(actual==expected,"Unexpected source delta: "+repr(sorted(set(actual.items())^set(expected.items())))[:1500])

def axiom_reports(text, roots):
    need(not re.search(r"\bsorryAx\b|(?:^|\n).*?\berror:",text),"Compiler error or sorryAx")
    found={}
    for m in re.finditer(r"(?m)^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)[ \t]*(?=\n|$)",text):
        name,raw=m.groups()
        need(name in roots and name not in found,"Unexpected or duplicate axiom root: "+name)
        values=[] if raw is None else [x.strip() for x in raw.split(",") if x.strip()]
        need(len(values)==len(set(values)) and set(values)<=ALLOWED,"Nonstandard axiom: "+name)
        found[name]=sorted(values)
    need(set(found)==set(roots),"Missing named axiom reports")
    return found

def check():
    s=load(HERE/"LOCK.json")
    need(s["schema"]=="OPICA_INTEGRATED_SOURCE_CANDIDATE_V1" and all(s[k]==v for k,v in CLAIMS.items()),"Claim boundary")
    head=git("rev-parse","HEAD")
    need(git("rev-parse",s["parent"]+"^{tree}")==s["parent_tree"],"Parent tree mismatch")
    need(git("merge-base",s["parent"],head)==s["parent"],"Wrong ancestry")
    need(not git("status","--porcelain","--untracked-files=all"),"Dirty worktree")
    overlay=s["overlays"]
    need(len(overlay)==26 and len({x["path"] for x in overlay})==26,"Overlay count")
    need(len(s["roots"])==len(set(s["roots"]))==183 and s["historical_root_count"]==167 and s["bipolar_root_count"]==16,"Root census")
    need(all(re.fullmatch(r"[\w.']+",x) for x in s["roots"]),"Invalid declaration name")
    own={REL+x for x in ("LOCK.json","review.py","test_review.py","README.md")}|{WORKFLOW}
    raw=git("diff","--name-status","--no-renames",s["parent"],head)
    pairs=[x.split("\t",1) for x in raw.splitlines()]
    need(all(len(x)==2 for x in pairs),"Invalid change record")
    actual={p:a for a,p in pairs}
    need(len(actual)==len(pairs),"Duplicate change")
    check_delta(actual,{x["path"] for x in overlay}|own,{FC,SEM})
    for donor,t in s["donor_trees"].items():
        need(git("rev-parse",donor+"^{tree}")==t,"Donor tree mismatch")
    for row in overlay:
        p=row["path"]
        need(git("rev-parse",row["donor"]+":"+p)==row["sha"]==git("rev-parse","HEAD:"+p),"Donor blob drift: "+p)
        f=ROOT/p
        need(f.is_file() and not f.is_symlink(),"Nonregular overlay")
        if "sha256" in row:
            need(sha(f)==row["sha256"],"Historical port bytes drift")
        need(not re.search(r"\b(sorry|admit|axiom)\b",re.sub(r"/-.*?-/|--[^\n]*","",f.read_text(),flags=re.S)),"Potential proof escape: "+p)
    for row in s["existing_native_modules"]:
        need(sha(ROOT/row["path"])==row["sha256"],"Existing native module differs")
    need((ROOT/"lean-toolchain").read_text().strip()==s["toolchain"],"Toolchain differs")
    need([x["rev"] for x in load(ROOT/"lake-manifest.json")["packages"] if x["name"]=="mathlib"]==[s["mathlib"]],"Mathlib differs")
    fc=json.loads(git("show",s["parent"]+":"+FC))
    fc["rules"]=s["classification_rules"]+fc["rules"]
    need(load(ROOT/FC)==fc,"Classification exceeds reviewed overlay")
    sem=json.loads(git("show",s["parent"]+":"+SEM))
    need(not set(sem["standalone_module_roles"])&set(s["module_roles"]),"Role collision")
    sem["standalone_module_roles"].update(s["module_roles"])
    need(load(ROOT/SEM)==sem,"Module roles exceed reviewed overlay")
    return {"schema":"OPICA_INTEGRATED_SCOPE_RECEIPT_V1","status":"SOURCE_SCOPE_ONLY","head":head,"tree":git("rev-parse","HEAD^{tree}"),"parent":s["parent"],"overlays":overlay,"root_count":183,"source_sha256":{p:sha(ROOT/p) for p in sorted(actual)},**CLAIMS}

def api(path):
    return json.loads(run("gh","api",path))

def readiness():
    s=load(HERE/"LOCK.json")
    rows=[]
    for x in s["prerequisites"]:
        try:
            repo=os.environ["GITHUB_REPOSITORY"]
            a=api(f"repos/{repo}/actions/runs/{x['run']}")
            need(a["head_sha"]==x["head"] and a["path"].split("@")[0]==x["path"] and a["repository"]["full_name"]==repo,"Producer identity")
            attempt=a["run_attempt"]
            jj=api(f"repos/{repo}/actions/runs/{x['run']}/attempts/{attempt}/jobs?per_page=100")
            need(jj["total_count"]==len(jj["jobs"]),"Incomplete job population")
            jobs=[{"name":j["name"],"status":j["status"],"conclusion":j["conclusion"]} for j in jj["jobs"]]
            ready=all(sum(j["name"]==n and j["conclusion"]=="success" for j in jobs)==1 for n in x["jobs"])
            rows.append({"run":x["run"],"head":a["head_sha"],"attempt":attempt,"required":x["jobs"],"jobs":jobs,"ready":ready})
        except Exception as exc:
            rows.append({"run":x["run"],"ready":False,"error":str(exc)[:1200]})
    return {"schema":"OPICA_INTEGRATED_READINESS_V1","status":"READY_FOR_CANDIDATE_REPLAY" if all(r["ready"] for r in rows) else "WAITING_FOR_UPSTREAM_EVIDENCE","producers":rows,"independent_integrated_replay":"NOT_RUN",**CLAIMS}

def build(out):
    before=check()
    need(not out.exists() and not out.is_relative_to(ROOT),"Fresh external output required")
    out.mkdir(parents=True)
    s=load(HERE/"LOCK.json")
    receipt={**before,"status":"INCOMPLETE","stages":[],"independent_full_closure":"NOT_RUN"}
    def command(label,args,timeout=9000,env=None):
        with (out/(label+".log")).open("xb") as log:
            subprocess.run(args,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=timeout,env=env)
    try:
        modules=[x["module"] for x in s["overlays"]+s["existing_native_modules"]]
        command("build",["lake","build",*modules,"Zeta23.RHRC.OpicaComposition.Export"])
        receipt["stages"].append("NATIVE_BUILD_PASS")
        for i,row in enumerate(s["overlays"]):
            command(f"strict_{i}",["lake","env","lean","-DwarningAsError=true",row["path"]],1800)
        receipt["stages"].append("STRICT_SOURCE_PASS")
        roots=s["roots"]
        audit=out/"OPICAIntegratedAudit.lean"
        audit.write_text("\n".join("import "+m for m in modules if not m.endswith(".BipolarVerify"))+"\nimport Zeta23.RHRC.OpicaComposition.Export\nset_option pp.fullNames true\nset_option pp.universes false\n"+"\n".join("#check @"+n+"\n#print axioms "+n+"\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget "+chr(96)+n+' "type"' for n in roots)+"\n")
        command("root_audit",["lake","env","lean","--root="+str(out),"-DwarningAsError=true","-o",str(out/"OPICAIntegratedAudit.olean"),str(audit)])
        log=(out/"root_audit.log").read_text()
        receipt["axioms"]=axiom_reports(log,roots)
        expressions=[json.loads(x.split("\t",1)[1]) for x in log.splitlines() if x.startswith("OPICA_TARGET\t")]
        need(len(expressions)==len(roots),"Missing type DAGs")
        sys.path.insert(0,str(ROOT))
        from research.RHRC.integration.opica_composition.inventory import expression_hash
        save(out/"NATIVE_TYPE_CANDIDATES.json",[{"name":n,"expression":e,"sha256":expression_hash(e)} for n,e in zip(roots,expressions)])
        receipt["stages"].append("NAMED_AXIOMS_AND_TYPE_EXPORT_PASS")
        checker=Path(run("lake","env","lean","--print-prefix"))/"bin"/"leanchecker"
        need(checker.is_file(),"Stock kernel unavailable")
        env=dict(os.environ)
        env["LEAN_PATH"]=str(out)+os.pathsep+run("lake","env","printenv","LEAN_PATH")
        command("stock_fresh",[str(checker),"--fresh","--verbose","OPICAIntegratedAudit"],env=env)
        receipt["stages"].append("FRESH_STOCK_KERNEL_PASS")
        need(check()==before,"Source changed during build")
        receipt["status"]="INTEGRATED_NATIVE_CANDIDATE_PASS_ONLY"
    except BaseException as exc:
        receipt.update(status="INCOMPLETE_OR_REJECTED",failure=str(exc)[:2000])
        raise
    finally:
        save(out/"receipt.json",receipt)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("mode",choices=["source","readiness","build","canonical"])
    ap.add_argument("output",type=Path)
    a=ap.parse_args()
    out=a.output.resolve()
    need(not out.is_relative_to(ROOT),"Evidence must stay outside checkout")
    if a.mode=="source":
        save(out,check())
    elif a.mode=="readiness":
        check()
        save(out,readiness())
    else:
        r=readiness()
        need(r["status"]=="READY_FOR_CANDIDATE_REPLAY","Upstream evidence incomplete")
        if a.mode=="build":
            build(out)
        else:
            before=check()
            sys.path.insert(0,str(ROOT))
            from research.RHRC.integration.opica_next_epoch.scope import canonical_candidate
            canonical_candidate(out,before["head"],before["tree"])

if __name__=="__main__":
    main()
