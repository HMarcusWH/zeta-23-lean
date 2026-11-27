"""Versioned registration-only source boundary. No theorem authority."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from research.RHRC.integration.documentation_2026_11_21 import source_scope as historical
from research.RHRC.integration.opica_round6 import source_scope as round6
from research.RHRC.integration.opica_composition.descendant import validate_workflow_migration

REPO = Path(__file__).resolve().parents[4]
BASE = "bb7c8184a135b2823c6296917c5ac893bebf2a71"
BASE_TREE = "2b19357e1b65cc500f3e3a5b5d4df14601b02062"
POLICY = "research/RHRC/integration/opica_dispatch_registration/SOURCE_POLICY.json"
VALIDATOR = "research/RHRC/integration/opica_dispatch_registration/gate.py"
POLICY_BLOB_OID = "00da1e16a9f3a5bc0c15e225f7459ab992174f51"
ADDED = frozenset([".github/workflows/opica-integrated-release-review.yml",".github/workflows/opica-dispatch-registration-review.yml",".github/workflows/opica-next-acceptance.yml",".github/workflows/opica-next-source-epoch.yml","research/RHRC/integration/opica_dispatch_registration/README.md","research/RHRC/integration/opica_dispatch_registration/SOURCE_POLICY.json","research/RHRC/integration/opica_dispatch_registration/gate.py","research/RHRC/integration/opica_dispatch_registration/test_gate.py"])
EDITED = frozenset([".github/workflows/documentation.yml","research/RHRC/integration/opica_composition/cli.py","research/RHRC/integration/opica_composition/service.py","research/RHRC/integration/opica_composition/tests/test_end_to_end.py"])
FROZEN = frozenset(round6.FROZEN_PRODUCTS)

class Reject(ValueError):
    pass

def need(ok, why):
    if not ok:
        raise Reject(why)

def git(*args, repo=REPO):
    return subprocess.check_output(["git","-C",str(repo),*args],text=True,timeout=180).strip()

def oid(raw):
    return hashlib.sha1(b"blob "+str(len(raw)).encode("ascii")+b"\0"+raw).hexdigest()

def normalized_validator(raw):
    anchor = ('POLICY_BLOB_OID = "'+POLICY_BLOB_OID+'"\n').encode("ascii")
    need(raw.count(anchor)==1,"exact policy anchor required")
    return oid(raw.replace(anchor,b'POLICY_BLOB_OID = "<policy-blob-oid>"\n'))

def validate_delta(parent,current,policy,active,validator_oid):
    need(set(policy)=={"schema","base","base_tree","reviewed_blobs","validator_template_blob_oid","added","edited","proof_acceptance","RH","C1","Step4"}
         and policy["schema"]=="OPICA_DISPATCH_REGISTRATION_SOURCE_V1"
         and policy["base"]==BASE and policy["base_tree"]==BASE_TREE
         and policy["proof_acceptance"] is False
         and all(policy[k]=="OPEN" for k in ("RH","C1","Step4")),"registration policy authority differs")
    need(policy["added"]==sorted(ADDED) and policy["edited"]==sorted(EDITED),"unreviewed path policy")
    need(set(parent)<=set(current) and set(current)-set(parent)==ADDED,"unreviewed addition/deletion")
    changed={p for p in parent if current[p]!=parent[p]}
    need(changed-set(active)==EDITED,"unreviewed parent changes")
    need(FROZEN<=set(parent) and all(current[p]==parent[p] for p in FROZEN),"frozen historical product changed")
    expected=policy["reviewed_blobs"]
    need(set(expected)==(ADDED|EDITED)-{POLICY,VALIDATOR},"incomplete reviewed blob inventory")
    need(all(current.get(p)==("100644","blob",v) and re.fullmatch(r"[0-9a-f]{40}",v) for p,v in expected.items()),"sealed content differs")
    need(current[POLICY]==("100644","blob",POLICY_BLOB_OID) and current[VALIDATOR]==("100644","blob",validator_oid),"policy or validator blob differs")
    need(all(current[p][:2]==("100644","blob") for p in changed),"nonregular source/generated edit")
    return sorted(changed&set(active))

def check(repo=REPO, *, require_clean=True):
    repo=Path(repo).resolve()
    need(git("rev-parse",BASE+"^{tree}",repo=repo)==BASE_TREE,"exact native baseline differs")
    need(git("merge-base",BASE,"HEAD",repo=repo)==BASE,"not a native baseline descendant")
    head=git("rev-parse","HEAD",repo=repo)
    current,parent=round6.tree(repo,head),round6.tree(repo,BASE)
    if require_clean:
        need(not git("status","--porcelain","--untracked-files=all",repo=repo),"dirty checkout")
    raw=(repo/POLICY).read_bytes()
    need(oid(raw)==POLICY_BLOB_OID,"unreviewed policy bytes")
    policy=json.loads(raw)
    source=(repo/VALIDATOR).read_bytes()
    need(normalized_validator(source)==policy["validator_template_blob_oid"],"validator template differs")
    manifest="research/RHRC/integration/opica_round4/BUILD_MANIFEST.json"
    products=[r["path"] for r in json.loads((repo/manifest).read_text())["generated"]]
    active=set(products)-FROZEN
    need(len(products)==len(set(products))==81 and len(active)==77 and len(FROZEN)==4,"exact canonical product boundary differs")
    changed=validate_delta(parent,current,policy,active,oid(source))
    historical.check_worktree(repo,current)
    validate_workflow_migration(repo)
    ignored=git("ls-files","--others","--ignored","--exclude-standard",repo=repo)
    need(not any(p.startswith(("Zeta23/","research/",".github/","docs/examples/")) and p.endswith((".lean",".lean.in",".py",".yml",".yaml")) for p in ignored.splitlines()),"ignored source provider")
    need(head==git("rev-parse","HEAD",repo=repo) and (not require_clean or not git("status","--porcelain","--untracked-files=all",repo=repo)),"checkout changed")
    return {"schema":"OPICA_DISPATCH_REGISTRATION_INSPECTION_V1","status":"PASS_SOURCE_SCOPE_ONLY","checked_commit":head,
            "checked_tree":git("rev-parse","HEAD^{tree}",repo=repo),"base":BASE,"base_tree":BASE_TREE,
            "manifest_sha256":hashlib.sha256((repo/manifest).read_bytes()).hexdigest(),
            "reviewed_blob_count":len(policy["reviewed_blobs"]),"delta":{"added":sorted(ADDED),"edited":sorted(EDITED),"generated":changed,"deleted":[]},
            "canonical_product_count":77,"unchanged_historical_product_count":4,
            "current_compiler_accepted":False,"full_round4_accepted":False,
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}

def validate_descendant(repo=REPO, *, require_clean=False):
    if POLICY in round6.tree(Path(repo),"HEAD"):
        return check(repo,require_clean=require_clean)
    return historical.validate_descendant(repo,require_clean=require_clean)

def check_classification():
    check()
    d=json.loads((REPO/"research/RHRC/graph/FILE_CLASSES.json").read_text())
    for p in sorted(ADDED|EDITED):
        hits=[r for r in d["rules"] if re.fullmatch(r["pattern"],p)]
        need(hits and hits[0]["file_class"]!=d["unknown_class"] and
             hits[0]["trust_zone"]=="AUDIT_ONLY","unclassified or promoted deployment source: "+p)
    return {"status":"PASS_REGISTRATION_CLASSIFICATION_ONLY","proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}

def canonical_candidate(output, checked_head, checked_tree):
    """Regenerate only independently enumerated active products; no source promotion."""
    from research.RHRC.integration.opica_round6.source_scope import FROZEN_PRODUCTS
    output=Path(output).resolve()
    need(not output.is_relative_to(REPO) and not output.exists(),
         "fresh external candidate directory required")
    output.mkdir(parents=True)
    receipt={"schema":"OPICA_CANONICAL_CANDIDATE_V3",
             "status":"INCOMPLETE","source_head":checked_head,
             "source_tree":checked_tree,"proof_acceptance":False,
             "RH":"OPEN","C1":"OPEN","Step4":"OPEN"}
    def persist():
        (output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    def run(command,label,timeout):
        receipt["phase"]=label
        persist()
        with (output/(label+".log")).open("xb") as out:
            subprocess.run(command,cwd=REPO,stdout=out,stderr=subprocess.STDOUT,
                           check=True,timeout=timeout)
    manifest="research/RHRC/integration/opica_round4/BUILD_MANIFEST.json"
    coverage="research/RHRC/graph/generated/REPOSITORY_COVERAGE.json"
    def clean_source():
        need(git("rev-parse","HEAD")==checked_head and
             git("rev-parse","HEAD^{tree}")==checked_tree,
             "candidate source head/tree changed")
    def hashes(paths):
        out={}
        for p in sorted(paths):
            f=REPO/p
            need(f.is_file() and not f.is_symlink(),"missing/nonregular product: "+p)
            out[p]=hashlib.sha256(f.read_bytes()).hexdigest()
        return out
    def changed(active):
        rows=[x.split("\t",1) for x in git("diff","--name-status","--no-renames","HEAD").splitlines()]
        need(all(len(x)==2 and x[0]=="M" and x[1] in active for x in rows),
             "candidate changed source or frozen/generated inventory: "+repr(rows)[:1500])
        need(not git("ls-files","--others","--exclude-standard"),
             "candidate introduced untracked files")
        clean_source()
        return sorted(x[1] for x in rows)
    try:
        clean_source()
        need(not git("status","--porcelain","--untracked-files=all"),
             "candidate must start from clean reviewed source")
        need(git("rev-parse","HEAD:"+manifest)==git("rev-parse",BASE+":"+manifest),
             "original 81-product manifest changed")
        items=json.loads((REPO/manifest).read_text())["generated"]
        all_paths={r["path"] for r in items}
        frozen=set(FROZEN_PRODUCTS)
        active=all_paths-frozen
        need(len(items)==len(all_paths)==81 and len(frozen)==4 and
             frozen<=all_paths and len(active)==77,"canonical 77+4 inventory differs")
        def coverage_matches():
            rows=json.loads((REPO/coverage).read_text())["declared_generated_products"]
            need(len(rows)==77 and set(rows)==active,
                 "generated coverage does not equal immutable active inventory")
        coverage_matches()
        for p in frozen:
            need(git("rev-parse","HEAD:"+p)==git("rev-parse",BASE+":"+p),
                 "frozen historical product Git blob changed: "+p)
        before=hashes(all_paths)
        run(["lake","build","Zeta23.RHRC.DeclarationDependencyExport",
             "Zeta23.RHRC.SourceCandidateResolution"],"compiler-preparation",7200)
        need(not changed(set()) and hashes(all_paths)==before,
             "compiler preparation changed tracked state")
        run([sys.executable,"-B","research/RHRC/tools/materialize_derived_state.py",
             "--write"],"write",10800)
        after_write=hashes(all_paths)
        coverage_matches()
        changed_paths=changed(active)
        need(all(after_write[p]==before[p] for p in frozen),
             "write modified frozen historical products")
        run([sys.executable,"-B","research/RHRC/tools/materialize_derived_state.py",
             "--check"],"check",10800)
        after_check=hashes(all_paths)
        need(after_check==after_write and changed(active)==changed_paths,
             "canonical check changed source or generated bytes")
        coverage_matches()
        need(all(after_check[p]==before[p] for p in frozen),
             "check modified frozen historical products")
        subprocess.run(["git","-C",str(REPO),"diff","--check","HEAD"],check=True)
        patch=subprocess.check_output(["git","-C",str(REPO),"diff","--binary","HEAD"])
        (output/"generated-state.patch").write_bytes(patch)
        receipt.update({"status":"REVIEW_ONLY_GENERATED_STATE","phase":"COMPLETE",
                        "active_count":77,"frozen_count":4,"total_count":81,
                        "before_sha256":before,"after_write_sha256":after_write,
                        "after_check_sha256":after_check,
                        "frozen_git_oids":{p:git("rev-parse",BASE+":"+p) for p in sorted(frozen)},
                        "changed_paths":changed_paths,"changed_count":len(changed_paths),
                        "patch_sha256":hashlib.sha256(patch).hexdigest(),
                        "logs_sha256":{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                                       for p in sorted(output.glob("*.log"))}})
        persist()
        print(json.dumps({k:receipt[k] for k in ("status","source_head","active_count",
                                                 "frozen_count","changed_count","proof_acceptance")}))
        return receipt
    except Exception as exc:
        receipt.update({"status":"INCOMPLETE_NOT_ACCEPTED",
                        "error_type":type(exc).__name__,"error":str(exc)[:1200]})
        persist()
        raise

def main():
    p=argparse.ArgumentParser()
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument("--output",type=Path)
    g.add_argument("--check-classification",action="store_true")
    g.add_argument("--canonical-candidate",type=Path)
    args=p.parse_args()
    if args.check_classification:
        print(json.dumps(check_classification()))
    elif args.canonical_candidate:
        r=check()
        canonical_candidate(args.canonical_candidate,r["checked_commit"],r["checked_tree"])
    else:
        target=args.output.resolve()
        need(not target.exists() and not target.is_relative_to(REPO),"fresh external source receipt required")
        target.parent.mkdir(parents=True,exist_ok=True)
        try:
            result=check()
        except Exception as exc:
            target.write_text(json.dumps({"status":"SOURCE_POLICY_REJECTED","error":str(exc)[:1500],
                "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"},indent=2)+"\n")
            raise
        target.write_text(json.dumps(result,indent=2)+"\n")
        print(json.dumps({k:result[k] for k in ("status","checked_commit","proof_acceptance","RH")}))

if __name__=="__main__":
    main()
