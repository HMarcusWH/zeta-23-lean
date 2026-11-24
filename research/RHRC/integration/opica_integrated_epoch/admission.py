"""Versioned integrated source admission; never a theorem/release receipt."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from ..opica_round6.source_scope import tree, FROZEN_PRODUCTS
from ..documentation_2026_11_21.source_scope import check_worktree
from ..opica_composition.descendant import validate_workflow_migration
from ..opica_composition.canonical import require

REPO=Path(__file__).resolve().parents[4]
BASE="885030b709544a645ecfcffdce8a7f649e81a857"
TREE="5dae1d77647921c91a53b04e6fc28887c20464dc"
DIR="research/RHRC/integration/opica_integrated_epoch/"
SEAL=DIR+"SOURCE_SEAL.json"
VALIDATOR=DIR+"admission.py"
SEAL_OID="1d8f603415bf62137e92a11fb8c90f15d06ab764"
MANIFEST="research/RHRC/integration/opica_round4/BUILD_MANIFEST.json"
FC="research/RHRC/graph/FILE_CLASSES.json"
CLAIMS={"RH":"OPEN","C1":"OPEN","Step4":"OPEN","proof_acceptance":False}

def git(repo,*args):
    return subprocess.check_output(["git","-C",str(repo),*args],text=True,timeout=180).strip()

def oid(raw):
    return hashlib.sha1(b"blob "+str(len(raw)).encode("ascii")+b"\0"+raw).hexdigest()

def template_oid(raw):
    anchor=('SEAL_OID="'+SEAL_OID+'"\n').encode("ascii")
    require(raw.count(anchor)==1,"Exact integrated validator anchor required")
    return oid(raw.replace(anchor,b'SEAL_OID="<SEAL_OID>"\n',1))

def active_products(repo,baseline,current):
    require(current[MANIFEST]==baseline[MANIFEST],"Frozen generated manifest changed")
    products=[x["path"] for x in json.loads((repo/MANIFEST).read_text())["generated"]]
    require(len(products)==len(set(products))==81 and len(FROZEN_PRODUCTS)==4 and FROZEN_PRODUCTS<=set(products),"Exact 81/77/4 product population")
    require(all(baseline[p]==current[p] for p in FROZEN_PRODUCTS),"Frozen historical product changed")
    return set(products)-set(FROZEN_PRODUCTS)

def verify_delta(baseline,current,policy,seal_oid,validator_oid,active):
    require(set(baseline)<=set(current),"Integrated predecessor path removed")
    delta={p:v for p,v in current.items() if baseline.get(p)!=v}
    generated={p:v for p,v in delta.items() if p in active}
    require(all(p in baseline and v[:2]==baseline[p][:2]==("100644","blob") for p,v in generated.items()),"Invalid generated delta")
    wanted={p:("100644","blob",v) for p,v in policy["reviewed"].items()}
    wanted.update({SEAL:("100644","blob",seal_oid),VALIDATOR:("100644","blob",validator_oid)})
    require({p:v for p,v in delta.items() if p not in active}==wanted,"Unreviewed integrated source delta")
    return sorted(generated)

def source_fingerprint(current,active):
    payload=json.dumps({p:v for p,v in current.items() if p not in active},sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()
    return hashlib.sha256(payload).hexdigest()

def check(repo=REPO,*,require_clean=False):
    repo=Path(repo).resolve()
    head=git(repo,"rev-parse","HEAD")
    require(git(repo,"rev-parse",BASE+"^{tree}")==TREE and git(repo,"merge-base",BASE,head)==BASE,"Wrong integrated source ancestry")
    baseline,current=tree(repo,BASE),tree(repo,head)
    raw=(repo/SEAL).read_bytes()
    s=json.loads(raw)
    require(set(s)=={"schema","base","tree","reviewed","validator_template_oid",*CLAIMS} and s["schema"]=="OPICA_INTEGRATED_ADMISSION_POLICY_V1" and s["base"]==BASE and s["tree"]==TREE and all(s[k]==v for k,v in CLAIMS.items()),"Integrated policy authority differs")
    require(oid(raw)==SEAL_OID,"Integrated source seal differs")
    validator=(repo/VALIDATOR).read_bytes()
    require(template_oid(validator)==s["validator_template_oid"],"Integrated validator template differs")
    require(all(re.fullmatch(r"[0-9a-f]{40}",v) for v in s["reviewed"].values()),"Bad reviewed blob")
    active=active_products(repo,baseline,current)
    changed=verify_delta(baseline,current,s,SEAL_OID,oid(validator),active)
    require(not git(repo,"status","--porcelain","--untracked-files=all"),"Integrated source checkout dirty")
    check_worktree(repo,current)
    validate_workflow_migration(repo)
    ignored=git(repo,"ls-files","--others","--ignored","--exclude-standard").splitlines()
    require(not any(p.startswith(("Zeta23/","research/",".github/","docs/examples/")) and p.endswith((".lean",".lean.in",".py",".yml",".yaml",".toml")) for p in ignored),"Ignored source provider")
    require(git(repo,"rev-parse","HEAD")==head,"Integrated head changed")
    return {"schema":"OPICA_INTEGRATED_SOURCE_ADMISSION_V1","status":"PASS_SOURCE_SCOPE_ONLY",
      "checked_commit":head,"checked_tree":git(repo,"rev-parse","HEAD^{tree}"),
      "base":BASE,"base_tree":TREE,"source_fingerprint":source_fingerprint(current,active),
      "source_policy_sha256":hashlib.sha256(raw).hexdigest(),
      "manifest_sha256":hashlib.sha256((repo/MANIFEST).read_bytes()).hexdigest(),
      "delta":{"added":sorted(set(current)-set(baseline)),
        "edited":sorted(p for p in baseline if baseline[p]!=current[p] and p not in active),
        "generated":changed,"deleted":[]},
      "canonical_product_count":77,"unchanged_historical_product_count":4,
      "current_compiler_accepted":False,"full_round4_accepted":False,
      "successor_human_review":"PENDING",**CLAIMS}

def validate_descendant(repo=REPO,*,require_clean=False):
    repo=Path(repo).resolve()
    if SEAL in tree(repo,"HEAD"):
        return check(repo,require_clean=require_clean)
    from ..opica_next_acceptance import gate
    return gate.validate_descendant(repo,require_clean=require_clean)

def check_classification(repo=REPO):
    repo=Path(repo).resolve()
    receipt=check(repo,require_clean=True)
    lock=json.loads((repo/(DIR+"LOCK.json")).read_text())
    d=json.loads((repo/FC).read_text())
    paths={r["path"] for r in lock["overlays"]}|set(receipt["delta"]["added"])
    for p in paths:
        rows=[r for r in d["rules"] if re.fullmatch(r["pattern"],p)]
        require(rows and rows[0]["file_class"]!=d["unknown_class"] and rows[0]["trust_zone"]!=d["unknown_trust_zone"],"Unknown integrated path: "+p)
    return {"status":"PASS_INTEGRATED_CLASSIFICATION_ONLY","head":receipt["checked_commit"],**CLAIMS}

def main():
    p=argparse.ArgumentParser()
    a=p.add_mutually_exclusive_group(required=True)
    a.add_argument("--output",type=Path)
    a.add_argument("--check-classification",action="store_true")
    args=p.parse_args()
    if args.check_classification:
        print(json.dumps(check_classification()))
    else:
        out=args.output.resolve()
        require(not out.is_relative_to(REPO) and not out.exists(),"Fresh external admission output required")
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(json.dumps(check(),indent=2)+"\n")

if __name__=="__main__":
    main()
