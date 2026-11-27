"""Reconstruct a review-only layout on the existing repository, without updating a branch."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

MAIN = "d4c7fc7114e5f1b61b90ea9037890969358ff0cc"
PAPER = "30b3a430c350eeeef9ff1aa8c99d10cd30dc3fb3"
REGISTRATION = "f92691ef1d0cd8129e0df01cee747e5d70f939f6"
PAPER_POLICY = "b1e57c979ee75cf833c2c6587ff4049dee42a8f3"
DOC = ".github/workflows/documentation.yml"
PKG = "research/RHRC/integration/opica_composition/"
CLI, SERVICE = PKG+"cli.py", PKG+"service.py"
MANIFEST = "research/RHRC/integration/opica_round4/BUILD_MANIFEST.json"
OUTPUT = Path(__file__).resolve().parent

def check(condition,message):
    if not condition:
        raise ValueError(message)

def once(body, before, after):
    check(body.count(before)==1, "Source anchor differs: "+before[:80])
    return body.replace(before, after)

def build(repo):
    env = {**os.environ, "GIT_NO_REPLACE_OBJECTS":"1", "GIT_NO_LAZY_FETCH":"1",
           "GIT_AUTHOR_NAME":"Closure rehearsal","GIT_COMMITTER_NAME":"Closure rehearsal",
           "GIT_AUTHOR_EMAIL":"rehearsal@localhost","GIT_COMMITTER_EMAIL":"rehearsal@localhost",
           "GIT_AUTHOR_DATE":"2026-11-27T15:10:00Z","GIT_COMMITTER_DATE":"2026-11-27T15:10:00Z"}
    def git(*args, data=None):
        return subprocess.check_output(["git","-C",str(repo),*args],input=data,env=env)
    def show(rev,path):
        return git("show",rev+":"+path).decode()
    def inventory(rev):
        result = {}
        for row in git("ls-tree","-r","-z",rev).split(b"\0"):
            if row:
                meta,path=row.split(b"\t",1)
                result[path.decode()]=meta.decode().split()
        return result
    current=inventory(PAPER)
    base=inventory(MAIN)
    manifests=json.loads(show(PAPER, MANIFEST))["generated"]
    check(base[MANIFEST]==current[MANIFEST],"Parent product inventories changed")
    frozen=set(json.loads(show(PAPER,"research/RHRC/integration/opica_round6/SOURCE_SCOPE.json")).get("frozen_products",[]))
    if not frozen:
        predecessor=json.loads(show(PAPER,"research/RHRC/integration/documentation_2026_11_21/SOURCE_SCOPE.json"))
        frozen={x["path"] for x in manifests}-set(predecessor["generated"])
    products={x["path"] for x in manifests}
    active=products-frozen
    check(len(manifests)==len(products)==81 and len(active)==77 and len(frozen)==4,"Product scope")
    check(all(current[p]==base[p] for p in frozen),"Frozen parent products differ")
    merge=subprocess.run(["git","-C",str(repo),"merge-tree","--write-tree","--name-only",MAIN,PAPER],capture_output=True,env=env)
    rows=merge.stdout.decode().split("\n\n",1)[0].splitlines()
    check(merge.returncode==1 and len(rows)==13,"Actual conflict census moved")
    seed=rows[0]
    conflicts=set(rows[1:])
    check(conflicts-active=={DOC,CLI,SERVICE} and len(conflicts&active)==9,"Unexpected conflict scope")
    paper_cli=show(PAPER,CLI)
    # Both reviewed production modules retain their original code. A mixed tree cannot
    # select either one's historical policy by the presence of a file.
    routing=(OUTPUT/"routing.py.inc").read_text()
    cli=once(paper_cli,"from ..documentation_2026_11_26.source_scope import SCHEMA as PAPER_DOCUMENTATION_SCHEMA, validate_descendant",
            "from ..documentation_2026_11_26.source_scope import SCHEMA as PAPER_DOCUMENTATION_SCHEMA")
    cli=once(cli,"def classification_command(source):",routing+"\n\ndef classification_command(source):\n    if source.get('schema') == 'OPICA_DISPATCH_REGISTRATION_INSPECTION_V1':\n        return [sys.executable, '-B', '-m', 'research.RHRC.integration.opica_dispatch_registration.gate', '--check-classification']")
    paper_doc=show(PAPER,DOC)
    main_doc=show(MAIN,DOC)
    start='          python3 -B -m research.RHRC.integration.documentation_2026_11_26.source_scope --check > "$out/source-scope.json"'
    end='      - name: Check reader links'
    paper_commands=paper_doc[paper_doc.index(start):paper_doc.index(end)].rstrip()
    start_main='          if test -f research/RHRC/integration/opica_dispatch_registration/SOURCE_POLICY.json; then'
    old_commands=main_doc[main_doc.index(start_main):main_doc.index(end)].rstrip()
    old_registration,old_legacy=old_commands.split('          else\n')
    old_registration=old_registration.split('\n',1)[1]
    old_legacy=old_legacy.rsplit('\n          fi',1)[0]
    preamble="""          epoch=$(python3 -B -c 'from pathlib import Path; from research.RHRC.integration.opica_composition.cli import documentation_epoch; print(documentation_epoch(Path.cwd()))')
          case "$epoch" in
            paper)
"""
    rejection="""            combined)
              python3 -B -m research.RHRC.integration.opica_composition.cli check-descendant --repo . --output "$out/combined-source.json"
              ;;
            *) exit 2 ;;
          esac
"""
    join=preamble+"\n".join("    "+line for line in paper_commands.splitlines())+"\n              ;;\n            registration)\n"+old_registration+"\n              ;;\n            historical)\n"+old_legacy+"\n              ;;\n"+rejection
    doc=once(paper_doc,paper_commands+"\n",join)
    # The canonical job also uses the production selector, including its mixed-source refusal.
    doc=once(doc,'\n'+start,'\n'+'          python3 -B -m research.RHRC.integration.opica_composition.cli check-descendant --repo . --output "$out/source-scope.json"')
    authored={DOC:doc.encode(),CLI:cli.encode(),SERVICE:show(PAPER,SERVICE).encode()}
    with tempfile.TemporaryDirectory() as td:
        env["GIT_INDEX_FILE"]=str(Path(td)/"index")
        git("read-tree",seed)
        for p in sorted(active):
            mode,kind,obj=current[p]
            check([mode,kind]==["100644","blob"],"Nonregular product "+p)
            git("update-index","--cacheinfo",mode,obj,p)
        for p,raw in authored.items():
            blob=git("hash-object","-w","--stdin",data=raw).decode().strip()
            git("update-index","--cacheinfo","100644",blob,p)
        tree=git("write-tree").decode().strip()
        commit=git("commit-tree",tree,"-p",MAIN,"-p",PAPER,data=b"Review-only registration and paper source reconciliation. Canonical outputs pending.\n").decode().strip()
    result=inventory(commit)
    ancestor=git("merge-base",MAIN,PAPER).decode().strip()
    ancestor_tree=inventory(ancestor)
    for p in (set(ancestor_tree)|set(current)|set(base)|set(result))-set(authored)-active:
        left,right,common=base.get(p),current.get(p),ancestor_tree.get(p)
        check(left==right or left==common or right==common,"Unresolved two-sided authored change: "+p)
        wanted=right if left==common else left
        check(result.get(p)==wanted,"Incorrect inherited path: "+p)
    check(all(result[p]==current[p] for p in products),"Seed product identity differs")
    archive=json.loads(show(PAPER,"research/RHRC/integration/documentation_2026_11_26/ARCHIVE_BYTES.json"))
    pdfs={p:current[p][2] for p,row in archive["added"].items() if row["file_kind"]=="BINARY_PDF"}
    check(len(pdfs)==6 and all(result[p]==current[p] for p in pdfs),"Original PDF mismatch")
    authored_rows={p:row for p,row in result.items() if p not in active}
    projection=hashlib.sha256(json.dumps(authored_rows,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    info={"scope":"Unreviewed two-parent source layout; all 77 product inputs are paper-epoch seeds.",
          "parents":[MAIN,PAPER],"commit":commit,"tree":tree,"tracked":len(result),"non_generated_projection_sha256":projection,
          "canonical_77_regenerated":False,"approved":False,"RH":"OPEN",
          "authored_resolutions":{p:result[p] for p in authored},"generated_conflicts":sorted(conflicts&active),
          "permitted_products":sorted(active),"frozen":{p:current[p][2] for p in sorted(frozen)},"original_pdfs":pdfs}
    (OUTPUT/"layout.json").write_text(json.dumps(info,indent=2)+"\n")
    (OUTPUT/"authored.patch").write_bytes(git("diff","--binary",PAPER,commit,"--",*authored))
    print(commit,tree,len(result),projection)
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("repo",type=Path)
    build(p.parse_args().repo.resolve())
