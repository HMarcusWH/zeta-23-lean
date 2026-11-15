"""SHA256-pinned, real V2 independent numerical replay. NONACCEPTING.
Two distinct clean checkouts are compulsory: the pinned #299 subject at the
original worker path, and a separately checked controller. This script only
tests a fixed historic SOURCE_NUMERICS producer artifact and never promotes RH.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess
from zipfile import ZipFile

FROZEN_HEAD = "df914f38f26bdc4109aeaa13f48b3896c3bc61b1"
FROZEN_TREE = "5fc2aa4793b658c58dd89c1d36b0ceee756d400d"
FROZEN_BLOBS = {
    "research/RHRC/integration/opica_round4/source_evaluator.py":"bf26f9c7771f76505e5c8116287ed89b3c122025",
    "research/RHRC/integration/opica_round4/source_checker.py":"0dcfad9ebf16b342d6f31570ead0e8f69371974e",
    "research/RHRC/integration/opica_round4/source_backend.py":"d4368a9f6b2501f8463210d38668f1b4934495de",
    "research/RHRC/integration/opica_round3/source_backend.py":"48bc049e8ddf5a4a4ac6b1a897f6e437997cdca",
}
PRODUCER_RUN = "43700869719"
PRODUCER_ATTEMPT = 1
PRODUCER_SHA256 = "d38c2eeeab0d14033e93ce9fcb6e370ee19456728fde695687d378af9898beb7"


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git","-C",str(root),*args],
                                   env={**os.environ,"GIT_NO_LAZY_FETCH":"1",
                                        "GIT_TERMINAL_PROMPT":"0"},text=True).strip()


def verify_frozen_subject(root: Path) -> dict:
    # Never infer subject from import location or the mutable controller.
    root=root.resolve(strict=True)
    if (root/"research/RHRC/integration/opica_composition/post299/portable_runtime.py").exists():
        raise RuntimeError("Frozen subject checkout contains post299 controller")
    if git(root,"rev-parse","HEAD") != FROZEN_HEAD or git(root,"rev-parse","HEAD^{tree}") != FROZEN_TREE:
        raise RuntimeError("Subject checkout is not the exact frozen PR299 commit/tree")
    if git(root,"status","--porcelain","--untracked-files=all"):
        raise RuntimeError("Frozen subject checkout is dirty")
    for p, expected in FROZEN_BLOBS.items():
        if git(root,"rev-parse","HEAD:"+p) != expected or git(root,"hash-object","--",p) != expected:
            raise RuntimeError("Frozen subject proof-source blob changed: "+p)
    return {"head":FROZEN_HEAD,"tree":FROZEN_TREE,
            "source_blobs":dict(sorted(FROZEN_BLOBS.items()))}


def _safe_name(p: str, *, directory: bool = False) -> str:
    if not isinstance(p,str) or not p or "\\\\" in p or "\\x00" in p:
        raise RuntimeError("Unsafe artifact filename")
    s=p[:-1] if directory and p.endswith("/") else p
    pure=PurePosixPath(s)
    if pure.is_absolute() or ".." in pure.parts or not pure.parts or str(pure)!=s:
        raise RuntimeError("Noncanonical artifact filename: "+p)
    return s


def unpack_exact_producer(input_dir: Path, output: Path) -> dict:
    if output.exists():
        raise RuntimeError("Refuse to overwrite independent evidence")
    names={p.name for p in input_dir.iterdir()}
    if names != {"bundle.zip","transport.json"}:
        raise RuntimeError("Expected exactly a GitHub SOURCE_NUMERICS transport pair")
    outer=json.loads((input_dir/"transport.json").read_bytes())
    e=outer.get("experiment",{})
    if (outer.get("schema")!="OPICA_EVIDENCE_TRANSPORT_V1"
        or outer.get("lane_id")!="SOURCE_NUMERICS"
        or e.get("run_id")!=PRODUCER_RUN
        or type(e.get("attempt")) is not int or e["attempt"]!=PRODUCER_ATTEMPT
        or e.get("requested_commit")!=FROZEN_HEAD
        or e.get("requested_tree")!=FROZEN_TREE):
        raise RuntimeError("Historical transport run/attempt/source mismatch")
    raw=(input_dir/"bundle.zip").read_bytes()
    digest=hashlib.sha256(raw).hexdigest()
    if (digest!=PRODUCER_SHA256
        or outer.get("container")!={"bytes":len(raw),"sha256":digest}):
        raise RuntimeError("Frozen original SOURCE_NUMERICS container bytes changed")
    manifest=outer["manifest"]
    expected={_safe_name(row["path"]):row for row in manifest["files"]}
    dirs={_safe_name(d, directory=True) for d in manifest["directories"]}
    if len(expected)!=len(manifest["files"]) or len(dirs)!=len(manifest["directories"]):
        raise RuntimeError("Duplicated artifact manifest entries")
    if not {"source-producer/normal/result.json","source-producer/optimized/result.json"} <= set(expected):
        raise RuntimeError("Missing original producer modes")
    output.mkdir(parents=True)
    with ZipFile(input_dir/"bundle.zip") as z:
        infos=z.infolist()
        names=[f.filename for f in infos]
        if len(names)!=len(set(names)):
            raise RuntimeError("Duplicate zip entry")
        file_names={_safe_name(f.filename) for f in infos if not f.is_dir()}
        dir_names={_safe_name(f.filename,directory=True) for f in infos if f.is_dir()}
        if file_names!=set(expected) or dir_names!=dirs:
            raise RuntimeError("ZIP and signed transport manifest inventory differ")
        for info in infos:
            # Refuse Unix symlinks and unsupported special members.
            mode=(info.external_attr >> 16)
            if stat.S_IFMT(mode) not in (0,stat.S_IFREG,stat.S_IFDIR):
                raise RuntimeError("Unexpected ZIP filesystem object")
            if info.is_dir():
                continue
            row=expected[info.filename]
            if info.file_size!=row["bytes"] or info.file_size>5_000_000:
                raise RuntimeError("Oversized or mismatched transport member: "+info.filename)
            value=z.read(info)
            if len(value)!=row["bytes"] or hashlib.sha256(value).hexdigest()!=row["sha256"]:
                raise RuntimeError("Changed evidence member: "+info.filename)
            if info.filename.startswith("source-producer/"):
                target=output/info.filename
                target.parent.mkdir(parents=True,exist_ok=True)
                target.write_bytes(value)
    return {"run_id":PRODUCER_RUN,"attempt":PRODUCER_ATTEMPT,
            "source":FROZEN_HEAD,"source_tree":FROZEN_TREE,
            "container_sha256":digest,"manifest_entries":len(expected)}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--subject",type=Path,required=True)
    parser.add_argument("--artifact",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    subject=args.subject.resolve(strict=True)
    output=args.output.resolve()
    if output.exists() or output.is_relative_to(subject) or output.is_relative_to(Path.cwd().resolve()):
        raise RuntimeError("Independent evidence must be new and external")
    subject_receipt=verify_frozen_subject(subject)
    downloaded=unpack_exact_producer(args.artifact.resolve(strict=True),output)
    # Import only AFTER source identity has been independently authenticated.
    os.environ["OPICA4_V2_SUBJECT_ROOT"]=str(subject)
    from . import source_checker_v2 as verifier
    if verifier.B.REPO.resolve()!=subject or verifier.HERE!=subject/"research/RHRC/integration/opica_round4":
        raise RuntimeError("Controller silently imported a different source checkout")
    result=verifier.verify_evaluator_evidence(
        output/"source-producer",output/"source-direct-independent",
        require_clean=True,expected_head=FROZEN_HEAD,expected_tree=FROZEN_TREE)
    if (result["status"]!="CANDIDATE_V2_RECOMPUTED_FINITE_SOURCE_NOT_RELEASE"
        or result["schema"]!="OPICA4_SOURCE_NUMERICS_LANE_V2_CANDIDATE"
        or result["acceptance_eligible"] is not False
        or result["independently_recomputed_cases"]!=6
        or result["contained_interval_comparisons"]<=0):
        raise RuntimeError("Source replay failed its finite independent candidate contract")
    report={
        "schema":"OPICA4_POST299_REAL_TWO_CHECKOUT_REPLAY_DIAGNOSTIC_V1",
        "authority":"CANDIDATE_ONLY_NOT_ACCEPTANCE",
        "subject":subject_receipt,"original_producer":downloaded,
        "source_independent":result,"RH":"OPEN","Step4":"OPEN",
    }
    (output/"v2-real-source-report.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":result["status"],
        "cases":result["independently_recomputed_cases"],
        "containments":result["contained_interval_comparisons"],
        "authority":"CANDIDATE_ONLY_NOT_ACCEPTANCE","RH":"OPEN","Step4":"OPEN"}))


if __name__=="__main__":
    main()
