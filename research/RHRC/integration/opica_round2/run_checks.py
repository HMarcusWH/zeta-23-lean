"""Explicit Round2 checks: compiler work, source plans and acceptance stay distinct."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid

try:
    from .certificate_io import InvalidCertificate, failure_envelope, load_strict_json
    from . import build_receipt as compiler, controls, dependency_delta, harvest_workflows
    from . import validate_contract as contract
except ImportError:
    from certificate_io import InvalidCertificate, failure_envelope, load_strict_json
    import build_receipt as compiler
    import controls
    import dependency_delta
    import harvest_workflows
    import validate_contract as contract

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise InvalidCertificate("run_checks", message)


def selected_targets(repo: Path, lane: str) -> list[str]:
    workflow = load_strict_json(repo/"research/RHRC/integration/opica_round2/WORKFLOW_CONTRACT.json")
    require(lane in workflow["formal_lane_targets"], "Unknown formal lane")
    targets = workflow["formal_lane_targets"][lane]
    require(type(targets) is list and targets and len(set(targets)) == len(targets)
            and all(type(t) is str and compiler.NAME.fullmatch(t)
                    and t.startswith("Zeta23.OPICARound2.") for t in targets), "Unsafe or duplicate formal target")
    for target in targets:
        require(contract.file_at(repo, target.replace(".", "/")+".lean").is_file(), "Formal target source is absent: "+target)
    return targets


def execute_formal(repo: Path, output: Path, lane: str, lake: str, timeout: int) -> dict:
    targets = selected_targets(repo, lane)
    sources = compiler.source_manifest(repo)
    identity = {"checked_commit": contract.git(repo,"rev-parse","HEAD"),
                "checked_tree": contract.git(repo,"rev-parse","HEAD^{tree}")}
    environment = compiler.validate_environment(repo)
    output.mkdir(parents=True)
    command = compiler.run_command(repo, [lake,"build",*targets],output,"formal-"+lane,identity["checked_tree"],timeout=timeout)
    require(command["returncode"] == 0, "Native formal lane failed; raw logs were preserved")
    require(compiler.source_manifest(repo) == sources, "Source changed while formal lane compiled")
    return {"schema":"OPICA2_NATIVE_LANE_BUILD_V1","status":"PASS_NATIVE_COMPILER_COMMAND_ONLY",
            **identity, **environment,"lane":lane,"targets":targets,"command":command,
            "source_manifest_sha256":compiler.canonical_sha256(sources),
            "object_cache":"EXISTING_PROJECT_AND_PINNED_PACKAGE_OBJECTS_ALLOWED",
            "complete_type_axiom_dependency_export":False,"independent_human_review":"NOT_ESTABLISHED",
            "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}


def execute_generated(repo: Path, output: Path, timeout: int) -> dict:
    manifest=load_strict_json(HERE/"BUILD_MANIFEST.json",8*1024*1024)
    paths=[r["path"] for r in manifest["generated"]]
    require(paths and len(set(paths))==len(paths),"Exact generated product inventory required")
    def snapshot():
        rows=[]
        for relative in paths:
            path=contract.file_at(repo,relative)
            require(path.is_file(),"Generated product missing before check: "+relative)
            rows.append({"path":relative,"bytes":path.stat().st_size,"sha256":contract.digest(path)})
        return rows
    before=snapshot()
    output.mkdir(parents=True)
    tree=contract.git(repo,"rev-parse","HEAD^{tree}")
    command=compiler.run_command(repo,[sys.executable,"-B","research/RHRC/tools/materialize_derived_state.py","--check"],
                                 output,"canonical-generated-check",tree,timeout=timeout)
    after=snapshot()
    require(command["returncode"]==0,"Canonical generated check failed; inputs were inspected before any regeneration")
    require(before==after,"Check-only generated validation changed a product")
    return {"schema":"OPICA2_GENERATED_CHECK_V1","status":"PASS_CANONICAL_CHECK_WITHOUT_REWRITE",
            "before":before,"after":after,"command":command,"full_core_accepted":False,
            "full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}




def execute_ancestry(repo: Path, output: Path, projection: Path, lake: str, timeout: int) -> dict:
    """Actually run frozen original CLIs and separate current76/100 exporters."""
    try:
        from . import capture_ancestor
    except ImportError:
        import capture_ancestor
    before=compiler.source_manifest(repo)
    head,tree=contract.git(repo,"rev-parse","HEAD"),contract.git(repo,"rev-parse","HEAD^{tree}")
    output.mkdir(parents=True)
    capture=capture_ancestor.capture(repo,projection,output/"baseline",populations=("76","100"),lake=lake,timeout=timeout)
    require(capture.get("status")=="LEGACY_RECEIPTS_PRODUCED_NOT_YET_INDEPENDENTLY_REPLAY_VERIFIED",
            "Frozen baseline compiler replay failed or was incomplete")
    paths={"baseline76":output/"baseline/original-76/compiler-receipt.json",
           "baseline100":output/"baseline/original-100/compiler-receipt.json"}
    for population in (76,100):
        target=output/("current"+str(population))
        dependency_delta.produce_current_export(repo,target,population=population,lake=lake,timeout=timeout)
        paths["current"+str(population)]=target/"current-compiler-receipt.json"
    exports=[];inputs=[]
    for role,population,commit,source_tree in (("baseline76",76,contract.FROZEN_COMMIT,contract.FROZEN_TREE),
        ("current76",76,head,tree),("baseline100",100,contract.FROZEN_COMMIT,contract.FROZEN_TREE),("current100",100,head,tree)):
        path=paths[role]
        verify=dependency_delta.verify_legacy if role.startswith("baseline") else dependency_delta.verify_current_export
        exports.append(verify(repo,path,path.parent,population=population,expected_commit=commit,expected_tree=source_tree))
        inputs.append({"role":role,"receipt":path.relative_to(output).as_posix(),"receipt_sha256":contract.digest(path)})
    comparison=dependency_delta.ancestry_report(*exports,current_commit=head,current_tree=tree)
    require(compiler.source_manifest(repo)==before and contract.git(repo,"rev-parse","HEAD")==head,
            "Current source changed during baseline/current ancestry compiler replay")
    return {"schema":"OPICA2_AUTHENTICATED_ANCESTRY_RUN_V1","status":"PASS_EXECUTED_BASELINE_AND_CURRENT_COMPILER_COMPARISON",
            "checked_commit":head,"checked_tree":tree,"inputs":inputs,"comparison":comparison,
            "source_manifest_sha256":compiler.canonical_sha256(before),"fresh_processes_executed_here":True,
            "provider_authenticity_established_here":False,"ancestor_baseline_replay":True,"ancestor_current_compatibility":True,
            "scope":"FROZEN_76_100_BASELINES_AND_CURRENT_SOURCE_BOUND_COMPILER_COMPATIBILITY",
            "full_core_accepted":False,"full_release_accepted":False,"human_review":"NOT_ESTABLISHED","RH":"OPEN","Step4":"OPEN"}


def compose_inputs(repo: Path, args, raw_path: Path, artifacts: Path) -> dict:
    required=(args.clause_evidence,args.control_evidence,args.optimized_control_evidence,args.ancestry_evidence)
    require(all(path is not None for path in required),
            "Composition requires exact clause metadata, both normal/optimized runtime controls and both baseline/current ancestry evidence")
    return compiler.compose_core_evidence(repo,raw_path,artifacts,load_strict_json(args.query_plan,32*1024*1024),
        clause_evidence=args.clause_evidence,control_evidence=args.control_evidence,
        optimized_control_evidence=args.optimized_control_evidence,ancestry_evidence=args.ancestry_evidence)


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check",choices=("contract","formal","controls","ancestry","aggregate","generated","harvest","acceptance"))
    parser.add_argument("--repo",type=Path,default=REPO)
    parser.add_argument("--lane",choices=("causal","filtered","gram","structural"))
    parser.add_argument("--scope",choices=("minimal","full-core"),default="full-core")
    parser.add_argument("--evidence-dir","--output-dir",dest="evidence_dir",type=Path)
    parser.add_argument("--query-plan",type=Path)
    parser.add_argument("--formal-receipt",type=Path)
    parser.add_argument("--formal-artifacts",type=Path)
    parser.add_argument("--ancestor-projection",type=Path)
    parser.add_argument("--clause-evidence",type=Path)
    parser.add_argument("--control-evidence",type=Path)
    parser.add_argument("--optimized-control-evidence",type=Path)
    parser.add_argument("--ancestry-evidence",type=Path)
    parser.add_argument("--classifications",type=Path)
    parser.add_argument("--snapshot",type=Path)
    parser.add_argument("--previous",type=Path)
    parser.add_argument("--snapshot-mode",choices=("in-workflow","post-run"),default="in-workflow")
    parser.add_argument("--lake",default="lake")
    parser.add_argument("--timeout",type=int,default=3600)
    parser.add_argument("--build-mode",choices=("warm","cold"),default="warm")
    for name in ("baseline76","current76","baseline100","current100"):
        parser.add_argument("--"+name,type=Path)
    args=parser.parse_args()
    repo=args.repo.resolve()
    root=args.evidence_dir or (Path(os.environ["OPICA2_OUTPUT_DIR"]) if os.environ.get("OPICA2_OUTPUT_DIR") else
        repo.parent/"opica2-check-evidence"/(datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")+"-"+uuid.uuid4().hex[:8]))
    output=root.resolve()/args.check
    output_existed=output.exists()
    try:
        require(not output.is_relative_to(repo),"Evidence must be external to the source checkout")
        require(not output.exists(),"Refuse to overwrite an earlier check observation")
        require(type(args.timeout) is int and args.timeout>0,"Positive execution timeout required")
        if args.check=="contract":
            output.mkdir(parents=True)
            result=contract.preflight(repo,repo/"research/RHRC/integration/opica_round2",scope=args.scope)
        elif args.check=="formal":
            require(args.lane is not None,"Formal execution needs an explicit lane")
            result=execute_formal(repo,output,args.lane,args.lake,args.timeout)
        elif args.check=="controls":
            output.mkdir(parents=True)
            result=controls.run_controls(registry_path=HERE/"CONTROL_REGISTRY.json",mapping_path=HERE/"PAPER_CROSSWALK.json",
                evidence_dir=output/"runtime",repo=repo,lake=args.lake,timeout=args.timeout)
        elif args.check=="aggregate":
            require(args.query_plan is not None,"Aggregate export needs independently reviewed exact root/query inventory")
            composition_inputs=(args.clause_evidence,args.control_evidence,args.optimized_control_evidence,args.ancestry_evidence)
            require(not any(path is not None for path in composition_inputs) or all(path is not None for path in composition_inputs),
                    "Partial evidence cannot silently produce full-core coverage")
            plan=load_strict_json(args.query_plan,32*1024*1024)
            receipt=compiler.produce_receipt(repo,output,compiler.compiler_plan_data(plan),lake=args.lake,
                build_mode=args.build_mode,timeout=args.timeout)
            if all(path is not None for path in composition_inputs):
                result=compose_inputs(repo,args,output/"compiler-receipt.json",output)
                (output/"composed-receipt.json").write_bytes((json.dumps(result["composed_receipt"],indent=2)+"\n").encode("utf-8"))
                (output/"core-composition.json").write_bytes((json.dumps(result,indent=2)+"\n").encode("utf-8"))
            else:
                result={"status":"PASS_SCOPED_COMPILER_EXPORT","receipt":receipt,
                        "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}
        elif args.check=="generated":
            result=execute_generated(repo,output,args.timeout)
        elif args.check=="ancestry":
            if args.ancestor_projection is not None:
                require(all(getattr(args,name) is None for name in ("baseline76","current76","baseline100","current100")),
                        "Fresh ancestry orchestration cannot mix separately supplied receipts")
                result=execute_ancestry(repo,output,args.ancestor_projection,args.lake,args.timeout)
            else:
                head,tree=contract.git(repo,"rev-parse","HEAD"),contract.git(repo,"rev-parse","HEAD^{tree}")
                inputs=[]
                for name,population,commit,source_tree in (("baseline76",76,contract.FROZEN_COMMIT,contract.FROZEN_TREE),
                    ("current76",76,head,tree),("baseline100",100,contract.FROZEN_COMMIT,contract.FROZEN_TREE),("current100",100,head,tree)):
                    path=getattr(args,name)
                    require(path is not None,"Both exact frozen and current76/100 compiler artifacts are mandatory: "+name)
                    verify=dependency_delta.verify_current_export if name.startswith("current") else dependency_delta.verify_legacy
                    inputs.append(verify(repo,path,path.parent,population=population,expected_commit=commit,expected_tree=source_tree))
                result=dependency_delta.ancestry_report(*inputs,current_commit=head,current_tree=tree)
                output.mkdir(parents=True)
        elif args.check=="harvest":
            require(args.classifications is not None,"Every workflow/job needs reviewed classification and scientific scope")
            head,tree=contract.git(repo,"rev-parse","HEAD"),contract.git(repo,"rev-parse","HEAD^{tree}")
            snapshot=load_strict_json(args.snapshot,64*1024*1024) if args.snapshot else harvest_workflows.collect(
                harvest_workflows.public_json,"HMarcusWH","zeta-23-lean",head)
            rules=load_strict_json(args.classifications)
            result=harvest_workflows.harvest(snapshot,head=head,tree=tree,classifications=rules,
                previous=load_strict_json(args.previous,64*1024*1024) if args.previous else None,
                snapshot_mode=args.snapshot_mode,required_jobs=rules.get("required_jobs"),
                current_run_id=int(os.environ["GITHUB_RUN_ID"]) if os.environ.get("GITHUB_RUN_ID") else None)
            output.mkdir(parents=True)
            (output/"provider-snapshot.json").write_text(json.dumps(snapshot,indent=2)+"\n",encoding="utf-8")
        else:
            require(args.formal_receipt is not None and args.query_plan is not None,
                    "Acceptance requires exact formal artifacts and independently reviewed query plan")
            artifacts=args.formal_artifacts or args.formal_receipt.parent
            composition=compose_inputs(repo,args,args.formal_receipt,artifacts)
            output.mkdir(parents=True)
            composed_path=output/"composed-receipt.json"
            composed_path.write_bytes((json.dumps(composition["composed_receipt"],indent=2)+"\n").encode("utf-8"))
            def reparse(receipt,source):
                return source.resolve()==repo and receipt==composition["composed_receipt"]
            result=contract.acceptance(repo,repo/"research/RHRC/integration/opica_round2",
                                       formal_receipt=composed_path,receipt_verifier=reparse)
            result["composition_sha256"]=compiler.canonical_sha256(composition)
            result["provider_authenticity_established_here"]=False
            result["fresh_compiler_replay"]=False
            (output/"core-composition.json").write_bytes((json.dumps(composition,indent=2)+"\n").encode("utf-8"))
    except (OSError,ValueError,TypeError,KeyError,subprocess.SubprocessError) as exc:
        result=failure_envelope("run_checks_"+args.check,exc)
        if output_existed:
            print(json.dumps(result,indent=2))
            return 1
        if not output.exists():
            output.mkdir(parents=True)
    (output/"result.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"check":args.check,"result":str(output/"result.json"),
        "status":result.get("status",result.get("outcome")),"RH":"OPEN","Step4":"OPEN"}))
    return 0 if result.get("status","").startswith("PASS_") or result.get("schema")=="OPICA2_WORKFLOW_HARVEST_V1" else 1


if __name__=="__main__":
    raise SystemExit(main())
