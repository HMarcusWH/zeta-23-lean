"""Independent replay, not producer receipt authentication by serialization."""
from __future__ import annotations
from pathlib import Path
from dataclasses import replace
from .canonical import require, load_bytes, canonical_bytes, digest, validate_path_inventory, ContractError
import subprocess
from .contracts import (AttemptArtifacts, CompositionProposal, TargetSpec, VerifiedApplication,
                        SearchBudget, ObjectBinding, as_record)
from .snapshot import file_hash, unlinked, check_snapshot
from .executor import execute_attempt, generate_source, generate_consumer, run_worker, parse_native, worker_environment, validate_output_inventory, worker_failure_reason
from .inventory import expression_hash

def validate_artifact_manifest(artifacts):
    artifacts=as_record(artifacts,AttemptArtifacts)
    paths=validate_path_inventory(artifacts.manifest)
    root=unlinked(artifacts.output)
    validate_output_inventory(root)
    actual={p.name for p in root.iterdir() if p.is_file() and p.name!="receipt.json"}
    require(actual==set(paths),"artifact inventory differs")
    for path in paths: require(file_hash(root/path)==artifacts.manifest[path],"artifact bytes differ: "+path)
    return root

def verify_application(artifacts,target,snapshot,check_output,*,worker=None):
    artifacts=as_record(artifacts,AttemptArtifacts); target=as_record(target,TargetSpec)
    snapshot=check_snapshot(snapshot)
    require(artifacts.target_digest==target.digest and artifacts.snapshot_digest==snapshot.digest,
            "receipt source/target substitution")
    root=validate_artifact_manifest(artifacts)
    require(artifacts.status=="PROVED_CONDITIONAL","producer did not establish an application")
    proposal=CompositionProposal.from_dict(load_bytes((root/"proposal.json").read_bytes()))
    require(proposal.digest==artifacts.proposal_digest,"proposal digest differs")
    require(load_bytes((root/"target.json").read_bytes())==target.to_dict(),"producer target differs")
    require(load_bytes((root/"snapshot.json").read_bytes())==snapshot.to_dict(),"producer snapshot differs")
    table=load_bytes((root/"constant-table.json").read_bytes())
    require((root/"OpicaAttempt.lean").read_text(encoding="utf-8")==generate_source(proposal,target,table),
            "producer used a different checker recipe")
    producer=parse_native(root/"OpicaAttempt.lean.log","OPICA_NATIVE")
    require(artifacts.native.get("exit_code")==0,"producer exit not successful")
    require(expression_hash(producer["type_expression"])==target.expected_type_hash,"producer target differs")
    # A fresh process re-elaborates the restricted plan; it never imports an
    # untrusted producer object. A second fresh process then imports its object.
    replay=execute_attempt(proposal,target,snapshot,check_output,worker=worker,constant_table=table)
    if replay.status!="PROVED_CONDITIONAL":
        return VerifiedApplication(replay.status,target.digest,snapshot.digest,proposal.digest,
            replay.digest,snapshot.generation,[],[],[],{"replay":replay.to_dict()},False)
    check=Path(check_output)
    (check/"OpicaConsumer.lean").write_text(generate_consumer(target),encoding="utf-8",newline="\n")
    budget=SearchBudget(**(worker.budget or {}))
    if worker.production:
        before=worker_environment(worker)
        require(before==snapshot.environment["worker_environment"],"independent consumer import inputs changed")
        (check/"consumer-imports-before-summary.json").write_bytes(canonical_bytes(before))
    try:
        consumer=run_worker(worker,check,"OpicaConsumer.lean","OpicaConsumer.olean",budget)
    except (ContractError,OSError,subprocess.SubprocessError) as exc:
        return VerifiedApplication("ENVIRONMENT_ERROR",target.digest,snapshot.digest,proposal.digest,replay.digest,
            snapshot.generation,[],[],[],{"replay":replay.to_dict(),"consumer_error":str(exc)},False)
    check_snapshot(snapshot)
    if worker.production:
        after=worker_environment(worker)
        (check/"consumer-imports-after-summary.json").write_bytes(canonical_bytes(after))
        require(after==snapshot.environment["worker_environment"],"independent consumer import inputs changed during check")
    if consumer["resource_status"] or consumer["exit_code"]!=0:
        status="RESOURCE_EXHAUSTED" if consumer["resource_status"] else "ENVIRONMENT_ERROR"
        return VerifiedApplication(status,target.digest,snapshot.digest,proposal.digest,replay.digest,
            snapshot.generation,[],[],[],{"replay":replay.to_dict(),"consumer":consumer,
                "reason":worker_failure_reason(consumer)},False)
    row=parse_native(check/"OpicaConsumer.lean.log","OPICA_INDEPENDENT")
    validate_output_inventory(check)
    require(expression_hash(row["type_expression"])==target.expected_type_hash,"independent target changed")
    require(set(row["axioms"])<=set(target.allowed_axioms),"unapproved independently replayed axiom")
    require(not(set(row["constants"])&set(target.forbidden_constants or [])),"hidden answer dependency")
    require((check/"OpicaConsumer.olean").is_file(),"independent consumer object absent")
    replay=replace(replay,manifest={p.name:file_hash(p) for p in check.iterdir() if p.is_file() and p.name!="receipt.json"})
    (check/"receipt.json").write_bytes(canonical_bytes(replay.to_dict()))
    evidence={p.name:file_hash(p) for p in check.iterdir() if p.is_file()}
    gate_refs={
        "SOURCE":[evidence["snapshot.json"]],
        "KERNEL":[evidence["OpicaAttempt.olean"],evidence["OpicaConsumer.olean"]],
        "AXIOMS":[evidence["OpicaAttempt.lean.log"],evidence["OpicaConsumer.lean.log"]],
        "INDEPENDENT_EXPECTED_TYPE":[evidence["target.json"],evidence["OpicaConsumer.lean"],evidence["OpicaConsumer.lean.log"]]}
    gates=[{"gate_id":name,"status":"PASS","checker_id":"OPICA_NATIVE_REPLAY_V1",
            "source_generation":snapshot.generation,"evidence_refs":gate_refs[name]} for name in target.required_gates]
    eligible=(worker.production and snapshot.source_policy=="REVIEWED_FROZEN" and
              consumer["capability"]=="LINUX_ISOLATED")
    objects=[]
    for obj in row["object_bindings"]:
        context=row["context"][:obj["scope_index"]]
        context_digest=digest(context,domain="OPICA_ORDERED_OBJECT_CONTEXT_V1")
        objects.append(ObjectBinding(snapshot.source_digest,context_digest,obj["scope_index"],obj["object_kind"],
            obj["term_expression"],obj["type_expression"],context).to_dict())
    result=VerifiedApplication("PROVED_CONDITIONAL",target.digest,snapshot.digest,proposal.digest,
        digest(evidence,domain="OPICA_INDEPENDENT_EVIDENCE_V1"),snapshot.generation,row["axioms"],
        row["constants"],row["context"],{"output":str(check),"manifest":evidence,
         "replay":replay.to_dict(),"consumer":consumer,"required_gates":target.required_gates,"gate_evidence":gates},eligible,objects)
    # Keep this envelope outside the imported proof directory, avoiding a
    # self-referential artifact manifest and preserving replayability.
    (check.parent/(check.name+"-verified-application.json")).write_bytes(canonical_bytes(result.to_dict()))
    return result

def replay_verified_application(verified,target,snapshot,check_output,*,worker):
    """Publication must call this trusted replay, never trust a Python class flag."""
    verified=as_record(verified,VerifiedApplication)
    replay=AttemptArtifacts.from_dict(verified.independent_replay["replay"])
    return verify_application(replay,target,snapshot,check_output,worker=worker)
