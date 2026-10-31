"""Real runbook services over frozen sources, native Lean and the journal.

Only the independently supplied ExperimentSpec and committed target registry
choose proof targets, imports and constants. Proposal files cannot supply them.
All runtime products are external; no service writes protected source state.
"""
from __future__ import annotations
import os
from pathlib import Path
from .canonical import require,canonical_bytes,load_bytes,digest,validate_path_inventory
from .contracts import (ExperimentSpec,SnapshotIdentity,StatementInventory,CohortInventory,TargetSpec,
    GrammarProfile,SearchBudget,CompositionProposal,AttemptArtifacts,StatementContract,PER_ATTEMPT_GATES,as_record)
from .snapshot import unlinked,file_hash,check_snapshot,freeze_source_epoch
from .executor import execute_attempt,worker_environment,worker_capability
from .evidence import verify_application
from .inventory import load_statement_inventory,check_membership_coverage
from .proposals import enumerate_candidates

HERE=Path(__file__).resolve().parent
GOLD=["Zeta23.OPICAComposition.cofinal_newborn_packet_calibration",
      "Zeta23.OPICAComposition.cofinal_schur_packet_calibration"]

def _external(repo,path):
    path=unlinked(path).absolute()
    require(not path.is_relative_to(Path(repo).resolve()),"runtime output must be external")
    return path

def _write(repo,path,value):
    path=_external(repo,path);require(not path.exists(),"immutable output already exists")
    path.parent.mkdir(parents=True,exist_ok=True)
    raw=value.to_bytes() if hasattr(value,"to_bytes") else canonical_bytes(value)
    with path.open("xb") as stream: stream.write(raw)
    return path

def _directory(repo,path):
    path=_external(repo,path);require(not path.exists(),"fresh output directory required")
    path.mkdir(parents=True);return path

def _snapshot(repo,value):
    if isinstance(value,(str,Path)): value=load_bytes(unlinked(value).read_bytes())
    snapshot=as_record(value,SnapshotIdentity)
    require(Path(snapshot.repo).resolve()==Path(repo).resolve(),"snapshot belongs to another checkout")
    return check_snapshot(snapshot)

def _profile(repo): return load_bytes((Path(repo)/"research/RHRC/integration/opica_composition/PROFILE.json").read_bytes())

def _registry(repo):
    return load_bytes((Path(repo)/"research/RHRC/integration/opica_composition/PUBLIC_TARGETS.json").read_bytes())

def _target(repo,snapshot,target_id):
    registry=_registry(repo)
    rows=[*registry["calibration"],*registry.get("open",[]),*registry.get("open_research",[]),*registry.get("intermediate",[])]
    matches=[r for r in rows if r["id"]==target_id]
    require(len(matches)==1,"target is not uniquely registered in the frozen evaluator inventory")
    row=matches[0]
    names={"And.intro":"Init.Prelude","Exists.intro":"Init.Core"}
    if target_id in {"D02_D05","D02_D04"}:
        names["Zeta23.OPICARound3.cofinally_both_neutral_negative_of_off_line_zero"]="Zeta23.OPICARound3.CofinalSimultaneousNegative"
        if target_id=="D02_D05": names["Zeta23.OPICARound3.first_simultaneous_newborn_source_witnesses"]="Zeta23.OPICARound3.NewbornSource"
        else: names["Zeta23.OPICARound3.first_simultaneous_neutral_negative_cutoff"]="Zeta23.OPICARound3.FirstSimultaneousNegative"
    else:
        # OPEN targets begin with their explicitly reviewed finite menu; an
        # empty menu gives NO_MATCH_IN_GRAMMAR, never an assumed source bound.
        names={}
        for item in row.get("approved_constants",[]):
            require(set(item)=={"declaration","module"},"closed evaluator constant entry required")
            require(item["declaration"] not in names,"duplicate approved declaration")
            names[item["declaration"]]=item["module"]
    constants={};table=[]
    for name,module in sorted(names.items()):
        cid=digest({"source_generation":snapshot.generation,"declaration":name,"module":module},domain="OPICA_APPROVED_CONSTANT_V1")
        constants[cid]=name;table.append({"id":cid,"declaration":name,"module":module,"role":"constant"})
    forbidden=GOLD+[n if "." in n else "Zeta23.OPICAComposition."+n for n in row.get("forbidden_gold",[])]
    target=TargetSpec(target_id,row["declaration"],row["module"],row["expected_type_sha256"],constants,
        ["propext","Classical.choice","Quot.sound"],[row["module"]],list(PER_ATTEMPT_GATES),row.get("target_kind","value"),sorted(set(forbidden)))
    return target,table

def _search_contract(repo,target):
    """Source-bound compiler DAGs guide retrieval, never confer acceptance."""
    from .inventory import expression_hash
    path=Path(repo)/'research/RHRC/integration/opica_composition/SEARCH_CONTRACTS.json'
    if not path.exists():
        return None
    doc=load_bytes(path.read_bytes())
    require(doc['schema']=='OPICA4_SEARCH_CONTRACTS_V1' and doc['kernel_acceptance'] is False,
            'retrieval registry authority differs')
    rows=[row for row in doc['targets'] if row['target_id']==target.target_id]
    require(len(rows)<=1,'duplicate retrieval target')
    if not rows:
        return None
    row=rows[0]
    require(expression_hash(row['expected_expression'])==target.expected_type_hash,
            'retrieval target is not the independent expected type')
    allowed=set(target.allowed_constants.values())
    statements=[x for x in doc['statements'] if x['declaration'] in allowed]
    require(len({x['declaration'] for x in statements})==len(statements),'duplicate retrieval statement')
    for item in [row,*statements]:
        require(file_hash(Path(repo)/item['source_path'])==item['source_sha256'],
                'retrieval contract source is stale')
    return {'expected_expression':row['expected_expression'],'statements':statements,'proof_constants':row['proof_constants']}

def freeze(repo,experiment,output,*,worker):
    """Freeze only an independently reviewed complete source/worker profile."""
    from .descendant import validate_descendant
    from .config import check_configuration
    from .qualification import _packages
    repo=unlinked(repo).resolve();worker_capability(worker)
    require(worker.production is True,"production Linux worker required for a production source freeze")
    validate_descendant(repo,require_clean=True);check_configuration(repo);_packages(repo)
    if isinstance(experiment,(str,Path)): experiment=load_bytes(unlinked(experiment).read_bytes())
    approved=as_record(experiment,ExperimentSpec)
    require(approved.source_policy=="REVIEWED_FROZEN","independently reviewed source policy required")
    require(approved.profile_id==_profile(repo)["profile_id"],"approved profile differs from frozen host profile")
    require(approved.environment.get("worker_environment")==worker_environment(worker),"approved compiler/import-object environment differs")
    snapshot=freeze_source_epoch(repo,approved)
    _write(repo,output,snapshot);return snapshot

def inventory(repo,snapshot,output,*,worker):
    from .qualification import check_current_compatibility,frozen_atlas
    snapshot=_snapshot(repo,snapshot);output=_directory(repo,output)
    require(worker.production is True,"production native inventory required")
    native=check_current_compatibility(Path(repo),output/"compiler",worker)
    require(native["status"]=="PASS_CURRENT_COMPATIBILITY","complete actual native inventory did not pass")
    result=load_statement_inventory(snapshot,Path(native["native_export_path"]))
    expected=frozen_atlas(Path(repo));membership={r["declaration"]:[{"cohort":m["cohort"],"root_id":m["identity"],"declaration":r["declaration"]}
        for m in r["memberships"]] for r in expected}
    statements=[]
    for row in result.statements:
        require(row["declaration"] in membership,"unexpected compiler declaration")
        statements.append({**row,"memberships":membership[row["declaration"]]})
    result=StatementInventory(snapshot.generation,statements,result.native_export_sha256)
    cohort=CohortInventory(sorted(membership),[m for rows in membership.values() for m in rows])
    coverage=check_membership_coverage(result,cohort);require(coverage.complete,"exact source/cohort membership coverage failed")
    check_snapshot(snapshot)
    _write(repo,output/"inventory.json",result);_write(repo,output/"coverage.json",coverage)
    return result

def _load_inventory(snapshot,path):
    result=StatementInventory.from_bytes(unlinked(path).read_bytes())
    require(result.snapshot_digest==snapshot.generation,"inventory belongs to another mathematical generation")
    from .qualification import frozen_atlas
    expected={r["declaration"]:r for r in frozen_atlas(Path(snapshot.repo))}
    require(len(result.statements)==len(expected) and {r["declaration"] for r in result.statements}==set(expected),"complete frozen declaration inventory differs")
    for row in result.statements:
        contract=StatementContract.from_dict({k:v for k,v in row.items() if k!="memberships"})
        original=expected[contract.declaration]
        require(contract.type_sha256==original["type_sha256"] and contract.module==original["module"] and
                contract.axioms==original["statement"]["axioms"],"inventory changed the frozen full contract")
        members=[{"cohort":m["cohort"],"root_id":m["identity"],"declaration":contract.declaration} for m in original["memberships"]]
        require(row.get("memberships")==members,"cohort membership was dropped or replaced")
    return result

def plan(repo,snapshot,inventory_file,target_id,output,*,budget=None):
    snapshot=_snapshot(repo,snapshot);table_inventory=_load_inventory(snapshot,inventory_file)
    target,constants=_target(repo,snapshot,target_id);budget=budget or SearchBudget()
    grammar=GrammarProfile(GOLD,[])
    candidates=enumerate_candidates(table_inventory,target,grammar,budget,search_contract=_search_contract(repo,target))
    output=_directory(repo,output)
    proposals={r["action_id"]:CompositionProposal(r["action_id"],target_id,snapshot.generation,r["term_plan"]).to_dict() for r in candidates.candidates}
    row={"schema":"OPICA_SERVICE_PLAN_V1","source_generation":snapshot.generation,"snapshot_digest":snapshot.digest,
         "target_id":target_id,"target":target.to_dict(),"constant_table":constants,"budget":budget.to_dict(),
         "inventory_digest":table_inventory.digest,"candidates":candidates.to_dict(),"proposals":proposals}
    _write(repo,output/"inventory.json",table_inventory);_write(repo,output/"plan.json",row)
    return row

def _journal_snapshot(path): return Path(path).with_name(Path(path).name+".snapshot.json")

def run_one(repo,snapshot,proposals,journal,output,*,worker,budget=1):
    from .journal import Journal,publish_verified_application
    from research.RHRC.permansson.opica_composition import Action
    from research.RHRC.ffbbp.opica_composition import build_falsifier_requirements
    from research.RHRC.ool.opica_composition import verify_interfaces
    from .applications import application_from_publication
    snapshot=_snapshot(repo,snapshot);require(worker.production is True,"isolated production worker required")
    folder=unlinked(proposals);folder=folder.parent if folder.is_file() else folder
    supplied=load_bytes((folder/"plan.json").read_bytes())
    require(set(supplied)=={"schema","source_generation","snapshot_digest","target_id","target","constant_table","budget","inventory_digest","candidates","proposals"}
            and supplied["schema"]=="OPICA_SERVICE_PLAN_V1","closed service plan required")
    require(supplied["source_generation"]==snapshot.generation and supplied["snapshot_digest"]==snapshot.digest,"stale plan epoch")
    target,table=_target(repo,snapshot,supplied["target_id"])
    require(supplied["target"]==target.to_dict() and supplied["constant_table"]==table,"candidate attempted to replace target/import/constant policy")
    inv=_load_inventory(snapshot,folder/"inventory.json");search=SearchBudget.from_dict(supplied["budget"])
    require(search==SearchBudget(**(worker.budget or {})),"planner/worker resource profile differs")
    candidates=enumerate_candidates(inv,target,GrammarProfile(GOLD,[]),search,search_contract=_search_contract(repo,target))
    require(supplied["inventory_digest"]==inv.digest and supplied["candidates"]==candidates.to_dict(),"menu/inventory reconstruction differs")
    wanted={r["action_id"]:CompositionProposal(r["action_id"],target.target_id,snapshot.generation,r["term_plan"]) for r in candidates.candidates}
    require(supplied["proposals"]=={k:v.to_dict() for k,v in wanted.items()},"proposal/menu substitution")
    require(type(budget)is int and 0<=budget<=10000,"bounded host dispatch budget required")
    falsifiers=build_falsifier_requirements({"source":"ACTUAL_CANONICAL","target":target.target_id,
        "newborn":target.target_id=="D02_D05","shell_unit":True,"witness_nonzero":True})
    output=_directory(repo,output);journal=_external(repo,journal)
    native=os.environ.get("OPICA_NATIVE_OUTPUT");require(native and journal.parent.is_relative_to(unlinked(native).resolve()),"journal/check output must be on the provisioned bounded native volume")
    with Journal(journal,repository=Path(repo)) as log:
        state=log.state();profile=file_hash(Path(repo)/"research/RHRC/integration/opica_composition/PROFILE.json")
        anchor=_journal_snapshot(journal)
        if state["generation"] is None:
            require(not anchor.exists(),"journal source anchor exists without a current generation")
            _write(repo,anchor,snapshot)
            log.activate(snapshot.generation,snapshot.source_digest,profile,expected_revision=state["revision"])
        else:
            require(state["generation"]==snapshot.generation and state["source"]==snapshot.source_digest and state["profile"]==profile,"journal world differs; explicit invalidation required")
            require(SnapshotIdentity.from_bytes(anchor.read_bytes()).digest==snapshot.digest,"journal source anchor differs")
        actions=[Action(r["action_id"],snapshot.source_digest,1 if r.get("scientific_scope")=="KNOWN_ENDPOINT_CALIBRATION" else 0,1) for r in candidates.candidates]
        menu=log.db.execute("SELECT body FROM menus WHERE generation=?",(snapshot.generation,)).fetchone()
        if menu is None:log.freeze_menu(actions,frozenset(wanted),generation=snapshot.generation,source=snapshot.source_digest,expected_revision=log.state()["revision"])
        else:
            actual=load_bytes(menu[0]);expected={"actions":[{"action_id":a.action_id,"source":a.source,"priority":a.priority,"cost":a.cost} for a in sorted(actions,key=lambda a:a.action_id)],"eligible_ids":sorted(wanted)}
            require(actual==expected,"menu changed within a source generation")
        choice=log.dispatch({k:v.digest for k,v in wanted.items()},budget,generation=snapshot.generation,source=snapshot.source_digest,expected_revision=log.state()["revision"])
        if choice["kind"]=="STOP": result={"schema":"OPICA_SERVICE_ITERATION_V1",**choice,"RH":"OPEN","Step4":"OPEN"}
        else:
            attempt=execute_attempt(wanted[choice["action_id"]],target,snapshot,output/"producer",worker=worker,constant_table=table)
            if attempt.status=="PROVED_CONDITIONAL":
                event=publish_verified_application(log,choice["attempt_id"],attempt,snapshot,target,worker=worker,
                    generation=snapshot.generation,source=snapshot.source_digest,expected_revision=choice["revision"])
                application=application_from_publication(log,choice["attempt_id"])
                packets=[(key,obj) for key,obj in application["witness_bindings"].items() if obj["object_kind"]=="DEPENDENT_PROOF_PACKET"]
                require(len(packets)==1,"independent native proof packet missing")
                packet_id,packet=packets[0]
                wanted_port={"id":"frozen-target-packet","source":snapshot.source_digest,"context":packet["context_digest"],
                    "producer":packet_id,"consumer":packet_id,"witness":packet_id,"phase":"CONFIRMATORY_FROZEN"}
                observed={**wanted_port,"observed_phase":"CONFIRMATORY_FROZEN","receipt":application["proof_evidence"],"transport":None}
                verify_interfaces([wanted_port],[observed],lambda req,row:row["witness"] in application["witness_bindings"] and
                    application["source_generation"]==snapshot.generation and application["target_digest"]==target.digest and
                    row["receipt"]==application["proof_evidence"])
            else:event=log.record_outcome(choice["attempt_id"],attempt.status,{"reason":attempt.reason,"receipt":str(output/"producer/receipt.json")},
                generation=snapshot.generation,source=snapshot.source_digest,expected_revision=choice["revision"])
            result={"schema":"OPICA_SERVICE_ITERATION_V1","status":attempt.status,"choice":choice,"event":event,"receipt":str(output/"producer/receipt.json"),
                    "falsifier_requirements":list(falsifiers),"RH":"OPEN","Step4":"OPEN"}
    _write(repo,output/"iteration.json",result);return result

def verify(repo,snapshot,receipt,output,*,worker):
    snapshot=_snapshot(repo,snapshot);receipt=unlinked(receipt)
    artifacts=AttemptArtifacts.from_bytes(receipt.read_bytes())
    supplied=TargetSpec.from_bytes((Path(artifacts.output)/"target.json").read_bytes())
    expected,_=_target(repo,snapshot,supplied.target_id)
    require(supplied.to_dict()==expected.to_dict(),"receipt changed the independently registered target policy")
    return verify_application(artifacts,expected,snapshot,_external(repo,output),worker=worker)

def replay(repo,journal,output):
    from .journal import Journal
    anchor=_journal_snapshot(_external(repo,journal));snapshot=_snapshot(repo,anchor)
    output=_directory(repo,output)
    with Journal(journal,repository=Path(repo)) as log:
        state=log.verify_chain()
        require(state["generation"]==snapshot.generation and state["source"]==snapshot.source_digest,"journal active source differs")
        (output/"EVENTS.jsonl").write_bytes(log.export_events())
        result={"schema":"OPICA_SERVICE_REPLAY_V1","status":"JOURNAL_CHAIN_RECONSTRUCTED","state":state,"RH":"OPEN","Step4":"OPEN"}
    _write(repo,output/"replay.json",result);return result

def export(repo,journal,output):
    from .journal import Journal
    from .views import export_state
    snapshot=_snapshot(repo,_journal_snapshot(_external(repo,journal)))
    output=_directory(repo,output)
    with Journal(journal,repository=Path(repo)) as log:
        state=log.verify_chain();require(state["generation"]==snapshot.generation and state["source"]==snapshot.source_digest,"stale current view export")
        products=export_state(log);validate_path_inventory(products)
        for name,raw in products.items():(output/name).write_bytes(raw)
    return {"schema":"OPICA_SERVICE_EXPORT_V1","artifacts":{name:file_hash(output/name) for name in products},"RH":"OPEN","Step4":"OPEN"}
