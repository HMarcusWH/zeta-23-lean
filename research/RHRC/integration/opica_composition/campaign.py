"""Bounded real proof attempts across the three framework interfaces."""
from __future__ import annotations
from pathlib import Path
import uuid
from .canonical import require, digest, canonical_bytes
from .contracts import CompositionProposal
from .executor import execute_attempt
from .journal import Journal, publish_verified_application
from .applications import application_from_publication
from research.RHRC.ffbbp.opica_composition import build_falsifier_requirements
from research.RHRC.ool.opica_composition import verify_interfaces
from research.RHRC.permansson.opica_composition import Action

def run_bounded_campaign(*, snapshot, targets: dict, proposals: dict, constant_tables: dict,
                         output: Path, worker, budget: int, priorities: dict,
                         complete_menu: bool = True) -> dict:
    require(type(budget) is int and budget >= 0, "bounded integer budget required")
    require(complete_menu is True, "incomplete enumeration cannot yield an empty-menu stop")
    require(set(targets) == set(proposals) == set(constant_tables) == set(priorities),
            "frozen target/proposal/menu inventories differ")
    from .snapshot import unlinked
    output = unlinked(output).absolute()
    require(not output.resolve().is_relative_to(Path(snapshot.repo).resolve()),'campaign output must be external')
    require(not output.exists(), "campaign output already exists")
    output.mkdir(parents=True)
    actions=[]
    for key,target in targets.items():
        require(proposals[key].target_id == target.target_id and proposals[key].source_generation == snapshot.generation,
                "proposal targets another world")
        require(type(priorities[key]) is dict and set(priorities[key]) == {'priority','cost'}, "host-owned scheduling fields required")
        actions.append(Action(key,snapshot.source_digest,**priorities[key]))
    dispositions=[]; remaining=budget
    with Journal(output/'journal.db', repository=Path(snapshot.repo)) as journal:
        profile=digest({'id':snapshot.profile_id},domain='OPICA_PROFILE_ID_V1')
        journal.activate(snapshot.generation,snapshot.source_digest,profile,expected_revision=0)
        journal.freeze_menu(actions,frozenset(targets),generation=snapshot.generation,
                            source=snapshot.source_digest,expected_revision=1)
        for _ in range(len(actions)):
            state=journal.state()
            choice=journal.dispatch({k:proposals[k].digest for k in proposals},remaining,
                generation=snapshot.generation,source=snapshot.source_digest,expected_revision=state['revision'])
            if choice['kind']=='STOP':break
            key=choice['action_id'];target=targets[key];remaining-=priorities[key]['cost']
            controls=build_falsifier_requirements({'source':'ACTUAL_CANONICAL','target':target.target_id})
            attempt=execute_attempt(proposals[key],target,snapshot,output/'attempts'/choice['attempt_id'],
                                    worker=worker,constant_table=constant_tables[key])
            if attempt.status=='PROVED_CONDITIONAL':
                event=publish_verified_application(journal,choice['attempt_id'],attempt,snapshot,target,
                    worker=worker,generation=snapshot.generation,source=snapshot.source_digest,
                    expected_revision=choice['revision'])
                matches=[r for r in journal.current_applications() if r['proposal_digest']==proposals[key].digest]
                require(len(matches)==1,'native published application identity ambiguous')
                app=matches[0]
                application=application_from_publication(journal,choice['attempt_id'])
                proof_packets=[(key,obj) for key,obj in application['witness_bindings'].items()
                               if obj['object_kind']=='DEPENDENT_PROOF_PACKET']
                require(len(proof_packets)==1,'native proof packet binding missing')
                packet_id,packet=proof_packets[0]
                wanted={'id':'native-target','source':snapshot.source_digest,'context':packet['context_digest'],
                    'producer':packet_id,'consumer':packet_id,'witness':packet_id,
                    'phase':'CONFIRMATORY_FROZEN'}
                observed={**wanted,'observed_phase':'CONFIRMATORY_FROZEN','receipt':app['evidence_digest'],'transport':None}
                verify_interfaces([wanted],[observed],lambda req,row:
                    row['receipt']==app['evidence_digest'] and app['target_digest']==target.digest and
                    row['witness'] in application['witness_bindings'] and app['publication_eligible'])
                dispositions.append({'action':key,'status':'PROVED_CONDITIONAL','controls':list(controls),
                    'evidence':app['evidence_digest'],'journal_revision':event['revision'],
                    'frameworks':['FFBBP','POLICY_ADAPTER_ONLY','OOL','NATIVE_EXPECTED_TYPE_REPLAY']})
            else:
                journal.record_outcome(choice['attempt_id'],attempt.status,{'reason':attempt.reason},
                    generation=snapshot.generation,source=snapshot.source_digest,expected_revision=choice['revision'])
                dispositions.append({'action':key,'status':attempt.status,'reason':attempt.reason})
        events=journal.export_events();(output/'EVENTS.jsonl').write_bytes(events)
        applications=journal.current_applications()
    result={'schema':'OPICA_BOUNDED_CAMPAIGN_V1','source_generation':snapshot.generation,
            'initial_budget':budget,'remaining_budget':remaining,'dispositions':dispositions,
            'published_applications':len(applications),'RH':'OPEN','Step4':'OPEN'}
    (output/'campaign.json').write_bytes(canonical_bytes(result))
    return result

def require_hidden_partition(proposer: dict, confirmation: dict) -> None:
    require(not set(proposer) & {'gold','expected_outcome','answer','confirmation_labels'},'answer-label leakage')
    require(proposer.get('partition')=='CONSTRUCTION' and confirmation.get('partition')=='CONFIRMATORY_FROZEN',
            'construction/confirmation partition differs')
    require(not set(proposer.get('retrieved_ids',[])) & set(confirmation.get('gold_ids',[])),
            'indirect evaluator answer retrieval')
