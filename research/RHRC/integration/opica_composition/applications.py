"""Proof-linked application records. Associations remain nonimplicative edges."""
from __future__ import annotations
from .canonical import require, digest, digest_text, canonical_bytes, load_bytes

EDGE_KINDS = frozenset({"USES_CONSTANT", "SHARES_SOURCE", "HAS_SIMILAR_FORM", "CANDIDATE_APPLICATION",
    "CHECKED_APPLICATION", "CONTRADICTS_UNDER_CONTEXT", "MISSING_ADAPTER", "FALSIFIED_UNDER_PREMISES"})
_PUBLISHED_NATIVE = object()

def checked_application(verified, *, inputs=None, output=None, substitutions=None,
                        witness_bindings=None, open_premises=None, issuer=None) -> dict:
    require(issuer is _PUBLISHED_NATIVE, 'resolve a native writer-published record; JSON flags are not proof evidence')
    row = verified.to_dict() if hasattr(verified, 'to_dict') else verified
    require(row.get('status') == 'PROVED_CONDITIONAL' and row.get('publication_eligible') is True,
            'independent production proof replay required')
    require(bool(row.get('independent_replay')), 'independent replay absent')
    objects=row.get('object_bindings',[])
    packets=[o for o in objects if o.get('object_kind')=='DEPENDENT_PROOF_PACKET']
    require(len(packets)==1,'native dependent proof packet binding missing')
    packet=packets[0]
    native_output=digest({'source_generation':row['source_generation'],
        'context':packet['context'],'type_expression':packet['type_expression']},domain='OPICA_PROPOSITION_INSTANCE_V1')
    native_inputs=[];native_objects={}
    for obj in objects:
        oid=digest(obj,domain='OPICA_NATIVE_OBJECT_BINDING_V1');native_objects[oid]=obj
        if obj['object_kind']=='AUTHORIZED_LOCAL' and row['context'][obj['scope_index']-1]['is_prop']:
            native_inputs.append(oid)
    native_substitutions={'verified_plan':row['proposal_digest'],'proof_expression':packet['term_expression']}
    for supplied,actual,label in ((inputs,native_inputs,'inputs'),(output,native_output,'output'),
            (substitutions,native_substitutions,'substitutions'),(witness_bindings,native_objects,'object bindings'),
            (open_premises,[],'new premises')):
        require(supplied is None or supplied==actual,'caller relabelled compiler-derived '+label)
    inputs,output,substitutions,witness_bindings,open_premises=native_inputs,native_output,native_substitutions,native_objects,[]
    for ref in [*inputs, output, *open_premises]: digest_text(ref)
    require(len(inputs) == len(set(inputs)) and len(open_premises) == len(set(open_premises)), 'duplicate proposition port')
    require(not set(inputs) & set(open_premises), 'open premise treated as supplied proof')
    body = {'schema':'OPICA_CHECKED_APPLICATION_V1','kind':'CHECKED_APPLICATION',
        'source_generation':row['source_generation'],'target_digest':row['target_digest'],
        'proof_evidence':row['evidence_digest'],'context':row['context'],
        'inputs':inputs,'output':output,'substitutions':substitutions,
        'witness_bindings':witness_bindings,'open_premises':open_premises,
        'authority':'PROVED_CONDITIONAL','unconditional':not open_premises and not row['context']}
    semantic={k:v for k,v in body.items() if k!='proof_evidence'}
    return {**body,'id':digest(semantic,domain='OPICA_APPLICATION_INSTANCE_V1')}

def require_applicable(record: dict, *, source_generation: str, authorized_context: list,
                       supplied_propositions: set[str], proof_registry: dict) -> None:
    require(record.get('kind') == 'CHECKED_APPLICATION', 'association edge grants no implication')
    require(record.get('source_generation') == source_generation, 'stale application generation')
    require(record.get('context') == authorized_context, 'context differs; checked transport required')
    require(record.get('proof_evidence') in proof_registry and
            proof_registry[record['proof_evidence']].get('target_digest') == record['target_digest'],
            'checked native proof origin missing')
    reconstructed=checked_application(proof_registry[record['proof_evidence']],issuer=_PUBLISHED_NATIVE)
    require(canonical_bytes(record)==canonical_bytes(reconstructed),
            'application ports or substitutions differ from the independently checked native proof')
    require(set(record['inputs']) <= supplied_propositions, 'required proof premise absent')
    require(not record['open_premises'], 'application still has open proof premises')

def export_applications(rows: list[dict]) -> bytes:
    require(len({r['id'] for r in rows}) == len(rows), 'duplicate application identity')
    return b''.join(canonical_bytes({k:v for k,v in r.items() if k!='proof_evidence'})+b'\n'
                    for r in sorted(rows,key=lambda r:r['id']))

def application_from_publication(journal, attempt_id: str, **ports) -> dict:
    """Resolve an actual writer-published record; a JSON verified flag is insufficient."""
    state=journal.verify_chain()
    expected=journal.db.execute('SELECT proposal FROM attempts WHERE attempt_id=?',(attempt_id,)).fetchone()
    require(expected is not None,'unknown native attempt')
    row=journal.db.execute('SELECT body FROM applications WHERE attempt_id=? AND generation=? AND source=?',
        (attempt_id,state['generation'],state['source'])).fetchall()
    require(len(row)==1,'published native application absent or ambiguous')
    from .canonical import load_bytes
    record=load_bytes(row[0][0])
    require(record.get('proposal_digest')==expected[0],'published attempt/proposal identity differs')
    return checked_application(record,issuer=_PUBLISHED_NATIVE,**ports)
