"""Deterministic external views; operational timestamps stay in the journal."""
from .canonical import canonical_bytes, require
from .applications import export_applications,application_from_publication

def semantic_projection(record: dict) -> dict:
    volatile={'run_id','run_attempt','timestamp','worker_id','execution_id'}
    def project(value):
        if type(value) is dict:return {k:project(v) for k,v in value.items() if k not in volatile}
        if type(value) is list:return [project(v) for v in value]
        return value
    return project(record)

def export_state(journal) -> dict[str, bytes]:
    state=journal.verify_chain()
    attempts=journal.db.execute('SELECT attempt_id FROM applications WHERE generation=? AND source=? ORDER BY application_id',
        (state['generation'],state['source'])).fetchall()
    # Repeated independent checks of the same semantic application retain their
    # distinct operational events, while contributing one mathematical edge.
    applications={}
    for row in attempts:
        application=application_from_publication(journal,row[0])
        applications.setdefault(application['id'],application)
    # All rows are resolved from the verified journal projection, never supplied flags.
    return {'EVENTS.jsonl':journal.export_events(),
            'APPLICATIONS.jsonl':export_applications(list(applications.values())),
            'CURRENT_STATE.json':canonical_bytes({'generation':state['generation'],'source':state['source'],
                'revision':state['revision'],'applications':len(applications),'RH':'OPEN','Step4':'OPEN'})+b'\n'}
