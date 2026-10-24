from pathlib import Path
from collections import Counter,defaultdict
import hashlib,json
S=Path(__file__).resolve().parent;W=S.parent;R=W/'opica-followup-repo'
C=R/'research/RHRC/integration/opica_followup/continuation/2026-10-22';E=C/'evidence/current-codex/stage21'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(p,q):
    assert p.is_file() and not q.exists(),(p,q)
    q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
native=json.loads((S/'record-validation/native/summary.json').read_bytes());linux=json.loads((S/'record-validation/linux/summary.json').read_bytes())
assert native['status']=='PASS_TESTS_AND_FROZEN_REPLAY_ONLY' and native['source_before']==native['source_after']
assert linux['status']=='PASS_FOCUSED_PARENT_TESTS_ONLY' and linux['source_hashes_unchanged']
for row in native['commands']:
    log=(S/'record-validation/native'/row['log']).read_text(encoding='utf-8',errors='replace');assert row['exit_code']==0
    if row['name'].startswith('child-'):assert 'Ran 185 tests' in log and '\nOK\n' in log
for row in linux['commands']:
    log=(S/'record-validation/linux'/row['log']).read_text(encoding='utf-8',errors='replace')
    assert row['exit_code']==0 and 'Ran 82 tests' in log and '\nOK\n' in log and 'skipped=' not in log
for p in (S/'record-validation').rglob('*'):
    if p.is_file() and not any(x.startswith('temp') for x in p.relative_to(S/'record-validation').parts):put(p,E/'python'/p.relative_to(S/'record-validation'))
for name in ['validate_record_native.py','validate_record_linux.py','repair_control_classification.py','finalize_record.py']:
    put(S/name,E/name)
put(S/'live-pr-snapshot.json',E/'live-pr-snapshot.json')
put(W/'audit-offcritical-real-basis/STAGE21_WEIGHTED_BUDGET_SUPPLEMENTARY_AGENT_REVIEW.json',E/'support/independent-review/STAGE21_WEIGHTED_BUDGET_SUPPLEMENTARY_AGENT_REVIEW.json')
ledger=json.loads((C/'ROOT_LEDGER_100.json').read_bytes());units=defaultdict(list)
for row in ledger['roots']:
    for paper in row['contract']['paper_ids']:units[paper].append(row)
counts=Counter();unit_rows={}
for paper,rows in sorted(units.items()):
    missing=[r['full_name'] for r in rows if not r['current_status'].startswith('PROVED_')]
    state='COMPLETE_HISTORICAL_OR_NARROW_EVIDENCE_ONLY' if not missing else 'PARTIAL'
    counts[state]+=1;unit_rows[paper]={'state':state,'root_count':len(rows),'missing_bodies':missing,'full_contract_unit_acceptance':False}
assert len(units)==28 and counts=={'COMPLETE_HISTORICAL_OR_NARROW_EVIDENCE_ONLY':28}
coverage={'schema':'OPICA_STAGE21_PAPER_UNIT_COVERAGE_ONLY_V1','ledger_sha256':sha(C/'ROOT_LEDGER_100.json'),'counts':dict(counts),'units':unit_rows,'aggregate_accepted':False,'formal_unit_acceptance_established':False,'physical_interface_findings_still_open':True}
(E/'PAPER_UNIT_COVERAGE.json').write_text(json.dumps(coverage,indent=2)+'\n',encoding='utf-8')
p=E/'STATUS.json';status=json.loads(p.read_bytes())
status['paper_unit_evidence_coverage']={'receipt':'PAPER_UNIT_COVERAGE.json','complete':28,'partial':0,'absent':0,'acceptance_established':False}
status['record_phase_validation']={'child':{'tests_per_mode':185,'modes':['normal','optimized'],'receipt':'python/native/summary.json'},'parent':{'tests_per_mode':82,'modes':['normal','optimized'],'no_skips':True,'real_Linux_tmp_fixtures':True,'receipt':'python/linux/summary.json'},'frozen':{'checks_per_mode':[5112,18862,14672,1274],'numeric_suites':3,'numerical_authority':'CONSISTENCY_ONLY','receipt':'python/native/summary.json'},'proof_or_full_release_authority':False}
status['retained_workflow_consumers']={'receipt':'workflow-consumers/CHECK_RESULT.json','W04_W07_closures':52,'W06_closures':14,'standard_axioms_only':True}
p.write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8',newline='\n')
p=C/'STAGE21_HANDOVER.md';t=p.read_text(encoding='utf-8')
needle='## What changed\n';assert t.count(needle)==1
t=t.replace(needle,'The separate W04/W07 and W06 current-source consumers pass (52 +14 standard-axiom closures). Record-phase child tests pass185/185 in each Python mode; real-Linux parent fixtures pass82/82 in each mode with no skips. Frozen suites replay5112/18862/14672/1274 checks per mode and three numerical CONSISTENCY_ONLY suites. Paper-unit body/evidence coverage is28/28, with no unit acceptance. These infrastructure results confer no additional theorem or release authority.\n\n'+needle)
t=t.replace('The W04/W07 and W06 source-specific consumers are separately replayed. Record-phase infrastructure results are appended after their actual completion.','The W04/W07 and W06 source-specific consumers and record-phase infrastructure have completed as recorded below.')
t=t.replace('In total, 17 negative source files are rejected and four positive control files pass.','In total,17 negative source files are rejected and four positive control files pass. The first classifier misread Lean’s `error(lean.invalidField):` format for the deliberately missing independence argument. Its original FAIL receipt and exact compiler exit1/log remain preserved; a source-unchanged classification repair recognizes that genuine argument failure without rerunning or changing the compiler evidence.')
p.write_text(t,encoding='utf-8',newline='\n')
print(json.dumps({'status_sha256':sha(E/'STATUS.json'),'handover_sha256':sha(p),'child':'185/185 each mode','parent':'82/82 each mode no skips','frozen':'PASS consistency-only'},indent=2))
