"""Record exact Stage21 narrow evidence, without granting aggregate acceptance."""
from pathlib import Path
from collections import Counter
import copy,gzip,hashlib,io,json,re,subprocess,tarfile

S=Path(__file__).resolve().parent;W=S.parent;R=W/'opica-followup-repo'
C=R/'research/RHRC/integration/opica_followup/continuation/2026-10-22';E=C/'evidence/current-codex/stage21'
HEAD='139c1a0d88cc0fb2d8a0d8ea71e152b25b14c36e';TREE='3e63b0c72fc04da7bab45388d6096e82e95c4acb'
NARROW='PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING';ABSENT='OPEN_NO_COMPLETE_CANDIDATE';HIST='PROVED_IN_ORIGINAL_41_ROOT_SOURCE_BOUND_SUBSET'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True).strip()
def read(p):return json.loads(p.read_bytes())
def write(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8',newline='\n')
def put(p,q):
    assert p.is_file() and not q.exists(),(p,q)
    q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
assert git('rev-parse','HEAD')==HEAD and git('rev-parse','HEAD^{tree}')==TREE and not git('status','--porcelain')
assert sha(R/'research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json')=='2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41'
assert sha(R/'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md')=='de9aabe7985f839c39b62e82c3407c97bc21d831e283199ab5d81784fe68f327'
runner=read(S/'clean-runner/CHECK_RESULT.json');controls=read(S/'clean-controls/CHECK_RESULT.json');workflow=read(S/'clean-workflow-consumers/CHECK_RESULT.json')
assert runner['status']=='PASS_NARROW_ONLY' and runner['head']==HEAD and runner['tree']==TREE and runner['dirty_status']=='' and runner['source_unchanged']
assert not runner['full_release_accepted'] and not runner['aggregate_registration_accepted']
assert controls['status']=='PASS_CONTROLS_ONLY' and controls['checked_commit']==HEAD and controls['checked_tree']==TREE and controls['source_unchanged']
assert len(controls['controls'])==21 and all(c['passed'] for c in controls['controls'])
assert workflow['status']=='PASS_NARROW_WORKFLOW_CONSUMERS_ONLY' and workflow['checked_commit']==HEAD and workflow['checked_tree']==TREE and workflow['source_unchanged']
assert sum(r['printed_closures'] for r in workflow['consumers'])==66
by={c['name']:c for c in runner['consumers']};assert len(by)==35
closures=sum(len(c['axioms']) for c in by.values());assert closures==271
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for c in by.values() for a in c['axioms'].values())
snapshot=read(S/'clean-runner/source-before.json')
archive=subprocess.check_output(['git','archive',HEAD,'Zeta23','lean-toolchain','lake-manifest.json','lakefile.toml','research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers','research/RHRC/integration/opica_followup/continuation/2026-10-22/run_candidate_checks.py'],cwd=R)
with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
    committed={m.name:hashlib.sha256(tf.extractfile(m).read()).hexdigest() for m in tf if m.isfile()}
for relative,h in snapshot.items():assert sha(R/relative)==h and committed[relative]==h,relative
for cmd in runner['commands']:assert cmd['exit_code']==0 and sha(S/'clean-runner'/cmd['log'])==cmd['log_sha256']
for row in controls['controls']:assert sha(S/'clean-controls'/row['file'])==row['source_sha256'] and sha(S/'clean-controls'/row['log'])==row['log_sha256']
for directory,target in [('clean-runner','runner'),('clean-controls','controls'),('clean-workflow-consumers','workflow-consumers')]:
    for p in sorted((S/directory).iterdir()):
        if p.is_file():
            q=E/target/p.name
            if p.name in ['build.log','source-before.json']:
                q=q.with_name(q.name+'.gz');assert not q.exists();q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(gzip.compress(p.read_bytes(),mtime=0))
            else:put(p,q)
support=[
 ('audit-finite-span/SEALED_FINITE_SPAN_2026-10-24.zip','finite-span/SEALED_FINITE_SPAN_2026-10-24.zip'),
 ('audit-finite-span/FINITE_SPAN_FINAL_RECEIPT_2026-10-24.json','finite-span/FINITE_SPAN_FINAL_RECEIPT_2026-10-24.json'),
 ('audit-budget/FIXED_BASIS_BUDGET_RECEIPT_2026-10-24.json','budget/FIXED_BASIS_BUDGET_RECEIPT_2026-10-24.json'),
 ('audit-budget/POST_GREEN_FIXED_BASIS_BUDGET_2026-10-24.md','budget/POST_GREEN_FIXED_BASIS_BUDGET_2026-10-24.md'),
 ('audit-novelty/TEN_ROOT_NOVELTY_SYNTHESIS_2026-10-24.md','novelty/TEN_ROOT_NOVELTY_SYNTHESIS_2026-10-24.md'),
 ('audit-drive-completeness/DRIVE_COMPLETENESS_RECEIPT_2026-10-24.json','novelty/DRIVE_COMPLETENESS_RECEIPT_2026-10-24.json'),
 ('audit-drive-completeness/DRIVE_COMPLETENESS_INCREMENT_2026-10-24.md','novelty/DRIVE_COMPLETENESS_INCREMENT_2026-10-24.md'),
 ('audit-independent-contract-review/INDEPENDENT_FINDINGS.md','independent-review/INDEPENDENT_FINDINGS.md'),
 ('audit-independent-contract-review/ALL100_REVIEW_MATRIX.md','independent-review/ALL100_REVIEW_MATRIX.md'),
 ('audit-independent-contract-review/all100-semantic-review.json','independent-review/all100-semantic-review.json')]
for p,q in support:put(W/p,E/'support'/q)
for name in ['FINITE_SPAN_INSTALL.json','COMPATIBILITY_INSTALL.json','SCOPING_REPAIR.json','FACADE_GATE_EXTENSION.json']:
    put(S/name,E/'implementation'/name)
for p in sorted((S/'precommit-consumers').glob('*')):
    if p.is_file():put(p,E/'development/precommit-consumers'/p.name)
for p in S.glob('production-preliminary-build*.log'):
    q=E/'development'/(p.name+'.gz');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(gzip.compress(p.read_bytes(),mtime=0))
roots={
 'finite_zero_span_positive_only_zero':('FiniteSpanSeparation','ExpectedFullFiniteSpan','IndependentFullFiniteSpan.full_original_domain_and_independent_basis','ACTUAL_AVAILABLE_ZERO_JETS_BOTH_UNIVERSAL_MEASURE_AND_INDEPENDENT_REAL_BASIS_CLAUSES'),
 'fixed_basis_negative_mass_budget':('FiniteSpanSeparation','ExpectedActualFixedBudget','IndependentActualFixedBudget.expected_full_actual_euclidean_budget','ACTUAL_CANONICAL_GLOBAL_OFF_INTEGER_NEGATIVE_MASS_LITERAL_EUCLIDEAN_SQRT_SUM_SQUARES'),
 'actual_zero_measure_span_consumer':('Consumers','ExpectedSpanPhysicalConsumer','IndependentSpanPhysicalConsumer.expected_actual_zero_measure_span_consumer','ACTUAL_ZERO_PROFILES_ZEROTH_JET_IDENTIFICATION_SELFDUALITY_GAP_AND_BOTH_SPAN_CONCLUSIONS')}
# Expected names are checked against real compiler output, never inferred from filenames.
assert all(expected in by[consumer]['axioms'] for _,consumer,expected,_ in roots.values()),[(c,list(by[c]['axioms'])) for _,c,_,_ in roots.values()]
ledger=read(C/'ROOT_LEDGER_100.json');assert ledger['status_counts']=={ABSENT:3,HIST:41,NARROW:56}
contracts={r['full_name']:copy.deepcopy(r['contract']) for r in ledger['roots']}
status={'schema':'OPICA_STAGE21_NARROW_SOURCE_PINNED_V1','status':'PASS_NARROW_ONLY','checked_commit':HEAD,'checked_tree':TREE,'dirty_status_during_checks':'','source_unchanged':True,'roots':{},'runner':'runner/CHECK_RESULT.json','controls':'controls/CHECK_RESULT.json','printed_closures':closures,'local_control_counts':{'positive_source_files':4,'rejected_negative_source_files':17,'new_finite_span_mutations':4},'full_original_contract_acceptance':False,'full_release_accepted':False,'aggregate_registration_accepted':False,'independent_human_review':'NOT_ESTABLISHED','RH':'OPEN','Step4':'OPEN','independent_closing_inequalities':'OPEN'}
for row in ledger['roots']:
    short=row['full_name'].split('.')[-1]
    if short in roots:
        module,consumer,expected,domain=roots[short];assert row['current_status']==ABSENT
        source='Zeta23/OPICAFollowup/'+module+'.lean';assert row['path']==source
        row.update(current_status=NARROW,source_file_present=True,declaration_lexically_present=True,source_sha256=sha(R/source))
        row['gates']={'implementation':'IMPLEMENTED_ORIGINAL_TWO_CLAUSE_PHYSICAL_CONTRACT_NARROW','module_compilation':'PASS_EXACT_CLEAN_COMMIT_SOURCE_PINNED_COMPILER','expected_type_consumer':'PASS_INDEPENDENT_FULL_ORIGINAL_TYPE','actual_domain_consumer':'PASS_'+domain,'axiom_check':'STANDARD_ONLY_TRANSITIVE_PRINTED_CLOSURES','aggregate_current_source_export':'OPEN','full_release_acceptance':'OPEN'}
        row['evidence']=['evidence/current-codex/stage21/STATUS.json','evidence/current-codex/stage21/runner/CHECK_RESULT.json']
        row['independent_consumer']={'path':'consumers/'+consumer+'.lean','sha256':sha(C/'consumers'/(consumer+'.lean')),'expected_declaration':expected}
        row['statement_formalization']=row['contract']['statement_contract']+' Current actual-domain audit: '+domain+'. Original contract unchanged.'
        status['roots'][row['full_name']]={'source':source,'source_sha256':row['source_sha256'],'consumer':row['independent_consumer'],'domain':domain,'status':'PROVED_NARROW_AGGREGATE_PENDING'}
    elif row['path'] in ['Zeta23/OPICAFollowup/Consumers.lean','Zeta23/OPICAFollowup/ConfluentProfiles.lean','Zeta23/OPICAFollowup/SquareDefect.lean']:
        prior={k:copy.deepcopy(row.get(k)) for k in ['source_sha256','gates','evidence','current_status']}
        row['source_sha256']=sha(R/row['path'])
        row.setdefault('revalidations',[]).append({'stage':21,'checked_commit':HEAD,'checked_tree':TREE,'source_sha256':row['source_sha256'],'status':'PASS_EXISTING_PRIMARY_NOT_ADDITIONAL_ROOT','evidence':['evidence/current-codex/stage21/runner/CHECK_RESULT.json'],'historical_source_provenance':prior})
        row['gates']['module_compilation']='PASS_EXACT_CLEAN_COMMIT_STAGE21_REVALIDATION'
    if row['path']=='Zeta23/OPICAFollowup/SquareDefect.lean':
        row['full_contract_followup']={'status':'OPEN_PHYSICAL_MEASURE_ADAPTER_AND_GENERAL_LATTICE_REPAIR_DOMAIN','review':'evidence/current-codex/stage21/support/independent-review/INDEPENDENT_FINDINGS.md','meaning':'Existing compiled proposition is retained as narrow evidence; it does not by itself discharge every original physical-domain obligation.'}
assert all(row['contract']==contracts[row['full_name']] for row in ledger['roots'])
counts=dict(sorted(Counter(row['current_status'] for row in ledger['roots']).items()));assert counts=={HIST:41,NARROW:59}
ledger['status_counts']=counts;vs=ledger['verification_summary'];assert not ledger['current_aggregate_accepted'] and not vs['current_aggregate_accepted']
vs.update(independently_verified_narrow_roots=59,open_no_complete_candidate_roots=0,receipt='STAGE21_HANDOVER.md',meaning='41 historical plus59 narrow roots gives100-root body/evidence coverage, not aggregate original-contract acceptance. Fresh SquareDefect physical/interface findings and all full release gates remain OPEN.')
vs['additional_stage21_primary_roots']=list(roots);vs['stage21_checked_source']={'commit':HEAD,'tree':TREE,'status':'evidence/current-codex/stage21/STATUS.json'}
vs['full_original_contract_audit']='OPEN_SEE_STAGE21_FRESH_NONAUTHOR_FINDINGS'
write(C/'ROOT_LEDGER_100.json',ledger);write(E/'STATUS.json',status)
report=(S/'STAGE21_HANDOVER.template.md').read_text(encoding='utf-8').replace('{{RUNNER_RESULT}}',runner['status']).replace('{{CLOSURES}}',str(closures)).replace('{{CONTROL_RESULT}}',controls['status']);assert '{{' not in report
(C/'STAGE21_HANDOVER.md').write_text(report,encoding='utf-8',newline='\n')
for p in [R/'AGENTS.md',C/'README.md',C/'DOCUMENTATION_INDEX.md',C/'NEXT_AGENT_PROMPT.md',C/'REMAINING_WORK.md',R/'research/RHRC/integration/opica_followup/README.md']:
    raw=p.read_bytes();t=raw.decode('utf-8').replace('\r\n','\n')
    if p.name=='AGENTS.md':
        old='Fifty-six additional roots passed narrow gates and 3 original roots still lack\ncomplete implementations. Read the continuation STAGE20_HANDOVER.md (and the'
        assert t.count(old)==1;t=t.replace(old,'Fifty-nine additional roots passed narrow gates; all100 original bodies now have\nhistorical or narrow evidence. Full original-contract acceptance remains OPEN.\nRead the continuation STAGE21_HANDOVER.md (and the')
    elif p.name=='REMAINING_WORK.md':
        t='''# Remaining work\n\nOriginal scope:100 primary roots /28 units, unchanged. [Stage21](STAGE21_HANDOVER.md) pins code139c1a0d and the exact narrow receipts.\n\n-41 historical source-bound roots.\n-59 additional narrow roots.\n-0 absent bodies.\n\nThis is body/evidence coverage, not aggregate original-contract acceptance. The fresh non-author review found SquareDefect actual measure/Jordan/growth and general lattice-repair obligations plus seven missing canonical interface definitions. Those must be integrated and checked, with no promotion from old raw-pairing evidence. Read the Stage21 review findings and full100 matrix.\n\nNext: physical SquareDefect repairs; seven canonical interfaces; full100 independent Validation with every compound clause; genuine cold full100 source/type/axiom/dependency receipt; independent review; concrete parent path/dependency amendment; registry; canonical generation; complete runtime and exact-head workflow harvest. Frozen parent seals, original contracts and all OPEN claims remain unchanged.\n\nThe full accepted producer still requires its independently reviewed seal; agent mathematical reviews are not independent human approval. RH, Step4 and independent closing inequalities remain OPEN.\n'''
    else:
        t='> Current checkpoint: [Stage21]('+('continuation/2026-10-22/' if p.parent.name=='opica_followup' else '')+'STAGE21_HANDOVER.md), checked code `'+HEAD+'`, tree `'+TREE+'`. Ledger:41 historical +59 narrow +0 absent bodies; this is not original-contract/aggregate acceptance. Fresh physical/interface findings and all release obligations remain OPEN. Earlier stage statements below retain their historical scope.\n\n'+t
        if p.name=='NEXT_AGENT_PROMPT.md':t=t.replace('the latest [STAGE20_HANDOVER.md](STAGE20_HANDOVER.md)','the latest [STAGE21_HANDOVER.md](STAGE21_HANDOVER.md)',1)
    p.write_bytes(t.replace('\n','\r\n').encode('utf-8') if b'\r\n' in raw else t.encode('utf-8'))
for name in ['record_stage21.py','run_clean_controls.py','replay_clean_workflow_consumers.py']:
    put(S/name,E/name)
write(E/'RECORD_CHANGE_SUMMARY.json',{'checked_commit':HEAD,'promoted_original_roots':list(roots),'frozen_contracts_unchanged':True,'protected_graph_sha256':sha(R/'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md'),'current_aggregate_accepted':False,'status_counts':counts,'semantic_findings_still_open':True,'supporting_not_primary':['fixed_basis_vanishing_negative_budget','offcritical_real_pair_proposal']})
print(json.dumps({'status':'RECORDED_NARROW_ONLY','counts':counts,'closures':closures,'checked_commit':HEAD,'handover_sha256':sha(C/'STAGE21_HANDOVER.md')},indent=2))
