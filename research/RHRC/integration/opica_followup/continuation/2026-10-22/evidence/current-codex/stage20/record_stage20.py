"""Record successful clean Stage20 evidence; never grants full acceptance."""
from pathlib import Path
from collections import Counter
import copy,gzip,hashlib,json,re,subprocess

S=Path(__file__).resolve().parent;W=S.parent;R=W/'opica-followup-repo'
C=R/'research/RHRC/integration/opica_followup/continuation/2026-10-22'
E=C/'evidence/current-codex/stage20'
HEAD='9a8b2a4baee49f2056c7945b1544a7bc2893735b';TREE='6aa53d22d50d2aa24046d73b128c64a1d262f7f3'
NARROW='PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING';ABSENT='OPEN_NO_COMPLETE_CANDIDATE';HIST='PROVED_IN_ORIGINAL_41_ROOT_SOURCE_BOUND_SUBSET'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True).strip()
def jread(p):return json.loads(p.read_bytes())
def jwrite(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=True)+'\n',encoding='utf-8',newline='\n')
def put(p,q):
    q.parent.mkdir(parents=True,exist_ok=True)
    assert not q.exists(),q
    q.write_bytes(p.read_bytes())
assert git('rev-parse','HEAD')==HEAD and git('rev-parse','HEAD^{tree}')==TREE and not git('status','--porcelain')
assert sha(R/'research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json')=='2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41'
assert sha(R/'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md')=='de9aabe7985f839c39b62e82c3407c97bc21d831e283199ab5d81784fe68f327'
runner=jread(S/'clean-runner/CHECK_RESULT.json');controls=jread(S/'clean-controls/CHECK_RESULT.json')
workflow=jread(S/'clean-workflow-consumers/CHECK_RESULT.json')
assert workflow['status']=='PASS_NARROW_WORKFLOW_CONSUMERS_ONLY' and workflow['checked_commit']==HEAD and workflow['checked_tree']==TREE and workflow['source_unchanged']
assert sum(r['printed_closures'] for r in workflow['consumers'])==66
assert runner['status']=='PASS_NARROW_ONLY' and runner['head']==HEAD and runner['tree']==TREE and runner['dirty_status']=='' and runner['source_unchanged']
assert not runner['full_release_accepted'] and not runner['aggregate_registration_accepted']
assert controls['status']=='PASS_CONTROLS_ONLY' and controls['checked_commit']==HEAD and controls['checked_tree']==TREE and controls['source_unchanged']
assert len(controls['controls'])==17 and all(c['passed'] for c in controls['controls'])
by={c['name']:c for c in runner['consumers']};assert len(by)==31
closures=sum(len(c['axioms']) for c in by.values());assert closures==266
assert all(set(xs)<={'propext','Classical.choice','Quot.sound'} for c in by.values() for xs in c['axioms'].values())
snapshot=jread(S/'clean-runner/source-before.json')
for relative,h in snapshot.items():
    assert sha(R/relative)==h
    assert hashlib.sha256(subprocess.check_output(['git','show',HEAD+':'+relative],cwd=R)).hexdigest()==h
for command in runner['commands']:
    assert command['exit_code']==0 and sha(S/'clean-runner'/command['log'])==command['log_sha256']
for row in controls['controls']:
    assert sha(S/'clean-controls'/row['file'])==row['source_sha256'] and sha(S/'clean-controls'/row['log'])==row['log_sha256']
for directory,target in [('clean-runner','runner'),('clean-controls','controls')]:
    for p in sorted((S/directory).iterdir()):
        if p.is_file():
            q=E/target/p.name
            if p.name in ['build.log','source-before.json']:
                q=q.with_name(q.name+'.gz');q.parent.mkdir(parents=True,exist_ok=True)
                assert not q.exists();q.write_bytes(gzip.compress(p.read_bytes(),mtime=0))
            else:put(p,q)
for p in sorted((S/'clean-workflow-consumers').iterdir()):
    if p.is_file():put(p,E/'workflow-consumers'/p.name)
support=[
 ('audit-math-grouped/OPICA_GROUPED_H2A_2026-10-24.zip','h2/OPICA_GROUPED_H2A_2026-10-24.zip'),
 ('audit-math-grouped/grouped-h2a-receipt.json','h2/grouped-h2a-receipt.json'),
 ('audit-math-grouped/H2A_GROUPED_PROOF_REPORT_2026-10-24.md','h2/H2A_GROUPED_PROOF_REPORT_2026-10-24.md'),
 ('audit-rate/POST_GREEN_FULL_WINDOW_RATES_2026-10-24.md','rates/POST_GREEN_FULL_WINDOW_RATES_2026-10-24.md'),
 ('audit-rate/POST_GREEN_ARITHMETIC_CONSUMERS_2026-10-24.md','rates/POST_GREEN_ARITHMETIC_CONSUMERS_2026-10-24.md'),
 ('audit-rate/staged/STAGED_RATE_COMPILER_RECEIPT_2026-10-24.json','rates/STAGED_RATE_COMPILER_RECEIPT_2026-10-24.json'),
 ('audit-rate/staged/STAGED_ARITHMETIC_CONSUMER_RECEIPT_2026-10-24.json','rates/STAGED_ARITHMETIC_CONSUMER_RECEIPT_2026-10-24.json')]
for p,q in support:put(W/p,E/'support'/q)
for directory in ['precommit-consumers','precommit-consumers-qualified']:
    for p in (S/directory).glob('*'):
        if p.is_file():put(p,E/'development'/directory/p.name)
for name in ['rates-preliminary-build.log','arithmetic-consumers-preliminary-build.log','confluent-preliminary-build.log','confluent-consumer-preliminary.log']:
    p=S/name
    if p.exists():
        q=E/'development'/(name+'.gz');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(gzip.compress(p.read_bytes(),mtime=0))
roots={
 'profile_jet_confluent_determinant':('ConfluentProfiles','ExpectedConfluentProfiles','OPICAConfluentProfilesIndependent.expected_profile_jet_confluent_determinant','DISTINCT_NONZERO_NODES_ARBITRARY_MULTIPLICITIES_CANONICAL_NORMALIZED_COLUMNS'),
 'finite_zero_jet_independent':('ConfluentProfiles','ExpectedConfluentProfiles','OPICAConfluentProfilesIndependent.expected_finite_zero_jet_independent','ACTUAL_STRIP_ZETA_ZEROS_REFLECTION_QUOTIENT_AVAILABLE_MULTIPLICITY_JET_MEASURES'),
 'native_fixed_source_window_rate':('NativeWindowRate','ExpectedPhysicalRates','IndependentPhysicalWindowRates.expected_fixed_source','ACTUAL_CONTINUOUS_WINDOW_ALL_SOURCE_ORDERS_C_GT_ONE_THETA_ZERO_ALL_MULTIPLICITIES'),
 'native_slow_source_window_rate':('MovingSourceWindowRate','ExpectedPhysicalRates','IndependentPhysicalWindowRates.expected_slow_source','ARBITRARY_REAL_COFINAL_TIME_ORIGINAL_MS1_SCHEDULE_FINITE_NONPOSITIVE_PREFIX'),
 'fixed_two_factor_mask_rate_theta':('Consumers','ExpectedArithmeticPhysical','IndependentArithmeticPhysical.expected_literal_raw_high_mask','BOTH_COMPLETE_ACTUAL_FIXED_HIGH_MASK_REALIZATIONS_RAW_AND_ABSORBED'),
 'quiet_balanced_observation_implies_native_cut':('Consumers','ExpectedArithmeticPhysical','IndependentArithmeticPhysical.expected_quiet_full_original_domain','EXPLICIT_OPEN_ACTUAL_QUIET_ANTECEDENT_D0_ALL_POSITIVE_DAMPING_LITERAL_L2_NATIVE_CUT_CONDITIONAL_RH')}
status={'schema':'OPICA_STAGE20_NARROW_SOURCE_PINNED_V1','status':'PASS_NARROW_ONLY','checked_commit':HEAD,'checked_tree':TREE,'dirty_status_during_checks':'','source_unchanged':True,'roots':{},'runner':'runner/CHECK_RESULT.json','controls':'controls/CHECK_RESULT.json','printed_closures':closures,'local_control_counts':{'positive':2,'rejected_mutations':15},'historical_workflow_harvest':'../stage19/workflow/LATER_HARVEST.json','exact_new_head_CI':'NOT_INHERITED_FROM_OLD_HEAD','full_release_accepted':False,'aggregate_registration_accepted':False,'RH':'OPEN','Step4':'OPEN','independent_closing_inequalities':'OPEN'}
ledger_path=C/'ROOT_LEDGER_100.json';ledger=jread(ledger_path)
assert ledger['status_counts']=={ABSENT:9,HIST:41,NARROW:50}
original_contracts={r['full_name']:copy.deepcopy(r['contract']) for r in ledger['roots']}
for row in ledger['roots']:
    short=row['full_name'].split('.')[-1]
    if short in roots:
        module,consumer,expected,domain=roots[short]
        assert row['current_status']==ABSENT and expected in by[consumer]['axioms']
        source='Zeta23/OPICAFollowup/'+module+'.lean';assert row['path']==source
        assert re.search(r'\btheorem\s+'+re.escape(short)+r'\b',(R/source).read_text(encoding='utf-8'))
        row.update(current_status=NARROW,source_file_present=True,declaration_lexically_present=True,source_sha256=sha(R/source))
        row['gates']={'implementation':'IMPLEMENTED_FULL_FROZEN_CONTRACT_REVIEWED_NARROW','module_compilation':'PASS_EXACT_CLEAN_COMMIT_SOURCE_PINNED_COMPILER','expected_type_consumer':'PASS_INDEPENDENT_FULL_ORIGINAL_TYPE','actual_domain_consumer':'PASS_'+domain,'axiom_check':'STANDARD_ONLY_TRANSITIVE_PRINTED_CLOSURES','aggregate_current_source_export':'OPEN','full_release_acceptance':'OPEN'}
        row['evidence']=['evidence/current-codex/stage20/STATUS.json','evidence/current-codex/stage20/runner/CHECK_RESULT.json']
        row['independent_consumer']={'path':'consumers/'+consumer+'.lean','sha256':sha(C/'consumers'/(consumer+'.lean')),'expected_declaration':expected}
        row['statement_formalization']=row['contract']['statement_contract']+' Exact current physical/domain audit: '+domain+'. Original contracts unchanged; no synthetic substitute or caller-supplied conclusion.'
        status['roots'][row['full_name']]={'source':source,'source_sha256':row['source_sha256'],'consumer':row['independent_consumer'],'domain':domain,'status':'PROVED_NARROW_AGGREGATE_PENDING'}
    elif row['path']=='Zeta23/OPICAFollowup/Consumers.lean':
        prior={k:copy.deepcopy(row.get(k)) for k in ['source_sha256','gates','evidence','current_status']}
        row['source_sha256']=sha(R/row['path'])
        if row['current_status']==NARROW:
            consumer='ExpectedWordJet' if short=='step123_word_jet_consumer' else 'ExpectedForceSampling'
            assert consumer in by
            row.setdefault('revalidations',[]).append({'stage':20,'checked_commit':HEAD,'checked_tree':TREE,'source_sha256':row['source_sha256'],'status':'PASS_EXISTING_PRIMARY_NOT_ADDITIONAL_ROOT','consumer':consumer,'evidence':['evidence/current-codex/stage20/runner/CHECK_RESULT.json'],'historical_source_provenance':prior})
            row['gates']['module_compilation']='PASS_EXACT_CLEAN_COMMIT_STAGE20_REVALIDATION'
assert all(row['contract']==original_contracts[row['full_name']] for row in ledger['roots'])
counts=dict(sorted(Counter(row['current_status'] for row in ledger['roots']).items()));assert counts=={ABSENT:3,HIST:41,NARROW:56}
ledger['status_counts']=counts;vs=ledger['verification_summary'];assert not vs['current_aggregate_accepted'] and not ledger['current_aggregate_accepted']
vs.update(independently_verified_narrow_roots=56,open_no_complete_candidate_roots=3,receipt='STAGE20_HANDOVER.md',meaning='41 historical plus56 narrow roots is not aggregate97-root acceptance. Three original finite-span primaries and all full-integration/release gates remain OPEN; original100/28 contracts unchanged.')
vs['receipt_scope']='Six Stage20 original primaries, with retained word/jet and force/sampling revalidation; supporting audit declarations are not additional roots. Prior index: '+vs['receipt_scope']
vs['additional_stage20_primary_roots']=list(roots);vs['stage20_checked_source']={'commit':HEAD,'tree':TREE,'status':'evidence/current-codex/stage20/STATUS.json','runner':'evidence/current-codex/stage20/runner/CHECK_RESULT.json'}
jwrite(ledger_path,ledger);jwrite(E/'STATUS.json',status)
report=(S/'STAGE20_HANDOVER.template.md').read_text(encoding='utf-8').replace('{{RUNNER_RESULT}}',runner['status']).replace('{{CLOSURES}}',str(closures)).replace('{{CONTROL_RESULT}}',controls['status'])
assert '{{' not in report;(C/'STAGE20_HANDOVER.md').write_text(report,encoding='utf-8',newline='\n')
def edit(path,old,new):
    b=path.read_bytes();text=b.decode('utf-8').replace('\r\n','\n');assert text.count(old)==1,(path,old)
    text=text.replace(old,new)
    path.write_bytes(text.replace('\n','\r\n').encode('utf-8') if b'\r\n' in b else text.encode('utf-8'))
edit(R/'AGENTS.md','Fifty additional roots passed narrow gates and 9 original roots still lack\ncomplete implementations. Read the continuation STAGE19_HANDOVER.md (and the','Fifty-six additional roots passed narrow gates and 3 original roots still lack\ncomplete implementations. Read the continuation STAGE20_HANDOVER.md (and the')
p=C/'REMAINING_WORK.md';t=p.read_text(encoding='utf-8').replace('- 50: `PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`','- 56: `PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`').replace('- 9: `OPEN_NO_COMPLETE_CANDIDATE`','- 3: `OPEN_NO_COMPLETE_CANDIDATE`')
a=t.index('## 9 roots without complete candidate implementations');b=t.index('## Other unfinished gates',a)
t=t[:a]+'''## 3 roots without complete candidate implementations

### Zeta23.OPICAFollowup.FiniteSpanSeparation

- `finite_zero_span_positive_only_zero`
- `fixed_basis_negative_mass_budget`

### Zeta23.OPICAFollowup.Consumers

- `actual_zero_measure_span_consumer`

The [Stage20 handover](STAGE20_HANDOVER.md) records the six newly verified original jet, window-rate and physical-consumer roots, their exact source pin, independent full signatures and post-green research.

'''+t[b:]
t=t.replace('Implement the 9 absent roots above. Fifty roots now have narrow module,','Implement the 3 absent roots above. Fifty-six roots now have narrow module,')
(C/'REMAINING_WORK.md').write_text(t,encoding='utf-8',newline='\n')
p=C/'README.md';t=p.read_text(encoding='utf-8')
t=t.replace('The latest [Stage 19 handover](STAGE19_HANDOVER.md)','The preceding [Stage 19 handover](STAGE19_HANDOVER.md)',1)
t=t.replace('`REMAINING_WORK.md` lists the 9 absent proofs.','`REMAINING_WORK.md` lists the 3 absent proofs.').replace('- Fifty additional original roots','- Fifty-six additional original roots').replace('- 9 original primary implementations are still absent.','- 3 original primary implementations are still absent.').replace('Complete the 9 absent roots','Complete the 3 absent roots').replace('builds 21 candidate modules','builds 24 candidate modules').replace('28 explicit independent consumer files','31 explicit independent consumer files').replace('`consumers/`: 28 independent','`consumers/`: 31 independent').replace('the 21-module narrow replay','the 24-module narrow replay')
t='''> Latest: [Stage20](STAGE20_HANDOVER.md), checked code `9a8b2a4baee49f2056c7945b1544a7bc2893735b`, tree `6aa53d22d50d2aa24046d73b128c64a1d262f7f3`. The unchanged100-root ledger records41 historical +56 narrow +3 absent. Six original H2a/J5.2/MS1/Q3 roots now have clean full-type/domain/axiom evidence. Full release, RH and Step4 remain OPEN. Earlier stage descriptions below retain their historical scope.

'''+t
p.write_text(t,encoding='utf-8',newline='\n')
p=C/'DOCUMENTATION_INDEX.md';t=p.read_text(encoding='utf-8');t=t.replace('[STAGE19_HANDOVER.md](STAGE19_HANDOVER.md)','[STAGE20_HANDOVER.md](STAGE20_HANDOVER.md)',1)
t='''> Current source-pinned research report: [Stage20](STAGE20_HANDOVER.md). Read its exact theorem domains, controls, all-workflow provenance and novelty comparison before using older stage descriptions. Status:41 historical +56 narrow +3 absent; full release/RH/Step4 OPEN.

'''+t;p.write_text(t,encoding='utf-8',newline='\n')
p=C/'NEXT_AGENT_PROMPT.md';t=p.read_text(encoding='utf-8').replace('the latest [STAGE19_HANDOVER.md](STAGE19_HANDOVER.md)','the latest [STAGE20_HANDOVER.md](STAGE20_HANDOVER.md)',1).replace('`59ff485551771c0ab6322562d18fb8e9d4166da4`, tree `396665de3d14c2db60a4a85c646dd56d718f07ff` (Stage 19)','`'+HEAD+'`, tree `'+TREE+'` (Stage 20)',1).replace('41 historical, 50 narrow (`PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`) and 9 absent','41 historical, 56 narrow (`PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`) and 3 absent',1)
a=t.index('## The 9 absent roots, in a workable order');b=t.index('Then complete the release:',a)
t=t[:a]+'''## The 3 absent roots, in a workable order

1. `FiniteSpanSeparation.finite_zero_span_positive_only_zero`: every actual finite real combination nonnegative off the integer lattice is zero, and coordinates vanish on every specified independent actual real basis. Derive all measure/growth/selfdual/gap premises internally.
2. `FiniteSpanSeparation.fixed_basis_negative_mass_budget`: for each fixed independent actual real basis, prove a strictly positive constant times the coefficient Euclidean norm is bounded by global sinc-weighted negative mass. No uniform collision/growing-set constant.
3. `Consumers.actual_zero_measure_span_consumer`: instantiate actual zero profiles and all separator premises; do not assume measure status or the desired conclusion in a packet.

Stage20 closes full H2a actual jet independence, J5.2/MS1 continuous actual-source window rates and both physical rate/conditional quietness consumers. The quiet antecedent remains OPEN; its independent audit proves it equivalent to Θ=0 for these complete observations.

'''+t[b:];p.write_text(t,encoding='utf-8',newline='\n')
p=R/'research/RHRC/integration/opica_followup/README.md';t=p.read_text(encoding='utf-8');a=t.index('\n---\n')
t='''# Current draft checkpoint — 24 October 2026

Start at [the continuation guide](continuation/2026-10-22/README.md), root AGENTS.md,
[Stage20](continuation/2026-10-22/STAGE20_HANDOVER.md) and the [current ledger](continuation/2026-10-22/ROOT_LEDGER_100.json).
All100 original primary roots and28 acceptance units remain required.

The ledger records41 historical source-bound roots,56 additional narrow roots and3 absent implementations. This is not aggregate97-root acceptance. Stage20 verifies the original full confluent determinant, actual zero-jet independence, fixed/slow original-source window rates, both actual fixed high-mask rates and the conditional complete-observation quietness consumer.

Checked code `'''+HEAD+'''`, tree `'''+TREE+'''`. Read [STATUS](continuation/2026-10-22/evidence/current-codex/stage20/STATUS.json) and the handover for exact source/type/domain/axiom evidence, rejected mutations, complete old-head workflow dispositions and the post-green mathematical/novelty assessment. The existing word/jet and force/sampling consumers are revalidated at the changed source hash. Supporting audit lemmas do not add primaries.

The cold full100 receipt, genuine independent review, parent extension, registration, canonical regeneration and complete exact-head workflow harvest remain OPEN. Full release, RH, Step4 and independent closing inequalities remain OPEN. The following preserved baseline narrative retains its historical scope; use the current ledger for moving status.
'''+t[a:];p.write_text(t,encoding='utf-8',newline='\n')
put(S/'run_clean_controls.py',E/'run_clean_controls.py')
jwrite(E/'RECORD_CHANGE_SUMMARY.json',{'checked_commit':HEAD,'promoted_original_roots':list(roots),'frozen_contracts_unchanged':True,'protected_graph_sha256':sha(R/'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md'),'current_aggregate_accepted':False,'status_counts':counts,'supporting_not_primary':['complete_quiet_upper_iff_zero_supremum','finite_quiet_samples_do_not_supply_cofinal_upper','all normalization/domain controls']})
print(json.dumps({'status':'RECORDED_NARROW_ONLY','counts':counts,'closures':closures,'code_commit':HEAD,'handover_sha256':sha(C/'STAGE20_HANDOVER.md')},indent=2))
