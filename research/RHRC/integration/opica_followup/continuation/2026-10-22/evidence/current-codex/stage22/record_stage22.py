"""Preserve exact Stage22 narrow proof evidence; never grant full acceptance."""
from pathlib import Path
from collections import Counter
import copy, gzip, hashlib, io, json, re, subprocess, tarfile

S=Path(__file__).resolve().parent; W=S.parent; R=W/'opica-followup-repo'
C=R/'research/RHRC/integration/opica_followup/continuation/2026-10-22'
E=C/'evidence/current-codex/stage22'
HEAD='2440dcde7607baa7bcff2ce9626effa1ae9f3f07'
TREE='dee5bc2fa3148ad42e3ef1fef17c4acf6a408f99'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a): return subprocess.check_output(['git',*a],cwd=R,text=True).strip()
def read(p): return json.loads(p.read_bytes())
def write(p,d):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8',newline='\n')
def put(p,q,compress=False):
    assert p.is_file() and not q.exists(),(p,q)
    q.parent.mkdir(parents=True,exist_ok=True)
    q.write_bytes(gzip.compress(p.read_bytes(),mtime=0) if compress else p.read_bytes())

assert git('rev-parse','HEAD')==HEAD and git('rev-parse','HEAD^{tree}')==TREE
assert not git('status','--porcelain') and not E.exists()
assert sha(R/'research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json')=='2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41'
assert sha(R/'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md')=='de9aabe7985f839c39b62e82c3407c97bc21d831e283199ab5d81784fe68f327'
runner=read(S/'clean-runner/CHECK_RESULT.json')
controls=read(S/'clean-controls/CHECK_RESULT.json')
workflow=read(S/'clean-workflow-consumers/CHECK_RESULT.json')
native=read(S/'record-validation/native/summary.json')
linux=read(S/'record-validation/linux/summary.json')
warm=read(S/'warm-export-smoke-rooted/SUMMARY.json')
assert warm['status']=='PASS_UNACCEPTED_WARM_EXPORT_PARSER_ONLY' and warm['checked_source']['checked_commit']==HEAD
assert warm['source_unchanged'] and warm['declared_root_queries']==100
assert runner['status']=='PASS_NARROW_ONLY' and runner['head']==HEAD and runner['tree']==TREE
assert runner['dirty_status']=='' and runner['source_unchanged']
assert len(runner['consumers'])==44
closures=sum(len(c['axioms']) for c in runner['consumers'])
assert closures==311,closures
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for c in runner['consumers'] for a in c['axioms'].values())
assert controls['status']=='PASS_CONTROLS_ONLY' and controls['checked_commit']==HEAD and controls['checked_tree']==TREE and controls['source_unchanged']
assert all(c['passed'] for c in controls['controls'])
assert workflow['status']=='PASS_NARROW_WORKFLOW_CONSUMERS_ONLY' and workflow['checked_commit']==HEAD and workflow['checked_tree']==TREE and workflow['source_unchanged']
assert sum(r['printed_closures'] for r in workflow['consumers'])==66
assert native['status']=='PASS_TESTS_AND_FROZEN_REPLAY_ONLY' and native['source_before']==native['source_after']
assert linux['status']=='PASS_FOCUSED_PARENT_TESTS_ONLY' and linux['source_hashes_unchanged']
for row in native['commands']:
    t=(S/'record-validation/native'/row['log']).read_text(encoding='utf-8',errors='replace')
    assert row['exit_code']==0
    if row['name'].startswith('child-'): assert 'Ran 228 tests' in t and '\nOK\n' in t
for row in linux['commands']:
    t=(S/'record-validation/linux'/row['log']).read_text(encoding='utf-8',errors='replace')
    assert row['exit_code']==0 and 'Ran 82 tests' in t and '\nOK\n' in t and 'skipped=' not in t
snapshot=read(S/'clean-runner/source-before.json')
archive=subprocess.check_output(['git','archive',HEAD,'Zeta23','lean-toolchain','lake-manifest.json','lakefile.toml','research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers'],cwd=R)
with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
    committed={m.name:hashlib.sha256(tf.extractfile(m).read()).hexdigest() for m in tf if m.isfile()}
for p,h in snapshot.items(): assert committed[p]==h==sha(R/p),p
for row in runner['commands']: assert row['exit_code']==0 and sha(S/'clean-runner'/row['log'])==row['log_sha256']
for directory,target in [('clean-runner','runner'),('clean-controls','controls'),('clean-workflow-consumers','workflow-consumers')]:
    for p in sorted((S/directory).rglob('*')):
        if p.is_file():
            rel=p.relative_to(S/directory)
            compress=p.name in {'build.log','source-before.json'}
            q=E/target/rel
            if compress:q=q.with_name(q.name+'.gz')
            put(p,q,compress)
for p in (S/'record-validation').rglob('*'):
    if p.is_file() and not any(x.startswith('temp') for x in p.relative_to(S/'record-validation').parts):
        put(p,E/'python'/p.relative_to(S/'record-validation'))
for directory in ['precommit-consumers','precommit-consumers-offcritical-qualified','precommit-final-support']:
    for p in (S/directory).glob('*'):
        if p.is_file():put(p,E/'development'/directory/p.name)
for p in S.glob('production-*.log'):put(p,E/'development'/(p.name+'.gz'),True)
for directory,target in [('warm-export-smoke','development/exporter-no-root-failure'),('warm-export-smoke-rooted','warm-export')]:
    for p in (S/directory).iterdir():
        if p.is_file() and p.suffix!='.olean':
            compress=p.name in {'bindings.log','compiler-export.json'}
            q=E/target/(p.name+('.gz' if compress else ''))
            put(p,q,compress)
for p in S.glob('LINUX_*.json'):put(p,E/'linux-runtime'/p.name)
put(S/'linux-cache-get.log',E/'linux-runtime/linux-cache-get.log.gz',True)
for p in (S/'warm-registry-review').glob('*'):
    if p.is_file():put(p,E/'unregistered-review-proposal'/p.name)
for p in S.glob('*INSTALL.json'):put(p,E/'implementation'/p.name)
for name in ['OWNER_INSTALL.json','RUNTIME_INSTALL.json','OFFCRITICAL_AUDIT_QUALIFICATION.json','NEARGAP_SUPPORT_INSTALL.json','code-preflight.json']:
    p=S/name
    if p.exists() and not (E/'implementation'/name).exists():put(p,E/'implementation'/name)

bundles=[
 ('audit-release/OPICA_STAGE22_CANONICAL_VALIDATION_PROPOSAL_2026-10-24.zip','canonical/OPICA_STAGE22_CANONICAL_VALIDATION_PROPOSAL_2026-10-24.zip'),
 ('audit-square-physical/SEALED_SQUARE_PHYSICAL_2026-10-24.zip','square/SEALED_SQUARE_PHYSICAL_2026-10-24.zip'),
 ('audit-tempered-lattice/SEALED_TEMPERED_LATTICE_2026-10-24.zip','square/SEALED_TEMPERED_LATTICE_2026-10-24.zip'),
 ('audit-runtime-proposal/OPICA_PLANNED_RUNTIME_PROPOSAL_2026-10-24.zip','runtime/OPICA_PLANNED_RUNTIME_PROPOSAL_2026-10-24.zip'),
 ('audit-ct13/OPICA_CT13_SINC_BUDGET_2026-10-24.zip','near-gap/OPICA_CT13_SINC_BUDGET_2026-10-24.zip'),
 ('audit-independent-expected-types/HT2_COMPACT_CONTINUOUS_EXTRACTION_2026-10-24.zip','near-gap/HT2_COMPACT_CONTINUOUS_EXTRACTION_2026-10-24.zip')]
for p,q in bundles:put(W/p,E/'support'/q)
for p in (W/'audit-finite-span').glob('*FINITE_POSITIVE_TEST*'):
    if p.is_file():put(p,E/'support/post-green'/p.name)
for directory,target in [('audit-independent-contract-review/stage22','independent-review/stage22'),('audit-independent-contract-review/after-bridge','independent-review/after-bridge'),('audit-independent-contract-review/independent-types','independent-review/independent-types'),('audit-independent-contract-review/ht2-ct13','independent-review/ht2-ct13')]:
    for p in (W/directory).rglob('*'):
        if p.is_file() and p.suffix not in {'.olean','.pyc'}:
            put(p,E/'support'/target/p.relative_to(W/directory))
for directory,target in [('audit-independent-expected-types','independent-expected-types'),('audit-offcritical-real-basis','offcritical-real-basis'),('audit-independent-complex-mobius','independent-complex-mobius')]:
    for p in (W/directory).glob('*'):
        if p.is_file() and p.suffix in {'.lean','.json','.md','.log','.txt'}:
            put(p,E/'support'/target/p.name)
for directory in ['export2440','complex-mobius-review']:
    for p in (W/'audit-independent-full-review'/directory).rglob('*'):
        if p.is_file() and p.suffix not in {'.olean','.pyc'}:
            q=E/'support/independent-review/full-review-preparation'/directory/p.relative_to(W/'audit-independent-full-review'/directory)
            compress=p.stat().st_size>1024*1024
            if compress:q=q.with_name(q.name+'.gz')
            put(p,q,compress)
for name in ['record_stage22.py','run_clean_controls.py','replay_clean_workflow_consumers.py','validate_record_native.py','validate_record_linux.py']:
    put(S/name,E/name)
for p in (W/'opica-stage22-control-proposal').rglob('*'):
    if p.is_file() and '__pycache__' not in p.parts and p.suffix not in {'.pyc','.olean'}:
        put(p,E/'support/control-proposal'/p.relative_to(W/'opica-stage22-control-proposal'))

ledger=read(C/'ROOT_LEDGER_100.json')
contracts={r['full_name']:copy.deepcopy(r['contract']) for r in ledger['roots']}
old_counts=copy.deepcopy(ledger['status_counts'])
for row in ledger['roots']:
    p=R/row['path']; old=row.get('source_sha256'); now=sha(p)
    row['source_sha256']=now
    row.setdefault('revalidations',[]).append({'stage':22,'checked_commit':HEAD,'checked_tree':TREE,
        'source_sha256':now,'prior_source_sha256':old,'status':'PASS_MODULE_AND_EXPLICIT_CONSUMER_REVALIDATION_NOT_AGGREGATE',
        'evidence':['evidence/current-codex/stage22/runner/CHECK_RESULT.json'],
        'root_count_delta':0,'full_release_acceptance':False})
    if row['path'].endswith('/SquareDefect.lean'):
        row['full_contract_followup']={'status':'MATHEMATICAL_DOMAIN_FINDINGS_CLOSED_NARROW_SOURCE_PINNED_REVIEW_FULL_EXPORT_PENDING',
            'review':'evidence/current-codex/stage22/support/independent-review/after-bridge/BRIDGE_REVIEW_ADDENDUM.md',
            'actual_measure_and_distribution_tempered_domain':True,'full_release_acceptance':False}
assert all(r['contract']==contracts[r['full_name']] for r in ledger['roots'])
assert ledger['status_counts']==old_counts==dict(sorted(Counter(r['current_status'] for r in ledger['roots']).items()))
vs=ledger['verification_summary']
vs.update(receipt='STAGE22_HANDOVER.md',full_original_contract_audit='INDEPENDENT_MATHEMATICAL_FINDINGS_CLOSED_FULL_SOURCE_TYPE_EXPORT_SEAL_PENDING',
    meaning='41 historical +59 narrow original roots; Stage22 closes physical/canonical/continuous-compact domain findings at exact source. Full aggregate acceptance and registered-source export remain OPEN.',
    stage22_checked_source={'commit':HEAD,'tree':TREE,'status':'evidence/current-codex/stage22/STATUS.json'})
assert not ledger['current_aggregate_accepted'] and not vs['current_aggregate_accepted']
write(C/'ROOT_LEDGER_100.json',ledger)
status={'schema':'OPICA_STAGE22_FULL_DOMAIN_NARROW_SOURCE_PINNED_V1','status':'PASS_NARROW_ONLY',
    'checked_commit':HEAD,'checked_tree':TREE,'dirty_status_during_checks':'','source_unchanged':True,
    'primary_count_delta':0,'original_root_counts':old_counts,'modules':28,'consumers':44,'standard_axiom_closures':closures,
    'runner':'runner/CHECK_RESULT.json','controls':'controls/CHECK_RESULT.json','control_source_files':len(controls['controls']),
    'workflow_consumers':'workflow-consumers/CHECK_RESULT.json','retained_workflow_closures':66,
    'protocol_tests_per_mode':228,'parent_Linux_tests_per_mode':82,'parent_skips':0,
    'frozen_exact_checks_per_mode':[5112,18862,14672,1274],'numeric_authority':'CONSISTENCY_ONLY',
    'closed_mathematical_findings':['canonical_seven_definitions','actual_square_Jordan_adapter','arbitrary_distribution_tempered_compact_compatible_lattice_domain','seven_independently_written_full_expected_types','HT2_continuous_compact_measure_topology'],
    'supporting_results':['actual_offcritical_canonical_real_pair_independence_and_budget','exact_CT13_sinc_budget_slope_and_quadratic_divergence'],
    'warm_full100_export':warm,'accepted_cold_source_type_dependency_export':'OPEN','full_review_seal':'UNSET','aggregate_registration_accepted':False,
    'full_release_accepted':False,'independent_human_review':'NOT_ESTABLISHED','RH':'OPEN','Step4':'OPEN','independent_closing_inequalities':'OPEN'}
write(E/'STATUS.json',status)
report=(S/'STAGE22_HANDOVER.template.md').read_text(encoding='utf-8').replace('{{CLOSURES}}',str(closures)).replace('{{PROTOCOL_RESULT}}','228/228 child tests in both modes; 82/82 real-Linux parent fixtures in both modes with no skips; frozen 5,112/18,862/14,672/1,274 exact checks per mode and three numerical suites')
assert '{{' not in report
(C/'STAGE22_HANDOVER.md').write_text(report,encoding='utf-8',newline='\n')
for p in [R/'AGENTS.md',C/'README.md',C/'DOCUMENTATION_INDEX.md',C/'NEXT_AGENT_PROMPT.md',C/'REMAINING_WORK.md',R/'research/RHRC/integration/opica_followup/README.md']:
    raw=p.read_bytes(); t=raw.decode('utf-8').replace('\r\n','\n')
    if p.name=='AGENTS.md':t=t.replace('Read the continuation STAGE21_HANDOVER.md','Read the continuation STAGE22_HANDOVER.md',1).replace('the nine repaired modules','all28 continuation modules',1)
    elif p.name=='REMAINING_WORK.md':
        t='# Remaining work\n\nOriginal100 roots /28 units unchanged:41 historical +59 narrow +0 absent bodies. [Stage22](STAGE22_HANDOVER.md) pins code `'+HEAD+'`, tree `'+TREE+'`. The full physical/canonical and HT2 continuous-compact findings are closed by actual Lean proofs and nonauthor mathematical review. This is not aggregate acceptance.\n\nRemaining release work: full100 cold source/type/constructor/private-dependency export; independently reviewed source/type/registry seal; exact parent-extension amendment and actual P0 intake/current-child replay; registry and class/dependency extension; unchanged canonical62-product generation; real runtime/canonical/workflow companion validation and all-job exact-head harvest. Preserve original contracts, historical evidence and all OPEN claims.\n\nThe unchanged Windows symbolic-link cold-isolation gate fails with actual WinError1314. Any separate junction diagnostic remains explicitly UNACCEPTED. Do not relabel its protocol or set a review seal from producer digests. Agent semantic review does not invent human approval. RH,Step4 and independent closing inequalities remain OPEN.\n\nHighest mathematical information gain: quantify actual source-dependent offcritical real-pair coercivity versus observation recovery cost, retaining height and multiplicity; attack uniform/growing-basis extensions using the real-node boundary and exact CT1.3 linear budget before building around them.\n'
    else:
        prefix='continuation/2026-10-22/' if p.parent.name=='opica_followup' else ''
        t='> Current checkpoint: [Stage22]('+prefix+'STAGE22_HANDOVER.md), checked code `'+HEAD+'`, tree `'+TREE+'`. All100 original bodies have historical/narrow evidence. Physical/canonical and continuous-compact domain findings are mathematically closed; full export, registry, parent extension, canonical and release acceptance remain OPEN. Earlier statements retain their historical scope.\n\n'+t
        if p.name=='NEXT_AGENT_PROMPT.md':t=t.replace('the latest [STAGE21_HANDOVER.md](STAGE21_HANDOVER.md)','the latest [STAGE22_HANDOVER.md](STAGE22_HANDOVER.md)',1)
    p.write_bytes(t.replace('\n','\r\n').encode() if b'\r\n' in raw else t.encode())
print(json.dumps({'status':'RECORDED_NARROW_ONLY','checked_commit':HEAD,'closures':closures,'controls':len(controls['controls']),'handover_sha256':sha(C/'STAGE22_HANDOVER.md')},indent=2))
