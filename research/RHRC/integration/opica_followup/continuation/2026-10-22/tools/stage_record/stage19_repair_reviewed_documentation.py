from pathlib import Path
import hashlib,json,subprocess
S=Path(__file__).resolve().parent;R=S.parent/'opica-followup-repo';C=R/'research/RHRC/integration/opica_followup/continuation/2026-10-22'
relative='research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md';target=R/relative
raw=subprocess.check_output(['git','show','59ff485551771c0ab6322562d18fb8e9d4166da4:'+relative],cwd=R)
assert hashlib.sha256(raw).hexdigest()=='de9aabe7985f839c39b62e82c3407c97bc21d831e283199ab5d81784fe68f327'
assert hashlib.sha256(target.read_bytes()).hexdigest()=='b89d8082f72f68a5f25818e031dc6b91cba2331ecc2d036ad4d04a3de7afc30a'
target.write_bytes(raw)
# Preserve the original applied plan as history, but make the reusable updater
# obey the parent's independent seven-document seal on any future replay.
for p in (S/'update_stage19_records.py',C/'tools/stage_record/stage19_update_stage19_records.py'):
    t=p.read_text(encoding='utf-8')
    marker='\n\ndef main() -> int:'
    assert t.count(marker)==1
    t=t.replace(marker,"\n\n# Parent documentation bytes have their own fixed review seal. The continuation\n# inventory cannot authorize edits to this manual graph. Preserve the draft\n# edit data above as provenance; exclude it from the executable record plan.\nSEALED_MANUAL_GRAPH = 'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md'\nDOC_EDIT_DATA['edits'] = [e for e in DOC_EDIT_DATA['edits'] if e['path'] != SEALED_MANUAL_GRAPH]\nDOC_EDIT_DATA['allowed_document_paths'] = [p for p in DOC_EDIT_DATA['allowed_document_paths'] if p != SEALED_MANUAL_GRAPH]\n"+marker)
    old="    old_mermaid = re.findall(r'```mermaid\\n.*?\\n```', old_docs[manual], re.S)\n    new_mermaid = re.findall(r'```mermaid\\n.*?\\n```', new_docs[manual], re.S)\n    require(old_mermaid == new_mermaid, 'Manual navigation arrows changed')"
    new="    require(sha(repo / manual) == DOC_EDIT_DATA['expected_input_sha256'][manual],\n            'Independently sealed manual graph bytes changed; continuation inventory cannot repin them')"
    assert t.count(old)==1
    p.write_text(t.replace(old,new),encoding='utf-8',newline='\n')
repair={'schema':'OPICA_STAGE19_DOCUMENTATION_REPAIR_V1','trigger':'Parent DocumentationReview.test_exact_seven_reviewed_files_pass failed after manual navigation edit',
        'action':'Restored exact59ff committed manual graph bytes; no parent validator, review hash, protected-state object or test changed',
        'path':relative,'restored_sha256':hashlib.sha256(raw).hexdigest(),
        'failed_log':'record-validation-initial/linux/normal.log','mathematical_source_changes':[],
        'original_applied_plan_preserved':True,'required_followup':'Rerun both complete unmodified parent test modes'}
repair['RH']='OPEN';repair['Step4']='OPEN'
(S/'DOCUMENTATION_REPAIR.json').write_text(json.dumps(repair,indent=2)+'\n',encoding='utf-8')
p=C/'STAGE19_HANDOVER.md';t=p.read_text(encoding='utf-8')
needle='## Workflow harvest\n'
paragraph='''The first record-phase parent suite rejected an edit to the manual graph page: its seven reviewed documentation files have a separate fixed byte seal. The graph page was restored byte-for-byte to the checked source. No parent validator, review table, protected-state object or test was changed. The failed log is retained, and both full parent modes are rerun after the repair. Current findings remain in this dated report and the moving ledger; the historical manual graph retains its reviewed scope.\n\n'''
assert t.count(needle)==1;p.write_text(t.replace(needle,paragraph+needle),encoding='utf-8',newline='\n')
print(json.dumps(repair,indent=2))
