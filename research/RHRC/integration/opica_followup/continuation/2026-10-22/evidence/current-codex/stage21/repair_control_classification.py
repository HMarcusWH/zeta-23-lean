"""Repair a tool-output parser, preserving its original FAIL and compiler evidence."""
from pathlib import Path
import hashlib,json,re,subprocess
S=Path(__file__).resolve().parent;R=S.parent/'opica-followup-repo';O=S/'clean-controls'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=O/'CHECK_RESULT.json';original=p.read_bytes();data=json.loads(original)
assert data['status']=='FAIL' and data['source_unchanged']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()==data['checked_commit']
assert not subprocess.check_output(['git','status','--porcelain'],cwd=R,text=True).strip()
failed=[r for r in data['controls'] if not r['passed']]
assert len(failed)==1 and failed[0]['name']=='NegativeBudgetIndependenceFinal'
for row in data['controls']:
    assert sha(O/row['file'])==row['source_sha256'] and sha(O/row['log'])==row['log_sha256']
for rel,h in json.loads((O/'source-before.json').read_bytes()).items():assert sha(R/rel)==h
row=failed[0];log=(O/row['log']).read_text(encoding='utf-8')
assert row['exit_code']!=0 and re.search(r'\berror(?:\([^)]+\))?:',log)
assert 'error(lean.invalidField): Invalid field `choose`' in log and 'LinearIndependent' in log
assert not any(x in log for x in ['unknown module','unknown identifier','invalid import','object file','sorryAx'])
old=O/'INITIAL_PARSER_RESULT.json';assert not old.exists();old.write_bytes(original)
row.update(observed='REJECTED_INTENDED_MUTATION',passed=True)
data['status']='PASS_CONTROLS_ONLY'
data['classification_repair']={'original_result':'INITIAL_PARSER_RESULT.json','original_result_sha256':sha(old),'compiler_rerun':False,'compiler_logs_changed':False,'reason':'Lean renders this genuine missing-independence argument failure as error(lean.invalidField):, while the first parser only recognized error:. The original compiler exit1 and exact log are retained. This repairs classification only.','accepted_error_pattern':r'\berror(?:\([^)]+\))?:','reviewed_expected_failure':'Applying .choose to the still-conditional function LinearIndependent → exists c; the required independence argument was deliberately omitted.'}
p.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
print(data['status'],sha(p))
