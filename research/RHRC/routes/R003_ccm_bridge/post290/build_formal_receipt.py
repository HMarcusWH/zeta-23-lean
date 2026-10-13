"""Build exact component type/axiom receipts from the existing Lean resolver."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
AUDIT = REPO / 'Zeta23/RHRC/Step123OutputBindings.lean'
ALLOW = {'propext','Classical.choice','Quot.sound'}

def build(log):
    roots = dict(re.findall(r'\(``([\w.]+),\s*"([\w.]+)"\)', AUDIT.read_text()))
    if not roots:
        raise ValueError('component binding scope empty')
    types, axioms = {}, {}
    for line in log.read_text(encoding='utf-8-sig').splitlines():
        if line.startswith('RHRC_CANDIDATE_RESULT\t'):
            fields = line.split('\t')
            if len(fields) != 10 or fields[2] != 'RESOLVED_UNIQUE' or fields[3] != '1':
                raise ValueError('compiler did not uniquely resolve an exact root')
            source_id, name, module, kind, internal, type_text = fields[1],fields[4],fields[5],fields[6],fields[7],fields[8]
            if name != source_id or roots.get(name) != module or kind != 'THEOREM' or internal != '0':
                raise ValueError('compiler binding identity/kind mismatch')
            if name in types or not type_text:
                raise ValueError('duplicate or empty compiler type')
            types[name] = type_text
        elif line.startswith('POST290_AXIOMS\t'):
            _,name,values = line.split('\t')
            footprint = set(filter(None, values.split(',')))
            if name in axioms or not footprint <= ALLOW:
                raise ValueError('duplicate or unadmitted axiom report')
            axioms[name] = sorted(footprint)
    if set(types) != set(roots) or set(axioms) != set(roots):
        raise ValueError('incomplete type or axiom receipt')
    git = lambda *args: subprocess.check_output(['git',*args],cwd=REPO,text=True).strip()
    head,tree = git('rev-parse','HEAD'),git('rev-parse','HEAD^{tree}')
    sources = sorted({module.replace('.','/')+'.lean' for module in roots.values()} | {'Zeta23/RHRC/Step123OutputBindings.lean'})
    if git('diff','HEAD','--',*sources):
        raise ValueError('compiled source tree has local modifications')
    declarations = [{'theorem':name,'module':roots[name],'source_tree':tree,'authority':'PROVED',
        'normalized_type':types[name],'normalized_type_sha256':hashlib.sha256(types[name].encode()).hexdigest(),
        'normalization':'existing RHRC compiler pretty-type field, not a prose-derived type',
        'axioms':axioms[name],'axiom_audit_pass':True} for name in sorted(roots)]
    return {'schema_version':'RH_POST290_COMPONENT_COMPILER_RECEIPT_1.0',
        'execution_status':'SUCCESS','integrity_status':'PASS','scientific_disposition':'PARTIAL_OUTPUT_RH_OPEN',
        'claim_cap':'RH_OPEN','head':head,'source_tree':tree,
        'compiler_log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
        'declarations':declarations,'producer_complete':False,'independent_assumption_review_pass':False,
        'scope':'Compiled supporting components only; no filled Step123 output producer or RH sufficiency wrapper.',
        'source_blobs':[{'path':path,'git_blob':git('rev-parse',head+':'+path)} for path in sources]}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--log',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    args = p.parse_args()
    result = build(args.log)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'head':result['head'],'declarations':len(result['declarations']),
                      'scientific_disposition':result['scientific_disposition']}))
