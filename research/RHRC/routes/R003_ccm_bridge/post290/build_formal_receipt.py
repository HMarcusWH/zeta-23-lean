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
KIND_CROSSWALK=REPO/'research/RHRC/integration/post290/review_execution_2026-10-14/spec/API_CROSSWALK.json'
KIND_BLOB_SHA1='254e2c4a8ad05bd1647c2175d86472755c795c41'
OUTPUT_FIELD_CONTRACT=REPO/'research/RHRC/integration/post290/review_execution_2026-10-14/spec/OUTPUT_FIELD_CONTRACT.json'
OUTPUT_FIELD_BLOB_SHA1='201cc611cd19bcc33c3a1b0f9e7983d9e2bb35a8'



def compiler_records(text,roots,head,tree,expected_kinds=None):
    if not roots:raise ValueError('empty compiler root scope')
    if expected_kinds is None:expected_kinds={name:'THEOREM' for name in roots}
    if set(expected_kinds)!=set(roots) or not set(expected_kinds.values())<={'THEOREM','DEFINITION','INDUCTIVE'}:
        raise ValueError('invalid exact source-kind inventory')
    types,axioms={},{}
    contexts=[]
    for line in text.splitlines():
        if line.startswith('POST290_COMPILER_CONTEXT\t'):
            fields=line.split('\t')
            if len(fields)!=3:raise ValueError('malformed compiler source context')
            contexts.append(tuple(fields[1:]))
        elif re.search(r'(?:^|:\d+:\d+:\s*)error:',line):
            raise ValueError('compiler log contains a failed check')
        elif line.startswith('RHRC_CANDIDATE_RESULT\t'):
            fields=line.split('\t')
            if len(fields)!=10 or fields[2]!='RESOLVED_UNIQUE' or fields[3]!='1':
                raise ValueError('compiler did not uniquely resolve an exact root')
            source_id,name,module,kind,internal,type_text=fields[1],fields[4],fields[5],fields[6],fields[7],fields[8]
            if name!=source_id or roots.get(name)!=module or kind!=expected_kinds.get(name) or internal!='0':
                raise ValueError('compiler binding identity/kind mismatch')
            if name in types or not type_text:raise ValueError('duplicate or empty compiler type')
            types[name]=type_text
        elif line.startswith('POST290_AXIOMS\t'):
            fields=line.split('\t')
            if len(fields)!=3:raise ValueError('malformed axiom report')
            _,name,values=fields
            footprint=set(filter(None,values.split(',')))
            if name in axioms or not footprint<=ALLOW:raise ValueError('duplicate or unadmitted axiom report')
            axioms[name]=sorted(footprint)
    if contexts!=[(head,tree)]:raise ValueError('stale, missing or duplicated compiler head/tree context')
    if set(types)!=set(roots) or set(axioms)!=set(roots):raise ValueError('incomplete type or axiom receipt')
    return types,axioms

def audit_roots(text):
    entries=re.findall(r'\(``([\w.\']+),\s*"([\w.]+)",\s*"([A-Z]+)"\)',text)
    if not entries:
        raise ValueError('component binding scope empty')
    kind_map={'THEOREM':'THEOREM','DEF':'DEFINITION','INDUCTIVE':'INDUCTIVE'}
    if len({name for name,_,_ in entries})!=len(entries):
        raise ValueError('duplicate exact source root')
    if any(kind not in kind_map for _,_,kind in entries):
        raise ValueError('unknown exact source kind')
    if len(re.findall(r'\(``',text))!=len(entries):
        raise ValueError('source root missing explicit kind')
    return ({name:module for name,module,_ in entries},
            {name:kind_map[kind] for name,_,kind in entries})


def load_frozen_json(path, git_blob_sha):
    raw=path.read_bytes().replace(b'\r\n',b'\n')
    framed=b'blob '+str(len(raw)).encode()+b'\0'+raw
    if hashlib.sha1(framed).hexdigest()!=git_blob_sha:
        raise ValueError('reviewed public source/field contract hash mismatch: '+str(path))
    return json.loads(raw)

def independent_complete_review(review_file, roots, kinds, head, tree):
    if review_file is None:
        raise ValueError('complete-output mode requires a separately supplied independent semantic review')
    api=load_frozen_json(KIND_CROSSWALK,KIND_BLOB_SHA1)
    requested={r['requested_name']:r['required_kind'] for r in api['rows']}
    if len(requested)!=99 or len(api['rows'])!=99:
        raise ValueError('mandatory public API census not 99 unique exports')
    normalized={'THEOREM':'THEOREM','DEFINITION':'DEFINITION',
                'INDUCTIVE':'INDUCTIVE','STRUCTURE':'INDUCTIVE'}
    if set(roots)<set(requested):
        missing=sorted(set(requested)-set(roots))
        raise ValueError('complete producer missing exact compiler roots: '+','.join(missing))
    if any(kinds[name]!=normalized[kind] for name,kind in requested.items()):
        raise ValueError('complete producer public roots have incorrect Lean declaration kinds')
    contract=load_frozen_json(OUTPUT_FIELD_CONTRACT,OUTPUT_FIELD_BLOB_SHA1)
    ids=[f['id'] for f in contract['field_groups']]
    if len(ids)!=44 or len(set(ids))!=44:
        raise ValueError('mandatory 44-field specification altered')
    raw=review_file.read_bytes()
    evidence=json.loads(raw)
    if (evidence.get('schema_version')!='POST290_INDEPENDENT_SEMANTIC_REVIEW_1.0' or
        evidence.get('reviewed_head')!=head or evidence.get('reviewed_tree')!=tree or
        evidence.get('independent_assumption_review_pass') is not True or
        evidence.get('reviewer_identity') in (None,'','SELF','AUTOMATED') or
        evidence.get('external_review_reference') in (None,'') or
        evidence.get('reviewer_is_source_author') is not False):
        raise ValueError('independent source/axiom/provenance review missing or inapplicable')
    reviews=evidence.get('field_reviews')
    if not isinstance(reviews,list) or len(reviews)!=44:
        raise ValueError('44 independent source-output field reviews required')
    review_ids=[row.get('id') for row in reviews]
    if set(review_ids)!=set(ids) or len(set(review_ids))!=44:
        raise ValueError('reviewed field identities mismatch frozen output contract')
    for field in reviews:
        claim=field.get('declaration_ref')
        if (field.get('semantic_proof_review')!='PASS' or
            field.get('evidence_verified') is not True or
            not isinstance(claim,str) or claim not in roots or
            not isinstance(field.get('reason'),str) or not field['reason']):
            raise ValueError('unproved or unsupported field in complete-output review: '+str(field.get('id')))
    return hashlib.sha256(raw).hexdigest()

def build(log,mode='component',independent_review=None):
    if mode not in {'component','complete-output'}:raise ValueError('unknown receipt mode')
    roots,kinds=audit_roots(AUDIT.read_text())
    git = lambda *args: subprocess.check_output(['git',*args],cwd=REPO,text=True).strip()
    head,tree = git('rev-parse','HEAD'),git('rev-parse','HEAD^{tree}')
    types,axioms=compiler_records(log.read_text(encoding='utf-8-sig'),roots,head,tree,kinds)
    sources = sorted({module.replace('.','/')+'.lean' for module in roots.values()} | {'Zeta23/RHRC/Step123OutputBindings.lean'})
    if git('status','--porcelain','--untracked-files=all','--','*.lean','lean-toolchain','lake-manifest.json','lakefile.lean','lakefile.toml'):
        raise ValueError('compiled source tree has local modifications')
    package_manifest=json.loads((REPO/'lake-manifest.json').read_text())
    mathlib=[p for p in package_manifest['packages'] if p['name']=='mathlib']
    if len(mathlib)!=1:raise ValueError('missing exact Mathlib package revision')
    packages=[]
    for package in package_manifest['packages']:
        if package.get('type')!='git':raise ValueError('untracked package source type')
        location=REPO/package_manifest['packagesDir']/package['name']
        actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=location,text=True).strip()
        dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=all','--','*.lean','lean-toolchain','lake-manifest.json','lakefile.lean','lakefile.toml'],cwd=location,text=True).strip()
        if actual!=package['rev'] or dirty:raise ValueError('wrong or modified Lean dependency: '+package['name'])
        packages.append({'package':package['name'],'revision':actual,'lean_source_clean':True})
    compiler_version=subprocess.check_output(['lake','env','lean','--version'],cwd=REPO,text=True).strip()
    declared=(REPO/'lean-toolchain').read_text().strip()
    if 'version '+declared.rsplit(':v',1)[-1] not in compiler_version:raise ValueError('running Lean compiler differs from declared toolchain')
    def record(name):
        return {'declaration':name,'declaration_kind':kinds[name],
        'module':roots[name],'source_tree':tree,
        'normalized_type':types[name],'normalized_type_sha256':hashlib.sha256(types[name].encode()).hexdigest(),
        'normalization':'existing RHRC compiler pretty-type field, not a prose-derived type',
        'axioms':axioms[name],'axiom_audit_pass':True}
    declarations = [dict(record(name),theorem=name,authority='PROVED')
        for name in sorted(roots) if kinds[name]=='THEOREM']
    definitions = [dict(record(name),authority='DEFINED_DATA_NOT_A_THEOREM')
        for name in sorted(roots) if kinds[name]!='THEOREM']
    independent_digest=(independent_complete_review(independent_review,roots,kinds,head,tree)
        if mode=='complete-output' else None)
    complete=independent_digest is not None
    return {'schema_version':'RH_POST290_COMPONENT_COMPILER_RECEIPT_1.0',
        'execution_status':'SUCCESS','integrity_status':'PASS',
        'scientific_disposition':'CORE_OUTPUT_COMPLETE_RH_OPEN' if complete else 'PARTIAL_OUTPUT_RH_OPEN',
        'claim_cap':'RH_OPEN','head':head,'source_tree':tree,
        'compiler_log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
        'compiler_context':{'head':head,'tree':tree,'declared_toolchain':declared,'actual_compiler_version':compiler_version,'mathlib_revision':mathlib[0]['rev'],'dependencies':packages,'tracked_lean_toolchain_manifest_clean':True},
        'declarations':declarations,'definitions':definitions,'audited_root_count':len(roots),
        'producer_complete':complete,
        'independent_assumption_review_pass':complete,
        'independent_review_sha256':independent_digest,
        'mode':mode,
        'scope':('Complete 44-field producer independently reviewed; A-X/B-Y/C-Schur still OPEN.'
                 if complete else 'Compiled supporting components only; full source and 44-field producer unverified. Independent closing premises remain unproved.'),
        'source_blobs':[{'path':path,'git_blob':git('rev-parse',head+':'+path)} for path in sources]}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--log',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--mode',choices=('component','complete-output'),default='component')
    p.add_argument('--independent-review',type=Path)
    args = p.parse_args()
    result = build(args.log,args.mode,args.independent_review)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'head':result['head'],'declarations':len(result['declarations']),
                      'scientific_disposition':result['scientific_disposition']}))
