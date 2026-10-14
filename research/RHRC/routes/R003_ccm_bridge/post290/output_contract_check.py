"""Reject completion unless every mandatory producer and D2 gate has receipts.

This is an integrity check, not a mathematical proof. Exact compiler receipts
and independent mathematical review are both required by the original contract.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

REPO=Path(__file__).resolve().parents[5]
IMMUTABLE_SPEC=REPO/'research/RHRC/integration/post290/spec/BUILD_MANIFEST.json'
IMMUTABLE_SPEC_SHA256='1a36cb3ff2cb39017bdb34cb4f56f831f40c611472f840af8b3dce9dafa71760'
# The reviewed source provides exact requested kinds for all 99 public exports.
# Lean represents a structure as an inductive declaration; neither is theorem
# authority. Pin the original crosswalk by Git blob SHA-1.
FROZEN_API_CROSSWALK=REPO/'research/RHRC/integration/post290/review_execution_2026-10-14/spec/API_CROSSWALK.json'
FROZEN_API_CROSSWALK_BLOB_SHA='254e2c4a8ad05bd1647c2175d86472755c795c41'

FORMAL_JOB=('RHRC post290 source and output proof components','lean-components')
REGRESSION_JOB=('RHRC post290 source and output proof components','exact-controls')
NATIVE_JOB=('RHRC post290 source and output proof components','native-observations')
RESEARCH_JOBS={('RHRC post290 D2 SECOND continuation (manual)','d2-second-continuation'),('RHRC post290 K3 independent no-search shards','assemble-nonpartial')}
ALLOW_AXIOMS={'propext','Classical.choice','Quot.sound'}
CLASSIFICATIONS={'FORMAL_VALIDITY_GATE','REGRESSION_GATE','RESEARCH_PRODUCING_CHECK'}


def checked_checkout(job, expected_tree):
    """Preserve API branch identity while checking a separately reviewed merge.

    GitHub's PR API reports the branch SHA even when checkout uses the synthetic
    merge commit. A different checked HEAD requires both Git objects and a
    hashed runner log; equality of displayed tree strings alone is insufficient.
    This is reviewed evidence plumbing, not a mathematical authority source.
    """
    branch=job.get('head')
    if re.fullmatch('[0-9a-f]{40}',str(branch)) is None or job.get('head_tree')!=expected_tree:
        return None
    runner=job.get('runner_checked_head')
    runner_tree=job.get('runner_checked_tree')
    if runner is None and runner_tree is None:
        return branch
    if runner_tree!=expected_tree or re.fullmatch('[0-9a-f]{40}',str(runner)) is None:
        return None
    review=job.get('checkout_identity_review') or {}
    if (review.get('integrity_status')!='PASS'
        or review.get('evidence_source')!='GITHUB_GIT_OBJECTS_AND_RUNNER_LOG'
        or review.get('branch_head')!=branch or review.get('branch_tree')!=expected_tree
        or review.get('runner_checked_head')!=runner or review.get('runner_checked_tree')!=expected_tree
        or re.fullmatch('[0-9a-f]{64}',str(review.get('checkout_log_sha256'))) is None):
        return None
    branch_object=review.get('branch_git_commit',{})
    runner_object=review.get('runner_git_commit',{})
    if (branch_object.get('sha')!=branch or branch_object.get('tree',{}).get('sha')!=expected_tree
        or runner_object.get('sha')!=runner or runner_object.get('tree',{}).get('sha')!=expected_tree):
        return None
    if runner==branch:
        return runner if review.get('checkout_kind')=='BRANCH_HEAD' else None
    base=review.get('reviewed_pr_base_head')
    parents=runner_object.get('parents',[])
    if (review.get('checkout_kind')!='PR_SYNTHETIC_MERGE'
        or re.fullmatch('[0-9a-f]{40}',str(base)) is None or base==branch
        or len(parents)!=2 or {p.get('sha') for p in parents}!={base,branch}):
        return None
    return runner


def frozen_spec():
    raw=IMMUTABLE_SPEC.read_bytes()
    # Compare the original bundle bytes; a Windows text checkout may change
    # newline encoding, which is explicitly normalized only for this comparison.
    if hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest()!=IMMUTABLE_SPEC_SHA256:
        raise ValueError('immutable original acceptance specification changed')
    return json.loads(raw)

def frozen_export_kinds(expected):
    raw=FROZEN_API_CROSSWALK.read_bytes().replace(b'\r\n',b'\n')
    # Git's content identity includes the "blob <size>\0" framing.
    framed=b'blob '+str(len(raw)).encode()+b'\0'+raw
    if hashlib.sha1(framed).hexdigest()!=FROZEN_API_CROSSWALK_BLOB_SHA:
        raise ValueError('reviewed public API kind contract changed')
    rows=json.loads(raw)['rows']
    names=[r.get('requested_name') for r in rows]
    if len(rows)!=99 or len(set(names))!=99 or not all(isinstance(n,str) and n for n in names):
        raise ValueError('invalid 99-name public API kind inventory')
    spec_names={name for module in expected['new_lean_modules']
                for name in module['proposed_exports']}
    if set(names)!=spec_names:
        raise ValueError('API crosswalk does not match immutable 25-module export inventory')
    kinds={'THEOREM':'THEOREM','DEFINITION':'DEFINITION',
           'STRUCTURE':'INDUCTIVE','INDUCTIVE':'INDUCTIVE'}
    if any(row.get('required_kind') not in kinds for row in rows):
        raise ValueError('unrecognized required public source kind')
    return {row['requested_name']:kinds[row['required_kind']] for row in rows}

def release_gaps(manifest, formal, d2, jobs):
    gaps = []
    expected=frozen_spec()
    if manifest.get('claim_cap') != 'RH_OPEN':
        gaps.append('claim firewall changed')
    modules=manifest.get('new_lean_modules',[])
    frozen={r['id']:r for r in expected['new_lean_modules']}
    ids=[r.get('id') for r in modules]
    if len(ids)!=25 or len(set(ids))!=25 or set(ids)!=set(frozen):
        gaps.append('immutable 25-module acceptance inventory missing or duplicated')
    for module in modules:
        prior=frozen.get(module.get('id'))
        if prior and (module.get('mandatory_core') is not prior.get('mandatory_core') or module.get('proposed_exports')!=prior.get('proposed_exports')):
            gaps.append('immutable module acceptance narrowed or changed: '+module['id'])
    packages=manifest.get('work_packages',[])
    package_ids=[r.get('id') for r in packages]
    prior_packages={r['id']:r for r in expected['work_packages']}
    if len(package_ids)!=11 or len(set(package_ids))!=11 or set(package_ids)!=set(prior_packages):
        gaps.append('immutable 11-work-package inventory missing or duplicated')
    for package in packages:
        prior=prior_packages.get(package.get('id'))
        if prior and package.get('mandatory') is not prior.get('mandatory'):
            gaps.append('mandatory work package demoted: '+package['id'])
        if prior and prior.get('mandatory') and package.get('status')!='COMPLETE_VERIFIED':
            gaps.append('unfulfilled work-package acceptance: '+package['id'])
    expected_kinds=frozen_export_kinds(expected)
    declarations=formal.get('declarations',[])
    definitions=formal.get('definitions',[])
    all_bindings=declarations+definitions
    names=[r.get('declaration',r.get('theorem')) for r in all_bindings]
    if len(names)!=len(set(names)) or any(not isinstance(n,str) or not n for n in names):
        gaps.append('duplicate or malformed compiler declaration receipts')
    bindings = {r.get('declaration',r.get('theorem')):r for r in all_bindings}
    tree = formal.get('source_tree')
    if not isinstance(tree,str) or re.fullmatch('[0-9a-f]{40}',tree) is None:
        gaps.append('exact compiler-tested tree missing')
    head=formal.get('head')
    if not isinstance(head,str) or re.fullmatch('[0-9a-f]{40}',head) is None:
        gaps.append('exact compiler-tested head missing')
    if formal.get('producer_complete') is not True:
        gaps.append('supporting components do not fill mandatory output producer')
    if formal.get('execution_status')!='SUCCESS' or formal.get('integrity_status')!='PASS' or formal.get('claim_cap')!='RH_OPEN':
        gaps.append('formal receipt execution/integrity/claim unverified')
    context=formal.get('compiler_context',{})
    if context.get('head')!=head or context.get('tree')!=tree:
        gaps.append('compiler-generated head/tree context missing or stale')
    for module in modules:
        if not module.get('mandatory_core'):
            continue
        for name in module['proposed_exports']:
            receipt = bindings.get(name)
            if not receipt:
                gaps.append('missing producer: ' + name)
            else:
                required_kind=expected_kinds[name]
                kind=receipt.get('declaration_kind')
                authority=receipt.get('authority')
                if (kind!=required_kind or
                    authority!=('PROVED' if kind=='THEOREM' else 'DEFINED_DATA_NOT_A_THEOREM')
                    or receipt.get('source_tree') != tree or
                    not receipt.get('normalized_type') or
                    hashlib.sha256(receipt.get('normalized_type','').encode()).hexdigest() != receipt.get('normalized_type_sha256')
                    or receipt.get('axiom_audit_pass') is not True or
                    not isinstance(receipt.get('axioms'),list) or
                    not set(receipt.get('axioms',[]))<=ALLOW_AXIOMS):
                    gaps.append('unverified, wrong-kind or stale producer: ' + name)
        if module.get('status') != 'COMPLETE_VERIFIED':
            gaps.append('unfulfilled module acceptance: ' + module['id'])
    required_d2 = ('complete_layers','unresolved_tiles','unrun_tiles','missing_artifacts','unverified_tiles','nonfinite_enclosures')
    if (d2.get('status') != 'D2_COMPLETE' or d2.get('complete_layers') != 30
        or d2.get('source_tree')!=tree or d2.get('terminal_claim')!='RH_OPEN' or d2.get('not_a_lean_proof') is not True
        or d2.get('independent_nonpartial_verified') is not True or d2.get('both_parities') is not True
        or d2.get('physical_seams_verified') is not True or any(type(d2.get(k)) is not int for k in required_d2)
        or any(d2.get(k,1) != 0 for k in required_d2[1:])):
        gaps.append('D2 continuous full-domain gate incomplete')
    # The compiler receipt binds the actual checkout. The configured formal
    # job supplies the API branch identity, retained unchanged in every job.
    formal_jobs=[j for j in jobs if (j.get('workflow'),j.get('name'))==FORMAL_JOB and j.get('latest_attempt') is not False]
    branch_heads={j.get('head') for j in formal_jobs}
    branch_head=next(iter(branch_heads)) if len(branch_heads)==1 else head
    if len(branch_heads)!=1:
        gaps.append('configured formal jobs do not identify one reviewed branch head')
    known_required=[]
    formal_runner_matched=False
    for job in jobs:
        if not all(k in job for k in ('name','workflow','required','head','head_tree','status','conclusion','scientific_acceptance','classification','output_reviewed')):
            gaps.append('raw or mismatched workflow harvest schema')
            continue
        if job['classification'] not in CLASSIFICATIONS or job.get('output_reviewed') is not True:
            gaps.append('workflow source/output review incomplete: '+job['name'])
        if job.get('latest_attempt') is False:
            continue
        if type(job['required']) is not bool or type(job['scientific_acceptance']) is not bool:
            gaps.append('workflow acceptance flags must be Boolean')
            continue
        pair=(job['workflow'],job['name'])
        configured=pair in {FORMAL_JOB,REGRESSION_JOB,NATIVE_JOB}|RESEARCH_JOBS
        if configured and job['required'] is not True:
            gaps.append('configured required job demoted: '+job['name'])
        if job['required']:
            known_required.append(pair)
        checked_head=checked_checkout(job,tree)
        if job.get('required') and (job.get('head_tree') != tree or job.get('status') != 'completed'
            or job.get('head')!=branch_head or checked_head is None
            or job.get('conclusion') != 'success' or job.get('scientific_acceptance') is not True):
            gaps.append('required job unestablished: ' + job['name'])
        if (pair==FORMAL_JOB and checked_head==head and job.get('required') is True
            and job.get('status')=='completed' and job.get('conclusion')=='success'
            and job.get('scientific_acceptance') is True):
            formal_runner_matched=True
        if pair==NATIVE_JOB:
            review=job.get('native_output_review',{})
            if (review.get('head')!=checked_head or review.get('source_tree')!=tree or review.get('scope')!='FINITE_FIXED_PROBES'
                or review.get('frozen_panel_complete') is not True or review.get('pair_count')!=44 or review.get('row_count')!=176
                or review.get('evaluated_rows')!=176 or review.get('unresolved_rows')!=0 or review.get('verified_pairs')!=44
                or review.get('unresolved_pairs')!=0 or review.get('universal_theorem_authority') is not False):
                gaps.append('native finite observation output not independently reviewed')
    if FORMAL_JOB not in known_required:gaps.append('configured formal validity job missing')
    if not formal_runner_matched:gaps.append('compiler receipt does not match a validated formal runner checkout')
    if REGRESSION_JOB not in known_required:gaps.append('configured exact regression job missing')
    if NATIVE_JOB not in known_required:gaps.append('configured native observation job missing')
    if not set(known_required)&RESEARCH_JOBS:gaps.append('configured independent D2 research job missing')
    if not jobs:
        gaps.append('workflow harvest missing')
    if formal.get('independent_assumption_review_pass') is not True:
        gaps.append('independent producer assumption review missing')
    return gaps

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--formal', type=Path, required=True)
    p.add_argument('--d2', type=Path, required=True)
    p.add_argument('--harvest', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    read = lambda path: json.loads(path.read_text())
    gaps = release_gaps(read(args.manifest),read(args.formal),read(args.d2),read(args.harvest).get('jobs',[]))
    result = {'execution_status':'SUCCESS', 'integrity_status':'PASS' if not gaps else 'RELEASE_REJECTED',
              'scientific_disposition':'CORE_OUTPUT_COMPLETE_RH_OPEN' if not gaps else 'PARTIAL_OUTPUT_RH_OPEN',
              'claim_cap':'RH_OPEN', 'unfulfilled_requirements':gaps}
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'scientific_disposition':result['scientific_disposition'],'unfulfilled_requirements':len(gaps)}))
    raise SystemExit(0 if not gaps else 2)
