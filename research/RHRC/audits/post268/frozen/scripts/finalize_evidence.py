"""Freeze audit observations; no repository writes or formal theorem promotion."""
from pathlib import Path
import json, hashlib, collections, subprocess, platform, importlib.metadata
A=Path('/mnt/data/rh_audit');R=A/'snapshot/zeta-23-lean-main';O=A/'results'
manifest=[json.loads(x) for x in (O/'file_manifest.jsonl').read_text().splitlines()]
changes=[]
for x in manifest:
 p=R/x['path']
 if not p.is_file(): changes.append({'path':x['path'],'issue':'missing'})
 elif hashlib.sha256(p.read_bytes()).hexdigest()!=x['sha256']:changes.append({'path':x['path'],'issue':'content_changed'})
identity=json.loads((O/'snapshot_identity.json').read_text())
res={'status':'PASS' if not changes else 'FAIL','tracked_files_checked':len(manifest),'changes':changes,'original_tree':identity['computed_git_tree'],'current_index_tree':subprocess.check_output(['git','write-tree'],cwd=R,text=True).strip(),'note':'Working-tree source hashes checked against the original ZIP manifest; untracked __pycache__ and local .git are not source changes.'}
(O/'final_integrity.json').write_text(json.dumps(res,indent=2)+'\n')
assert not changes
# A compact, line-anchored source register for third-party review.
targets={
'Zeta23/CCM/GlobalParityBottomIntertwining.lean':['evenEigenmode_shiftedOdd_eq_sourceCubic','oddEigenmode_pulledBack_shiftedEven_eq_neg_sourceCubic'],
'Zeta23/CCM/GlobalParityBottomSourceMoment.lean':['momentFour_ne_zero_of_evenGround_strict'],
'Zeta23/CCM/GlobalParityBottomReverseGroundTransfer.lean':['oddGround_pulledBack_source_ne_zero_of_strict'],
'Zeta23/CCM/GlobalParityBottomSpectrum.lean':['exists_eigenmode_at_parityRayleighBottom_succ','boundaryFlatRayleighBottom_eq_min_parity','canonicalCarrierBottom_hierarchy','globalParitySuccessorBottom_neg_iff_anyParityBad'],
'Zeta23/CCM/GlobalParityBottomNFlow.lean':['globalParitySuccessorBottom_antitone_of_le'],
'Zeta23/CCM/CanonicalPrimeRemainder.lean':['canonicalPrimeRemainderEnergy','canonicalPrimeFreeBudget','canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget'],
'Zeta23/CCM/GlobalParityBottomPrimeWeightJets.lean':['primeTestWeight_endpoint_order_eight_of_evenStrict'],
'Zeta23/ExceptionalZero/ApertureFreedom.lean':['eventually_all_apertures_have_anyParityBad_of_offLine_zero'],
'Zeta23/ExceptionalZero/CanonicalArithmeticCriterion.lean':['canonicalFiniteWeilPositivity_iff_riemannHypothesis','canonicalPrimeRemainderDominance_iff_riemannHypothesis'],
'Zeta23/ExceptionalZero/GlobalParityBottomArithmeticEquivalenceAudit.lean':['globalBottomResidualExclusion_iff_riemannHypothesis'],
'Zeta23/ExceptionalZero/ProbeGramNegativity.lean':['not_onLineCombination_of_pairBlock'],
'research/RHRC/integration/candidate_exactify.py':['import Zeta23.CCM','import Zeta23.ExceptionalZero'],
}
mr={x['path']:x for x in manifest}; anchors=[]
for path,terms in targets.items():
 lines=(R/path).read_text().splitlines()
 for term in terms:
  matches=[i+1 for i,l in enumerate(lines) if term in l]
  # Prefer declaration start rather than mentions/print commands.
  starts=[i for i in matches if any(t in lines[i-1] for t in ['theorem ','def ','import '])]
  start=(starts or matches)[0] if matches else None
  if start is None:raise ValueError((path,term))
  end=min(len(lines),start+22)
  anchors.append({'path':path,'symbol_or_text':term,'start_line':start,'end_line':end,'sha256':mr[path]['sha256'],'git_blob':mr[path]['git_blob'],'url':f'https://github.com/HMarcusWH/zeta-23-lean/blob/{identity["archive_commit_comment"]}/{path}#L{start}-L{end}','excerpt':'\n'.join(lines[start-1:end])})
(O/'source_anchor_index.json').write_text(json.dumps(anchors,indent=2,ensure_ascii=False)+'\n')
# Candidate-resolution holes are checked against the separate binding authority.
g=json.loads((O/'independent_graph_audit.json').read_text())
b=json.loads((R/'research/RHRC/REGISTERED_THEOREM_BINDINGS.json').read_text())['bindings']
miss=[]
for x in g['unresolved_source_identities']:
 bs=[z['id'] for z in b if z['source']==x['path'] and (z['theorem']==x['declared_name'] or z['theorem'].endswith('.'+x['declared_name']))]
 miss.append({'module':x['module'],'declared_name':x['declared_name'],'path':x['path'],'line':x['line'],'candidate_resolution':x['resolution_status'],'separately_registered_claims':bs})
(O/'candidate_resolution_holes.json').write_text(json.dumps(miss,indent=2)+'\n')
u=json.loads((R/'research/RHRC/graph/generated/UNRESOLVED_GRAPH_ITEMS.json').read_text())
(O/'graph_semantic_scope.json').write_text(json.dumps({'closed':u['closed_in_final_closure_pass'],'deferred':u['deferred_to_later_phases'],'warning':'File/import/declaration coverage is not complete historical or mathematical-premise semantics.'},indent=2)+'\n')
packages={}
for p in ['numpy','scipy','sympy','mpmath','networkx','python-flint','pytest']:
 try:packages[p]=importlib.metadata.version(p)
 except importlib.metadata.PackageNotFoundError:packages[p]=None
(O/'environment.json').write_text(json.dumps({'python':platform.python_version(),'platform':platform.platform(),'packages':packages,'local_Lean_build':'NOT_RUN_NO_LEAN_LAKE_TOOLCHAIN','network_python_flint_install':'ATTEMPT_FAILED_SEE_LOG','randomized_or_float_claim_cap':'EXPERIMENTAL_SIGNAL_ONLY'},indent=2)+'\n')
print(json.dumps(res,indent=2));print('source anchors',len(anchors),'separately registered unresolved',sum(bool(x['separately_registered_claims']) for x in miss))
