"""Serialize the live GitHub observations made during this audit.
These are extracted observations, not copies of the complete remote job logs.
"""
from pathlib import Path
import json
A=Path('/mnt/data/rh_audit')
rows=[
('lean',36146664342,108109428281,'FORMAL VALIDITY GATE','CCM/ExceptionalZero and declared audit builds, placeholder rejection and axiom gates succeeded.','Existing theorem authority preserved; no RH theorem proved.'),
('python-rhrc',36146664342,108109428763,'REGRESSION GATE','RHRC registries, integration, graph, control and Python test suite succeeded.','Software/control consistency, not arithmetic positivity.'),
('r003-normalization-audit',36146664342,108109428619,'REGRESSION GATE','Frozen normalization, source/energy identities, threshold and research-scope checks succeeded.','A normalization/research replay does not promote bounded signals to universal statements.'),
('rhkg-compiler-receipt',36146664342,108109428602,'FORMAL VALIDITY GATE','Compiler dependency receipt/export comparison succeeded.','Certifies its declared import/root scope, not all source declarations in all audit modules.'),
('materialize',36146664275,108109427730,'FORMAL VALIDITY GATE + RESEARCH-PRODUCING CHECK','Regenerated compiler/graph/candidate/FFBBP/OoL products; steady-state gate passed; committed 8bb0f5f7b6c778d58bf9a30810fa9f1db29d7e5e.','New candidate visibility is metadata, not new mathematical proof. Final commit has no separate attached check runs.'),
('lean-permansson',36146664277,108109426955,'FORMAL VALIDITY GATE','Separate Permansson formalization job succeeded.','Separate domain/theorem scope; not RH and not every claim in the Permansson paper.'),
('post190-canonical-realizability',36146664439,108109428234,'REGRESSION GATE','REALIZABILITY_TARGET_IDENTIFIED; BASE_UNKNOWN; BLOCKED_TIGHTENED; QUOTIENT_SPACE_SCAN_DEFERRED_BASE_UNKNOWN.','Frozen pressure result; quotient scan was not executed.'),
('post192-parity-trajectory-rigidity',36146664278,108109428012,'REGRESSION GATE','LOCAL_TAYLOR_FAILURE_ACCEPTED; REFUTED_TIGHTENED_PACKAGE; MULTIMODE_LOCAL_TAYLOR_DISMISSAL_ALL_MODES.','Preserves failure of the tested local Taylor closure, not a positivity theorem.'),
('post194-parity-trajectory-sharp-enclosure',36146664457,108109428399,'REGRESSION GATE','PARTIAL_TRAJECTORY_ORIENTATION; 49 leaves with 48 certified and 1 unresolved span.','Partial frozen coverage only.'),
('post196-q14-residual-cell-replay',36146664402,108109428105,'REGRESSION GATE','GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE; remaining frozen span resolved.','GLOBAL is the frozen Q14 hull, not all apertures or Loewner monotonicity.'),
('post198-q14-source-mechanism',36146664438,108109428682,'REGRESSION GATE','SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED; NO_UNIQUE_COLLAPSED_UNIFORM_LOCK; chosen lock null.','No uniform source mechanism selected.'),
('post200-q14-discrepancy-mechanism',36146664411,108109428383,'REGRESSION GATE','DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED; NO_UNIQUE_PRIMARY_LOCK; paired enclosure 0/49 positive leaves.','Identity compatibility did not yield required sign.'),
('post202-q14-composite-parity-gap',36146664334,108109427810,'REGRESSION GATE','COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED; PATTERN_FALSIFIED_BEFORE_FULL_COVER.','Full cover was not executed after the central falsifier.'),
('post214-kernel-dual-geometry',36146664395,108109428559,'REGRESSION GATE','FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED; FULL_SPACE_SIGN_INDEFINITE_CERTIFIED; Q13/Q15 controls preserved.','FULL_SPACE is the tested dual/kernel geometry, not the unrestricted canonical carrier of PR268.'),
('post222-biregular-zero-shift-scalar',36146664310,108109428526,'REGRESSION GATE','NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED; qualified cell-minimal states 0.','Pointwise bi-regular scalar identities do not certify the retained whole-cell state and do not exclude it.'),
]
jobs=[]
for name,run,job,cls,disp,cap in rows:
 jobs.append({'name':name,'run_id':run,'job_id':job,'url':f'https://github.com/HMarcusWH/zeta-23-lean/actions/runs/{run}/job/{job}','github_conclusion':'success','classification':cls,'disposition':disp,'claim_limit':cap,'comparison':'Frozen research semantics preserved where the job is a regression; this audit is not a byte-for-byte comparison of every artifact from every historical run.'})
r={'scope':'EXTRACTED_LIVE_GITHUB_OBSERVATIONS_NOT_FULL_RAW_LOG_ARCHIVE','as_of':'2026-09-25','job_count':len(jobs),'workflow_run_count':len({j['run_id'] for j in jobs}),'all_remote_conclusions_success':True,'associated_head':'8c6c49cff82d4dec1b5d496089f0d644fe72ab88','ordinary_checkout_commit':'40024eb14f2b220e5d5f0d64a2f1920273df4dd7','ordinary_checkout_tree':'5ff508904a92ee936edf10600e86f30f77ece30b','associated_head_tree':'5ff508904a92ee936edf10600e86f30f77ece30b','materialized_head':'8bb0f5f7b6c778d58bf9a30810fa9f1db29d7e5e','materialized_and_merged_tree':'0fdd3151c86989f7cf7123be322b3968e89e3263','finalization_delta':'Temporary materializer workflow removal and generated evidence products; no Lean source delta. GitHub comparison fetched separately.','final_head_separate_check_runs':0,'merge_commit_separate_check_runs':0,'jobs':jobs}
(A/'results/workflow_harvest.json').write_text(json.dumps(r,indent=2)+'\n')
print('harvest',r['job_count'],'jobs',r['workflow_run_count'],'runs')
