import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
const cwd=process.cwd();
const prior=path.join(cwd,'work/audit-independent-contract-review/stage22');
const out=path.join(cwd,'work/audit-independent-contract-review/after-bridge');
const bridge=path.join(cwd,'work/audit-tempered-lattice');
const sha=p=>crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const read=p=>JSON.parse(fs.readFileSync(p,'utf8'));
const write=(name,v)=>fs.writeFileSync(path.join(out,name),JSON.stringify(v,null,2)+'\n');
fs.mkdirSync(out,{recursive:true});
const sourceNames=['SchwartzCompactApprox.lean','TemperedLatticeNoRepair.lean','ExpectedTemperedLatticeNoRepair.lean','TemperedLatticeAxiomAudit.lean','NegativeOmitsCompactCompatibility.lean'];
const sources=sourceNames.map(n=>({path:path.join(bridge,n),sha256:sha(path.join(bridge,n)),text:fs.readFileSync(path.join(bridge,n),'utf8')}));
const receipts=[];
for (const name of ['cutoff7','bridge1','expected1','negative1','audit1']) {
  const p=path.join(bridge,name+'.receipt.json');
  if(!fs.existsSync(p)) continue;
  const r=read(p),log=path.join(bridge,name+'.log');
  const checks=Object.entries(r.source_before??{}).map(([p,h])=>({path:p,before:h,after:r.source_after?.[p],current:fs.existsSync(p)?sha(p):null}));
  receipts.push({name,receipt_sha256:sha(p),exit_code:r.exit_code,source_unchanged:r.source_unchanged,head:r.head,tree:r.tree,compiler_version:r.compiler_version,command:r.command,recorded_log_sha256:r.log_sha256,actual_log_sha256:sha(log),all_recorded_files_match:checks.every(c=>c.before===c.after&&c.before===c.current),recorded_files:checks.length,reviewed_source_checks:checks.filter(c=>c.path.includes('audit-tempered-lattice')||c.path.includes('audit-square-physical')),log:fs.readFileSync(log,'utf8')});
}
for(const n of ['cutoff7','bridge1','expected1']) {
  const r=receipts.find(r=>r.name===n);
  if(!r||r.exit_code!==0||!r.source_unchanged||!r.all_recorded_files_match||r.recorded_log_sha256!==r.actual_log_sha256) throw new Error('Evidence not stable: '+n);
}
const preserved=['INDEPENDENT_FINDINGS.md','all100-semantic-review.json','stage22/REREVIEW_FINDINGS.md','stage22/ROOT_REVIEW.json','stage22/UNIT_REVIEW.json','stage22/DEFINITION_REVIEW.json'].map(n=>{const p=path.join(cwd,'work/audit-independent-contract-review',n);return {path:p,sha256:sha(p)}});
const rootReview=read(path.join(prior,'ROOT_REVIEW.json'));
const unitReview=read(path.join(prior,'UNIT_REVIEW.json'));
const defReview=read(path.join(prior,'DEFINITION_REVIEW.json'));
const meta={review_kind:'ACTUAL_NONAUTHOR_MATHEMATICAL_CONTRACT_REVIEW',review_status:'COMPLETED_NO_ADDITIONAL_MATHEMATICAL_CONTRACT_GAP_FOUND_IN_PINNED_CANDIDATE_PLUS_BRIDGE',bridge_disposition:'CORRECT_CANDIDATE_FORMALLY_COMPILED',human_review:'NOT_ESTABLISHED',seal_created:false,owner_production_bridge_replay:'NOT_ESTABLISHED_BY_THIS_REVIEW',aggregate:'OPEN',full_release:'OPEN',RH:'OPEN',Step4:'OPEN',independent_closing_inequalities:'OPEN',review_scope:'Carry forward the exact earlier all100/28/83 assembled review and independently inspect the final compiled bridge delta; final clean owner source pin still requires refresh.',preserved_findings:preserved,bridge_source_pins:sources.map(({text,...s})=>s)};
Object.assign(rootReview,meta);
Object.assign(unitReview,meta);
Object.assign(defReview,meta);
const r80=rootReview.roots.find(r=>r.full_name==='Zeta23.OPICAFollowup.square_no_lattice_repair');
if(!r80) throw new Error('Missing root80');
r80.prior_status=r80.status;
r80.status='NONAUTHOR_FROZEN_CLAUSES_REVIEWED_NO_ADDITIONAL_MATHEMATICAL_GAP_FOUND_WITH_FULL_DOMAIN_BRIDGE';
r80.review_note='Original polynomial-atomic root unchanged. The actual canonical tau and true-TV-temperate measure theorem are supplemented by the final direct bridge theorem quantifying arbitrary actual locally finite complex sigma, arbitrary tempered T, true total-variation support on the integer lattice, and agreement only on compact smooth tests. Full Schwartz cutoff convergence derives lattice-zero annihilation and congruence; no TV-growth, coefficient reconstruction, global Schwartz-integrability or desired no-repair premise is assumed.';
r80.physical_domain_completion={theorem:'Zeta23.OPICAFollowup.square_actual_no_distribution_tempered_measure_repair',source:sources.find(s=>s.path.endsWith('TemperedLatticeNoRepair.lean')).path,sha256:'bd0c74c720d1c7eb56f19d60b8845b887db8c2ba54bfec000f02c4007da11af5',line:72,full_domain_consumer:'Zeta23.OPICAFollowup.expected_original_distribution_tempered_domain',expected_source:sources.find(s=>s.path.endsWith('ExpectedTemperedLatticeNoRepair.lean')).path,expected_sha256:'9e9edd98bda335a4b3a04aa490a7816639ca7620f14757e53fba30f1c52d7cc8',consumer_line:9,disposition:'CORRECT_CANDIDATE_FORMALLY_COMPILED',owner_final_source_replay:'PENDING'};
const us3=unitReview.units.find(u=>u.paper_id==='R2-S3');
us3.prior_status=us3.status;
us3.status='NONAUTHOR_FROZEN_UNIT_REVIEWED_NO_ADDITIONAL_MATHEMATICAL_GAP_FOUND_WITH_FULL_DOMAIN_BRIDGE';
us3.review_note='Actual canonical tau measure, density Fourier defect and genuine tempered projection retained. The compiled direct compact-compatible tempered-extension theorem supplies the broader original lattice-correction domain without true-TV-growth. This closes the previously isolated mathematical interpretation boundary for the candidate, with no additional primary root or scope amendment.';
us3.physical_domain_completion=r80.physical_domain_completion;
if(rootReview.roots.length!==100||unitReview.units.length!==28||defReview.definitions.length!==83) throw new Error('Review count mismatch');
write('ROOT_REVIEW.json',rootReview);
write('UNIT_REVIEW.json',unitReview);
write('DEFINITION_REVIEW.json',defReview);
write('BRIDGE_EVIDENCE.json',{...meta,sources:sources.map(({text,...s})=>s),receipts});
write('SOURCE_SNAPSHOT.json',{scope:'Read-only source snapshots, no proof implementation or approval',sources});
write('FINDINGS_DIFF.json',{...meta,counts:{original_roots:100,frozen_units:28,canonical_definitions:83,new_primary_roots:0},changed_root_findings:[{name:r80.full_name,prior_status:r80.prior_status,new_status:r80.status,physical_domain_completion:r80.physical_domain_completion}],changed_unit_findings:[{paper_id:'R2-S3',prior_status:us3.prior_status,new_status:us3.status}],canonical_definition_changes:[],all_other_mathematical_findings:'UNCHANGED_FROM_PINNED_STAGE22_REVIEW',exact_type_coverage:{diagnostic_scope:'Warm scratch default definitional equality, not independent semantic acceptance',required_exact:93,additional_full_signature_exact:7,selected_full_root_types:100,all_required_expected_names_present:100,all_seven_full_signature_companions_must_be_explicitly_wired:true,especially_required_consumer_only_nonzero:'dilation_near_gap_family'},remaining_acceptance_work:['Retain all seven reviewed full-signature companions in physical/unit coverage and declaration export.','Integrate bridge and literal full-domain consumers into the planned owner modules, preserve imports and record exact dependency refinements.','Refresh non-author review on a final clean owner commit/tree/source inventory, then replay all required cold compiler/type/axiom/dependency/constructor gates and harvest every job.','Independent human review remains NOT_ESTABLISHED; this review grants no seal-setting or release authority.']});
const md=`# Non-author bridge review addendum

The remaining S3 mathematical domain gap is resolved for the exact compiled candidate: **CORRECT_CANDIDATE_FORMALLY_COMPILED**. This is an actual non-author mathematical review, not independent human review, owner production acceptance, aggregate acceptance or a hardcoded review seal.

The initial findings and the Stage22 assembled review are preserved unchanged; their hashes appear in FINDINGS_DIFF.json. This addendum carries forward that exact all-100 root, all-28 frozen-unit and all-83 canonical-definition review, then reviews the bridge delta. The three complete JSON matrices here retain the earlier frozen clauses, source signatures, expected consumers and notes. Only root square_no_lattice_repair and unit R2-S3 change mathematical disposition. The primary count stays 100 and the canonical required-definition count stays 83.

## Exact reviewed bridge

| Source | SHA-256 |
|---|---|
| SchwartzCompactApprox.lean | f2ceb97fa0d10b67bcf7036709e898087dfd04bf44808098ac0f4461a1600ad9 |
| TemperedLatticeNoRepair.lean | bd0c74c720d1c7eb56f19d60b8845b887db8c2ba54bfec000f02c4007da11af5 |
| ExpectedTemperedLatticeNoRepair.lean | 9e9edd98bda335a4b3a04aa490a7816639ca7620f14757e53fba30f1c52d7cc8 |

All exact source text is preserved in SOURCE_SNAPSHOT.json. Native receipts identify the warm owner base as commit 5ad2fc2df49ed551a8e3040a0dff65939aef015a, tree bb9a2c03d02f34db68e59ee89bb80a1e24e31c7b and Lean 4.33.0-rc2, compiler commit d8b18978322de05a8f3dba51ef03cf5461676c17. This is not a clean final combined-source pin.

## Mathematical review

At SchwartzCompactApprox:68, cutoff_tendsto proves convergence in **every Schwartz seminorm**. It is stronger than pointwise or compact-test convergence. The explicit scaled smooth unit bump is one on the radius N+1 interval; all derivative bounds are uniform in N. The Leibniz estimate uses the input's k+1 weighted seminorm to bound the tail by C/(N+1), and local equality to one makes every derivative of the error zero inside that interval. No measure or distribution assertion is among its hypotheses.

The actual compactApprox at line 142 is compactly supported, converges to the given Schwartz test, and preserves every pointwise zero. This zero preservation is the crucial support mechanism; it is proved by its literal scalar multiplication formula.

At TemperedLatticeNoRepair:14, ExtendsCompactPairing means exactly: for every compactly supported Schwartz test phi, T(phi)=sigma.integral(phi). T is an arbitrary genuine tempered distribution and sigma an arbitrary genuine locally finite complex measure. It assumes neither polynomial weights, true-total-variation temperate growth, global Schwartz integrability, lattice-test congruence nor the desired no-repair conclusion. Compact compatibility is the ordinary distribution-tempered measure interface here.

At lines 32–66, the true total-variation support condition is converted to support of the four coordinate Jordan measures through the already reviewed variationControl <= TV+TV theorem. Actual measure integrals annihilate each lattice-zero compact approximation; compact compatibility identifies these with T, and continuity in the full Schwartz topology passes to the original test. Lattice congruence follows by applying annihilation to phi-psi. Thus neither property is smuggled into the caller's assumptions. The uniqueness theorem at lines 20–30 uses the same compact density to show that such a tempered extension, if supplied, is unique; no support or growth assumption is needed for uniqueness.

At line 72, square_actual_no_distribution_tempered_measure_repair uses the genuine canonical tau distribution already reviewed in c65b7b8e, arbitrary sigma and T, true-TV lattice support, and compact compatibility. It invokes the generic periodicity obstruction only after deriving its two lattice-test premises. This directly covers the broader reading of the frozen no-tempered-lattice-measure-repair clause. It does not need or claim a theorem equating distribution temperateness with total-variation growth. The original polynomial-weight root, the actual true-TV-growth theorem, all four original S3 primary proof bodies, and their existing authority stay unchanged.

At line 99 the result survives addition of any genuine Fourier-selfdual tempered distribution. This includes the actual finite real zero-jet span using its existing selfduality theorem. The addition does not assume independence or a positive measure conclusion. It adds no new primary root.

ExpectedTemperedLatticeNoRepair:9 explicitly writes the full compact compatibility hypothesis inline, quantifies arbitrary sigma and T, and has the literal actual-tau conclusion. The same file supplies the earlier true-TV-growth domain as an instance, extension uniqueness with inline compatibility, and the arbitrary-selfdual mixed barrier. These are useful full physical consumers; their producer authorship alone is not independent mathematical acceptance. This review independently checked their exact assumptions and conclusions against the frozen S3 clauses.

## Evidence and falsification

BRIDGE_EVIDENCE.json independently recomputes source, receipt and log hashes. Cutoff, bridge and full expected-consumer runs exit 0 with unchanged sources and only propext, Classical.choice and Quot.sound in the observed closure prints. The bridge log contains a deprecation warning, not a proof error. The missing-compact-compatibility control exits 1 because a Schwartz test cannot replace the required ExtendsCompactPairing proof.

The expected file also proves a genuine falsifier: for arbitrary tempered S, choosing T=-S makes S+T Fourier-selfdual. This proves why some link between the actual supported measure and T is necessary. Support of an unrelated sigma alone cannot constrain a free T. The compact compatibility premise is substantive and appropriate, rather than an extra conclusion-bearing assumption.

These are warm scratch runs. The final qualified closure audit is separate evidence if/when received; no missing or running job is counted as passed here. Scratch proof success does not establish the final owner namespace adaptation, import DAG, constructor/declaration export, cold replay or aggregate receipt.

## All-100 / 28 / 83 disposition and remaining work

After this delta review, I find no additional mathematical statement/domain gap in the pinned Stage22 assembled candidate plus the bridge. All 100 original roots, 28 frozen units and 83 canonical definitions retain actual source/type/domain review findings in the adjacent matrices. This judgment depends on retaining the actual physical adapters and full consumers identified there; it is not based on name matching.

Exact type evidence remains 93 required-name types plus seven additional full-signature types, giving 100 selected full-root types in the warm definitional-equality diagnostic. All 100 required expected names remain present. All seven full-signature companions must be explicitly included in reviewed physical/unit/export coverage; dilation_near_gap_family's required-name consumer alone states only nonzero distribution. The bridge adds physical consumers and zero primary roots. It neither alters nor automatically promotes those type-coverage results.

The smallest remaining work is exact owner integration/replay of the bridge and literal full-domain consumers; explicit seven-companion coverage; exact import/refinement recording; a clean final source pin; and the complete cold compiler/type/axiom/constructor/dependency protocol and workflow harvest. Earlier import-list deviations include more than NativeJetAdapter and remain release metadata work even where the dependency is mathematically legitimate. This mathematical review does not approve an allowlist or populate an accepted registry.

The review-authority finding is unchanged: inspected requirements do not explicitly restrict semantic review to a human/external reviewer, but that does not authorize setting any seal. This report is actual non-author model review. Independent human review is NOT_ESTABLISHED.

## Post-green research pass

**What became formally true:** the exact scratch bridge and expected types establish no lattice repair for the full compact-compatible tempered extension domain, plus uniqueness and arbitrary selfdual-addition stability. The displayed source pins and explicit support/compatibility premises define its authority.

**Workflow harvest:** cutoff, bridge and expected runs passed; missing compatibility was correctly rejected. Prior failed analytic drafts are not evidence of the final object. Final owner and cold aggregate jobs remain distinct.

**What changed:** the remaining distribution-versus-true-TV-growth presentation boundary is removed by a direct argument. No atomic coefficient reconstruction or equivalence of temperateness definitions is necessary.

**Upstream implications:** compact smooth density with preserved zeros is a reusable interface for actual supported measure extensions. Uniqueness makes arbitrary compact-compatible embeddings canonical when they exist.

**Downstream implications:** the actual square defect cannot be canceled by any such lattice measure even after adding any selfdual distribution, including all actual finite zero-jet spans.

**Resurrected routes:** support-based actual distribution arguments can use compact compatibility directly. This does not revive unrestricted square projection as a gap-preserving repair, nor the uncontrolled normalized delta-derivative measure route.

**New clues — LEAD/HYPOTHESIS:** anti-selfdual defect control may organize correction-space obstructions more generally. Extending it beyond the lattice requires an actual source-sensitive theorem, rather than a formal rewriting.

**Falsification checks:** a free T=-S cancels every S, so compatibility cannot be omitted. Nonlattice corrections, nonlinear constructions, colliding bases and diverging normalization remain outside the proved repair obstruction.

**Highest-leverage next move:** finish exact integration and its cold verification, then investigate an independent source-sensitive complete-observation upper or defect estimate. The conditional quiet upper remains an explicit OPEN premise.

RH OPEN; Step4 OPEN; independent closing inequalities OPEN; aggregate OPEN; full release OPEN; independent human review NOT_ESTABLISHED. No proof, owner source, registry, CI or shared cache was edited by this review.
`;
fs.writeFileSync(path.join(out,'BRIDGE_REVIEW_ADDENDUM.md'),md);
console.log(JSON.stringify({out,roots:rootReview.roots.length,units:unitReview.units.length,definitions:defReview.definitions.length,bridge_disposition:meta.bridge_disposition,evidence:receipts.map(r=>({name:r.name,exit_code:r.exit_code,all_recorded_files_match:r.all_recorded_files_match})),addendum_sha256:sha(path.join(out,'BRIDGE_REVIEW_ADDENDUM.md'))},null,2));
