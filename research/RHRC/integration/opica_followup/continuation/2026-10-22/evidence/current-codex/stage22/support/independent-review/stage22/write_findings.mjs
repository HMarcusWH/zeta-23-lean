import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
const cwd=process.cwd(), out=path.join(cwd,'work/audit-independent-contract-review/stage22');
const read=p=>fs.readFileSync(path.join(cwd,p),'utf8'), sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const input=JSON.parse(read('work/audit-independent-contract-review/stage22/ASSEMBLED_REVIEW_INPUT.json'));
const old=JSON.parse(read('work/audit-independent-contract-review/all100-semantic-review.json'));
const typeMatrix=JSON.parse(read('work/audit-release/full-type-consumer-matrix.json'));
const typeReceipt=JSON.parse(read('work/audit-release/stage22-type-control-receipt.json'));
const squareReceipt=JSON.parse(read('work/audit-square-physical/SQUARE_PHYSICAL_FINAL_RECEIPT_2026-10-24.json'));
const revisions={
6:'All actual generator classes retained. New named filter definitions expose the existing actual causal state actions with transform companions; endpoint distributions and real residual cutoffs remain explicit.',
7:'Actual right-zero unit factors retained; added canonical interfaces do not add caller-supplied pole/unit conclusions or global inverse-filter variation assumptions.',
16:'Actual joint Hilbert observation, quotient/range recovery and orthogonal extension now also exposed as genuine canonical definitions.',
17:'Exact canonical ratio-supremum and orthogonalRecovery, attained minimal norm and zero-target convention; no construction chosen from a record carrying the conclusion.',
18:'Canonical optimal-recovery noise companion now proves the exact optimalRecoveryCost*epsilon bound for the actual orthogonal extension.',
38:'Required consumer omits only extra pointwise-plus-L1 estimate; full_signature companion retains entire root. Both carry actual source-order norms, drive L2 and continuum cancellation.',
39:'Required consumer existentializes Cd; full_signature companion retains the canonical actual field-order constant. Same full-horizon physical envelope and uniform source-order cost.',
55:'Required consumer expands near-gap/TV/support definitions and binder packaging; full_signature retains literal signed Jordan interface. No domain narrowing.',
56:'Required consumer expands common TV bound and keeps redundant supplied growth proofs; full_signature uses the canonical CommonLinearMassBound-derived growth. Same Schwartz limit.',
57:'Required expected name alone proves only nonzero distribution, insufficient for group. Full_signature companion retains actual decomposition, common18 TV, selfduality, gap, positivity, origin and evenness.',
58:'Required consumer packages the explicit canonical normalized limit existentially; full_signature also retains cell identities and TV-normalization divergence. Nonmeasure scope is preserved.',
76:'Required consumer writes actual finite data and sqrt(sum squares); full_signature uses EuclideanSpace norm. These are the same finite fixed-basis domain, not a reduced subcase.',
78:'Actual canonical square Jordan measure and explicit density/punctured-comb parts, local finiteness, mutual singularity, TV growth, gap/origin/sign/evenness and actual TD pairing are supplied by candidate c65b.',
79:'Defect origin value and strict positive cases remain exact. New actual-tau TD defect adapter binds the literal continuous real C0 Lebesgue density to the actual measure.',
80:'Original polynomial-atomic root unchanged. New actual arbitrary true-TV-temperate lattice measure no-repair theorem closes that physical domain. Broader merely compact-compatible TD-extension-to-TV bridge remains pending review.',
81:'New genuine TD projection of actual tau has global tau+d/2dx identity and strict local positive density. Frozen source does not separately require a global projected Jordan constructor.',
98:'Existing actual same-state Step123 consumer preserved. FollowupNativeOutput now directly names that actual parent-generated output with source/field/input and phase-cofinal construction companions.'
};
const roots=input.rows.map(r=>({...r,status:r.index===80?'REVIEWED_WITH_BROADER_EXTENSION_DOMAIN_GAP':'NONAUTHOR_FROZEN_CLAUSES_REVIEWED_NO_ADDITIONAL_MATHEMATICAL_GAP_FOUND',review_note:revisions[r.index]??old.rows.find(x=>x.full_name===r.full_name).notes,selected_full_type_consumer:typeMatrix.rows.find(x=>x.root===r.full_name).chosen_full_type_check_consumer,required_consumer_limit:r.index===57?'Only nonzero: full companion mandatory for complete coverage':r.full_signature_companion?'Required type uses alternate packaging or omits additional root clauses; retain reviewed full companion':null,acceptance:'NO_RELEASE_OR_REVIEW_SEAL_CREATED'}));
const unitNotes={
'R1-NB1':'Literal source and actual weak causal generator states; finite words preserve affine histories and arbitrary zero multiplicity. Optional contour cost remains explicit.',
'R1-AT1':'Generic seminormed-group result covers real/complex Hilbert cases; actual native masks and norm-first transfer use exact same field. No signed upper inferred.',
'R1-AT2':'Exact allocation and maximum-rate lower result; no common maximizing branch or branchwise equality.',
'R1-HT1':'Actual noncompact mixer, weighted logarithmic Mobius inverse and actual sharp gap/leakage. Strict moment threshold and endpoint density distinction retained.',
'R1-HT2':'Actual signed Jordan measures, exact near-gap finite-region constant and Schwartz limit under a single common TV budget. Full companions retain complete types.',
'R1-CT1':'Actual near-gap comb family and normalized nonmeasure limit. Required nonzero-only consumer is insufficient alone; complete family/limit companions must be included.',
'R1-MC1':'Explicit rational inner targets and actual integral exponential Gram. Supporting inverse-entry divergence accompanies finite coupled cost; synthetic control only.',
'R1-CP1':'Actual cutoff local-TV measure identification, normalized actual-zero properties and height-qualified sign failure; no contact/source identity or RH exclusion.',
'R2-Q1a':'Literal infinite source product, normal limiting identity, whole-plane bound and exact fixed decay coefficient.',
'R2-Q1b':'Moving integer left line, all real ordinates and both zeta/derivative; one universal constant, no reciprocal-zeta premise.',
'R2-Q2':'Physical forward kernel inversion and uniform contour envelope before optimization; fixed orders and all t>=0.',
'R2-Q3':'Actual arithmetic Dirichlet products and repeated primes; real slack cutoffs, frozen per-window palette, full support delay and fixed Pj instance.',
'R2-O1':'Actual joint observation, genuine quotient/range/orthogonal recovery, exact canonical cost and zero-target convention.',
'R2-O2':'Canonical optimal noise bound and actual left-null certificate. History errors and recovery cost remain visible; no cheap-native-recovery inference.',
'R2-J1':'Actual meromorphic disk and integer Laurent degree; explicit native word coefficient/corrections/recovery, factorial and sharp boundary companions.',
'R2-S1a':'Actual zero profile, Bernoulli expansion and endpoint jumps; even/continuous/selfdual/L1/L2, no positivity or simplicity assumption.',
'R2-S1b':'Actual integer atomic forcing and log form domain; no homogeneous self-adjoint eigenvector inference.',
'R2-S2':'Actual samples and Gram integrals, convergent endpoint boundary limits, PSD forms and undivided identity at conjugate coincidence.',
'R2-H1':'Actual multiplicity-bounded kappa jets, local inverse and parameter limits; true measures and actual growth/gap/origin/forced chain.',
'R2-H2a':'Full confluent determinant of actual normalized first-cell rows; distinct kappa nodes remove reflection duplicates; no collision conditioning claim.',
'R2-H2b':'Actual finite realified jet span and fixed independent real-basis sinc-weighted negative budget. Extra offcritical 2D pair is supporting only.',
'R2-H3':'Explicit first interval and exact mass constants with all height/displacement qualifiers; critical-line applicability prevents zero-exclusion overclaim.',
'R2-S3':'Actual tau measure/defect/projection adapters now supplied. General correction theorem covers arbitrary true-TV-temperate lattice measure; broader extension-only characterization still pending.',
'F1':'Actual sawtooth derivative force with subtraction before temperate extension, both Fourier conventions and exact finite weighted zeta moment.',
'F2':'Actual forced H1 resolvent, H-1/H1 sample pairing, positive arithmetic Stieltjes density and norm/form budgets at nonreal kappa.',
'F3':'Generic forced profile at nonzero-zeta parameters, actual boundary amplitude and plateau iff zero. Diagnostic only.',
'J5.2':'Actual full continuous real-horizon rate for every fixed d,C>1, arbitrary multiplicity and Theta=0; entire residual/memory chain actual.',
'MS1':'Any cofinal real horizon sequence with d log(d+2)/T->0; both signs of source multiplier cost, fixed chosen zero before each lower-limit argument.'
};
const units=input.units.map(u=>({...u,status:u.paper_id==='R2-S3'?'NONAUTHOR_REVIEW_WITH_EXTENSION_DOMAIN_GAP':'NONAUTHOR_FROZEN_UNIT_REVIEWED_NO_ADDITIONAL_MATHEMATICAL_GAP_FOUND',review_note:unitNotes[u.paper_id],root_review_names:u.required_roots,acceptance:'NO_UNIT_ACCEPTANCE_SEAL_CREATED'}));
const definitionNotes={
'NativeSourceFamily':'Literal recursive P source, parent physical prime/integer histories, actual forward integer translations and true causal gap.',
'NativeSourceTransforms':'Actual integral transforms and source-specific meromorphic germ; native pole/continuation identities proved by roots.',
'NativeFilters':'Explicit local causal states and concrete action constructors; the four new canonical action names preserve actual actions, real cutoff and safe-domain transform companions.',
'NativeTransformationWords':'Finite generator words, actual-history continuation certificates without desired preservation conclusions, retained affine correction and explicit product/count.',
'NormFirstTransfer':'Squared norm energy on the generic normed additive structure; no native asymptotic property in definition.',
'JointObservation':'True Hilbert product observation; exact ratio-sup cost and quotient/range-factor followed by orthogonal projection. Necessary kernel condition explicit.',
'RobustLaurent':'Actual germ-defined Laurent coefficient and actual circle error budget; the budget is a visible conditional input, not assumed native nonvanishing.',
'SourceVerticalBounds':'Exact source-fixed coefficient (log8)*sqrt(s0)/4.',
'BalancedCoefficients':'Actual ArithmeticFunction Dirichlet convolution and Mobius small/large split, not pointwise powers.',
'LogSlackBalance':'Explicit real horizon-dependent slack cutoffs and actual physical Type-I/balanced histories.',
'NativeExplicitFormula':'Supremum over insert0 of actual positive right displacements; not an assumed or attained extreme zero.',
'AuxiliaryCompletions':'Explicit beta polynomial causal filter, actual integer completion action, rational transform, true decay rate and prescribed constant.',
'MultiplicityTail':'Actual finite truncated residual and physical terminal memory; no global prime-field weighted L2 premise.',
'NativeWindowRate':'Literal actual terminal-window energy on real horizons.',
'ComplexLocalMeasures':'True pair of locally finite real Jordan measures; local variation uses actual compact complex variation, not weak-test convergence renamed.',
'DilatedComb':'Actual scaled full integer measure/distribution and its actual Schwartz pairing.',
'WeightedMixing':'True exponential variation moment, actual noncompact physical mixture and positive-axis weighted logarithmic measure transport.',
'NearGapLimits':'Actual canonical near-gap dilation Jordan comb, not a conclusion-bearing synthetic packet.',
'RenormalizedCoPoisson':'Actual subtraction before distributional integration, actual cutoff measures, finite arithmetic density and source-specific normalization/zero measure.',
'ProfileEulerMaclaurin':'Actual Bernoulli fractional-part polynomials with right integer endpoint convention.',
'ZeroProfiles':'Actual spectral coordinate rho(1-rho) and normalized arithmetic profile; no profile positivity field.',
'LogFourierSobolev':'Actual log-coordinate transform/unitary/form and local absolute-continuity plus L2 form domain; no forced conclusion built into domain.',
'SamplingCompatibility':'Actual convergent physical integrals and integer sample sum, with linear-first complex convention retained.',
'CoPoissonJets':'Actual normalized parameter derivatives below analytic multiplicity; measure constructor and actual growth/forcing supplied by roots.',
'ConfluentProfiles':'Actual first-cell normalized derivative matrix and kappa-node distinctness; reflection duplicates quotiented.',
'FiniteSpanSeparation':'Actual complex-scaled finite jet sum followed by real Jordan part; public alias retains this actual construction.',
'SquareDefect':'Original raw square pairing/actual convolution defect retained and now identified with canonical tau measure and genuine TD adapters.',
'SawtoothForce':'Literal sawtooth and derivative-of-integrable-function tempered force; compact-test arithmetic representation is derived.',
'WeightedSpectralMeasure':'Actual positive zeta density measure, correct spectral coordinate and Stieltjes integral off spectrum; no finite total mass assumption.',
'NativeResolvent':'Actual Fourier quotient inverse giving the unique forced H1 log solution; actual-source identification is proved.',
'BoundaryAmplitude':'Actual generic forced arithmetic profile and exact zeta-normalized boundary amplitude; no independent zero-exclusion field.',
'Consumers':'Actual accepted parent GeneratedStep123CompleteOutput with same zero/aperture/phase/horizon; physical view and phase-cofinal construction companions.'
};
const definitions=input.definitions.map(d=>({...d,status:'NONAUTHOR_CANONICAL_SEMANTICS_AND_ORIGIN_REVIEWED_NO_ADDITIONAL_GAP_FOUND',review_note:definitionNotes[d.original_module.split('.').at(-1)],origin_relocation:false,acceptance:'NO_HARDCODED_OR_REGISTRY_SEAL_CREATED'}));
const checks=[];
for(const c of typeReceipt.commands){for(const [kind,rel,digest] of [['source',c.source,c.source_sha256],['log',c.log,c.log_sha256]]){const file=path.join(cwd,'work/audit-release',rel);checks.push({lane:c.label,kind,file,expected_sha256:digest,actual_sha256:sha(fs.readFileSync(file)),matches:sha(fs.readFileSync(file))===digest,exit_code:c.exit_code});}}
for(const [rel,digest] of Object.entries(squareReceipt.source_sha256)){const file=path.join(cwd,'work/audit-square-physical',rel);checks.push({lane:'square-physical',kind:'source',file,expected_sha256:digest,actual_sha256:sha(fs.readFileSync(file)),matches:sha(fs.readFileSync(file))===digest});}
const prefix=fs.readFileSync(path.join(cwd,'work/opica-followup-repo/Zeta23/OPICAFollowup/SquareDefect.lean'));
checks.push({lane:'square-original-prefix',matches:fs.readFileSync(path.join(cwd,'work/audit-square-physical/SquareDefectPhysicalFullCandidate.lean')).subarray(0,prefix.length).equals(prefix),prefix_sha256:sha(prefix)});
const status={review_kind:'ACTUAL_NONAUTHOR_MATHEMATICAL_CONTRACT_REVIEW',review_status:'COMPLETED_WITH_EXPLICIT_S3_BROADER_DOMAIN_GAP',human_review:'NOT_ESTABLISHED',seal_created:false,owner_head:input.owner_head,owner_tree:input.owner_tree,all100_root_source_present:true,all100_required_expected_consumers_present:true,canonical_definitions:83,RH:'OPEN',Step4:'OPEN',independent_closing_inequalities:'OPEN',aggregate:'OPEN',full_release:'OPEN'};
for(const [file,object] of [['ROOT_REVIEW.json',{...status,roots}],['UNIT_REVIEW.json',{...status,units}],['DEFINITION_REVIEW.json',{...status,definitions}],['EVIDENCE_CHECKS.json',{...status,checks}]])fs.writeFileSync(path.join(out,file),JSON.stringify(object,null,2));
const table=(headers,rows)=>['| '+headers.join(' | ')+' |','|'+headers.map(()=>'---').join('|')+'|',...rows.map(r=>'| '+r.map(x=>String(x).replaceAll('|','\\|').replaceAll('\n',' ')).join(' | ')+' |')].join('\n');
fs.writeFileSync(path.join(out,'ALL100_ROOT_MATRIX.md'),'# Stage22 non-author root review\n\nActual mathematical contract review; no human approval, registry seal, aggregate receipt or full-release acceptance. Sources and full types are in ROOT_REVIEW.json.\n\n'+table(['#','Root','Actual source line','Finding'],roots.map(r=>[r.index,r.full_name.split('.').at(-1),r.actual.line,r.review_note]))+'\n');
fs.writeFileSync(path.join(out,'ALL28_UNIT_MATRIX.md'),'# Stage22 non-author unit review\n\nEvery frozen unit retained. R2-S3 broader extension-only domain remains pending; no acceptance seal.\n\n'+table(['Unit','Finding'],units.map(u=>[u.paper_id,u.review_note]))+'\n');
console.log(JSON.stringify({roots:roots.length,units:units.length,definitions:definitions.length,evidence_checks:checks.length,evidence_mismatch:checks.filter(c=>!c.matches),status}));
