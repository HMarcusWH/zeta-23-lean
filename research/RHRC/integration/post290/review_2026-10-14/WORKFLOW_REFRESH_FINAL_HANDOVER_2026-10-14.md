# Workflow, D2, native selection and complex transform handover

Frozen on the user's request to round up this iteration, push the completed work, and wait for third-party review. No new mathematical obligations or executions should be started from this handover. This note reports this subagent's scope; the root handover covers the complete W00–W10/M01–M25 build.

## Exact verification state

The final local receipt is `NATIVE_CONSUMER_CLOSURE_GREEN_2026-10-14.json`, SHA256 `561cedb82387fb3857798f1e3f048bc6eb467609b83ae1d970d9fe338b2f5328`. It records **22 modules and 87 printed roots**, each with current source, compiler log and olean SHA256. All listed exact builds exited successfully and printed only subsets of `[propext, Classical.choice, Quot.sound]`; none printed `sorryAx` or compiler errors. The pinned compiler is Lean 4.33.0-rc2, through the repository's local driver, single job, 800000 heartbeats and `relaxedAutoImplicit=false`.

The receipt names local HEAD `d5b867ef467b4eb5d5e38e500577fda2b2a5f91b` and explicitly records a frozen working-tree source state. This is **local exact compiler evidence**, not a claim that all 22 source files had already passed remote CI at that head. The root agent owns final source commits, source-origin bindings and exact-head CI/whole-workflow harvest.

All owned local compiler runners have finished. The last was session 98811, NativeCompletedInputZetaLaplace, EXIT0. There are no active local runners or unfinished Lean candidates in this agent's scope. The separately approved production D2 GitHub workflow is a shared external execution, not a local runner; its final status and budget ledger remain under root ownership.

The 22 frozen modules in the receipt are:

- FiniteBottomGapSelector.
- CanonicalDeepThresholdGap and CanonicalDeepThresholdSelection.
- NativePoleNeutralTrialDepth and NativeDeepThresholdGround.
- NativeDeepThresholdInverseBudgets, NativeDeepThresholdSimplicity and NativeDeepThresholdEvenMoment.
- NativeDetectorSchur, NativeSelectedGroundSchur and DetectorRetainedSchurState.
- CanonicalTrialResidualChannels and Step123PrimeSeam.
- OriginalDetectorNativeRetainedSelection (explicitly the unpadded helper).
- OriginalDetectorAdmissibleSelector and OriginalDetectorPaddedRetainedSelection (the final padded construction).
- NativeCompletionComplexLaplace and NativeCompletedInputComplexLaplace.
- NativeIntegerKernelComplexLaplace and NativePositiveCompletionComplexLaplace.
- NativeIntegerDriveComplexLaplace and NativeCompletedInputZetaLaplace.

The root and other agents separately verified the upstream native operators, corrected source/tie geometry, positive-padding pipeline, actual source transform, causal zero jets, general compact inverse and analytic continuation helper. Those files are deliberately not relabelled as this agent's independent 22-module check.

## What became formally true

### Bottom-only gap and actual selected ground

The finite avoidance theorem uses only the actual global native bottoms at cutoffs 3 through Kd, hence Kd−2 forbidden real values. The midpoint-grid gap is exactly `D / [12(Kd−1)]` with `D/3 < eta < D/2`. The finite real gap selector is valid also at n=0 and for repeated forbidden values; its non-strict distance conclusion is essential.

A supplied actual legal mixed-parity unit trial of canonical energy at most −D bounds the actual global bottom. Splitting it into actual even and odd components pays both the norm-square and energy decompositions; no pure-parity premise or manufactured ground is inserted.

The least actual bottom crossing yields actual data with cutoff 3≤K≤Kd, actual spectral value lam, a unit ground in at least one actual parity, earlier bottom gaps and both predecessor lower bounds. The first nonempty cutoff K=3 uses the genuinely zero-dimensional predecessor spaces at K=2. No bottom of an empty spectrum is assigned.

At lam, the predecessor has coercivity 2g; at detector shift −eta, it has coercivity g. Four actual inverses are constructed, with respective norm bounds `6(Kd−1)/D` and `12(Kd−1)/D`. Their first-cutoff norms are zero. The proofs supply these inverses rather than taking inverse existence or its bound as a premise.

The one-dimensional new native shell proves both parity eigenspaces at lam have dimension at most one. The parity containing a nonzero selected ground has dimension exactly one. An even/odd tie remains possible. The selected even ground has nonzero fourth moment, including at a tie; corrected-source nonvanishing still requires the separate strict-below-odd-bottom condition.

### Two distinct Schur records

The selected-ground record uses the actual one-dimensional successor shell at K and actual ground shift lam, including its exact Schur kernel/scalar identity. The original detector record uses Kd and the entire complement of the embedded predecessor at K−1. Its dimension is exactly Kd−K+1. Its shift remains −eta.

The literal original detector satisfies the exact completed-square identity and retains a nonzero complementary coordinate with signed Schur energy at most `−(D−eta) < −D/2`. The selected ground is stored separately. No original source phase, positivity or higher-moment property is copied onto it.

### Canonical M12 interface and acyclic dependency

The following old roots and definition moved unchanged from CanonicalDeepThresholdSelection to CanonicalDeepThresholdGap:

- `nativeDeepThresholdGap` (definition).
- `nativeDeepThresholdGap_pos`.
- `exists_nativeDeepThreshold_bottom_separator`.
- `nativeDeepThreshold_crossing_retains_gap`.
- `nativeDeepThreshold_noncrossing_has_lower_gap`.

NativePoleNeutralTrialDepth now imports Gap. The canonical Selection facade imports Gap and the completed simplicity chain, avoiding a cycle, and exports the required actual statements:

- `exists_bottomAvoidingThreshold`.
- `exists_least_deepPoleNeutralCutoff`.
- `deepThreshold_predecessor_inverse_bound` (all four explicit 6/12 bounds).
- `deepThreshold_selectedParity_simple` (the full actual even/odd alternative).

The root must update exact source-module origin pairs for the moved roots in the compiler/type audit. No old root was renamed or weakened.

### Actual padded source to native retained selection

OriginalDetectorAdmissibleSelector defines a rho-free predicate using actual native data: 4<L; **both** literal padded phase vectors nonzero; **both** literal true-norm phase images of norm one; Kd=ceil(L^4), D=exp(beta L), exact g; 3≤K≤Kd; eta bounds; actual selected bottom depth; all earlier nonempty bottom lower bounds; and the explicit empty-predecessor clause. It contains no rho, no desired Schur upper bound, and no extra detector-energy assumption narrowing the C-Schur upper-bound cut.

OriginalDetectorPaddedRetainedSelection proves that each requested ReversalParity is produced cofinally from an actual off-line zero with the stated beta gap. The producer chooses lateness beyond the common both-phase normalization threshold, then constructs the actual retained state and proves `state.detector = literal native padded source unit`. It proves the phase-independent Admissible predicate at that state's actual eta and cutoff. Both source phases are normalized at that aperture; the two phases do not need a common deep aperture.

The earlier OriginalDetectorNativeRetainedSelection proves the corresponding unpadded source-to-state helpers. It is explicitly labelled as a helper and does not substitute for mandatory positive padding.

### Actual complex arithmetic transforms

Let `R(w)=(w−1/2)/[(w+1/2)(w+3/2)]` and let J be the unchanged literal full-line transform of the actual source j=P²q.

The actual signed correction kernel c has complex Laplace transform R(w) on Rew>−1/2, including a full-line causal bridge and the correct sign. This is derived from the two genuinely integrable exponentials.

The literal stable input Y=c*U has its pointwise exponentially weighted convolution identity and full-line transform product on Rew≥0. Generic causal L1 complex damping integrability and Fubini are proved. No X-L2 or range premise is used.

For Rew>1/2, the actual native square-root integer coefficient times its exponential delay is exactly `1/n^(w+1/2)`, including n=0 under the actual coefficient convention. Each kernel term is integrable, and the integrals of the norms are summable before the sum/integral exchange. This proves the actual a=c*N transform is R(w)ζ(w+1/2).

The literal a transform is analytic on Rew>0 by its independently constructed causal L2 class. The separately proved connected punctured half-plane continuation then gives the same formula for Rew>0, w≠1/2. The exceptional point is evaluated separately using the true ζ residue:

`Laplace(a)(1/2) = 1/2`.

It is not replaced by the incorrect totalized value R(1/2)ζ(1)=0.

For the unchanged U coefficients, the actual log-weighted Dirichlet series is −ζ′(w+1/2), with absolute norm summability paid using the L-series derivative theorem. The literal j damping is integrable by its actual compact support and smoothness. The same justified exchange proves `Laplace(U)(w) = −ζ′(w+1/2) J(w)` first on Rew>1/2.

NativeCompletedInputZetaLaplace then uses actual causal L2 analyticity of U and the **entire actual J** to continue this identity to Rew>0, w≠1/2. Combining it with the already proved c*U product gives:

`Laplace(Y)(w) = R(w) [−ζ′(w+1/2)] J(w)`.

The literal Y transform at w=1/2 is separately zero by the actual c transform and finite actual U transform; no totalized ζ′ value at its pole is substituted.

J's analyticity and formula retain exactly one Q factor: `((I*w)^2+1/4)^2 Q(I*w)`. They consume the common actual-source definition and proved physical Fourier identification. The detector autocorrelation's Q² multiplier is not substituted for J.

## Workflow harvest and D2 evidence

The completed historical head-72bc harvest is in the tracked `WORKFLOW_HARVEST_72bc63fe.json/.md`: 20 runs, 54 jobs, 49 success, 3 failure, 2 skipped, no pending disposition in that snapshot. It identifies the exact checked head/tree and merge tree. All 52 non-skipped logs were read and 27 artifact ZIPs downloaded and digest-checked. Formal validity, frozen regression and research-producing authority are distinguished. The root owns later exact-head inventories.

That historical harvest retained the actual scientific limits: source-decomposition and inherited field contacts remained unresolved where applicable; the composite parity pattern was falsified at its actual scope; frozen SECOND 18/18 replay did not authorize FOURTH; finite K2 windows and generic countermodels retained their historical domains and hypotheses. No green replay became new RH authority.

The ancestral D2 run 38461259594 at head 4789c93f6dd60817936793935211522a0b8100e1 was cancelled during independent 768-bit checking. Its final NON-PARTIAL gate failed because the full checker result was absent. Producer/SECOND assembly and artifact upload had completed. Its archive 11865755269 had exact SHA256 `0077e514187a0cb326170b7b13e9e699d898a2ba10d8b4b20fa75a5cd6072b92`.

The immutable old campaign preserved 256 completed SECOND children, 288 old receipt hashes, 66,395 accepted leaves, and 460 children labelled UNRUN_SECOND_CHILD_CAP. Those 460 were unrun geometry, not failed attempts eligible for a silent retry. The original cap and protocol were not rewritten to claim completion.

The separately reviewed continuation proposal fixed all 460 child IDs and rational endpoints before arithmetic, preserved old receipts, and received explicit user approval: “Approve the 460-child continuation and its stated resource limit”. The approved new protocol fixes 512-bit SECOND, depth48, node8192, 1800seconds per unique child, at most8 globally, two sequential matrix waves256+204 and at most230 search runner-hours. Budget reset, timed-out child retry and historical FOURTH are not authorized.

The implementation freezes source, archive, proposal, geometry and all controls before evaluation; claims each child durably before launch; starts the supervisor clock before Popen; enforces the subprocess limit; uploads checkpoints every45seconds with an upload-time failure stop; preserves partial geometry; and publishes a global negative stop. Exact-name artifact retrieval avoids truncation among the many checkpoint artifacts. Reassembly includes old accepted leaves plus actual new accepted coverage, never missing-child success, and still requires fresh 768-bit all-30-layer independent verification and the unchanged NON-PARTIAL gate.

The initial manual REST dispatch returned404 because the new workflow was not yet registered; no run or child budget was consumed. Root added the narrow branch/path push bootstrap and launched approved production run **38569316691** at **a55fbeeed6500bffe2ccac3960258ca5c590c7ee**. Freeze job115870018390 succeeded. All24 resource controls, archive/source intake and the actual SDK upload→exact-name lookup→byte-identical download preflight passed. The exact plan SHA256 is `433107bbfe412625223fe1f08da36ca7d837bd82e7a536fc50a2d447886cf6ef`.

This agent independently verified the first durable child claim, checkpoints and completed child4 receipt, with API ZIP digests and contained hashes. Child4 was Q13_even_C00_P07_R00001_P0, job115870746281. Its result was PASS,31 tested nodes,16 accepted leaves,0 unresolved,no negative,191.47 worker seconds and192.7392 supervisor seconds. This closes one previously unrun search child's coverage only; its independent final replay remained pending. Root later observed more completed/active search jobs, but this agent did not independently harvest all their scientific artifacts. Therefore this note makes **no blanket scientific PASS claim for those jobs**.

Detailed outside-repo evidence is in `D2_PRODUCTION_FIRST_RECEIPTS.json/.md`, `D2_PRODUCTION_FIRST_COMPLETED_CHILD.json`, the preserved freeze log and exact downloaded ZIPs. Local D2 controls and canonical-Git-LF archive tests passed without running unapproved local arithmetic. Signed artifact download URLs in transient download manifests are not review artifacts and must not be committed or published.

## What changed versus earlier attempts

Proof engineering exposed real interface distinctions. Dependent cutoff rewriting must preserve the bottom's proof arguments. Native nested subtype norms and inner products must use the actual inherited dictionaries; broad unfolding of the old even/odd legal carriers was avoided. The parity wrapper is now a transparent alias with explicit matching actual normed groups. No scalar, metric, source matrix or hypothesis was replaced.

The selected-cutoff least crossing now supplies, rather than assumes, the simplicity and inverse budgets that downstream source/Schur consumers needed. The literal original source producer now reaches a retained detector state, with actual source equality and both normalization clauses. The new complex transforms pay the arithmetic bridge formerly missing between real c calculations and the zeta-zero Hilbert witnesses.

## Upstream implications

The bottom-only finite avoidance theorem is the smaller invariant beneath the selector: there is no need for all-eigenvalue avoidance. Its relocation to Gap removes the dependency cycle without changing its content. Native source-vector normalization has a uniform both-phase threshold, separate from the phase-dependent deep-excursion aperture.

The transform proof cleanly separates local finite integer histories from global absolute norm summability. A pointwise finite history alone is not permission to exchange an unbounded sum and integral. The c multiplier and its removable interaction with ζ are also distinct from the positive a kernel.

## Downstream implications and next review questions

The actual a multiplier supplies the already developed actual-kernel zero-jet composition. The actual Y multiplier now supplies the missing input-side algebra: at a ζ zero of order m, the ζ′ factor should give order m−1 when the actual R and J factors are nonzero. The native-completion agent reports that actual kernel annihilation/range and adjoint-kernel witnesses are green, but intentionally did not start this final **actual input/Y jet-order composition** after the review freeze. It is the precise next mathematical composition for third-party review.

That composition must pay the actual damped variable w+epsilon, positive real-part domain, the exclusion of the ζ pole, actual zero multiplicity including m>1, J nonvanishing at the actual off-line zero, and the distinction between complex Fourier and Laplace signs. It must use the single-Q source J, not the detector correlation transform.

The complete padded detector Schur record is now usable for the native C-Schur cut. The remaining question is a phase-uniform upper bound on the **complete signed scalar**, with constants independent of aperture, threshold, cutoff, phase and branch. The exact negative lower bound is proved; the desired subexponential upper bound is not. An inverse of size polynomial(L)exp(−beta L) alone still loses against a squared crude coupling of order polynomial(L)exp(L), leaving polynomial(L)exp((1−beta)L). A polynomial improvement is not an exponential closing law.

The actual stable Y=c*U membership does not establish that the original prime field X is L2, nor that Y lies in the closure of the actual completion operator's range. Monotone finite residual norms do not imply convergence to zero; the actual adjoint-kernel projection remains an obstruction. The small norm of convolution by a does not make convolution by a invertible: a contraction argument for I−A must not be substituted for an inverse of A.

The D2 continuation still requires complete artifact harvest, exact coverage reassembly, fresh768-bit all30-layer replay and successful NON-PARTIAL verification. Its finite certificate is not a Lean hWindows term without separate formal certificate reconstruction.

## Resurrected routes, clues and falsification

DERIVED: the new source-retained producer can feed the full signed Schur cut on an actual cofinal padded source sequence, rather than an arbitrary supplied trial. DERIVED: actual complex a/Y identities now make a zero-order comparison with the causal analytic obstruction possible. These are compositions to check, not an RH theorem.

LEAD: the most useful structural quantity is the actual full detector Schur loss, because it retains source depth without assuming original-detector overlap with an independently selected ground. Falsify any candidate upper estimate on both phases, strict odd and tied branches, first-cutoff empty predecessors and the entire Kd−K+1-dimensional detector complement. Existing modified-coefficient controls remain relevant: they must match actual divisor/source hypotheses before they constrain this native route.

At the analytic end, the fastest falsification checks are the exact w=1/2 values, multiplicity m>1, Fourier-sign conversion and the single-Q source factor. The proved a(1/2)=1/2 and Y(1/2)=0 demonstrate why totalized pole products are an invalid shortcut.

## Freeze and claim firewall

The precise remaining M20 proposed exports not produced in this scope are `Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_ne_zero` and `Zeta23.ExceptionalZero.nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero`. Their missing proof step is the actual stable-input jet-order/nonzero pairing composition described above; the physical transforms themselves are now proved. `Zeta23.ExceptionalZero.nativeZeroJet_annihilates_range` is reported GREEN in the separate NativeActualKernelZeroJets module, not as a declaration originating in NativeRangeZeroJetObstruction. Source-module audit bindings must retain that actual origin.

For the exact API/manifest review: the new full a-transform name is `Zeta23.CCM.nativePositiveCompletion_complexLaplace`, with arguments `0 < w.re` and `w ≠ 1/2`; its exceptional value is the separate `nativePositiveCompletion_complexLaplace_half`. The proposed older name `nativePositiveCompletion_laplace` was not introduced. The strict mass theorem's actual name remains `nativePositiveCompletion_mass_lt_605_div_621`, rather than the proposed shorthand `nativePositiveCompletion_mass_lt`. Actual full U and Y transform names are `nativeOriginalIntegerDrive_complexLaplace` and `nativeCompletedInput_complexLaplace`; both have the same regular positive-half-plane domain. J's entire-transform helper is `nativeOriginalSourceLaplace_analyticAt`. The rho-free selector's exact type is `AdmissibleDetectorSelector (beta L eta : ℝ) (K : ℕ)`; beta positivity belongs to the outer closing-law quantifiers and the cofinal producer, not as a new hidden selector assumption.

These exports do not themselves fill the whole M22/M23 output packet or prove any M24 unconditional closing law. Final native/paper route coverage, facade imports, renamed proposed exports, exact normalized audit types and module-origin bindings remain acceptance matters for the root's final review document. The intended release still requires every mandatory W00–W10/M01–M25 target and D2's nonpartial final check; this local green list is not a reduction of that scope.

No new search, workflow dispatch, child retry, source edit, theorem composition or closing-law attempt is authorized by this note. All owned local work is stopped; await the user's third-party review. The root owns final commits and exact final workflow harvest.

PROVED here means the exact local Lean statements and axiom checks described above. DERIVED implications are labelled. The actual Y jet-order composition, unconditional range/upper-bound closing laws, complete D2 release, and RH remain OPEN until their exact required gates pass. Green infrastructure, supporting lemmas, numerical receipts and frozen replays are not RH closure.
