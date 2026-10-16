# PR292 workflow harvest — b716fad7 historical snapshot

Snapshot **2026-10-13 23:21:04 UTC**. Exact branch HEAD b716fad759ca545352741057a203b866e2973585; tree d1981cdb54927b931cbcae02f6f4fcf15972d17f. The PR runner checkout 9f27c6ade8c7163d85831df977d47060a01e1398 has the same tree and the reviewed main+branch parents. Audit jobs explicitly check the branch; other checked PR jobs use the synthetic merge. API heads are preserved separately from runner identities.

All **20 runs / 54 job attempts** are classified from their exact workflow sources: 39 success, 2 failure, 10 cancelled, 2 skipped and **one WP2 transcript still running**. First-crossing API success has **OUTPUT_UNAVAILABLE**, so it creates no authority upgrade. The formal component job failed; its PR counterpart was cancelled. Full release and RH remain **OPEN**.

The [companion JSON](WORKFLOW_HARVEST_b716fad7.json) records all run/job IDs, source blobs, dispositions, decoded-log hashes and public artifact ZIP digests. The full detailed local review is bound by SHA-256 **201bda935052a26acd8b13034aaa3193bbad4b390ef5c7824f7b5a24f1653fc1**. This public index contains no raw artifacts, signed URLs or private review archive files. Artifact metadata was collected separately at 23:28:46 UTC; the later WP2 ZIP is explicitly unreviewed and does not rewrite the frozen running status.

| Run / job | Name | Source class | API result | Reviewed disposition |
|---|---|---|---|---|
|38480838046 / 115582738575|post190-canonical-realizability|RESEARCH_PRODUCING_CHECK|completed/success|CANONICAL_REALIZABILITY_LAYER3_TO5_UNRESOLVED|
|38480837395 / 115582735333|post202-q14-composite-parity-gap|RESEARCH_PRODUCING_CHECK|completed/success|COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED|
|38480837272 / 115582734714|wp2-k2-transcript|RESEARCH_PRODUCING_CHECK|in_progress/null|RUNNING_OR_QUEUED_UNESTABLISHED|
|38480837272 / 115582734906|wp4-k3-frozen-feasibility|RESEARCH_PRODUCING_CHECK|completed/success|BOUNDED_SECOND_GATE_PASS_18_FROZEN_BOXES|
|38480837272 / 115582735105|wp4-k2-odd-prerequisite|RESEARCH_PRODUCING_CHECK|completed/success|INTERVAL_EVIDENCE_FIXED_K2_ODD_PREREQUISITE|
|38480837272 / 115589946583|wp4-k3-fourth-order-alternative|RESEARCH_PRODUCING_CHECK|completed/skipped|NOT_EXECUTED_SOURCE_GUARD_REVIEWED|
|38480837416 / 115582735842|post214-kernel-dual-geometry|RESEARCH_PRODUCING_CHECK|completed/success|FULL_SPACE_DUAL_INDEPENDENCE_AND_SIGN_INDEFINITENESS_CERTIFIED|
|38480837600 / 115582736288|Audit runner adversarial regressions|REGRESSION_GATE|completed/success|AUDIT_PRODUCER_CONSUMER_GUARDS_PRESERVED|
|38480837600 / 115582736553|Extended audit shard 2|RESEARCH_PRODUCING_CHECK|completed/success|FROZEN_ASSIGNED_CHECK_PIPELINES_EXECUTED|
|38480837600 / 115582736671|Extended audit shard 3|RESEARCH_PRODUCING_CHECK|completed/success|FROZEN_ASSIGNED_CHECK_PIPELINES_EXECUTED|
|38480837600 / 115582736703|Extended audit shard 7|RESEARCH_PRODUCING_CHECK|completed/success|FROZEN_ASSIGNED_CHECK_PIPELINES_EXECUTED|
|38480837600 / 115582736707|Extended audit shard 0|RESEARCH_PRODUCING_CHECK|completed/success|FROZEN_ASSIGNED_CHECK_PIPELINES_EXECUTED|
|38480837600 / 115582736715|Extended audit shard 5|RESEARCH_PRODUCING_CHECK|completed/success|FROZEN_ASSIGNED_CHECK_PIPELINES_EXECUTED|
|38480837600 / 115582736733|Extended audit shard 4|RESEARCH_PRODUCING_CHECK|completed/success|FROZEN_ASSIGNED_CHECK_PIPELINES_EXECUTED|
|38480837600 / 115582736780|Extended audit shard 6|RESEARCH_PRODUCING_CHECK|completed/success|FROZEN_ASSIGNED_CHECK_PIPELINES_EXECUTED|
|38480837600 / 115582736856|Extended audit shard 1|RESEARCH_PRODUCING_CHECK|completed/success|FROZEN_ASSIGNED_CHECK_PIPELINES_EXECUTED|
|38480837600 / 115589475068|Complete 44-check execution harvest|REGRESSION_GATE|completed/success|COMPLETE_44_CHECK_EXECUTION_HARVEST_VERIFIED|
|38480837349 / 115582735742|wp6-source-specific-signed-ray|RESEARCH_PRODUCING_CHECK|completed/success|EXPERIMENTAL_SIGNAL_BOUNDED_SHIFTED_RAY_FALSIFIER_PRESERVED|
|38480837635 / 115582735849|post200-q14-discrepancy-mechanism|RESEARCH_PRODUCING_CHECK|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837400 / 115583178271|source-falsifier-research|RESEARCH_PRODUCING_CHECK|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837400 / 115583178547|lean-source-inertia|FORMAL_VALIDITY_GATE|completed/success|SUPPORTING_HISTORICAL_COMPILER_AND_SCOPE_GATES_PRESERVED|
|38480837400 / 115583179702|post287-full-k3|RESEARCH_PRODUCING_CHECK|completed/skipped|NOT_EXECUTED_SOURCE_GUARD_REVIEWED|
|38480837310 / 115582736291|exact-controls|REGRESSION_GATE|completed/success|EXACT_AND_INTEGRITY_CONTROLS_PRESERVED|
|38480837310 / 115582736694|native-observations|RESEARCH_PRODUCING_CHECK|completed/success|CHECKED_FINITE_NATIVE_OBSERVATIONS_UNIVERSAL_OPEN|
|38480837310 / 115582737053|lean-components|FORMAL_VALIDITY_GATE|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837389 / 115582736661|post192-parity-trajectory-rigidity|RESEARCH_PRODUCING_CHECK|completed/success|TRAJECTORY_RIGIDITY_UNRESOLVED|
|38480837369 / 115582735521|lean-permansson|FORMAL_VALIDITY_GATE|completed/success|EXISTING_MARKOV_PATH_LAW_THEOREM_COMPILED|
|38480837271 / 115582734805|wp5-modified-prime|RESEARCH_PRODUCING_CHECK|completed/success|MODIFIED_PRIME_CROSSING_INTERVAL_EVIDENCE|
|38480837271 / 115582734958|lean-step3|FORMAL_VALIDITY_GATE|completed/success|SUPPORTING_HISTORICAL_COMPILER_AND_SCOPE_GATES_PRESERVED|
|38480837348 / 115582735014|post194-parity-trajectory-sharp-enclosure|RESEARCH_PRODUCING_CHECK|completed/success|SHARP_ENCLOSURE_REPLAY_WITH_UNRESOLVED_SPAN|
|38480837690 / 115582737337|post222-biregular-zero-shift-scalar|RESEARCH_PRODUCING_CHECK|completed/success|NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED|
|38480837637 / 115582736442|post196-q14-residual-cell-replay|RESEARCH_PRODUCING_CHECK|completed/success|RESIDUAL_CELL_J_UNRESOLVED_PRESERVED|
|38480837571 / 115584046247|lean-contact-completion|FORMAL_VALIDITY_GATE|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837571 / 115584046518|lean-compressed-calculus|FORMAL_VALIDITY_GATE|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837571 / 115584046556|research-calibration|RESEARCH_PRODUCING_CHECK|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837571 / 115589931269|contact-calculus-complete|REGRESSION_GATE|completed/failure|GATE_FAILED|
|38480837571 / 115589931791|arb-contact-balance|RESEARCH_PRODUCING_CHECK|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837402 / 115583249972|lean|FORMAL_VALIDITY_GATE|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837402 / 115583250275|python-rhrc|REGRESSION_GATE|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837402 / 115583250287|r003-normalization-audit|RESEARCH_PRODUCING_CHECK|completed/success|SCOPED_NORMALIZATION_AND_FALSIFIER_REPLAYS_PRESERVED|
|38480837402 / 115583250317|rhkg-compiler-receipt|REGRESSION_GATE|completed/cancelled|CANCELLED_UNESTABLISHED|
|38480837505 / 115582735961|post198-q14-source-mechanism|RESEARCH_PRODUCING_CHECK|completed/success|SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED|
|38480837255 / 115582735025|lean-c|FORMAL_VALIDITY_GATE|completed/success|SUPPORTING_HISTORICAL_COMPILER_AND_SCOPE_GATES_PRESERVED|
|38480837255 / 115582735275|lean-strength-audit|FORMAL_VALIDITY_GATE|completed/success|SUPPORTING_HISTORICAL_COMPILER_AND_SCOPE_GATES_PRESERVED|
|38480837255 / 115582735281|lean-d-bindings|FORMAL_VALIDITY_GATE|completed/success|SUPPORTING_HISTORICAL_COMPILER_AND_SCOPE_GATES_PRESERVED|
|38480837255 / 115582735336|lean-b|FORMAL_VALIDITY_GATE|completed/success|SUPPORTING_HISTORICAL_COMPILER_AND_SCOPE_GATES_PRESERVED|
|38480837255 / 115582735358|lean-a|FORMAL_VALIDITY_GATE|completed/success|SUPPORTING_HISTORICAL_COMPILER_AND_SCOPE_GATES_PRESERVED|
|38480837255 / 115582735388|lean-first-crossing|FORMAL_VALIDITY_GATE|completed/success|SUCCESS_LABEL_WITH_OUTPUT_UNAVAILABLE|
|38480837255 / 115582735538|lean-contact|FORMAL_VALIDITY_GATE|completed/success|SUPPORTING_HISTORICAL_COMPILER_AND_SCOPE_GATES_PRESERVED|
|38480837255 / 115582735585|fast-integrity|REGRESSION_GATE|completed/success|EXACT_CLOSURE_INTEGRITY_PRESERVED|
|38480837255 / 115587861450|campaign-complete|REGRESSION_GATE|completed/success|HISTORICAL_CLOSURE_DEPENDENCY_GATE_PASSED|
|38480831587 / 115582716175|lean-components|FORMAL_VALIDITY_GATE|completed/failure|GATE_FAILED|
|38480831587 / 115582716300|native-observations|RESEARCH_PRODUCING_CHECK|completed/success|CHECKED_FINITE_NATIVE_OBSERVATIONS_UNIVERSAL_OPEN|
|38480831587 / 115582716367|exact-controls|REGRESSION_GATE|completed/success|EXACT_AND_INTEGRITY_CONTROLS_PRESERVED|

## What became formally true

PROVED supporting scope: five characteristic-law roots and eleven M14 canonical channel, residual, variance, Gram and compression-symmetry roots compiled at this exact branch checkout with only propext, Classical.choice and Quot.sound. The JSON binds every root to its source blob and successful individual target output. The complete component/binding/proof-escape/axiom receipt did not pass. Failed Mass integrability output contains sorryAx and supplies no formal bridge.

## Workflow harvest

The source-bound 44-check audit now validates all eight shard reports, all 44 log hashes and pipeline memberships, with zero missing, duplicate or failed checks. The previous 6ae receipt had 27 results, 17 missing and two source_after errors. Shared execution dispositions are unchanged. Relative to the inventory baseline, 30 environment blocks, one missing-input failure and one timeout now execute successfully. These changes restore checked coverage; theorem promotion remains false and scoped unresolved/falsified outcomes remain visible.

Both native runs freshly checked 44 pairs / 176 fixed rows, zero unresolved, with a 1024-bit checker sharing the analytic backend. Their pair values and source maps match 6ae after excluding only elapsed time. Odd K2 verifies 350 intervals over [1/512,log16] at 192 checker bits. SECOND preserves all 18 frozen box payloads, finishing in 1197.87 seconds; the fourth-order alternative is skipped. WP2 remains running in this snapshot. Historical even [1/400,log16] and odd [1/512,log16] domains stay separate; the even [1/512,1/400] sliver remains OPEN.

## What changed

The characteristic and M14 supporting statements gained actual compiler evidence. Complete 44-check coverage and 58 closure-integrity controls replace incomplete/stale historical gates. The shared numerical states remain preserved; neither a whole-kernel mass theorem nor full-domain K3 positivity follows.

## Upstream implications

The characteristic law isolates the remaining tail and density-transform obligations. M14 exposes canonical residual/Gram identities with their actual matrix, carrier and vector hypotheses. Preserve source identity and normalization when transporting these facts.

## Downstream implications

DERIVED: correctly matched finite native panels can be interpreted through the compiled M14 identities. Generated-detector vectors, original-source inversion, universal tails and ground exclusion remain OPEN. A strict native mass contraction still requires the successful analytic head/tail and measure-substitution bridge.

## Resurrected routes

The direct native mass route remains worth compiling: independent rational arithmetic supports its target comparison, while the analytic bridge failed at Mass line 25. Source-tail, pole-neutral intertwining and index-rigidity repairs remain concrete prerequisites. Unrestricted shifted-ray positivity stays falsified.

## New RH-relevant clues

LEAD: compose the genuine characteristic law with a source-bound tail/density transform, and compose M14 with actual generated detector data. These are hypotheses for the next investigation; they supply no RH-equivalent conclusion.

## Falsification checks

Attack source substitution, arbitrary probes relabelled generated, omitted Fourier tails, normalization/tie restrictions and unverified interval seams. The full replay preserves finite countermodels, mixed margin signs and uncertified Weil tails. Green replay creates no new theorem authority.

## Highest-leverage next moves

Compile and inspect the remaining exact source and pole-neutral interfaces before claiming producer completion. Preserve original D2 run 38461259594 until its archive exists, then revalidate exact source identity and freshly replay every 768-bit leaf in frozen 512-leaf shards. At the recorded 23:19:46 observation, D2 was still executing its original SECOND passes with zero artifacts; candidate assembly and all final checks were pending. Complete the original 25-module / 11-work-package scope. D2 and RH remain OPEN.
