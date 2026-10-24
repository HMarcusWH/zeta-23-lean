# PR #294 bounded all-workflow harvest — 2026-10-24

Live branch head `cea7b2f62ea847c18958cc7385151c8c2b09520d`, tree `377c7f6f36375a4ac35d3f3ad17ee95b340eb9eb`. Job snapshot: **2026-10-24 13:50:41 UTC**. This report is a bounded harvest, not full green acceptance. All 22 runs (21 pull-request and 1 push) and all 62 API-materialized jobs are included. Four workflow-declared downstream jobs were not yet materialized. Machine-readable details, individual steps and prior-job comparisons are in [HARVEST.json](HARVEST.json).

The PR synthetic merge `299c15a432a11c432ff108d6fa864d0f0a428c14` has parents main `d53dd70d38b0762af130b1d19b795af259f505f5` and the audited head. Its tree equals the branch tree exactly. Default-checkout workflows tested this synthetic commit; the follow-up workflow explicitly tested the branch head. No synthetic commit was relabelled as branch commit.

## What became formally true

The completed exact-head follow-up narrow candidate job120883714349 reports `PASS_NARROW_ONLY`, clean source and `source_unchanged=true`. Its downloaded artifact contains25 independent consumer files, including ExpectedBoundaryAmplitude and ExpectedCoPoissonJets, covering the20-module candidate build. Every printed consumer axiom closure is drawn from `propext`, `Classical.choice`, `Quot.sound`. W01 checks and W04/W07(52) and W06(14) independent domain/axiom checks also pass. The artifact explicitly says `full_release_accepted=false` and `aggregate_registration_accepted=false`. This replays existing narrow proof authority at the current head; it adds no primary root beyond the pre-existing41historical+49narrow ledger.

Other completed formal jobs replay registered, exceptional-zero, closure, post287, post284, contact-calculus and Permansson surfaces. Their hypotheses remain part of their statements. The broad main build has inherited linter warnings. No premise-free RH theorem or full100 acceptance was established.

## Workflow harvest

Job dispositions: {"completed/success":32,"completed/failure":6,"queued/null":14,"in_progress/null":6,"completed/skipped":4}. Running, queued and skipped work is not success. Scientific dispositions are attached to exact run/job identities; a companion PR result never passes a queued push job. Each primary classification is retained per job; scientific pipelines also replay frozen regressions.

| Workflow / event | Run | API run result | Jobs at bounded snapshot |
|---|---:|---|---|
| RHRC research and Lean checks / pull_request | [40097106377](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106377) | queued/null | lean: completed/success; python-rhrc: completed/failure; rhkg-compiler-receipt: completed/failure; r003-normalization-audit: queued/null |
| RHRC parallel closure campaign / pull_request | [40097106381](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106381) | queued/null | lean-first-crossing: completed/success; lean-contact: queued/null; lean-strength-audit: completed/success; fast-integrity: queued/null; lean-d-bindings: completed/success; lean-b: in_progress/null; lean-a: queued/null; lean-c: queued/null |
| RHRC post287 focused Step3 checks / pull_request | [40097106305](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106305) | completed/success | lean-step3: completed/success; wp5-modified-prime: completed/success |
| RHRC post268 complete audit replay / pull_request | [40097106323](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106323) | queued/null | Audit runner adversarial regressions: completed/success; Extended audit shard 3: completed/success; Extended audit shard 5: queued/null; Extended audit shard 2: queued/null; Extended audit shard 7: queued/null; Extended audit shard 6: queued/null; Extended audit shard 0: queued/null; Extended audit shard 1: queued/null; Extended audit shard 4: queued/null |
| RHRC post287 bounded signed-ray probe / pull_request | [40097106372](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106372) | completed/success | wp6-source-specific-signed-ray: completed/success |
| RHRC post-190 canonical realizability audit / pull_request | [40097106367](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106367) | completed/success | post190-canonical-realizability: completed/success |
| RHRC post-200 Q14 discrepancy mechanism / pull_request | [40097106406](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106406) | completed/success | post200-q14-discrepancy-mechanism: completed/success |
| RHRC post-202 Q14 composite parity gap / pull_request | [40097106336](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106336) | completed/success | post202-q14-composite-parity-gap: completed/success |
| RHRC post-196 Q14 residual cell replay / pull_request | [40097106356](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106356) | completed/success | post196-q14-residual-cell-replay: completed/success |
| RHRC post-222 bi-regular zero-shift scalar / pull_request | [40097106290](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106290) | completed/success | post222-biregular-zero-shift-scalar: completed/success |
| RHRC post-214 kernel dual geometry / pull_request | [40097106286](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106286) | completed/success | post214-kernel-dual-geometry: completed/success |
| Permansson v0.1.6 formal verification / pull_request | [40097106316](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106316) | completed/success | lean-permansson: completed/success |
| RHRC post287 WP2 and WP4 interval research / pull_request | [40097106364](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106364) | completed/success | wp4-k2-odd-prerequisite: completed/success; wp2-k2-transcript: completed/success; wp4-k3-frozen-feasibility: completed/success; wp4-k3-fourth-order-alternative: completed/skipped |
| RHRC post-192 parity trajectory rigidity / pull_request | [40097106317](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106317) | completed/success | post192-parity-trajectory-rigidity: completed/success |
| OPICA follow-up draft checkpoint / pull_request | [40097106349](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106349) | in_progress/null | Full release readiness (expected FAIL while scope is incomplete): completed/failure; Draft preparation contract (no theorem authority): completed/success; Exact-source implemented subset (full 100 remains required): in_progress/null; Narrow repaired candidates (aggregate acceptance remains open): completed/success; Frozen regression and fail-closed evidence tests: completed/success |
| RHRC OPICA full paper components / pull_request | [40097106418](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106418) | completed/failure | opica-regression: completed/success; opica-contract: completed/failure; opica-component-summary: completed/failure; opica-formal: completed/skipped; opica-dependency-delta: completed/skipped |
| RHRC post-194 parity trajectory sharp enclosure / pull_request | [40097106363](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106363) | completed/success | post194-parity-trajectory-sharp-enclosure: completed/success |
| RHRC post290 source and output proof components / pull_request | [40097106329](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106329) | completed/success | native-observations: completed/success; exact-controls: completed/success; lean-components: completed/success |
| RHRC post-198 Q14 parity source mechanism / pull_request | [40097106371](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106371) | completed/success | post198-q14-source-mechanism: completed/success |
| RHRC post-284 source inertia campaign / pull_request | [40097106328](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106328) | in_progress/null | lean-source-inertia: completed/success; source-falsifier-research: in_progress/null; post287-full-k3: completed/skipped |
| RHRC post-282 contact calculus / pull_request | [40097106361](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097106361) | in_progress/null | research-calibration: in_progress/null; lean-compressed-calculus: completed/success; lean-contact-completion: in_progress/null |
| OPICA follow-up draft checkpoint / push | [40097102752](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/40097102752) | queued/null | Draft preparation contract (no theorem authority): completed/success; Full release readiness (expected FAIL while scope is incomplete): completed/failure; Exact-source implemented subset (full 100 remains required): in_progress/null; Narrow repaired candidates (aggregate acceptance remains open): queued/null; Frozen regression and fail-closed evidence tests: queued/null |

### Scientific dispositions of completed green jobs

- The bounded signed-ray artifact says `FALSIFIED_AT_BOUNDED_TRUE_SOURCE_APERTURES`: unrestricted physical Q>=0 on all B>0 shifted K2 rays fails. Q is positive at B=3/20 and negative at B=69/100. The artifact explicitly excludes first contacts, the #247 selected ground, universal cancellation and RH from its claims.
- Q14 kernel dual geometry certifies dual independence and **full-space sign indefiniteness** together; OBS059i stays open.
- Canonical realizability retains an exact twin through layers 0/1 and general reflection; a specific layer 2 identity excludes it, while layers 3–5 remain UNRESOLVED.
- The original trajectory rigidity run remains UNRESOLVED (0 certified fraction); the sharper run covers63/64; the residual-cell replay completes a bounded J_POSITIVE hull. These are three different frozen questions, not contradictory current outcomes.
- Q14 source decomposition and discrepancy representation remain dependency-UNRESOLVED. The composite parity-gap pattern is **FALSIFIED before full cover**; no cover executed.
- The biregular zero-shift check certifies no frozen cell-minimal state (0 qualifying points).
- WP2 independently verifies1310 K2 intervals at192 bits; the odd prerequisite verifies350 intervals. WP4 passes18/18 frozen K3 boxes. Its output explicitly rejects interpretation as a continuous K3 positivity theorem; the fourth-order alternative is consequently skipped.
- The altered-prime WP5 model exhibits an interval-certified even sign change with odd positivity; true-zeta even values at both sampled endpoints stay positive. This is a non-zeta control.
- Post290 native observations independently reconstruct44 pairs at1024 bits:0 discrepancies/0 unresolved. The independent scalar arithmetic shares its analytic backend; universal and generated-detector scope stays open.
- Post290 component formal output is `PARTIAL_OUTPUT_RH_OPEN`:1664 audited roots/full Exprs and30 constructor types, but `producer_complete=false` and `independent_assumption_review_pass=false`. The44-field dossier remains UNAPPROVED.
- Post268 completed shard 3 executes six checks. Its legacy CCM–Weil assembly diagnostic explicitly has uncertified zero/Archimedean tails and no bridge-proof authority. The full 44-check harvest is pending.
- Frozen OPICA regression job120883714427 passes 185 child and 82 parent contract tests in both Python modes, and 5112/18862/14672/1274finite controls per mode. All 3 numerical suites remain CONSISTENCY_ONLY.

### Actual failures and incompleteness

- Both follow-up release gates retain `FAIL_RELEASE_INCOMPLETE`: no full100receipt and unwired independent release companions.
- Parent opica-contract and python-rhrc reject the absent full child reviewed-type table, then1346 static errors including unauthorized follow-up additions. These actual failures are deliberately preserved; static presence alone is not theorem authority.
- rhkg-compiler-receipt successfully extracts 14100 declarations from 194 registered roots, then fails canonical freshness because 39 follow-up standalone modules lack dispositions. No canonical graph regeneration is accepted.
- opica-formal and opica-dependency-delta are skipped after the failed parent contract; opica-component-summary fails.
- Four declared downstream jobs are still unmaterialized: campaign-complete, Complete 44-check execution harvest, arb-contact-balance, contact-calculus-complete. Their prerequisites remain pending.

## What changed

Against the c6ce649d partial harvest,13 matched completed research jobs have exactly equal parsed mathematical JSON outputs. Native44-pair panel data also remain exactly equal; its changed artifact hash was investigated: only source_identity commit/tree and44 elapsed_seconds fields differ. [native-panel-differences.json](native-panel-differences.json) records them.

The former c6ce649d source-falsifier-research job120868137077 is now confirmed **cancelled**, not passed. The formerly-running Q14discrepancy and WP2/WP4 jobs completed successfully. Current candidate CI now includes20 modules/25 consumers; the older c6ce649d narrow gate covered18 modules/23 consumers. Aggregate acceptance stays open.

## Upstream implications

PROVED in the preserved source-level programme: the multiplicity-sensitive zero-jet construction now has exact-head narrow consumer replay. Its zero dependence is isolated in analytic order and the vanishing boundary factor; generic-family identities should be reused for the confluent finite-span argument. Infrastructure freshness failures must be repaired through the full review/registration/disposition process, without loosening the gate.

## Downstream implications

DERIVED: current narrow CI supports proceeding to confluent independence and finite-span signed-measure restrictions while preserving the original physical contracts. The numerical sign-indefiniteness results require any positivity route to exploit the actual constrained cone; full-space positivity is unavailable. Neither finite Gram positivity nor the18frozen K3 boxes supplies the required global limit/selection theorem.

## Resurrected routes

LEAD: the completed zero-jet family supplies the previously-missing input to the confluent determinant and separator routes. No workflow replay rescues the falsified unrestricted shifted-ray inequality or composite parity-gap pattern. A revival requires a smaller, source-specific admissible domain and a new proof.

## New RH-relevant clues

LEAD: combine the zero-jet first-cell Hermite data, reflection-identification and signed-separator theorem to exclude finite positive repairs in a nontrivial finite span. LEAD: identify a canonical constrained sign cone compatible with actual zero forcing. These are hypotheses to test, not RH consequences already established.

## Falsification checks

The green wrappers preserve explicit falsifications and unresolved results above. Future sign arguments should first be checked at B=3/20 and69/100, against the full-space indefinite dual geometry, against reflected-node duplication, at zero/multiplicity boundaries, and against altered-prime controls. Eighteen frozen boxes cannot be promoted to a continuum cover. No unsigned/absolute-value replacement of the physical signed quantity is justified.

## Highest-leverage next moves

1. Finish the original force-sampling consumer with an independent full-type/domain consumer; then confluent determinant/independence and finite-span restrictions.
2. Preserve full100, parent-extension, external semantic review, canonical freshness and workflow-completeness as separate OPEN obligations.
3. Harvest the still-running/queued jobs after completion, especially source-falsifier-research and the remaining post268 shards. Do not push merely to stop them and then call the harvest complete.
4. Prefer a theorem that restricts the admissible zero-generated cone over larger frozen sample counts.

**RH, Step4, full aggregate acceptance and the independent closing inequalities remain OPEN.**
