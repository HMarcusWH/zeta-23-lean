# OPICA second continuation: audit and remaining build work

22 October 2026, Europe/Stockholm. This reviews the 18 latest uploaded files against PR #294 head `9b6a9a3a2badb4cff62a56c1158d9cef8759d30d`, tree `545ea182910db9c8d05c4c7e8ee229d119a9aa28`.

The specifications and foundational material are available. Further documents are not the immediate blocker. The remaining work is to write the 48 absent primary proofs, repair and validate the 11 delivered candidates, and complete the unchanged full acceptance contract.

| Original primary-root scope | Count | Authority |
|---|---:|---|
| Previously locally verified subset | 41 | Existing exact-source subset receipt; full release remains incomplete |
| New primary candidates in this delivery | 11 | Unaccepted; source checks expose failures or blocked dependencies |
| Primaries without a complete candidate in this delivery | 48 | OPEN implementation obligations |
| Newly accepted from this review | 0 | No candidate promoted |

All 59 outstanding roots still need their acceptance gates. Passing a leaf module, selected Python tests or a validation-module build alone would not establish full acceptance.

## Inputs, preservation and checkout boundary

All 18 files were copied into `input/` and hashed in INPUT_MANIFEST.json. Final rehashing confirms the original Downloads uploads are unchanged and all eight Lean files in the isolated review checkout match those uploaded bytes. The main PR checkout remains clean at the head/tree above; no review change was committed or pushed.

The three existing module overlays add source and imports without deleting existing source lines. The five other modules are new candidate files. Neither foundational PDF, the original normative Markdown/JSON, the original 100-root inventory nor the parent mathematical sources were edited. ROOT_LEDGER_100.json preserves every original root identity and its complete frozen statement/domain contract, alongside this delivery's separate status.

The existing refreshed PARENT_INTAKE.json remains authoritative for the accepted parent: merged commit `d53dd70d38b0762af130b1d19b795af259f505f5`, tree `12691099f1a155a8bfa3ad4f6689146175b233b2`, equal to the tested original/synthetic parent tree. Its earlier downloaded compiler artifact was revalidated for 76 parent roots, 613 public declarations and 8 constructors. Its complete earlier harvest records 59 successful effective jobs and two reviewed skips. This review independently verifies the immutable parent capture through the proposed wrapper; it does not pretend to have run a new complete parent compiler receipt.

Lean checks used the pinned Lean 4.33.0-rc2, compiler commit `d8b18978322de05a8f3dba51ef03cf5461676c17`, and pinned Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`. Missing inherited prerequisites were built narrowly in the isolated checkout. A cached old support-module object was never counted as successful compilation of its uploaded replacement.

## Lean and mathematical review

| Uploaded module | Target primaries | Actual disposition |
|---|---:|---|
| MaskedNativeRate | 2 | FAIL: actual uploaded-source errors in square-root limits, pinned APIs, measure/Lp inference and later dependent declarations |
| AuxiliaryCompletions | 3 | FAIL after building WeightedLaplace: real/complex polynomial coercions, Fourier/Poisson rescaling, summation and analytic/logarithmic proofs do not elaborate |
| ComplexLocalMeasures | 1 | FAIL: interval normalization, dyadic-tail powers, integral rewrites and finite-mass obligations |
| MultiplicityTail | 1 | BLOCKED in the genuine candidate chain by failed auxiliary source; an explicitly diagnostic-only inherited-Aux check also finds a wrong-case Mathlib import |
| DilatedComb | 1 | FAIL against the inherited complex support object: missing APIs, casts, local-finiteness/Jordan normalization, a parser error and Fourier scaling; this is not a successful check of the new complex dependency |
| RenormalizedCoPoisson | 1 | FAIL after building ZetaRealStripNonvanishing: parser errors, cast/algebra obligations and nonexistent complex hyperbolic-function APIs |
| FirstCellCost | 1 | BLOCKED before its proof body: the uploaded RenormalizedCoPoisson cannot supply a checked object |
| Consumers | 1 | BLOCKED before its proof body by missing inherited NativeJetAdapter.olean; its prerequisite build was deliberately stopped after expansion into a substantial parent rebuild |

The MultiplicityTail import is `Mathlib.Analysis.InnerProductSpace.L2Space`; the pinned file is `Mathlib.Analysis.InnerProductSpace.l2Space`. On Windows the wrong-case import collides with the already loaded module; on a case-sensitive filesystem that named module path does not exist. Its full proof body has not been validated in the genuine candidate environment.

The Consumers prerequisite target produced successful intermediate parent-module rebuilds but did not finish. Its displayed Lake target count expanded as additional dependencies were discovered; a static project import-closure check still found roughly 200 missing inherited project objects. The review stopped that preparation build rather than presenting its progress as a consumer result. Its terminal interruption is not a mathematical failure. The exact original Consumers invocation remains an import-cache block; no successful consumer-body check or axiom audit is claimed. A complete cached parent environment or clean CI rebuild is needed for that check.

The first-cell sign source also writes `<|gamma|` in hypotheses. Lean parses `<|` as application syntax, so the intended less-than followed by absolute value needs explicit spacing or parentheses. The cost theorem remains a separate dependency-blocked candidate; no admitted stub was used to manufacture a result.

Semantic inspection supports the intended directions: actual moving-palette window fields, the completion profile's endpoint atom, both Fourier signs, the filled half-point value, arbitrary-multiplicity Laguerre normalization, common-growth Schwartz convergence and literal finite-power-sum first-cell density. These inspections do not upgrade failed sources to PROVED.

There is a public-interface issue in the mask bounds: the proof chooses constants from fixed parameters, but the theorem type places the existential constants after the varying schedule/palette parameters. The frozen uniform statement should be exposed by a checked interface or independent uniform-strengthening consumer. Its rate-difference orientation also deserves an explicit expected-type consumer.

Module coverage is incomplete beyond root names. Required planned interfaces such as `nativeTruncatedResidual`, `tailMemory`, `dilatedComb`, `combPairing`, the global co-Poisson constructions and `FollowupNativeOutput` are not declared under their planned names in this delivery. Some alternative definitions may supply appropriate aliases; others represent the still-missing constructions. MODULE_CONTRACT_GAPS.json lists every actual import/refinement and missing planned name. Record such refinements explicitly rather than silently changing frozen manifests.

Detailed evidence is in MEASURE_AND_FIRST_CELL_REVIEW.md, theory-SEMANTIC_REVIEW.md, maskconsumer/MATHEMATICAL_REVIEW.json and the compiler logs. An interrupted mask repair draft is preserved externally under an abandoned label only; the reviewed overlay was restored to the exact upload and the draft carries no acceptance.

## Authentic CI failure and incomplete proposed repair

The supplied PR294_9b_subset_formal_failure.zip has SHA-256 `8a83803e516fc5e4817a375c30efaefb75a3d980e0e26f7c2a9f21410d9b67e1`. This matches GitHub's live provider digest for the PR-event subset artifact. The separately uploaded build.log and export.log are byte-identical to the ZIP members.

The validation build completed successfully, 4223 jobs. The exporter then failed on missing OpicaTypeExprExport.olean. This is an exporter prerequisite failure, not evidence that export or the entire subset CI passed. The earlier warm-cache local receipt and this cold CI failure describe different executed environments and are not contradictory.

The uploaded build_receipt.py adds OpicaTypeExprExport, but misses another direct project import: SourceCandidateResolution. That module is outside the complete project import closure of both proposed build targets. The current workflow supplies only a Mathlib cache before calling the builder. The cold repair must therefore explicitly build all three targets before export:

- `Zeta23.OPICAFollowup.Validation`
- `Zeta23.RHRC.OpicaTypeExprExport`
- `Zeta23.RHRC.SourceCandidateResolution`

cold-export-prerequisites.patch contains that adjustment against the current main checkout and passes `git apply --check`. It was not applied to the PR or executed as a fresh complete compiler receipt. It retains the exact existing 41-root selection and cannot make the full release ready.

## Python integration review

The supplied four short logs report 30 selected parent tests and 26 child tests per Python mode, without commands or individual test identities. Independent execution used an isolated byte-exact Git fixture and preserved the initial failed fixture attempts separately. The initial fixture inherited automatic line-ending conversion; its resulting descriptor hash failures were fixture failures, not relabelled as candidate passes.

Final runnable results in both normal Python and `-O`:

| Selection | Per-mode result | Relationship |
|---|---:|---|
| Runnable parent tests | 54 passed | Two of the full 56 are locally environment-blocked |
| Documented selected parent subset | 29 passed | Subset of the 54; remaining historical-Git test blocked |
| Projection tests runnable locally | 20 passed | Subset of the 54; real symlink test blocked |
| Existing child extension tests | 26 passed | Complete selected child module |

Thus 80 distinct selected tests pass per mode, not 129 distinct tests and not the entire repository suite. The actual full-56 parent attempts remain non-green. The blocked cases require a missing historical Git object and real file-symlink privileges, respectively. These are not proof requirements to be supplied by the user; they need an appropriate complete-checkout/CI environment. Commands, fixtures and dispositions are recorded under contracts/.

Independent adversarial probes found three real review gaps even though the runnable supplied tests pass. The structural child review helper accepts:

1. Route-authority metadata on both child claim and binding.
2. An empty child statement.
3. Unknown, self-referential and duplicate dependency identities.

The projected parent registration checks do not apply the corresponding metadata checks to those removed child rows. Add validation of those fields before projection and add mutation tests. These are latent full-extension defects; they do not turn the current incomplete checkpoint into an accepted full extension.

The actual current 41-root wrapper correctly rejects the absent full reviewed type table, preserves the raw parent context and returns an empty delta allowlist. Reframed parent-byte and registry captures are rejected. These results are preserved in contracts/INDEPENDENT_PROBES.json; the separate full parent static check is explicitly environment-blocked by the historical Git cache. The wrapper is structural validation, not a substitute for source-bound compiler evidence for all 100 roots.

## What is needed to finish

REMAINING_BUILD_WORK.md lists all 48 absent roots, grouped by their 20 planned modules. ROOT_LEDGER_100.json carries their complete original statement contracts. The eight-area summary is native multiplicity/rates (5), weighted mixtures (4), near-gap limits (4), global co-Poisson construction (3), profiles/Sobolev/sampling/separation (14), square/sawtooth (7), spectral/boundary (7), and final consumers (4).

For the eleven supplied candidates: repair the compiler failures, restore the exact required interfaces, complete independent expected-type and actual-domain consumers, and check all assumptions and boundary controls. For the whole PR: finish facade/import coverage, all public/helper/constructor and dependency export, source/type review, parent extension hardening, registration, canonical regeneration, generated-state freshness, full workflow implementation and exact-head acceptance. A guarded final patch and compiler-bound delivery record remain necessary.

The additional Post-Green Amendment results remain separately identified research/supporting lemmas unless explicitly promoted through a versioned amendment. The original acceptance scope and all 100 primary identities remain intact.

## Post-Green research state and required continuation

**What became formally true.** No new primary from this upload. Narrow inherited dependency builds succeeded and preserve existing mathematics; failed candidate files provide no new theorem authority. The existing 41-root local subset receipt remains the baseline, not full release acceptance.

**Workflow harvest.** A fresh live inventory captured 22 completed runs and 64 instantiated jobs at the current head: 52 success, 8 failure, 4 skipped. Both subset export jobs and both full-readiness jobs failed; preparation and frozen-regression jobs succeeded. Inherited parent extension/registration gates remain incomplete. WORKFLOW_REFRESH.md and LIVE_WORKFLOWS.json preserve every job disposition. This status refresh does not claim to have reinterpreted every newly completed research artifact; that mathematical artifact harvest is still required in the eventual full Post-Green Pass.

**What changed.** Eleven candidate primary statements and substantial proof bodies now exist. Their intended mathematics is more concrete, but the accepted root count did not change. The review exposed actual Lean/API blockers, a uniform-interface issue, an incomplete cold exporter repair and three structural validator gaps.

**Upstream implications.** Finish the auxiliary filled-transform/Poisson machinery and shared-growth complex measure API first where they support later proofs. The native top-moment/residual/memory constructions remain separate obligations; the generic Laguerre norm is insufficient to discharge them.

**Downstream implications.** A genuine comb Fourier law can support weighted mixtures and near-gap constructions; genuine common-growth local limits can support the global co-Poisson identification. First-cell sign and cost results become useful constraints on actual constructed measures only after those independent global/domain obligations are discharged. These are dependency observations, not newly formalized consequences.

**Resurrected routes.** None is promoted by a failed candidate. Once auxiliary and multiplicity results are accepted, revisit the actual native rate bridge; once global measure construction is accepted, revisit finite-span and force-sampling consumers. Preserve historical failure reasons until the missing prerequisites are genuinely solved.

**New RH-relevant clues.** No new theorem-backed RH clue is established here. Common growth plus local convergence and quantitative first-cell cost remain LEADS for composition, not closing estimates. The previously identified unrestricted C3 amendment inequality issue remains visible; repaired supporting statements must stay distinct.

**Falsification checks.** Required future controls include zero Fourier mode, k=0 endpoint atom versus k>=1 Poisson scope, the filled half-point transform, m=1 and arbitrary real tail thresholds, both ordinate signs, strict first-cell height cutoffs, common rather than individual growth budgets, varying palettes, and all-history local-word scope. The new validator mutation probes already falsify three proposed fail-closed metadata claims.

**Highest-leverage next moves.** Complete the actual missing proofs and their physical adapters, beginning with prerequisites that unblock multiple native rate/measure roots. Repair infrastructure without promoting partial results. After complete exact-source acceptance, perform the full mathematical and workflow Post-Green Research Pass, including every required source artifact and all nine research conclusions. Green infrastructure alone will not close the project.

RH, Step 4 and the independent closing inequalities remain **OPEN**.
