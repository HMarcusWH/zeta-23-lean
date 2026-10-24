# OPICA native follow-up — exact PR build specification

**Date:** 21 October 2026  
**Repository:** `HMarcusWH/zeta-23-lean`  
**Parent:** PR #293, inspected source head `553b4263b58d9fec178320de251ff299a0bd702a`  
**Tree:** `12691099f1a155a8bfa3ad4f6689146175b233b2`  
**Proposed branch:** `research/opica-native-followup`  
**Proposed title:** Formalize native OPICA transport, analytic window rates, and co-Poisson forcing  
**Authority of this document:** implementation specification, not a new theorem or compiler receipt.

## 0. Decision and complete deliverable

Build an additive **sibling** library with public import `Zeta23.OPICAFollowup`. Preserve `Zeta23.OPICA`, all existing mathematical source files, the legacy default import, the toolchain and the historical claim objects. Add an exact, fail-closed child-extension protocol to the parent **validator**, because its current closed inventories correctly reject arbitrary subsequent changes.

This specification elects the **full paper scope**: all 26 result/control groups in the final audited paper, and both direct analytic bridges J5.2 and MS1. MS1 is not needed by the fixed two-factor arithmetic application, but it is included here as a distinct obligation. F1–F3 are included, not deferred. The 25 first-PR families are prerequisites and are not counted again. No independent closing estimate is assumed or claimed.

The exact proposed footprint is **84 new files**, including **43 Lean files** (41 mathematical/facade files and two audit files), **12 existing authoritative files modified**, and the **62 existing generated outputs** refreshed through the existing producer. There are no deletions or renames. The generated list is a regeneration allowlist, not a requirement to manufacture different bytes in every file. No existing mathematical Lean body is edited; the only modified `.lean` file is the global audit binding file.

The target interface contains **100 primary theorem roots**, covering **28 acceptance units**: 26 paper groups plus two inherited analytic bridges. These are proposed declaration names, not claims that 100 proofs have already been written. All additional public definitions, helper theorems, structures, constructors, and transitive private project dependencies must also be exported and audited. There is no fixed predicted helper-declaration count.

The attached JSON manifests and root inventory are normative with this document. File or signature refinements require an explicit versioned amendment and regenerated coverage checks; they must not silently remove a difficult statement. A staged implementation is allowed, but an intermediate slice must remain labelled partial and cannot be merged under the full completion claim.

## 1. Exact parent state and acceptance boundary

The fresh PR metadata reports **open, draft, unmerged**. Main remains the PR #292 base `97926d6a949fed7af0429a373b47abc772012834`. The inspected branch is `research/opica-obstruction-preservation`.

At the inspected head, OPICA PR-event run `39586659233` has five successful component jobs. The formal job `119177561193` actually checked synthetic merge `875a321edf0362bbc170cc3177007c18172eeef0`, whose tree is the same `12691099f1a155a8bfa3ad4f6689146175b233b2`. Its log records a clean checkout, a completed compiler receipt, all 76 primary roots present, and a successful release-contract check. Artifact `12342876090` is `opica-formal.zip` with uploaded ZIP SHA-256 `1ffbc5055e27576599e957f3ad8a0a47ed5c69090d1281bd096d3e5cb4d3ad03`. The artifact's complete bytes were not downloaded for this specification; that digest is log-reported, not a fresh local hash calculation.

The parallel push run `39586645608` was still performing canonical materialization at the last detailed job read. Its compiler and release-contract steps had succeeded; generated-state freshness was pending. The current source-inertia research workflow also still had pending work. Therefore this specification does **not** certify the whole parent PR green or merged. The earlier checkpoint report at `567d78de11ee3e3b7ae7e455fab0bf096ce90c34` is historical evidence, not the current publication head.

### 1.1 Base policy

Implementation may be prepared as a local stacked branch from the pinned head above. Its acceptance base is the **eventually accepted #293 result**. Before marking the follow-up ready, record the accepted parent commit/tree, its actual compiler receipts, API/type fingerprints, constructor inventory, complete paginated job harvest, generated-state freshness and review disposition. If the accepted tree changes, compare the exact mathematical/API and validation surfaces and issue an amended pin. Do not fall back to old main or infer that a merge commit is a tested head.

A merge commit with the same tree can preserve source identity; its new commit identity still needs a fresh provenance record and the appropriate checkout tests. The parent requirement is not human independent review by fiat: compiler authority and human review status remain separate. A pending independent review must remain marked pending even when compiler gates pass.

### 1.2 What was actually inspected for this specification

Fresh live reads covered PR metadata, commit/tree metadata, workflow summaries, detailed OPICA job steps and the formal-job log; the public facade; actual native jet and arithmetic adapters; portions of the real locally finite measure and rate modules; the exact closed validator, receipt builder, exporter and workflow. The attached final paper/ledger/contract and the named relevant historical source bodies were inspected locally. This was not a new full semantic review of every repository theorem or all 16,159 historical pages.

The parent log supports the current 76-root release result. The 613-public-declaration/eight-constructor/143-consumer counts in the PR body describe its reported implementation/checkpoint inventory; this turn has not independently parsed all current type DAGs. The follow-up intake must obtain and validate those artifacts, not merely copy those numbers.

## 2. Frozen mathematical sources and authority

The controlling source is `OPICA_Followup_Final_Audited_Paper_2026-10-21.md`, SHA-256 `9525d5dad6f0a2e3abd6050edeb39e3a234b6a361046e746878a181970a789f0`. Its final ledger, contract, audit report and manifest are copied without changes into the new integration package's `paper/` directory. The PDF is a release artifact, not a second competing proof source in Git.

The paper has PAPER/DERIVED self-audit authority. Compilation changes authority only for exact accepted declarations, not for the paper as a whole or for its OPEN research goals. Preserve its terminology: source order, zero multiplicity, inverse-factor count, completion index, completion depth, palette, compact probe and spectral parameter are distinct.

**In scope:** R1-NB1/AT1/AT2/HT1/HT2/CT1/MC1/CP1; all fifteen R2 families; F1/F2/F3; fully native J5.2 and its explicitly scoped MS1 extension. The constant-scale countercontrols remain countercontrols, not actual zeta counterexamples. Classical analytic formulas are imported from proved declarations or actually proved in their assigned module; citations alone are not Lean imports.

**Not promoted:** RH, Step 4, A-X, B-Y, C-Schur, OPEN-J46, D2/WP4, native boundary-amplitude exclusion, universal impossibility of a class of RH proofs, or global novelty. The conditional quiet-observation consumer keeps its independent upper premise visible.

## 3. Findings from #293 that determine this design

### 3.1 Reuse real source adapters rather than their names

`Zeta23.OPICA.NativeJetAdapter` builds the actual completion and completed-input order witnesses from the existing physical transform theorems. Its completed-input jet and same-state output consumers are useful concrete inputs. However, `native_kernel_completion_consumer` still accepts a supplied `SimplePoleData`. It is not already a construction of the actual prime field's meromorphic pole datum. The follow-up's `nativePrimeField_visiblePole` must supply that missing source-specific datum from the physical transform identity and actual multiplicity.

`NativeArithmeticAdapter` already provides `nativeOriginalBoundedCausalDrive`, the actual original-j low-mask bound, `finitePaletteDrive`, `squarefreePaletteDrive`, and exact absolute palette cost. Reuse them. They do not, by naming, provide every higher differential source or higher forward convolution used in Q2/Q3. The new family begins with exact order-zero equalities to the existing objects and proves its higher-order support, moments, transforms and bounds.

### 3.2 Reuse the actual schedule and measure representations

Use `Zeta23.OPICA.HorizonSchedule`, `magnitudeRate`, `positiveRate`, and `SubexpAlong`; do not define subtly different copies. The norm-first theorem is a new Hilbert-space result using those rates, not the old stronger absolute squared-energy comparison renamed.

The parent `LocallyFiniteSignedMeasure` is a **real Jordan pair with local finiteness and mutual singularity**, not a globally finite signed measure and not a complex-measure API. The new zero profiles and jets are initially complex. `ComplexLocalMeasures.lean` must supply a faithful complex locally finite construction, compact restrictions, variation control, arithmetic and real/imaginary extraction, and prove compatibility with the parent's real separator. A formal distribution with a claimed positivity field is not acceptable.

### 3.3 Do not take the similarly named wrong zero-count theorem

The preserved source contains `Zeta23.RvM.zetaZeroConfig_local_count` and `Zeta23.WeilEF.EF_lit_zetaZeroConfig`. Those are actual zeta inputs. `Zeta23/XiPrime/ZeroCount.lean` concerns zeros of xi-prime and is not the relevant substitute. The native translated explicit-formula specialization still needs to be constructed; the existence of an explicit-formula module does not by itself discharge that source identification.

These existing declarations must be matched to the accepted parent blobs and exact types at implementation intake. Their bodies were inspected in the preserved source, not freshly recompiled here.

### 3.4 The existing audit is intentionally closed

The current parent `validate_contract.py` requires exactly 76 parent roots, 25 paper families, the original file inventory, exactly 198 global claim objects and 194 theorem bindings, and the parent-only semantic configuration. It also rejects tracked or untracked changes outside the first PR's allowlist against the old #292 base. The existing OPICA workflow runs on later main-targeting PRs, so a naive new namespace alone does not solve this.

The first implementation also deliberately classifies native OPICA adapters as `AUXILIARY_FORMALIZATION`, since the frozen source-only RH_FORMAL_CORE producer admits CCM/ExceptionalZero names. Retain that decision. Every child mathematical file receives auxiliary classification with an explicit native semantic role where applicable. Registered claims and compiler/source bindings, not misclassification, provide visibility.

## 4. New file inventory

The following list is exact. The responsibilities are acceptance obligations, not merely documentation headings. Project imports are listed separately in the attached manifest; Mathlib helper imports remain on the frozen revision and must be recorded in the actual source receipt.

| New Lean file | Lane | Responsibility |
|---|---|---|
| `Zeta23/OPICAFollowup/NativeSourceFamily.lean` | arithmetic | Define j_d=P^d j from the existing one-copy original source; define physical prime and integer translate histories and repeated forward translates. Prove support/regularity and d=0 equalities. |
| `Zeta23/OPICAFollowup/NativeSourceTransforms.lean` | arithmetic | Identify actual transforms on their initial safe half-plane and prove analytic continuation/nonvanishing for the exact one-copy source; construct the original visible simple-pole datum. |
| `Zeta23/OPICAFollowup/NativeFilters.lean` | local | Concrete generator definitions as actual local causal actions, their safe-domain transforms and unit factors. Inverse Euler filter is locally finite, not incorrectly global finite variation. |
| `Zeta23/OPICAFollowup/NativeTransformationWords.lean` | local | Instantiate the finite correction-aware law on actual native transformations, not a class defined by faithfulness. |
| `Zeta23/OPICAFollowup/NormFirstTransfer.lean` | local | Use existing HorizonSchedule, positiveRate and SubexpAlong. Prove norm-first comparison for real/complex Hilbert fields and allocation without assuming absolute energy error small. |
| `Zeta23/OPICAFollowup/JointObservation.lean` | local | Finite-dimensional joint contrast/history observation; exact cost including zero-map convention, extension, noise and incompatible data. |
| `Zeta23/OPICAFollowup/RobustLaurent.lean` | local | Cauchy coefficient estimates on a genuine common disk; apply to changing completion depth only with the full actual cost. |
| `Zeta23/OPICAFollowup/SourceVerticalBounds.lean` | arithmetic | Uniform whole-plane product estimate using the prescribed infinite box convolution, then source derivative cost bounds. |
| `Zeta23/OPICAFollowup/ZetaLeftLineBounds.lean` | arithmetic | Prove the moving-left-line zeta and derivative envelope using only valid functional equation, fixed-strip gamma and Cauchy estimates; include any needed library adapters here. |
| `Zeta23/OPICAFollowup/ForwardLocalization.lean` | arithmetic | Actual inversion, horizontal contour control, uniform factorial envelope and saddle selection. |
| `Zeta23/OPICAFollowup/BalancedCoefficients.lean` | arithmetic | Prove actual finite J17 Dirichlet-convolution identity and divisor envelopes with coprimality palette and repeated products. |
| `Zeta23/OPICAFollowup/LogSlackBalance.lean` | arithmetic | Prove logarithmic-slack decomposition with palette frozen per window and its full support-delay budget. |
| `Zeta23/OPICAFollowup/MaskedNativeRate.lean` | arithmetic | Bound both low-mask realizations at B(t)=exp(sqrt t), and apply norm-first transfer. This module has no Theta-equality assumption or conclusion. |
| `Zeta23/OPICAFollowup/NativeExplicitFormula.lean` | analytic | Specialize the actual zeta explicit formula to translated compact j_d. Derive absolute zero/trivial sums and the multiplicity-weighted source upper, not an assumed rate. |
| `Zeta23/OPICAFollowup/UniformSourceBounds.lean` | analytic | Uniform in derivative source order: Gevrey L1/Linfty costs, drive L2, and Theta-dependent physical field envelope. |
| `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean` | analytic | Construct actual c_k,a_k and the uniform beta/endpoint/Poisson estimates A4-A5 from Part II. |
| `Zeta23/OPICAFollowup/MultiplicityTail.lean` | analytic | Arbitrary-multiplicity actual residual and monic shifted Laguerre normalization, including stable-input estimate and finite truncation only. |
| `Zeta23/OPICAFollowup/NativeWindowRate.lean` | analytic | Full continuous fixed-source limit J5.2 using actual transforms and all uniform estimates; no bare nativeRate hypothesis. |
| `Zeta23/OPICAFollowup/MovingSourceWindowRate.lean` | analytic | Retain and formalize the optional-for-fixed-application MS1 as an explicit full-package coverage choice. |
| `Zeta23/OPICAFollowup/ComplexLocalMeasures.lean` | heat | A genuine complex locally finite measure API compatible with P0 real Jordan pairs, compact restrictions, total variation, S-prime embedding, real/imaginary extraction and linear-growth estimates. Do not use globally finite SignedMeasure as a replacement. |
| `Zeta23/OPICAFollowup/DilatedComb.lean` | heat | Actual scaled combs D_t on the full integer lattice with linear variation and Fourier transport on Schwartz tests. |
| `Zeta23/OPICAFollowup/WeightedMixing.lean` | heat | Noncompact absolute mixing class, real/complex measures, actual logarithmic Mobius inverse and leakage. Compact-support proof is not enough. |
| `Zeta23/OPICAFollowup/NearGapLimits.lean` | heat | Near-sharp mass bounds, S-prime compactness/vanishing under a common variation budget, and actual nonmeasure normalized limit. |
| `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean` | heat | Subtract origin/continuum before integration, prove entire tempered family then local total-variation identification as the exact density-plus-atom measure. |
| `Zeta23/OPICAFollowup/ProfileEulerMaclaurin.lean` | heat | Finite power-sum expansion with explicit endpoint convention and locally uniform parameter remainder, including differentiated finite sums. This is a foundation proof obligation, not an imported unverified formula. |
| `Zeta23/OPICAFollowup/ZeroProfiles.lean` | spectral | Actual h=1-Srho/brho, reflection quotient kappa, tail, integer jumps, integrals and ordinary Fourier identity. |
| `Zeta23/OPICAFollowup/LogFourierSobolev.lean` | spectral | Define true log unitary x=exp(t), the frequency convention without 2pi, weak derivatives, H1/H-1 realization and justified dual pairings. Derive convention conversion to pinned Mathlib Fourier; no imaginary separate force transforms. |
| `Zeta23/OPICAFollowup/ForcedEuler.lean` | spectral | Derive distributional cell equation with every atomic derivative jump and distinguish form versus operator domain. |
| `Zeta23/OPICAFollowup/SamplingCompatibility.lean` | spectral | Native finite multi-zero integrals and samples, exact undivided compatibility, and forced finite-dimensional countercontrol. |
| `Zeta23/OPICAFollowup/CoPoissonJets.lean` | heat | Actual parameter jets up to multiplicity minus one; local inverse rho(kappa), reflection duplicates and realification proved. |
| `Zeta23/OPICAFollowup/ConfluentProfiles.lean` | heat | Actual first-cell density to Hermite interpolation; normalized derivative coefficients and reflection quotient. |
| `Zeta23/OPICAFollowup/FiniteSpanSeparation.lean` | heat | Instantiate the real signed separator only after all complex-jet realification and variation hypotheses are proved. |
| `Zeta23/OPICAFollowup/FirstCellCost.lean` | heat | Quantitative first-cell density and required repair cost, with the height and delta conditions retained. |
| `Zeta23/OPICAFollowup/SquareDefect.lean` | heat | Actual nonlinear square, convolution Fourier defect, no tempered lattice-measure repair, gap filling under selfdual projection. |
| `Zeta23/OPICAFollowup/SawtoothForce.lean` | spectral | Define the tempered force from the derivative of integrable sawtooth before stating the compact-test lattice-minus-continuum equality. |
| `Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean` | spectral | Positive measure with finite weighted moment; do not impose finite unweighted total mass. |
| `Zeta23/OPICAFollowup/NativeResolvent.lean` | spectral | Identify actual zero profile with unique H1 forced log-resolvent and its actual sampling functional. |
| `Zeta23/OPICAFollowup/BoundaryAmplitude.lean` | spectral | Generic nonzero parameter forced solution and plateau coefficient; never register the diagnostic equivalence as an independent zero-exclusion theorem. |
| `Zeta23/OPICAFollowup/Counterexamples.lean` | controls | Reproduce the finite/functional countercontrols with exact types and no claim they are actual off-line zeros. |
| `Zeta23/OPICAFollowup/Consumers.lean` | consumers | Explicit actual-source consumers for arithmetic, multiplicity, co-Poisson, and source sampling. No single packet fabricates contact or real-profile equivalences. |
| `Zeta23/OPICAFollowup.lean` | entry | Public sibling entrypoint; leaves Zeta23.OPICA and the legacy root unchanged. |
| `Zeta23/OPICAFollowup/Validation.lean` | audit | Typed consumers, physical source/constructor obligations, exact scope checks; not imported by facade. |
| `Zeta23/RHRC/OpicaFollowupBindings.lean` | audit | Own OPICA_FOLLOWUP_COMPILER_V1 protocol, enumerate all child public declarations/constructors and recursive TYPE/VALUE/STRUCTURE closure; reuse unchanged exportType codec only. |

### 4.1 Integration, tests and frozen inputs

The new integration directory is `research/RHRC/integration/opica_followup/`. It does not replace the parent `opica/` package. Its source manifests are committed; source-specific runtime receipts remain workflow artifacts to avoid a self-referential commit hash.

| New non-Lean file | Responsibility |
|---|---|
| `research/RHRC/integration/opica_followup/README.md` | One entry point, exact build commands, scope, unresolved claims and no partial-completion wording. |
| `research/RHRC/integration/opica_followup/BUILD_SPEC.md` | Freeze this specification after base acceptance; amendments require explicit versioned review. |
| `research/RHRC/integration/opica_followup/BUILD_MANIFEST.json` | Exact child source, edit, regeneration, module and command inventory. |
| `research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json` | Exact primary target names and expected statements; pending proof status until actual validation. |
| `research/RHRC/integration/opica_followup/PAPER_CROSSWALK.json` | All26paper groups plusJ5.2/MS1, each subclause, root, physical consumer and rejection tests. |
| `research/RHRC/integration/opica_followup/SOURCE_REGISTER.json` | Hashes of exact paper inputs, inherited checkers and adaptation provenance; source vs proposed names separated. |
| `research/RHRC/integration/opica_followup/PARENT_INTAKE.json` | Parent head/tree/merge/event, compiler artifact identities, APIs, complete eventual workflow harvest and acceptance disposition. |
| `research/RHRC/integration/opica_followup/PARENT_EXTENSION.json` | Exact validated extension of parent path/registry/config projections; no blanket namespace or count exemption. |
| `research/RHRC/integration/opica_followup/PROTECTED_STATE.json` | Capture every parent tracked path/object from exact accepted pin, except this explicit edit/regeneration allowlist; APIs protected. |
| `research/RHRC/integration/opica_followup/WORKFLOW_CONTRACT.json` | Required child jobs/lanes, raw receipt schemas, exact command contracts, reviewed type hashes after compilation. |
| `research/RHRC/integration/opica_followup/REGRESSION_CONTRACT.json` | Frozen script hashes, group counts, expected39920 per mode,33numerical cases and numerical nonauthority. |
| `research/RHRC/integration/opica_followup/POST_GREEN_RESEARCH.md` | Initially pending; complete actual source/type/workflow/research implications only after green. |
| `research/RHRC/integration/opica_followup/validate_contract.py` | Fail closed on sources, groups, registry, roles, DAG, scope, protected state and type receipt requirements. |
| `research/RHRC/integration/opica_followup/parent_extension.py` | Pure strict extension verification and lossless parent-view projection used by the one patched P0 validator. |
| `research/RHRC/integration/opica_followup/capture_parent.py` | Read-only base/workflow intake and full source inventory; no inferred merge/approval or automatic rebase acceptance. |
| `research/RHRC/integration/opica_followup/build_receipt.py` | Build exact selected targets and export/validate all child declarations and transitive dependencies; original builder remains unchanged. |
| `research/RHRC/integration/opica_followup/replay_controls.py` | Run immutable check scripts with external output paths under normal and -O; compare group counts and hashes. |
| `research/RHRC/integration/opica_followup/harvest_workflows.py` | Paginate all attached runs/jobs/attempts, collect actual dispositions and compare same mathematical fixtures. |
| `research/RHRC/integration/opica_followup/dependency_delta.py` | Source-bound use graph and premise delta; shared deps do not imply equivalence. |
| `research/RHRC/integration/opica_followup/requirements-checks.txt` | Pin SymPy 1.14.0 and mpmath 1.3.0 to the supplied receipt environment; lock downloads separately; numerical tests are not Lean premises. |
| `research/RHRC/integration/opica_followup/python-checks.lock` | Platform-independent wheel/sdist SHA256 lock captured before network install; refuse unlocked downloads. Do not invent package digests. |
| `research/RHRC/integration/opica_followup/tests/test_contract.py` | Full source/root/group inventory, duplicate IDs, invalid premises and altered source inputs. |
| `research/RHRC/integration/opica_followup/tests/test_parent_extension.py` | Reject unauthorized registry deletion/mutation, arbitrary allowlist expansion, source drift, missing descriptor, invalid parent and bypassed P0 proofs. |
| `research/RHRC/integration/opica_followup/tests/test_receipt.py` | Reject stale head/tree, missing constructor/helper closure, truncated type DAG, unapproved axioms, wrong command exit and SHA records. |
| `research/RHRC/integration/opica_followup/tests/test_coverage.py` | Reject absent subclauses, swapped j/q*j/Pj, toy-native substitution, actual source property as caller hypothesis, optional-bridge laundering. |
| `research/RHRC/integration/opica_followup/tests/test_workflow_harvest.py` | Pagination, latest attempts, canceled/still running/skipped dispositions, mixed-source artifacts and output meaning versus process success. |
| `research/RHRC/integration/opica_followup/tests/test_file_classes.py` | Preserve all preexisting first-match classification and roles; child native modules auxiliary, audit-only unreachable from facade. |
| `research/RHRC/integration/opica_followup/tests/test_dependency_delta.py` | Verify unchanged old theorem types/axioms/dependencies; no assumed logical consequence from shared edges. |
| `research/RHRC/integration/opica_followup/tests/test_regression_replay.py` | Normal/-O checks must run, frozen checker identities/counts retained; numerical status cannot promote mathematical claims. |
| `research/RHRC/integration/opica_followup/paper/OPICA_Followup_Final_Audited_Paper_2026-10-21.md` | Byte-identical final paper release input; paper/self-audit authority retained. |
| `research/RHRC/integration/opica_followup/paper/OPICA_Final_Theorem_and_Audit_Ledger_2026-10-21.json` | Byte-identical final paper release input; paper/self-audit authority retained. |
| `research/RHRC/integration/opica_followup/paper/OPICA_Final_Followup_Paper_Contract_2026-10-21.md` | Byte-identical final paper release input; paper/self-audit authority retained. |
| `research/RHRC/integration/opica_followup/paper/OPICA_End_to_End_Audit_Report_2026-10-21.md` | Byte-identical final paper release input; paper/self-audit authority retained. |
| `research/RHRC/integration/opica_followup/paper/OPICA_EndToEnd_Final_Release_Manifest_2026-10-21.json` | Byte-identical final paper release input; paper/self-audit authority retained. |
| `research/RHRC/integration/opica_followup/checks/frozen_round1_check_round1.py` | Unchanged paper finite/symbolic/numerical reproduction. Use existing P0 check_exact.py for the5112 baseline controls. |
| `research/RHRC/integration/opica_followup/checks/frozen_round2_check_round2.py` | Unchanged paper finite/symbolic/numerical reproduction. Use existing P0 check_exact.py for the5112 baseline controls. |
| `research/RHRC/integration/opica_followup/checks/check_final_exact.py` | Unchanged paper finite/symbolic/numerical reproduction. Use existing P0 check_exact.py for the5112 baseline controls. |
| `research/RHRC/integration/opica_followup/checks/replay_copoisson_numeric.py` | Unchanged paper finite/symbolic/numerical reproduction. Use existing P0 check_exact.py for the5112 baseline controls. |
| `research/RHRC/integration/opica_followup/checks/frozen_round2_check_round2_numeric.py` | Unchanged paper finite/symbolic/numerical reproduction. Use existing P0 check_exact.py for the5112 baseline controls. |
| `research/RHRC/integration/opica_followup/checks/check_final_numeric.py` | Unchanged paper finite/symbolic/numerical reproduction. Use existing P0 check_exact.py for the5112 baseline controls. |
| `.github/workflows/rhrc_opica_followup.yml` | Read-only parent-compatible checks, explicit proof lanes, aggregate current-tree receipts, regressions, generated-state check, and post-green harvest. |

The dependency lock is populated from real package artifacts before the implementation's CI is accepted. It is not supplied with invented wheel hashes. The frozen receipts record SymPy 1.14.0 and mpmath 1.3.0; the original final audit used Python 3.13.5. Use Python 3.13 for this symbolic/numeric replay lane and record its exact patch version. Parent audit jobs keep their existing Python 3.14 contract. The Lean toolchain and Mathlib pin are unchanged.

## 5. Existing files changed, and files protected

| Existing authoritative file | Allowed change |
|---|---|
| `Zeta23/RHRC/RegisteredClaimBindings.lean` | Append exact defining-module imports, #check and #print axioms for compiled child primary roots only; preserve all previous rows. |
| `research/RHRC/CLAIM_REGISTRY.json` | Append one route-less supporting theorem object per accepted child primary root; explicit conditional premises retained. No existing object changed. |
| `research/RHRC/REGISTERED_THEOREM_BINDINGS.json` | Append exact source/theorem bindings for same accepted child roots. No old binding changed. |
| `research/RHRC/graph/FILE_CLASSES.json` | Insert only two child-specific rules before generic zeta_lean; preserve existing first-match meaning. |
| `research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json` | Append exactly the child standalone module roles; no existing config field or role changed. |
| `research/RHRC/tools/run_suite.py` | Add child structural/unit test discovery and parent extension tests; preserve all prior tests and their command semantics. |
| `README.md` | Add sibling public import, explicit build, scoped formal status, paper source and unresolved exclusions. |
| `research/RHRC/README.md` | Add child integration navigation and evidence/classification conventions. |
| `research/RHRC/CURRENT_RESEARCH_PLAN.md` | Record accepted mathematical state and Post-Green research questions; do not close independent obligations. |
| `research/RHRC/integration/opica/validate_contract.py` | Narrow wrapper for a strictly validated child extension: project exact child registry/config contributions and augment exact delta allowlist before existing P0 checks; preserve all original frozen constants, roots, checks and release type audit. |
| `research/RHRC/integration/opica/tests/test_contract.py` | Add integration tests for historical default behavior and registered child projection; do not remove or weaken original tests. |
| `research/RHRC/integration/opica/README.md` | Document that immutable P0 theorem/spec inventory remains unchanged while one exact child extension is supported. |

No other existing authoritative file may change under this specification. In particular, protect all mathematical sources in `Zeta23/OPICA/`, `Zeta23/CCM/`, `Zeta23/ExceptionalZero/`, other historical mathematics and `comparator/`; protect `Zeta23.lean`, `Zeta23/OPICA.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `formalization.yaml`; protect all existing workflows, parent exporters/builders/type expectations and frozen P0 manifests; protect historical route data and first-PR provenance reports. The parent README and validator/test files listed above are the only parent-package exceptions.

The new `PROTECTED_STATE.json` is captured from the exact accepted parent checkout **before implementation changes**. It lists every parent tracked file with Git blob and SHA-256, then the exact exceptions above and the 62 generated products. It also captures all 198 parent claim objects, all 194 parent binding objects, parent module roles/classification behavior, and all four OPEN claim IDs. Capturing this against a different main or after modifications is a failure.

This specification includes a scope-labelled parent intake, not a falsely claimed fresh hash of every file in the remote tree. The prior source-derived inventory and successful parent validation help navigate; the complete accepted-parent capture remains a mandatory start gate.

At full completion, adding the 100 listed primary roots yields **298 claim objects and 294 registered theorem bindings**, provided the accepted parent retains its 198/194 inventory. These counts are consequences of the exact ID sets, not substitutes for checking their contents. Every existing object remains unchanged. Additional helper declarations are audited but not automatically promoted to primary registered claims.

## 6. Exact parent-extension protocol

This is the only deliberate change to the parent's validation behavior. Its purpose is to validate a child, not to allow an arbitrary descendant to bypass parent checks.

1. **Historical default remains exact.** With no child descriptor, child source path, child role or child claim present, execute the existing P0 validation unchanged. Missing or malformed child metadata when any child marker exists is an error, not an opt-out.
2. **Recognize one explicit extension ID.** Load `opica_followup/PARENT_EXTENSION.json` through the new audited helper. Check the pinned parent identity, the frozen child specification/root/crosswalk hashes, the full expected path inventory and the exact authorized edits. Reject path traversal, duplicate IDs, symlink escapes and unlisted targets.
3. **Validate raw current state before projection.** The raw global registry must equal the protected parent objects plus exactly the child objects. All parent values must match, not merely IDs. The same rule applies to bindings, roles and class rules. Child claim names alone are not validation.
4. **Project only the validated additions.** For the existing P0 global-context predicates, remove exactly the validated child claim/binding objects and the two child class rules/role entries. The resulting view must equal the original expected P0 state. No source, proof, axiom, constructor or compiler-dependency record is filtered out to make a theorem pass.
5. **Extend the file-diff allowlist exactly.** Against the frozen #292 baseline, the cumulative allowed delta is the original P0 inventory plus this child manifest's exact creates/modifications/regenerations. Against the accepted #293 baseline, only this child delta is allowed. Both checks apply. No wildcard such as “ignore all OPICAFollowup files” is permitted.
6. **Preserve formal validation.** Run the original P0 receipt builder and release checker at the current clean checkout. The full P0 mathematical types, expected hashes, constructor fields, standard-axiom limits and recursive dependency closure are still checked. The parent's historical compiler hash is not a replacement for rebuilding its unchanged source in the child environment.
7. **Verify absence of back edges.** No P0 mathematical module imports the child; no existing mathematical declaration acquires a child dependency. Global audit imports are the sole intentional downstream addition.

The new helper exposes `validate_extension_context(raw_state, parent_baseline, child_contract)`, `project_parent_context(validated_context)` and `allowed_child_delta(validated_context)`. It is pure: it must not invoke the parent validator, child validator, compiler or a subprocess, avoiding a circular validation call chain.

The wrapper in `opica/validate_contract.py` should be small. Its pure original predicates remain testable against historical fixtures. The helper performs strict verification and returns a read-only projected context plus the exact additional path set. It may not override a failed original result or provide fabricated compiler rows. Keep original frozen constants and expected P0 totals; they apply to the projected P0 view. The child validator separately checks the full totals and raw state.

### 6.1 Required negative tests

The test suite must reject: an unlisted extra file; an extra child-looking claim; a duplicate existing theorem name; a changed old claim body; a changed old binding; missing extension metadata; malformed/wrong-base metadata; a new classification rule shadowing a parent file; arbitrary namespace permission; a changed old mathematical file; a dropped parent constructor; a new type premise hidden in a structure; a stale/mixed-tree compiler receipt; a nonzero compiler exit recorded as pass; incomplete dependency channels; a child module imported by P0; and a missing full-scope statement despite successful easy lanes.

Tests must also demonstrate that the original closed validator rejects the raw legitimate child additions before projection, and that the verified projection restores only the old contextual expectations. Run the original test suite unweakened and the new extension tests in normal and optimized Python.

## 7. Precise mathematical boundaries and source definitions

### 7.1 Actual source family

Define `sourceOrderFamily d` by applying the fixed differential operator P^d to `CCM.nativeOriginalSource`, and prove equality to the actual P^(d+2)q construction. Define fields through actual locally finite histories, not by inverse-transform declarations selected for convenience. The order-zero source/drive/field equalities are named roots. Let `g=log 2-s0`, with s0=1/4096, and prove causality for every required member.

`forwardKernel d ell` is the ell-fold actual integer translate action on the d-th drive. Its transform identity is first a convergent integral statement on Re z>1/2. Entire continuation and later inversion follow through proved estimates. No artificial field is permitted merely because it has the target RHS transform.

Finite causal words may have exponential growth and need not be tempered distributions on Schwartz space. Represent their derivative histories on compact tests, or by an equally explicit causal state class, and establish Laplace identities on a common genuine half-plane. A derivative of a zero extension retains its boundary delta derivatives. Do not reuse the tempered heat-measure space indiscriminately for this time-domain state.

Actual-zero theorems consume the existing `zetaZeroConfig` carrier, analytic multiplicity and reflection infrastructure. No simplicity premise, minimum displacement or attaining-zero assumption may be added. A general source structure is allowed as a reusable interface only when its actual constructor discharges every field; its “native” use cannot take the desired rate, range membership, self-duality, sign or transform identity as a caller premise.

### 7.2 Arithmetic and complex Hilbert comparisons

AT1 is genuinely the norm-first estimate in a real or complex Hilbert space. The native gcd sums may use the existing real drive API, but the generic estimate must not be quietly narrowed to real scalars. Positivity refers to the positive part of a real signed quadratic, not to every masked bilinear matrix being PSD.

The primitive low mask is `max(d,e)/gcd(d,e) <= B(t)` and includes the diagonal; the high mask is its strict complement. It is not “both primitive indices exceed B.” Cutoffs must be measurable. For kernel absorption, prove both low-mask budgets and the exact regrouping identity, not just equality of the scalar fields.

For Q3, r, d, C, eta and K are fixed before the horizon limit; the palette is fixed throughout its window and Q(T)<=T^eta. Pay both mass and maximum shift i log Q(T). The concrete instance is r=2,d=1,C=2,Q=1,K=8 and uses Pj. It gives polynomial powers of log X around sqrt X and a negligible Type I error, not a signed upper for the retained field.

### 7.3 J5.2 and MS1: no opaque native-rate premise

The source-parametric compact-test explicit formula, analytic zero multiplicities, actual zeta zero count, source-regularity cost, true drive L2 bound, beta filter, endpoint atom, actual Poisson sum, uniform completion ratios, Laguerre normalization, finite-residual support and terminal-memory inequality must all be bound to proved imports or new proofs. The master paper specifies the equations in Part II. The files above allocate every one of these obligations.

`native_fixed_source_window_rate` must end with the full continuous limit for each fixed source and C>1. `native_slow_source_window_rate` separately retains d_n log(d_n+2)=o(T_n), fixes a chosen hypothetical zero before each limit argument and prices both signs of the source multiplier's logarithm. The proof uses a supremum, not a rightmost zero. For an arbitrary cofinal real sequence, positivity holds eventually; normalize or discard a finite prefix before invoking HorizonSchedule and transfer back by eventual equality, rather than narrowing the native limit claim. Exact compensation means the field is independent of the palette; palette expansion estimates are not hidden inside MS1.

No unconditional theorem named RH or A-X is added. The final quiet-observation consumer is explicitly an implication with the complete signed upper as an open hypothesis. A successful compiler run for that implication cannot promote its antecedent.

### 7.4 Co-Poisson objects are measures before separator use

Use heat Fourier convention exp(-2pi i x xi). Define the renormalized K_t before integrating; neither divergent comb component is assigned a separate convergent integral. Prove entire tempered-family convergence on Schwartz tests. Then prove local total-variation convergence of actual cutoff measures to the explicit density/origin formula. Only after this identification are “measure”, “gap”, “sign” and Jordan parts legitimate.

For actual zeros retain 0<Re rho<1, rho!=1/2 and b_rho=(1-2rho)/(rho(1-rho)). Parameter derivatives stop at actual multiplicity minus one. Reflection rho and1-rho gives the same kappa and must be quotiented before the confluent determinant. Conjugates are retained when constructing real combinations. All native constructions prove their own growth; they do not assume a generic `isMeasure` or a wanted separator hypothesis.

For S1, h=1-g is continuous L1/L2, selfdual and plateau1, but not asserted positive. The forced Euler equation retains every integer atom. It is a form-domain identity, not an eigenfunction of a homogeneous L2 operator. The ordinary exact-cell formula and endpoint jumps must be proved before integration by parts across infinitely many cells.

### 7.5 F1–F3 keep the arithmetic force and both Fourier conventions

In log coordinates use exp(-i xi t), Plancherel factor1/(2pi). Define w(t)=exp(-t/2) frac(exp t) and the tempered force g=-(D+1/2)w. The expression N-exp(t/2)dt is first an equality on compact tests; those two growth terms are not independently transformed as tempered distributions.

The spectral measure is `|zeta(.5+i xi)|^2 dxi/(2pi)` with finite integral of 1/(xi^2+1/4), not finite total mass. The Stieltjes transform is defined off the real spectrum [1/4,infinity), and holomorphy uses locally uniform absolute bounds. For an off-line zero kappa is nonreal. Actual sample sums are identified through a continuous H^-1,H^1 pairing and justified endpoint limits; generic L2 point evaluation is not used.

Use the undivided multi-zero identity at conjugate-coincident parameters. Do not divide by a critical-line zero's vanishing imaginary part. The full master also mentions removable almost-everywhere quotients for actual critical-line zeros: retain that remark as unpromoted unless a separately specified proof is supplied. It is not a blanket principal-value theorem required to interpret the nonreal F2 statement.

F3 is a generic forced resolvent with its exact zeta boundary amplitude. Its plateau equivalence is a diagnostic representation, not independent exclusion. The generic profile is in the log form domain but need not be L1 in the physical variable.

### 7.6 Recovery and Laurent controls

Use P0's exact linear-algebra observation APIs when constructing the joint map A=(P,C). Derive the optimum norm, handle the zero-map/zero-target convention, extend by orthogonal projection and retain all history errors. The theorem does not construct cheap recovery for a particular native contrast unless that application's hypotheses and cost are proved.

A Laurent estimate requires a common meromorphic neighborhood of the closed disk, positive radius and no extra interior pole. Degree is an integer j>=-1. The coefficient error is r^(-j)E; unnormalized derivatives add j!. The strict survival test prices the actual native leading coefficient, changing depth, radius, corrections and observation errors. Compact-time convergence is not substituted for this topology.

## 8. Exact theorem/root crosswalk

The attached `OPICA_FOLLOWUP_PUBLIC_ROOTS_2026-10-21.json` is the normative declaration inventory. Every entry fixes a name, defining file, paper IDs, statement contract, required hypotheses, disallowed substitutes and an expected-type consumer name. Its names are newly proposed, not existing imports.

Below is the source-level family map. The executable crosswalk must test every listed subclause, not just the presence of one theorem name in each family.

### R1-NB1 — Concrete finite native transformation word

Source: Part IV / NB1.

Source hypotheses: Finite actual generator identities; off-line actual zero of arbitrary finite multiplicity; correction ledger retained.

Source conclusion: Corrected order p*m-1 and explicit nonzero leading coefficient.

Scope limit: Expands a specified native instantiation; not a universal no-go or independent exclusion.

- `Zeta23.OPICAFollowup.sourceFamily_zero_eq_original` in `Zeta23/OPICAFollowup/NativeSourceFamily.lean`.
- `Zeta23.OPICAFollowup.sourceFamily_support_smooth_moments` in `Zeta23/OPICAFollowup/NativeSourceFamily.lean`.
- `Zeta23.OPICAFollowup.sourceFamily_laplace_identity` in `Zeta23/OPICAFollowup/NativeSourceTransforms.lean`.
- `Zeta23.OPICAFollowup.nativePrimeField_visiblePole` in `Zeta23/OPICAFollowup/NativeSourceTransforms.lean`.
- `Zeta23.OPICAFollowup.nativeGenerator_transform` in `Zeta23/OPICAFollowup/NativeFilters.lean`.
- `Zeta23.OPICAFollowup.nativeGenerator_unit_or_completion` in `Zeta23/OPICAFollowup/NativeFilters.lean`.
- `Zeta23.OPICAFollowup.nativeWord_corrected_transform` in `Zeta23/OPICAFollowup/NativeTransformationWords.lean`.
- `Zeta23.OPICAFollowup.nativeWord_order_and_leading` in `Zeta23/OPICAFollowup/NativeTransformationWords.lean`.
- `Zeta23.OPICAFollowup.nativeWord_first_nonzero_derivative` in `Zeta23/OPICAFollowup/NativeTransformationWords.lean`.
- `Zeta23.OPICAFollowup.nativeWord_factor_costs` in `Zeta23/OPICAFollowup/NativeTransformationWords.lean`.
- `Zeta23.OPICAFollowup.nativeWord_contour_consumer` in `Zeta23/OPICAFollowup/RobustLaurent.lean`.
- `Zeta23.OPICAFollowup.step123_word_jet_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### R1-AT1 — Norm-first arithmetic rate transfer

Source: Part IV / AT1.

Source hypotheses: Exact F=S+B, real Q=norm(B)^2-L, common positive cofinal schedule.

Source conclusion: Subexponential Type I L2 norm and low-mask cost suffice for logarithmic energy-rate comparison.

Scope limit: Weakens earlier sufficient error requirements; no new signed upper or source-order schedule optimized.

- `Zeta23.OPICAFollowup.norm_first_log_comparison` in `Zeta23/OPICAFollowup/NormFirstTransfer.lean`.
- `Zeta23.OPICAFollowup.norm_first_rate_transfer` in `Zeta23/OPICAFollowup/NormFirstTransfer.lean`.
- `Zeta23.OPICAFollowup.balanced_coeff_divisor_bound` in `Zeta23/OPICAFollowup/BalancedCoefficients.lean`.
- `Zeta23.OPICAFollowup.log_slack_both_low_masks_subexp` in `Zeta23/OPICAFollowup/MaskedNativeRate.lean`.
- `Zeta23.OPICAFollowup.log_slack_masked_energy_rate_difference` in `Zeta23/OPICAFollowup/MaskedNativeRate.lean`.
- `Zeta23.OPICAFollowup.norm_first_strictly_weaker_control` in `Zeta23/OPICAFollowup/Counterexamples.lean`.
### R1-AT2 — Native energy allocation inequality

Source: Part IV / AT2.

Source hypotheses: Exact same field/mask partition; causal source and coefficient hypotheses for low-mask instance.

Source conclusion: Complete energy <= 2 TypeI energy + 2 positive high-mask + 2 absolute low-mask.

Scope limit: Positive rate must survive in a maximum if low cost is subexponential; no branchwise equality asserted.

- `Zeta23.OPICAFollowup.energy_allocation_bound` in `Zeta23/OPICAFollowup/NormFirstTransfer.lean`.
- `Zeta23.OPICAFollowup.energy_allocation_rate_lower` in `Zeta23/OPICAFollowup/NormFirstTransfer.lean`.
### R1-HT1 — Noncompact weighted-mixing obstruction and gap leakage

Source: Part IV / HT1.

Source hypotheses: Mixing measure has absolute exponential moment a>1/2; actual comb family and Fourier transport.

Source conclusion: Actual weighted Mobius inverse; sharp selfdual gap forces scalar comb; explicit weighted gap-leakage bound.

Scope limit: Extends compact M0043 to a particular noncompact class; not all renormalized or critical-tail maps.

- `Zeta23.OPICAFollowup.dilated_comb_fourier` in `Zeta23/OPICAFollowup/DilatedComb.lean`.
- `Zeta23.OPICAFollowup.weighted_mixture_exists_fourier` in `Zeta23/OPICAFollowup/WeightedMixing.lean`.
- `Zeta23.OPICAFollowup.weighted_mobius_inverse` in `Zeta23/OPICAFollowup/WeightedMixing.lean`.
- `Zeta23.OPICAFollowup.weighted_mixture_sharp_gap` in `Zeta23/OPICAFollowup/WeightedMixing.lean`.
- `Zeta23.OPICAFollowup.weighted_gap_leakage` in `Zeta23/OPICAFollowup/WeightedMixing.lean`.
### R1-HT2 — Near-sharp gap estimate and controlled limit

Source: Part IV / HT2.

Source hypotheses: Even real selfdual locally finite signed measures; common linear total-variation growth; positivity off integers; gaps tend to one.

Source conclusion: Finite-region off-lattice mass bounded by (1-a) variation budget; controlled sequence tends to zero on Schwartz tests.

Scope limit: Not convergence in total variation; no statement about unbounded normalization costs.

- `Zeta23.OPICAFollowup.near_gap_mass_bound` in `Zeta23/OPICAFollowup/NearGapLimits.lean`.
- `Zeta23.OPICAFollowup.near_gap_controlled_limit_zero` in `Zeta23/OPICAFollowup/NearGapLimits.lean`.
### R1-CT1 — Almost-gapped comb family and normalized distributional limit

Source: Part IV / CT1.

Source hypotheses: Explicit positive/negative dilation comb combination, 0<L<log 2.

Source conclusion: Finite-stage near-gap conditions hold; normalized limit has nonzero delta derivatives and leaves measure class.

Scope limit: Auxiliary counterexample to an unqualified limit passage, not a zeta counterexample.

- `Zeta23.OPICAFollowup.dilated_comb_fourier` in `Zeta23/OPICAFollowup/DilatedComb.lean`.
- `Zeta23.OPICAFollowup.dilation_near_gap_family` in `Zeta23/OPICAFollowup/NearGapLimits.lean`.
- `Zeta23.OPICAFollowup.dilation_normalized_limit_not_measure` in `Zeta23/OPICAFollowup/NearGapLimits.lean`.
### R1-MC1 — Two-zero coupled-conditioning control

Source: Part IV / MC1.

Source hypotheses: Explicit rational inner model and true exponential Gram, 0<h<1.

Source conclusion: Singular Gram inverse paired with coupled data has cost (2-h^2)/(1-h^2), tending to two.

Scope limit: No actual zeta zeros used; finite Gram theory already exists in archive.

- `Zeta23.OPICAFollowup.coupled_gram_collision_control` in `Zeta23/OPICAFollowup/Counterexamples.lean`.
### R1-CP1 — Renormalized actual-zero heat measure and explicit sign failure

Source: Part IV / CP1.

Source hypotheses: Actual zeta zero 0<Re(rho)<1, rho!=1/2; subtractions before cutoff limit; local measure proof.

Source conclusion: Nonzero even real selfdual signed measure, exact unit gap, zero origin, linear variation. Explicit negative density in first interval when |Im rho|>3*pi/(2 log 2). For off-line zeros with |Im rho|>2*pi/log 2, every nonzero real scalar projection of this single-zero measure has both density signs in the first lattice interval.

Scope limit: New derivation this round, related classical co-Poisson theory; off-lattice positivity fails, including critical-line case. Not literal-j/contact identity or RH exclusion.

- `Zeta23.OPICAFollowup.complex_local_measure_embedding_faithful` in `Zeta23/OPICAFollowup/ComplexLocalMeasures.lean`.
- `Zeta23.OPICAFollowup.dilated_comb_fourier` in `Zeta23/OPICAFollowup/DilatedComb.lean`.
- `Zeta23.OPICAFollowup.renormalized_copoisson_tempered_family` in `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`.
- `Zeta23.OPICAFollowup.renormalized_copoisson_order_zero` in `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`.
- `Zeta23.OPICAFollowup.zero_measure_exact_properties` in `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`.
- `Zeta23.OPICAFollowup.zero_measure_first_cell_sign` in `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`.
- `Zeta23.OPICAFollowup.actual_zero_measure_span_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### R2-Q1a — Uniform source-product vertical bound

Source: Part V / R2-Q1a.

Source hypotheses: Literal infinite-box q, real sigma and tau; entire normally convergent product.

Source conclusion: |Q0(sigma+i tau)| <= 8 exp(s0 |sigma|) exp(-cq sqrt(|tau|)), cq=(log 8)sqrt(s0)/4.

Scope limit: A uniform source estimate; not a reciprocal-zeta estimate.

- `Zeta23.OPICAFollowup.source_product_vertical_bound` in `Zeta23/OPICAFollowup/SourceVerticalBounds.lean`.
### R2-Q1b — Uniform moving left-line zeta/derivative envelope

Source: Part V / R2-Q1b.

Source hypotheses: Integer n>=1, all real tau; classical zeta functional equation and gamma strip bound.

Source conclusion: |zeta(-n+i tau)|+|zeta_prime(-n+i tau)| <= A0^(n+1)(n+2+|tau|)^(n+2).

Scope limit: Existence of a universal A0; its numerical value is not certified.

- `Zeta23.OPICAFollowup.zeta_left_line_uniform_bound` in `Zeta23/OPICAFollowup/ZetaLeftLineBounds.lean`.
### R2-Q2 — Fixed-order double-exponential forward localization

Source: Part V / R2-Q2.

Source hypotheses: Fixed m>=ell>=0,d>=0; exact entire forward transform R_m,ell.

Source conclusion: |R_m,ell^(d)(t)| <= A exp(-c exp(t/(2(ell+1)))) for t>=0.

Scope limit: Orders fixed before limit. Generalizes the inherited ell=0 scale; not an optimality claim.

- `Zeta23.OPICAFollowup.sourceFamily_support_smooth_moments` in `Zeta23/OPICAFollowup/NativeSourceFamily.lean`.
- `Zeta23.OPICAFollowup.forwardKernel_physical_laplace` in `Zeta23/OPICAFollowup/NativeSourceTransforms.lean`.
- `Zeta23.OPICAFollowup.forwardKernel_left_contour_budget` in `Zeta23/OPICAFollowup/ForwardLocalization.lean`.
- `Zeta23.OPICAFollowup.forwardKernel_double_exp_decay` in `Zeta23/OPICAFollowup/ForwardLocalization.lean`.
### R2-Q3 — Logarithmic-slack balanced native decomposition

Source: Part V / R2-Q3.

Source hypotheses: Fixed r>=2,m>=r-1,C>1,eta>=0; finite squarefree Q_T frozen per window, Q_T<=T^eta; K>C+r eta+2r.

Source conclusion: Y=e^(T/r)T^(-K/r), Z=e^(T/r-g)T^(K(r-1)/r); exact F_m=E+B with sup error <=C1 T^(r eta) exp(T/2-c T^p), p>1.

Scope limit: No signed upper for B, no improved zero-free strip, no MS1 required. No certified numeric starting horizon.

- `Zeta23.OPICAFollowup.native_binomial_inverse_identity` in `Zeta23/OPICAFollowup/BalancedCoefficients.lean`.
- `Zeta23.OPICAFollowup.balanced_coeff_divisor_bound` in `Zeta23/OPICAFollowup/BalancedCoefficients.lean`.
- `Zeta23.OPICAFollowup.log_slack_native_decomposition` in `Zeta23/OPICAFollowup/LogSlackBalance.lean`.
- `Zeta23.OPICAFollowup.log_slack_typeI_error` in `Zeta23/OPICAFollowup/LogSlackBalance.lean`.
- `Zeta23.OPICAFollowup.fixed_two_factor_preparation` in `Zeta23/OPICAFollowup/LogSlackBalance.lean`.
- `Zeta23.OPICAFollowup.log_slack_both_low_masks_subexp` in `Zeta23/OPICAFollowup/MaskedNativeRate.lean`.
- `Zeta23.OPICAFollowup.log_slack_masked_energy_rate_difference` in `Zeta23/OPICAFollowup/MaskedNativeRate.lean`.
- `Zeta23.OPICAFollowup.fixed_two_factor_mask_rate_theta` in `Zeta23/OPICAFollowup/Consumers.lean`.
- `Zeta23.OPICAFollowup.quiet_balanced_observation_implies_native_cut` in `Zeta23/OPICAFollowup/Consumers.lean`.
### R2-O1 — Joint source-history observation recovery and optimal norm

Source: Part V / R2-O1.

Source hypotheses: Finite-dimensional complex Hilbert spaces; joint observation A=(P,C), target linear functional ell.

Source conclusion: Recovery iff ker P intersect ker C subset ker ell; exact norm sup |ell(x)|/||Ax||, with zero-map convention.

Scope limit: A native recovery hypothesis and subexponential cost must still be established for any application.

- `Zeta23.OPICAFollowup.joint_recovery_iff` in `Zeta23/OPICAFollowup/JointObservation.lean`.
- `Zeta23.OPICAFollowup.joint_recovery_optimal_norm` in `Zeta23/OPICAFollowup/JointObservation.lean`.
### R2-O2 — Noisy recovery and quantitative compatibility test

Source: Part V / R2-O2.

Source hypotheses: Same O1 data; measurement error at most epsilon; finite compatibility matrix B.

Source conclusion: Target error <= recovery_norm epsilon; a unit left-null vector with pairing >epsilon certifies no epsilon-approximate compatibility.

Scope limit: Algebraic injectivity need not have acceptable cost; epsilon=e^(-aT) control exhibits exponential recovery.

- `Zeta23.OPICAFollowup.joint_recovery_noise_bound` in `Zeta23/OPICAFollowup/JointObservation.lean`.
- `Zeta23.OPICAFollowup.approx_compatibility_left_null` in `Zeta23/OPICAFollowup/JointObservation.lean`.
- `Zeta23.OPICAFollowup.recovery_subexp_budget` in `Zeta23/OPICAFollowup/JointObservation.lean`.
- `Zeta23.OPICAFollowup.history_recovery_cost_control` in `Zeta23/OPICAFollowup/Counterexamples.lean`.
### R2-J1 — Robust Laurent jets with changing completion depth

Source: Part V / R2-J1.

Source hypotheses: Common contour radius r; meromorphic error with only central pole; finite sup bound E; coefficient degree j>=-1.

Source conclusion: Coefficient error <= r^(-j)E; nonzero if E<|a_j|r^j; derivative version includes j!.

Scope limit: Does not establish the actual contour error bound; compact-time convergence is insufficient.

- `Zeta23.OPICAFollowup.laurent_coefficient_error_bound` in `Zeta23/OPICAFollowup/RobustLaurent.lean`.
- `Zeta23.OPICAFollowup.laurent_observation_survives` in `Zeta23/OPICAFollowup/RobustLaurent.lean`.
- `Zeta23.OPICAFollowup.nativeWord_contour_consumer` in `Zeta23/OPICAFollowup/RobustLaurent.lean`.
- `Zeta23.OPICAFollowup.step123_word_jet_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### R2-S1a — Actual-zero co-Poisson profile tail, self-duality and regularity

Source: Part V / R2-S1a.

Source hypotheses: Actual nontrivial zero 0<Re rho<1, rho!=1/2; kappa=rho(1-rho); normalized CP1 density.

Source conclusion: h=1-g is even continuous selfdual L1 and L2, equals one on [-1,1], integral half-line 1/2, tail kappa B2/(2x^2)+O(x^-3), h_prime=O(x^-2), integer jump -kappa/n^2.

Scope limit: Not positivity of h; not a literal-j/contact identity; no assumption of simple zeros.

- `Zeta23.OPICAFollowup.finite_sum_euler_maclaurin_uniform` in `Zeta23/OPICAFollowup/ProfileEulerMaclaurin.lean`.
- `Zeta23.OPICAFollowup.zero_profile_regular_selfdual` in `Zeta23/OPICAFollowup/ZeroProfiles.lean`.
- `Zeta23.OPICAFollowup.zero_profile_tail_and_jumps` in `Zeta23/OPICAFollowup/ZeroProfiles.lean`.
### R2-S1b — Forced Euler equation and form-domain distinction

Source: Part V / R2-S1b.

Source hypotheses: Same actual zero profile.

Source conclusion: -(x^2 h_prime)_prime = kappa(h-1+sum positive_integer_delta); positive form identity under log coordinates; nonzero atomic forcing prevents homogeneous L2 eigenproblem.

Scope limit: Does not infer kappa is real or invoke self-adjoint eigenvalue theory on a vector outside that operator domain.

- `Zeta23.OPICAFollowup.log_unitary_form_identity` in `Zeta23/OPICAFollowup/LogFourierSobolev.lean`.
- `Zeta23.OPICAFollowup.zero_profile_forced_euler` in `Zeta23/OPICAFollowup/ForcedEuler.lean`.
- `Zeta23.OPICAFollowup.zero_profile_not_homogeneous_operator_vector` in `Zeta23/OPICAFollowup/ForcedEuler.lean`.
- `Zeta23.OPICAFollowup.actual_force_sampling_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### R2-S2 — Native multi-zero sampling compatibility

Source: Part V / R2-S2.

Source hypotheses: Finite actual zero profiles, distinct kappa representatives; absolute integrability and summability from S1.

Source conclusion: Qij=kappa_i(Nij+conj b_j)=conj kappa_j(Nij+b_i); undivided identity; conditional divided-difference positivity; Q-(1/4)N PSD.

Scope limit: No uniform conditioning or independent bound/reality for sample sums. Synthetic forced models satisfy the same identities at nonreal parameters.

- `Zeta23.OPICAFollowup.native_sampling_gram_identity` in `Zeta23/OPICAFollowup/SamplingCompatibility.lean`.
- `Zeta23.OPICAFollowup.native_sampling_form_positive` in `Zeta23/OPICAFollowup/SamplingCompatibility.lean`.
- `Zeta23.OPICAFollowup.forced_positive_gram_nonreal_control` in `Zeta23/OPICAFollowup/Counterexamples.lean`.
### R2-H1 — Multiplicity-sensitive zero-jet measures

Source: Part V / R2-H1.

Source hypotheses: Actual zeros of multiplicities m_j; local inverse rho(kappa); derivative orders k<m_j.

Source conclusion: Normalized parameter jets are order-zero even selfdual measures, with exact gap/origin and linear growth; forced differentiated chain retained.

Scope limit: No gap beyond the actual multiplicity; this R2-H1 is not the original P0-H1 signed separator.

- `Zeta23.OPICAFollowup.complex_local_measure_embedding_faithful` in `Zeta23/OPICAFollowup/ComplexLocalMeasures.lean`.
- `Zeta23.OPICAFollowup.finite_sum_euler_maclaurin_uniform` in `Zeta23/OPICAFollowup/ProfileEulerMaclaurin.lean`.
- `Zeta23.OPICAFollowup.copoisson_zero_jets_measures` in `Zeta23/OPICAFollowup/CoPoissonJets.lean`.
- `Zeta23.OPICAFollowup.actual_zero_measure_span_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### R2-H2a — Finite zero-jet independence and explicit confluent determinant

Source: Part V / R2-H2a.

Source hypotheses: Finite distinct nonzero kappa nodes, total multiplicity M; reflection-duplicate parameters removed.

Source conclusion: Measures independent; determinant=(-1)^(M(M-1)/2) product kappa_j^m_j product_(i<j)(kappa_j-kappa_i)^(m_i m_j).

Scope limit: No uniform inverse norm at colliding or growing zero systems. Conjugacy handled when forming real measures.

- `Zeta23.OPICAFollowup.profile_jet_confluent_determinant` in `Zeta23/OPICAFollowup/ConfluentProfiles.lean`.
- `Zeta23.OPICAFollowup.finite_zero_jet_independent` in `Zeta23/OPICAFollowup/ConfluentProfiles.lean`.
### R2-H2b — Finite-span sign separation and fixed-basis negative-mass budget

Source: Part V / R2-H2b.

Source hypotheses: Real finite combinations of the H1 zero jets; all H1 measure hypotheses.

Source conclusion: Only zero can be nonnegative off lattice; on a fixed independent real basis, weighted negative mass >= c_basis ||coefficients||.

Scope limit: Finite generated span only; no exclusion of arbitrary nonlinear or uncontrolled infinite constructions.

- `Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero` in `Zeta23/OPICAFollowup/FiniteSpanSeparation.lean`.
- `Zeta23.OPICAFollowup.fixed_basis_negative_mass_budget` in `Zeta23/OPICAFollowup/FiniteSpanSeparation.lean`.
- `Zeta23.OPICAFollowup.actual_zero_measure_span_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### R2-H3 — Explicit first-interval correction cost

Source: Part V / R2-H3.

Source hypotheses: Normalized real actual-zero density; |delta|<1/2; |gamma|>=16.

Source conclusion: On log interval [4pi/(3|gamma|),5pi/(3|gamma|)], density <=-|gamma| e^(-u/2)/2; negative mass >=pi/6 and weighted mass >=8pi/(27 gamma^2).

Scope limit: Height hypothesis retained; also applies on critical line, so not an off-line-zero exclusion.

- `Zeta23.OPICAFollowup.first_cell_negative_mass_cost` in `Zeta23/OPICAFollowup/FirstCellCost.lean`.
### R2-S3 — Nonlinear square defect, no lattice repair, and gap-filling projection

Source: Part V / R2-S3.

Source hypotheses: Even continuous selfdual h in L1 intersect L2, h=A on [-1,1], vanishing at infinity, h nonzero.

Source conclusion: Positive gapped square measure has duality defect h*conj h-|h|^2, positive at origin; no lattice-supported tempered measure repairs it; selfdual projection fills gap near origin.

Scope limit: Specific square family only, including finite profile combinations; not a universal prohibition on nonlinear constructions.

- `Zeta23.OPICAFollowup.square_fourier_defect` in `Zeta23/OPICAFollowup/SquareDefect.lean`.
- `Zeta23.OPICAFollowup.square_defect_origin_positive` in `Zeta23/OPICAFollowup/SquareDefect.lean`.
- `Zeta23.OPICAFollowup.square_no_lattice_repair` in `Zeta23/OPICAFollowup/SquareDefect.lean`.
- `Zeta23.OPICAFollowup.square_selfdual_projection_fills_gap` in `Zeta23/OPICAFollowup/SquareDefect.lean`.
### F1 — Actual tempered arithmetic force and its Mellin budget

Source: Part III / F1.

Source hypotheses: Literal integer comb; w(t)=exp(-t/2){exp t}; log Fourier convention exp(-i xi t)

Source conclusion: g=-(D+1/2)w=N-exp(t/2)dt on compact tests; Flog(g)=zeta(1/2+i xi); exact weighted moment log(2pi)-EulerGamma

Scope limit: Tempered extension is after subtraction. This is a classical moment in the required normalization, not a novelty claim.

- `Zeta23.OPICAFollowup.log_unitary_form_identity` in `Zeta23/OPICAFollowup/LogFourierSobolev.lean`.
- `Zeta23.OPICAFollowup.log_fourier_plancherel` in `Zeta23/OPICAFollowup/LogFourierSobolev.lean`.
- `Zeta23.OPICAFollowup.sawtooth_integrable_force_identity` in `Zeta23/OPICAFollowup/SawtoothForce.lean`.
- `Zeta23.OPICAFollowup.sawtooth_actual_mellin_fourier` in `Zeta23/OPICAFollowup/SawtoothForce.lean`.
- `Zeta23.OPICAFollowup.sawtooth_norm_weighted_zeta_moment` in `Zeta23/OPICAFollowup/SawtoothForce.lean`.
- `Zeta23.OPICAFollowup.actual_force_sampling_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### F2 — Actual sampling Stieltjes representation

Source: Part III / F2.

Source hypotheses: Actual off-line zero profile; kappa nonreal; R2-S1 measure/profile identities

Source conclusion: b_kappa=kappa integral |zeta(1/2+i xi)|^2/(xi^2+1/4-kappa) dxi/(2pi); norm/form and priced source-moment bounds

Scope limit: Positive spectral density permits nonreal forced parameters; no independent exclusion or assumed sample reality.

- `Zeta23.OPICAFollowup.log_unitary_form_identity` in `Zeta23/OPICAFollowup/LogFourierSobolev.lean`.
- `Zeta23.OPICAFollowup.log_fourier_plancherel` in `Zeta23/OPICAFollowup/LogFourierSobolev.lean`.
- `Zeta23.OPICAFollowup.arithmetic_stieltjes_holomorphic` in `Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean`.
- `Zeta23.OPICAFollowup.arithmetic_stieltjes_sign_budget` in `Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean`.
- `Zeta23.OPICAFollowup.native_forced_resolvent_unique` in `Zeta23/OPICAFollowup/NativeResolvent.lean`.
- `Zeta23.OPICAFollowup.native_sample_stieltjes_identity` in `Zeta23/OPICAFollowup/NativeResolvent.lean`.
- `Zeta23.OPICAFollowup.native_profile_spectral_norms` in `Zeta23/OPICAFollowup/NativeResolvent.lean`.
- `Zeta23.OPICAFollowup.actual_force_sampling_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### F3 — Generic forced resolvent and exact plateau coefficient

Source: Part III / F3.

Source hypotheses: 1/2<Re rho<1, Im rho !=0, b_rho=(1-2rho)/(rho(1-rho))

Source conclusion: Unique log-form solution is 1-S_rho/b_rho-zeta(rho)x^(rho-1)/b_rho; plateau iff zeta(rho)=0

Scope limit: Diagnostic source identity, not a new proposed equivalent-condition campaign or proof of zero exclusion.

- `Zeta23.OPICAFollowup.finite_sum_euler_maclaurin_uniform` in `Zeta23/OPICAFollowup/ProfileEulerMaclaurin.lean`.
- `Zeta23.OPICAFollowup.log_unitary_form_identity` in `Zeta23/OPICAFollowup/LogFourierSobolev.lean`.
- `Zeta23.OPICAFollowup.generic_forced_profile_unique` in `Zeta23/OPICAFollowup/BoundaryAmplitude.lean`.
- `Zeta23.OPICAFollowup.generic_boundary_amplitude` in `Zeta23/OPICAFollowup/BoundaryAmplitude.lean`.
- `Zeta23.OPICAFollowup.actual_force_sampling_consumer` in `Zeta23/OPICAFollowup/Consumers.lean`.
### J5.2 — Native fixed-source logarithmic-window rate

Source: Part II.1-II.4.

- `Zeta23.OPICAFollowup.sourceFamily_zero_eq_original` in `Zeta23/OPICAFollowup/NativeSourceFamily.lean`.
- `Zeta23.OPICAFollowup.sourceFamily_laplace_identity` in `Zeta23/OPICAFollowup/NativeSourceTransforms.lean`.
- `Zeta23.OPICAFollowup.forwardKernel_physical_laplace` in `Zeta23/OPICAFollowup/NativeSourceTransforms.lean`.
- `Zeta23.OPICAFollowup.native_zero_count_summability` in `Zeta23/OPICAFollowup/NativeExplicitFormula.lean`.
- `Zeta23.OPICAFollowup.native_source_explicit_formula` in `Zeta23/OPICAFollowup/NativeExplicitFormula.lean`.
- `Zeta23.OPICAFollowup.native_zero_sup_bounds` in `Zeta23/OPICAFollowup/NativeExplicitFormula.lean`.
- `Zeta23.OPICAFollowup.source_order_uniform_norms` in `Zeta23/OPICAFollowup/UniformSourceBounds.lean`.
- `Zeta23.OPICAFollowup.native_field_theta_envelope` in `Zeta23/OPICAFollowup/UniformSourceBounds.lean`.
- `Zeta23.OPICAFollowup.aux_completion_actual_transform` in `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`.
- `Zeta23.OPICAFollowup.aux_completion_uniform_decay` in `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`.
- `Zeta23.OPICAFollowup.aux_completion_ratio_bounds` in `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`.
- `Zeta23.OPICAFollowup.native_auxiliary_top_moment` in `Zeta23/OPICAFollowup/MultiplicityTail.lean`.
- `Zeta23.OPICAFollowup.laguerre_tail_norm` in `Zeta23/OPICAFollowup/MultiplicityTail.lean`.
- `Zeta23.OPICAFollowup.native_auxiliary_tail_residual_lower` in `Zeta23/OPICAFollowup/MultiplicityTail.lean`.
- `Zeta23.OPICAFollowup.native_terminal_memory_lower` in `Zeta23/OPICAFollowup/MultiplicityTail.lean`.
- `Zeta23.OPICAFollowup.native_fixed_source_window_rate` in `Zeta23/OPICAFollowup/NativeWindowRate.lean`.
- `Zeta23.OPICAFollowup.fixed_two_factor_mask_rate_theta` in `Zeta23/OPICAFollowup/Consumers.lean`.
- `Zeta23.OPICAFollowup.quiet_balanced_observation_implies_native_cut` in `Zeta23/OPICAFollowup/Consumers.lean`.
### MS1 — Slowly changing native source logarithmic-window rate

Source: Part II.1-II.4.

- `Zeta23.OPICAFollowup.native_zero_sup_bounds` in `Zeta23/OPICAFollowup/NativeExplicitFormula.lean`.
- `Zeta23.OPICAFollowup.source_order_uniform_norms` in `Zeta23/OPICAFollowup/UniformSourceBounds.lean`.
- `Zeta23.OPICAFollowup.native_field_theta_envelope` in `Zeta23/OPICAFollowup/UniformSourceBounds.lean`.
- `Zeta23.OPICAFollowup.aux_completion_actual_transform` in `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`.
- `Zeta23.OPICAFollowup.aux_completion_uniform_decay` in `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`.
- `Zeta23.OPICAFollowup.aux_completion_ratio_bounds` in `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`.
- `Zeta23.OPICAFollowup.native_auxiliary_top_moment` in `Zeta23/OPICAFollowup/MultiplicityTail.lean`.
- `Zeta23.OPICAFollowup.laguerre_tail_norm` in `Zeta23/OPICAFollowup/MultiplicityTail.lean`.
- `Zeta23.OPICAFollowup.native_auxiliary_tail_residual_lower` in `Zeta23/OPICAFollowup/MultiplicityTail.lean`.
- `Zeta23.OPICAFollowup.native_terminal_memory_lower` in `Zeta23/OPICAFollowup/MultiplicityTail.lean`.
- `Zeta23.OPICAFollowup.native_slow_source_window_rate` in `Zeta23/OPICAFollowup/MovingSourceWindowRate.lean`.

## 9. Imports, build entrypoints and proof-lane wiring

The attached DOT graph is directed from dependencies to consumers. The manifest gives every direct project import. Use narrow defining-module imports where possible; do not make a new root import the global registered audit.

```text
existing P0 local/jet/native APIs
  -> actual source family/transforms -> concrete native filters/words
  -> robust Laurent observations -> same-state native consumers

existing P0 rate/mask/divisor APIs
  -> norm-first transfer + actual binomial coefficients
  -> source vertical bound + moving-left-line zeta bound
  -> actual forward localization -> logarithmic-slack arithmetic
  -> both low masks -> retained-rate comparison

actual compact-test EF + actual zeta local zero count
  -> source-specific explicit formula + uniform source costs
  -> explicit auxiliary completions + all-multiplicity tail residual
  -> native fixed-source J5.2 -> native slow-source MS1
  -> retained-rate = Theta consumer

P0 real locally finite measures + sinc/triangle pairing
  -> compatible complex locally finite measures + actual scaled combs
  -> weighted mixing / near-gap limits / renormalized co-Poisson family
  -> actual zero profiles + finite jets + Hermite independence
  -> finite-span separator and first-cell cost / square defect

actual profile + actual log Fourier/Sobolev conversion
  -> forced Euler + exact sampling compatibility
  -> sawtooth force + weighted positive spectral measure
  -> actual Stieltjes samples + generic forced boundary amplitude

all complete mathematical consumers
  -> Zeta23.OPICAFollowup
  -> Zeta23.OPICAFollowup.Validation
  -> Zeta23.RHRC.OpicaFollowupBindings [AUDIT_ONLY]
```

The sibling facade imports `Consumers`, which transitively reaches every new mathematical module. `Validation` and the RHRC exporter are unreachable from that facade. Original `Zeta23.OPICA` and `Zeta23` closures remain unchanged. The global audit `RegisteredClaimBindings` imports accepted child defining modules only downstream.

The four proof lanes are compilation units, not four independent claims of completion:

- `local`: actual word/jet targets, norm-first and joint recovery, with their source prerequisites;
- `arithmetic`: localization, exact balanced masks and both native window bridges;
- `heat`: full order-zero co-Poisson, weighted/near-gap statements, jets, sign budgets and square controls;
- `spectral`: exact profile, log form, source moment, Stieltjes sampling and boundary amplitude.

The exact lane target lists are in `formal_lane_targets` in the manifest. For each lane execute `lake build` on those targets, using the current checkout. `Consumers`, the facade, typed Validation and all audit targets are built by the aggregate command even when all lane builds passed.

Shared prerequisites may build in more than one lane. This does not count their theorem authority twice. Cache keys include toolchain, Mathlib revision and relevant source tree; no stale .olean is accepted as proof of a changed statement. The aggregate job builds every final target and re-exports one source-bound receipt on the same clean tree.

## 10. Compiler proof/type/source contract

The new exporter reuses `Zeta23.RHRC.OpicaTypeExprExport.exportType` without modifying its lossless DAG codec or budgets. It has its own `OPICA_FOLLOWUP_COMPILER_V1` protocol and an explicit defining-module whitelist. Do not mutate parent receipt-builder globals or make the parent primary count variable.

For every child public declaration record name, kind, actual defining module, complete untruncated type DAG, universe/binder information and standard-axiom closure. Record constructor types and fields for every child structure/inductive family. Traverse TYPE, VALUE and STRUCTURE dependencies through private project helpers, retaining source bindings and the explicit Mathlib boundary. Reject sorryAx, all unapproved project axioms, unsafe proof escape and a substituted source proposition. The permitted ordinary proof axioms remain propext, Classical.choice and Quot.sound.

Before using a primary root as accepted, `Validation.lean` must contain an independently written expected type for the intended mathematical statement. A bare `#check name` or a copied actual inferred type is not enough. Crosswalk clauses name their expected-type consumers and actual constructors. Compile them, then review/export full types and freeze approved type hashes. Do not prepopulate those hashes from an uncompiled plan, or auto-approve a changed type because the same source file generated it.

The aggregate receipt must bind requested parent/head, actual checkout commit/tree, synthetic merge parents where applicable, all new and modified authoritative file hashes, toolchain/Mathlib pins, each exact command and exit code, primary/helper/constructor inventories, and private dependency closure. Revalidate that source bytes did not change during compilation. External artifact digest verification is a separate integrity step. All receipt artifacts must belong to the same checked tree; no mix of successful easy-lane logs from different revisions.

Physical consumers are compulsory for native statements. In particular: actual j_d and its drive cannot be replaced by a generic source satisfying a claimed rate; the prime pole datum is constructed, not supplied; the co-Poisson object is proved to be a measure; Fourier duality is proved, not stored as an undisclosed field in a native instance; the sampling force remains present; and the conditional closing consumer visibly requires its still-open upper.

## 11. Registry, graph and canonical derived products

Add the exact child primary names under the `OPICA_FOLLOWUP_` claim-ID prefix after successful proof/type review. Preserve every old claim and binding byte-semantically, including the four OPEN IDs. New generic implication claims describe the implication exactly; “PROVED_UNCONDITIONAL” for a quantified theorem does not prove its mathematical antecedent. No new RH route or unconditional RH claim is introduced.

Insert these two rules before generic `zeta_lean`, and no broad override:

```text
opica_followup_audit
  ^Zeta23/(?:OPICAFollowup/Validation|RHRC/OpicaFollowupBindings)\.lean$
  LEAN_SOURCE / AUDIT_ONLY

opica_followup_math
  ^Zeta23/OPICAFollowup(?:/.*)?\.lean$
  LEAN_SOURCE / AUXILIARY_FORMALIZATION
```

Every new module gets its explicit standalone role, matching the current parent's role vocabulary for generic/native/audit entries. Preserve all previous first-match classifications. The child remains visible through its registered theorem objects and actual dependency export; do not relabel it as RH_FORMAL_CORE just to force source-only promotion.

Before generating canonical data, stage all new authoritative files: the existing source census uses tracked paths. Run the unchanged Linux producer over its complete existing output set:

```bash
python research/RHRC/tools/materialize_derived_state.py --write
python research/RHRC/tools/materialize_derived_state.py --check
```

The exact 62 paths are in the manifest and appendix. Commit only actual deterministic byte changes. Never hand-edit a generated graph, edit a historical snapshot, invent extra generated files to silence a checker, or refresh source hashes without regenerating the affected canonical outputs. Any later tracked documentation or source change requires the corresponding final refresh and check.

## 12. Workflows and regression requirements

Create `.github/workflows/rhrc_opica_followup.yml`. Keep every existing workflow byte-identical. Triggers are `pull_request` for `main` and the exact parent branch while the PR is stacked, push for `research/opica-native-followup`, and `workflow_dispatch`. Use read-only contents permissions; no workflow edits to branches, review approval, registry repair or generated-source commits. Pin third-party actions to the inspected immutable SHAs or separately reviewed replacements.

The parent workflow does not automatically run for every stacked parent-branch target, so the child workflow must explicitly run the P0 contract/build validation as part of its aggregate acceptance. Once targeted at main, inherited workflows remain part of the full acceptance harvest as well.

| New job | Classification | Exact disposition required |
|---|---|---|
| `followup-contract` | FORMAL_VALIDITY_GATE_STATIC | Parent pin and exact source/coverage/protection/extension contract; static pass is not a proof. |
| `followup-regression` | REGRESSION_GATE | Unchanged39920 finite checks per mode including P0, child mutation/unit tests,33 numerical consistency cases explicitly noninterval-certified. |
| `followup-formal` (four matrix lanes) | FORMAL_VALIDITY_GATE | Actual Lean targets per lane; missing foundation/measure/explicit-formula proof fails; no partial summary from successful easy lane. |
| `followup-aggregate` | FORMAL_VALIDITY_GATE | Build sibling facade, typed Validation, P0 audits, global registered bindings and child exporter at one clean tree; recompute complete merged compiler receipt. |
| `followup-generated` | REGRESSION_GATE | Existing canonical producer --check at current tracked tree; no CI repair or changed historical receipt. |
| `followup-research-delta` | RESEARCH_PRODUCING_CHECK | Exact clause/native-consumer and TYPE/VALUE/STRUCTURE delta, prior research dispositions; no equivalence inferred from graph connectivity. |
| `followup-summary` | COMPLETENESS_GATE | Fail on any missing/skipped/canceled/in-progress/failed required lane; record RH/Step4 OPEN and independent-review status separately. |

There are seven workflow job definitions and ten executed child job instances when all four formal lanes run. The final summary uses `if: always()` and rejects all missing, failed, canceled, timed-out, skipped or unfinished required lanes. Do not use `continue-on-error` for a proof, type, source, coverage or freshness gate. A properly documented historical conditional skip is recorded separately; it never substitutes for an unexecuted required child proof.

### 12.1 Frozen regressions

Replay the actual paper controls unchanged, with recorded script hashes and group counts:

| Suite | Expected exact checks per mode | Role |
|---|---:|---|
| Existing P0 `opica/check_exact.py` | 5,112 | Frozen regression, not a new theorem |
| Frozen Round 1 script | 18,862 | Exact finite arithmetic/algebra controls |
| Frozen Round 2 script | 14,672 | Exact rational/symbolic controls |
| Final source-completion script | 1,274 | Exact finite source/resolvent controls |
| Total per normal and optimized mode | 39,920 | Not infinite-analytic validation |

The current parent P0 checker is an integration-adapted script, with source SHA-256 `42a1b29e979a415647b2ad477df4aa8e00b46f1afa52c1748748af4c79aa6985`; its original paper checker has a different byte hash. Preserve the current parent script and compare mathematical group/fixture counts, not falsely claim those two scripts are byte-identical.

The CP1 replay script writes `receipts/copoisson_numeric.json` relative to its package root. The wrapper must copy that unchanged script into an external temporary `checks/` layout, create its sibling `receipts/`, execute it there and harvest the output. Never run it in the tracked integration folder and leave a new untracked receipt.

The 33 numerical consistency cases are a separate result stream, not interval-certified and not actual hypothetical off-line-zero experiments. Freeze code and tolerances; report individual outcomes and any nonreproduction without converting floating-point agreement into proof. The dependency lock protects the recorded SymPy/mpmath environment. Run new validator mutation tests in both modes; Python assertions must not be the sole failure mechanism of a scientific checker.

### 12.2 Exact implementation commands

The commands below are required interfaces for the proposed scripts, not claims those scripts already exist. Each must be implemented with the documented flags. Run from repository root; emit receipts outside the tracked source tree.

```bash
F=research/RHRC/integration/opica_followup
P=research/RHRC/integration/opica
mkdir -p /tmp/opica-followup

python "$F/capture_parent.py" --parent-pr 293 \
  --expected-head 553b4263b58d9fec178320de251ff299a0bd702a \
  --expected-tree 12691099f1a155a8bfa3ad4f6689146175b233b2 \
  --phase source --output /tmp/opica-followup/parent-intake.json

python "$F/validate_contract.py" --phase preflight \
  --parent-intake /tmp/opica-followup/parent-intake.json \
  --output /tmp/opica-followup/preflight.json

python -m unittest discover -s "$P/tests" -p 'test_*.py'
python -O -m unittest discover -s "$P/tests" -p 'test_*.py'
python -m unittest discover -s "$F/tests" -p 'test_*.py'
python -O -m unittest discover -s "$F/tests" -p 'test_*.py'
python "$F/replay_controls.py" --modes normal optimized \
  --include-numerical --output-dir /tmp/opica-followup/regression

lake build Zeta23.OPICA Zeta23.OPICA.Validation \
  Zeta23.RHRC.OpicaBindings Zeta23.OPICAFollowup \
  Zeta23.OPICAFollowup.Validation Zeta23.RHRC.OpicaFollowupBindings \
  Zeta23.RHRC.RegisteredClaimBindings \
  Zeta23.RHRC.DeclarationDependencyExport Zeta23.RHRC.SourceCandidateResolution

python "$P/build_receipt.py" --requested-head "$FOLLOWUP_HEAD" \
  --requested-base 97926d6a949fed7af0429a373b47abc772012834 \
  --output-dir /tmp/opica-followup/parent-current
python "$P/validate_contract.py" --phase release \
  --formal-receipt /tmp/opica-followup/parent-current/compiler-receipt.json \
  --output /tmp/opica-followup/parent-current/release.json

python "$F/build_receipt.py" --requested-head "$FOLLOWUP_HEAD" \
  --requested-base "$ACCEPTED_PARENT" --output-dir /tmp/opica-followup/formal
python "$F/validate_contract.py" --phase release \
  --parent-intake /tmp/opica-followup/parent-intake.json \
  --formal-receipt /tmp/opica-followup/formal/compiler-receipt.json \
  --parent-formal-receipt /tmp/opica-followup/parent-current/compiler-receipt.json \
  --output /tmp/opica-followup/release.json

python research/RHRC/tools/run_suite.py
python research/RHRC/tools/materialize_derived_state.py --check
python "$F/dependency_delta.py" \
  --parent-intake /tmp/opica-followup/parent-intake.json \
  --formal-receipt /tmp/opica-followup/formal/compiler-receipt.json \
  --output /tmp/opica-followup/dependency-delta.json
python "$F/harvest_workflows.py" --repo HMarcusWH/zeta-23-lean \
  --head "$FOLLOWUP_HEAD" --output /tmp/opica-followup/workflow-harvest.json
```

The source-phase intake above permits inspection and local work, not merge acceptance. Before a release validation, rerun `capture_parent.py --phase acceptance` with the exact parent compiler receipt/artifact and paginated workflow harvest supplied through `--formal-receipt` and `--workflow-harvest`; overwrite only the external intake path with a new, validated acceptance receipt. A source-only or pending intake is rejected by release mode. Parent receipt and workflow scopes must agree at that point.

`FOLLOWUP_HEAD` and `ACCEPTED_PARENT` are required actual40hex identities, not literals accepted by scripts. The displayed parent intake pin is amended only through the drift procedure when #293's accepted result changes. CI must not treat unresolved environment variables or empty inputs as the current head.

### 12.3 Full workflow harvesting

Enumerate all attached workflows and their paginated job/attempt lists for the final head, relevant merge check and push events. For each job record exact checked source, event, attempt, status, conclusion, conditional skips, artifact digests, commands, mathematical disposition, and comparison with the prior same fixture. Distinguish compiler validity, frozen regression and research-producing checks. A research run can succeed while reporting an unresolved feasibility claim or a falsified candidate.

Never hard-code “all55” or “all61” as permanent success. Do not infer current success from the parent PR body or an earlier checkpoint. Do not treat a running materializer or interval certificate job as finished. At full green, read successful proofs and all scientific outputs before choosing the next mathematical investigation.

## 13. Implementation sequence and stop conditions

**Stage0: accept/capture the parent and source papers.** Reconcile live head/tree, all current parent workflows, expected types, source APIs and immutable input hashes. Parent draft preparation is allowed, but merge readiness is blocked until acceptance is complete. Establish the child extension test harness before adding claims.

**Stage1: cheap exact interfaces.** Implement norm-first/allocation, joint observations/noise, Laurent budgets and elementary countercontrols using P0 APIs. These do not certify the full follow-up.

**Stage2: literal source family and actual generator words.** Prove source order0 identity, actual transforms, visible prime-pole construction and every named generator/source action. Build same-state consumers without weakening the old Step123 output.

**Stage3: quantitative arithmetic and analytic bridge.** Prove vertical source/gamma estimates before selecting moving contours. Construct actual forward kernels and true J17 coefficients, then log-slack and both masks. Separately complete actual translated EF/zero sums, source cost, explicit auxiliary completions and arbitrary-multiplicity residual, then J5.2/MS1 and the Theta consumer. A generic rate assumption is a blocked native milestone.

**Stage4: full measure/domain layer.** Establish complex locally finite measure and Fourier APIs with exact real separator compatibility; actual comb transport, weighted mixing and limits. Then renormalized CP1 local-TV identification before zero jets or sign claims. Prove the profile tail/jumps, finite Hermite determinant, span sign budgets and square controls.

**Stage5: actual sampling source and resolvent.** Prove the weak-derivative log transform, sawtooth Mellin/weighted moment, actual forced H1 resolvent, sample identity and generic boundary coefficient. Keep the lattice forcing and weighted rather than finite total spectral mass.

**Stage6: exact global registration and fresh acceptance.** Only now register every proved primary with its source/type/dependencies. Run full P0 and child validation, all generated-state and inherited jobs, compile actual expected-type consumers, harvest scientific results and complete Post-Green research. No source change after those receipts without another source-bound run.

If a proof reveals a false paper clause or missing classical input, record it explicitly and repair the argument or amend scope with review. Do not manufacture a new axiom, create a record carrying the conclusion as a field and call the consumer native, substitute a compact-support/finite-dimensional result for an infinite one, or rename the completed subset “full”.

## 14. Post-Green research pass and claim firewall

The follow-up's green result would formalize the listed preservation, preparation and countertest statements. It would not provide the independent opposing estimate. The final report must separately record:

- what exact statements became formally true, with assumptions and source head;
- what every compiler/regression/research workflow established, preserved, falsified or left pending;
- changes relative to the paper and parent APIs, including generalizations or stronger required hypotheses;
- upstream opportunities to simplify source families, avoid moving-order costs or remove redundant bridges;
- downstream consumers now backed by actual native rates/measure identities, not assumed conditions;
- historical routes genuinely revived, with their previous failure reasons retested;
- new hypotheses and fastest falsifiers, clearly not proofs;
- highest-information next native restriction to attempt.

Two immediate questions are prescribed by the paper: can one prove a genuine signed upper on the fixed two-factor complete observation, and can one derive an independent restriction on the actual boundary-amplitude functional? The Stieltjes identity is a representation of the force, not a homogeneous spectral exclusion. The newly formalized finite-span and square controls should prevent repeating the already falsified constructions, without declaring all nonlinear or spectral routes impossible.

The four original OPEN claim objects remain OPEN. D2/WP4 and independent human review are not auto-approved. No “quiet regime exists” statement is a theorem in this PR unless its genuine independent proof is separately developed and reviewed; it is not in this specification.

## 15. Acceptance checklist

Full completion requires all28coverage units, every primary and companion clause, all actual source constructors, all infinite-domain identities and all scope-specific countercontrols. Every required module must be reachable from the child mathematical facade, and every audit module excluded from it. All parent math and claims are unchanged. The raw global registry/config is exactly the protected parent plus verified child extension. Both original and child compiler/type/axiom contracts pass on the exact current tree. Every required scientific checker runs in its stated domain, and all generated files are canonical. All attached jobs have recorded dispositions. All source artifacts/digests are retained without claiming they are independent review.

A declaration can be kernel-valid yet prove a weaker proposition than the paper. For that reason, file presence, root count, dependency graph connectivity, static name checks, and absence of sorry do not independently establish mathematical coverage. The expected-type review and physical consumers are mandatory alongside compiler authority.

**Specification status:** exact build design completed against the inspected PR293 source; no repository implementation, new Lean theorem or new CI run produced in this task. Parent-wide publication-head acceptance is not claimed complete. The new artifacts are stored locally; current Drive discovery exposed read operations only, so no new upload is represented as successful.

## Appendix A. Exact generated-file allowlist

These are existing products of the canonical producer, inherited from the parent inventory. Do not create substitute paths.

```text
research/RHRC/ffbbp/generated/RHKG_CANDIDATE_REDUCTION_ASSURANCE.json
research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl
research/RHRC/graph/generated/CONTACT_QUOTIENT_DECLARATION_DEPENDENCIES.jsonl
research/RHRC/graph/generated/CONTACT_QUOTIENT_VIEW.json
research/RHRC/graph/generated/DEPENDENCY_BRIDGE_FRONTIERS.json
research/RHRC/graph/generated/DEPENDENCY_COHORT_ATOMS.json
research/RHRC/graph/generated/DEPENDENCY_COHORT_OVERLAP.json
research/RHRC/graph/generated/DEPENDENCY_KERNEL_ATLAS.json
research/RHRC/graph/generated/DEPENDENCY_KERNEL_QUOTIENT.json
research/RHRC/graph/generated/DEPENDENCY_PROJECTION_FRONTIERS.json
research/RHRC/graph/generated/DEPENDENCY_PROJECTION_QUOTIENTS.json
research/RHRC/graph/generated/DEPENDENCY_PROJECTION_SUMMARY.json
research/RHRC/graph/generated/DEPENDENCY_SIGNATURE_CLASSES.json
research/RHRC/graph/generated/DOCUMENT_SEMANTIC_CLOSURE.json
research/RHRC/graph/generated/ENTRYPOINT_REACHABILITY.json
research/RHRC/graph/generated/MODULE_SEMANTIC_CLOSURE.json
research/RHRC/graph/generated/REPOSITORY_COVERAGE.json
research/RHRC/graph/generated/THEOREM_CLAIM_MAP.json
research/RHRC/graph/generated/THEOREM_DEPENDENCY_CLOSURE.json
research/RHRC/graph/generated/UNRESOLVED_GRAPH_ITEMS.json
research/RHRC/graph/generated/lean_declarations.jsonl
research/RHRC/graph/generated/lean_modules.jsonl
research/RHRC/graph/generated/lean_source_declarations.jsonl
research/RHRC/graph/generated/registry_nodes.jsonl
research/RHRC/graph/generated/relations/relations-0.jsonl
research/RHRC/graph/generated/relations/relations-1.jsonl
research/RHRC/graph/generated/relations/relations-2.jsonl
research/RHRC/graph/generated/relations/relations-3.jsonl
research/RHRC/graph/generated/relations/relations-4.jsonl
research/RHRC/graph/generated/relations/relations-5.jsonl
research/RHRC/graph/generated/relations/relations-6.jsonl
research/RHRC/graph/generated/relations/relations-7.jsonl
research/RHRC/graph/generated/relations/relations-8.jsonl
research/RHRC/graph/generated/relations/relations-9.jsonl
research/RHRC/graph/generated/relations/relations-a.jsonl
research/RHRC/graph/generated/relations/relations-b.jsonl
research/RHRC/graph/generated/relations/relations-c.jsonl
research/RHRC/graph/generated/relations/relations-d.jsonl
research/RHRC/graph/generated/relations/relations-e.jsonl
research/RHRC/graph/generated/relations/relations-f.jsonl
research/RHRC/graph/generated/repository_files.jsonl
research/RHRC/integration/generated/RH_CORE_SOURCE_ONLY_THEOREMS.jsonl
research/RHRC/integration/generated/SOURCE_CANDIDATE_RESOLUTION.jsonl
research/RHRC/integration/generated/SOURCE_CANDIDATE_SUMMARY.json
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-0.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-1.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-2.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-3.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-4.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-5.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-6.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-7.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-8.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-9.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-a.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-b.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-c.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-d.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-e.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-f.jsonl
research/RHRC/ool/generated/RHKG_OOL_PHASE_ATLAS.json
research/RHRC/ool/generated/RHKG_OOL_ROUTE_CONTACTS.jsonl
```

## Appendix B. Root-level mathematical contracts

All names below are proposed under `Zeta23.OPICAFollowup`. Their full names, source groups and expected-consumer names also appear in the root JSON. Mathematical formulas are the acceptance target; elaborated Lean expected-type hashes must be produced and reviewed during implementation.

### `Zeta23.OPICAFollowup.sourceFamily_zero_eq_original`

Defining file: `Zeta23/OPICAFollowup/NativeSourceFamily.lean`. Source: R1-NB1, J5.2.

sourceOrderFamily 0 = CCM.nativeOriginalSource; prime and integer fields at order zero equal the existing nativeOriginalPrimeField and nativeOriginalIntegerDrive.

### `Zeta23.OPICAFollowup.sourceFamily_support_smooth_moments`

Defining file: `Zeta23/OPICAFollowup/NativeSourceFamily.lean`. Source: R1-NB1, R2-Q2.

For every d>=0, j_d is smooth with support in [-s0,s0], the physical fields vanish below g=log 2-s0>0, and the required elementary moments vanish with their exact orders.

### `Zeta23.OPICAFollowup.sourceFamily_laplace_identity`

Defining file: `Zeta23/OPICAFollowup/NativeSourceTransforms.lean`. Source: R1-NB1, J5.2.

J_d(z)=(z^2-1/4)^d J_0(z), with J_0 the actual original-source Laplace transform; J_d(p)!=0 at every actual right zero p=rho-1/2.

### `Zeta23.OPICAFollowup.forwardKernel_physical_laplace`

Defining file: `Zeta23/OPICAFollowup/NativeSourceTransforms.lean`. Source: R2-Q2, J5.2.

For d>=ell and Re z>1/2, the actual integral transform of R_d,ell equals -J_d(z) zeta(z+1/2)^ell zeta'(z+1/2); the RHS extends entirely after the elementary pole cancellation.

### `Zeta23.OPICAFollowup.nativePrimeField_visiblePole`

Defining file: `Zeta23/OPICAFollowup/NativeSourceTransforms.lean`. Source: R1-NB1.

Construct SimplePoleData for the meromorphic continuation of the literal prime field with residue -m J_0(p), for every actual right zero of arbitrary multiplicity m. Prove the source/center identity.

Rejected substitute: P0 native_kernel_completion_consumer with an arbitrary supplied SimplePoleData; the actual prime-transform pole must be constructed.

### `Zeta23.OPICAFollowup.nativeGenerator_transform`

Defining file: `Zeta23/OPICAFollowup/NativeFilters.lean`. Source: R1-NB1.

All seven named generator classes have their stated actual time/transform identities: source differentiation, delay, finite Euler, inverse Euler, rational and inverse rational, finite residual power, completion. Endpoint distributions stay in the correction state.

### `Zeta23.OPICAFollowup.nativeGenerator_unit_or_completion`

Defining file: `Zeta23/OPICAFollowup/NativeFilters.lean`. Source: R1-NB1.

At an actual right zero every generator multiplier is an analytic unit except its explicitly counted zeta completion factor; residual multipliers have value one there.

### `Zeta23.OPICAFollowup.nativeWord_corrected_transform`

Defining file: `Zeta23/OPICAFollowup/NativeTransformationWords.lean`. Source: R1-NB1.

For every concrete finite native word, transformedField-correction = U Z^p originalPrimeTransform on the identified germs; U(pole)!=0; the time/source adapters agree.

### `Zeta23.OPICAFollowup.nativeWord_order_and_leading`

Defining file: `Zeta23/OPICAFollowup/NativeTransformationWords.lean`. Source: R1-NB1.

The corrected order is p*m-1 and leading coefficient is -m J_0(lambda) U(lambda) (zeta^(m)(rho)/m!)^p; nonzero, including p=0 residue case.

### `Zeta23.OPICAFollowup.nativeWord_first_nonzero_derivative`

Defining file: `Zeta23/OPICAFollowup/NativeTransformationWords.lean`. Source: R1-NB1.

For p>=1 all lower derivatives vanish and the derivative of degree p*m-1 is (p*m-1)! times the exact normalized coefficient; retain all affine histories.

### `Zeta23.OPICAFollowup.nativeWord_factor_costs`

Defining file: `Zeta23/OPICAFollowup/NativeTransformationWords.lean`. Source: R1-NB1.

Price local leading-value changes from delays, source order, Euler factors, rational factors and completion count; derivative costs include factorial. No global operator bound inferred from a local unit.

### `Zeta23.OPICAFollowup.norm_first_log_comparison`

Defining file: `Zeta23/OPICAFollowup/NormFirstTransfer.lean`. Source: R1-AT1.

If F=S+B and q=||B||^2-l with q,l real, |log(1+||F||^2)-log(1+max(q,0))| <= 2 log(1+||S||)+log(1+|l|).

Premise qualification: Real or complex Hilbert space; no native rate assumption.

### `Zeta23.OPICAFollowup.norm_first_rate_transfer`

Defining file: `Zeta23/OPICAFollowup/NormFirstTransfer.lean`. Source: R1-AT1.

On a positive cofinal HorizonSchedule, subexponential ||S_n|| and l_n imply rate difference tends to zero; transfer existing limits and extended limsup/liminf.

Rejected substitute: Requiring subexponential difference of squared energies, or inserting a native Theta equality as the theorem conclusion without proof.

### `Zeta23.OPICAFollowup.energy_allocation_bound`

Defining file: `Zeta23/OPICAFollowup/NormFirstTransfer.lean`. Source: R1-AT2.

||F||^2 <= 2||S||^2 + 2 max(q,0)+2|l| for the same exact decomposition.

### `Zeta23.OPICAFollowup.energy_allocation_rate_lower`

Defining file: `Zeta23/OPICAFollowup/NormFirstTransfer.lean`. Source: R1-AT2.

With low-mask subexponential and full energy rate Theta>0, liminf log(1+max(||S_n||^2,max(q_n,0)))/(2T_n)>=Theta; no branchwise equality or common maximizing branch asserted.

### `Zeta23.OPICAFollowup.joint_recovery_iff`

Defining file: `Zeta23/OPICAFollowup/JointObservation.lean`. Source: R2-O1.

Recovery of ell from A=(P,C) exists iff ker P intersect ker C <= ker ell; construct the map on range and extend by orthogonal projection.

### `Zeta23.OPICAFollowup.joint_recovery_optimal_norm`

Defining file: `Zeta23/OPICAFollowup/JointObservation.lean`. Source: R2-O1.

The minimum norm is sup_{Ax!=0}|ell(x)|/||Ax||, with zero cost exactly for the zero target on the zero observation; an attained whole-space extension has that norm.

### `Zeta23.OPICAFollowup.joint_recovery_noise_bound`

Defining file: `Zeta23/OPICAFollowup/JointObservation.lean`. Source: R2-O2.

If epsilon>=0 and ||y-Ax||<=epsilon then |ell(x)-R y|<=optimalRecoveryCost*epsilon; include history noise in y.

### `Zeta23.OPICAFollowup.approx_compatibility_left_null`

Defining file: `Zeta23/OPICAFollowup/JointObservation.lean`. Source: R2-O2.

dist(b,range B)<=epsilon iff an epsilon-approximate solution exists; a unit left-null vector with |<v,b>|>epsilon excludes compatibility.

### `Zeta23.OPICAFollowup.recovery_subexp_budget`

Defining file: `Zeta23/OPICAFollowup/JointObservation.lean`. Source: R2-O2.

Subexponential recovery norm and observation/history error yield a subexponential recovered error on the same schedule; no quiet target from a quiet contrast alone.

### `Zeta23.OPICAFollowup.laurent_coefficient_error_bound`

Defining file: `Zeta23/OPICAFollowup/RobustLaurent.lean`. Source: R2-J1.

On radius r>0, a common meromorphic neighborhood with only the stated central pole and sup error<=E yields |delta a_j|<=r^(-j) E for integer j>=-1.

### `Zeta23.OPICAFollowup.laurent_observation_survives`

Defining file: `Zeta23/OPICAFollowup/RobustLaurent.lean`. Source: R2-J1.

If E<|a_j| r^j, the observed coefficient remains nonzero; equality-sharp monomial counterexample and j! derivative normalization retained.

### `Zeta23.OPICAFollowup.nativeWord_contour_consumer`

Defining file: `Zeta23/OPICAFollowup/RobustLaurent.lean`. Source: R2-J1, R1-NB1.

Instantiate j=p*m-1 and the actual word coefficient, affine corrections and any recovery errors; conclude nonvanishing only under the explicit combined circle budget.

### `Zeta23.OPICAFollowup.source_product_vertical_bound`

Defining file: `Zeta23/OPICAFollowup/SourceVerticalBounds.lean`. Source: R2-Q1a.

For every real sigma,tau, |Q0(sigma+i tau)|<=8 exp(s0|sigma|) exp(-cq sqrt|tau|), cq=(log 8)sqrt(s0)/4; prove passage through the normal product.

### `Zeta23.OPICAFollowup.zeta_left_line_uniform_bound`

Defining file: `Zeta23/OPICAFollowup/ZetaLeftLineBounds.lean`. Source: R2-Q1b.

Exists A0>=1, for all integer n>=1 and real tau: |zeta(-n+i tau)|+|zeta'(-n+i tau)|<=A0^(n+1)(n+2+|tau|)^(n+2).

Rejected substitute: A family of unspecified constants depending on n, a gamma bound used outside its sector, or any reciprocal-zeta/zero-free premise.

### `Zeta23.OPICAFollowup.forwardKernel_left_contour_budget`

Defining file: `Zeta23/OPICAFollowup/ForwardLocalization.lean`. Source: R2-Q2.

For fixed d>=ell>=0 and derivative order k, prove the integral envelope C exp(D n) n^(2(ell+1)n+B) for all integer n>=1 before optimizing n.

### `Zeta23.OPICAFollowup.forwardKernel_double_exp_decay`

Defining file: `Zeta23/OPICAFollowup/ForwardLocalization.lean`. Source: R2-Q2.

For fixed orders d>=ell,k>=0, exists A,c>0 independent of t with |R_d,ell^(k)(t)|<=A exp(-c exp(t/(2(ell+1)))) for every t>=0; compact initial interval included.

### `Zeta23.OPICAFollowup.native_binomial_inverse_identity`

Defining file: `Zeta23/OPICAFollowup/BalancedCoefficients.lean`. Source: R2-Q3.

For r>=2 and each real Y>=1, v_Q=s_r+c_r for the actual small/large Mobius split and free integer convolutions; prove local finiteness and original field identity.

### `Zeta23.OPICAFollowup.balanced_coeff_divisor_bound`

Defining file: `Zeta23/OPICAFollowup/BalancedCoefficients.lean`. Source: R1-AT1, R2-Q3.

For ell=2r-1, |c_r(n)|<=d_ell(n) and |s_r(n)|<=(2^r-1)d_ell(n) for actual coefficients, retaining nonsquarefree total products.

### `Zeta23.OPICAFollowup.log_slack_native_decomposition`

Defining file: `Zeta23/OPICAFollowup/LogSlackBalance.lean`. Source: R2-Q3.

Fixed r>=2,d>=r-1,C>1,eta>=0,K>C+r eta+2r; Q(T) finite squarefree<=T^eta. With stated real Y,Z obtain exact F_d=E_T+B_T on [T-C log T,T], using actual signed tuples and physical product support.

### `Zeta23.OPICAFollowup.log_slack_typeI_error`

Defining file: `Zeta23/OPICAFollowup/LogSlackBalance.lean`. Source: R2-Q3.

Uniform eventual sup bound C1 T^(r eta) exp(T/2-c T^p), p=(K-C-r eta)/(2r)>1. Constants do not depend on future T or the allowed palette, whose full i log Q delay is paid.

### `Zeta23.OPICAFollowup.fixed_two_factor_preparation`

Defining file: `Zeta23/OPICAFollowup/LogSlackBalance.lean`. Source: R2-Q3.

Specialize r=2,d=1,C=2,Q=1,K=8: exp(T/2)T^-4<a,b<=exp(T/2-g)T^4 and sup error<=C1 exp(T/2-cT^(3/2)); source is Pj, not j.

### `Zeta23.OPICAFollowup.log_slack_both_low_masks_subexp`

Defining file: `Zeta23/OPICAFollowup/MaskedNativeRate.lean`. Source: R1-AT1, R2-Q3.

For fixed orders/palette budget, both unabsorbed and absorbed-kernel low-mask budgets have logarithm<=sqrt T+O(log T); prove measurable native masks and exact regrouping.

### `Zeta23.OPICAFollowup.log_slack_masked_energy_rate_difference`

Defining file: `Zeta23/OPICAFollowup/MaskedNativeRate.lean`. Source: R1-AT1, R2-Q3.

Difference of retained positive-part rate and full physical F_d window rate tends to zero; no claim yet identifying either with Theta.

### `Zeta23.OPICAFollowup.native_zero_count_summability`

Defining file: `Zeta23/OPICAFollowup/NativeExplicitFormula.lean`. Source: J5.2.

Bind zetaZeroConfig, not xi-prime zeros; derive weighted zero summability from actual zeta_local_zero_count, with analytic multiplicities and both imaginary signs.

### `Zeta23.OPICAFollowup.native_source_explicit_formula`

Defining file: `Zeta23/OPICAFollowup/NativeExplicitFormula.lean`. Source: J5.2.

For t>s0 prove actual F_d equals the stated absolutely convergent nontrivial and trivial-zero series; retain the canceled elementary term and all signs/source shifts.

### `Zeta23.OPICAFollowup.native_zero_sup_bounds`

Defining file: `Zeta23/OPICAFollowup/NativeExplicitFormula.lean`. Source: J5.2, MS1.

Define Theta as supremum of positive right displacements of actual nontrivial zeros, prove 0<=Theta<=1/2 and the correct supremum-selection property; no maximal zero.

### `Zeta23.OPICAFollowup.source_order_uniform_norms`

Defining file: `Zeta23/OPICAFollowup/UniformSourceBounds.lean`. Source: J5.2, MS1.

For d>=0 and k=0,1,2, norms of j_d^(k) and ||U_d||_2 are <=exp(C(d+1)log(d+2)) with source-fixed C; physical moments supply continuum cancellation.

### `Zeta23.OPICAFollowup.native_field_theta_envelope`

Defining file: `Zeta23/OPICAFollowup/UniformSourceBounds.lean`. Source: J5.2, MS1.

|F_d(t)|<=C_d exp(Theta t) for t>=0 and log(1+C_d)<=C(d+1)log(d+2); independently prove coefficients, trivial tail and finite initial interval bounds.

### `Zeta23.OPICAFollowup.aux_completion_actual_transform`

Defining file: `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`. Source: J5.2, MS1.

Prove the explicit beta-polynomial filter transforms to r_k=(z-1/2)/prod_{j=k+1}^{2k+2}(z+j+1/2), a_k=c_k*N and its true transform domain.

### `Zeta23.OPICAFollowup.aux_completion_uniform_decay`

Defining file: `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`. Source: J5.2, MS1.

For integer k>=1, |a_k(t)|<=A_k exp(-(k+1/2)t), A_k=2 zeta(k+1)(1+2^(3k+4))/(2pi)^(k+1); retain endpoint atom and prove summability.

### `Zeta23.OPICAFollowup.aux_completion_ratio_bounds`

Defining file: `Zeta23/OPICAFollowup/AuxiliaryCompletions.lean`. Source: J5.2, MS1.

For fixed actual nontrivial right coordinate p, ||c_k||_1<=2/(k+1)!, ||c_k||_1/|r_k(p)|<=exp(Cp(k+1)), |r_k(p)|/A_k>=exp(-k log(k+1)-Cp(k+1)); constants uniform in k.

### `Zeta23.OPICAFollowup.native_auxiliary_top_moment`

Defining file: `Zeta23/OPICAFollowup/MultiplicityTail.lean`. Source: J5.2, MS1.

Actual y_k,d=c_k*U_d has vanishing moments below zero multiplicity minus one and exact top unnormalized derivative (-1)^m r_k(p)J_d(p) zeta^(m)(rho).

### `Zeta23.OPICAFollowup.laguerre_tail_norm`

Defining file: `Zeta23/OPICAFollowup/MultiplicityTail.lean`. Source: J5.2, MS1.

Degree m-1 monic shifted Laguerre times exp(-conj(p)t) on [T,infinity) has norm exp(-delta T)(m-1)!/(2delta)^(m-1/2), with correct shift and conjugation.

### `Zeta23.OPICAFollowup.native_auxiliary_tail_residual_lower`

Defining file: `Zeta23/OPICAFollowup/MultiplicityTail.lean`. Source: J5.2, MS1.

Actual finite-truncation residual in L2 has tail norm >=D_rho,d |r_k(p)| exp(delta T), D=(2delta)^(m-1/2)|J_d(p)zeta^(m)(rho)|/(m-1)!.

### `Zeta23.OPICAFollowup.native_terminal_memory_lower`

Defining file: `Zeta23/OPICAFollowup/MultiplicityTail.lean`. Source: J5.2, MS1.

Prove exact A6 with positive part and ||y|| subtraction, without assuming global weighted L2 membership of the prime field.

### `Zeta23.OPICAFollowup.native_fixed_source_window_rate`

Defining file: `Zeta23/OPICAFollowup/NativeWindowRate.lean`. Source: J5.2.

For each fixed d>=0,C>1, Tendsto [log(1+integral_[T-C log T,T]|F_d|^2)/(2T)] atTop (nhds Theta), including the Theta=0 case and arbitrary zero multiplicity.

### `Zeta23.OPICAFollowup.native_slow_source_window_rate`

Defining file: `Zeta23/OPICAFollowup/MovingSourceWindowRate.lean`. Source: MS1.

For any real cofinal horizons T_n (positive eventually; normalize a finite prefix for HorizonSchedule) and integer d_n with d_n log(d_n+2)=o(T_n), fixed C>1, the actual F_d_n window energy rate tends to Theta; source factor both signs priced.

### `Zeta23.OPICAFollowup.complex_local_measure_embedding_faithful`

Defining file: `Zeta23/OPICAFollowup/ComplexLocalMeasures.lean`. Source: R1-CP1, R2-H1.

Construct faithful locally finite complex measures/distributions with positive total-variation control and show real parts yield P0 Jordan measures; prove local-TV convergence implies local test convergence and compatible tempered identity under growth.

### `Zeta23.OPICAFollowup.dilated_comb_fourier`

Defining file: `Zeta23/OPICAFollowup/DilatedComb.lean`. Source: R1-HT1, R1-CT1, R1-CP1.

F(D_t)=D_-t with coefficient exp(t/2) and heat convention exp(-2pi i x xi); establish actual Schwartz convergence and point-count bound.

### `Zeta23.OPICAFollowup.weighted_mixture_exists_fourier`

Defining file: `Zeta23/OPICAFollowup/WeightedMixing.lean`. Source: R1-HT1.

Under integral exp(a|t|) d|sigma|<infinity, a>1/2, construct actual locally finite linear-growth mixture and Fourier-reflection law, with its exact origin atom.

### `Zeta23.OPICAFollowup.weighted_mobius_inverse`

Defining file: `Zeta23/OPICAFollowup/WeightedMixing.lean`. Source: R1-HT1.

In the stated weighted measure algebra prove eta=N*sigma and sigma=M_mu*eta, using absolute Fubini; norm M_mu is zeta(a+1/2)/zeta(2a+1).

### `Zeta23.OPICAFollowup.weighted_mixture_sharp_gap`

Defining file: `Zeta23/OPICAFollowup/WeightedMixing.lean`. Source: R1-HT1.

Self-dual mixture with gap (-1,1) except possible origin is c*integerComb; zero origin forces zero. No positivity premise, but strict a>1/2 retained.

### `Zeta23.OPICAFollowup.weighted_gap_leakage`

Defining file: `Zeta23/OPICAFollowup/WeightedMixing.lean`. Source: R1-HT1.

Prove exact weighted variation leakage and continuous-density supremum counterpart, including endpoint b supremum distinct from a<b measure integrability.

### `Zeta23.OPICAFollowup.near_gap_mass_bound`

Defining file: `Zeta23/OPICAFollowup/NearGapLimits.lean`. Source: R1-HT2.

For gap a in (0,1], fixed R>=1,d in (0,1/2], positivity off Z and self-duality give mass E_R,d <=pi^2 R^2 (1-a)|nu|([-1,1])/(4d^2).

### `Zeta23.OPICAFollowup.near_gap_controlled_limit_zero`

Defining file: `Zeta23/OPICAFollowup/NearGapLimits.lean`. Source: R1-HT2.

With one common linear total-variation constant and a_n->1, all Schwartz pairings tend to zero; prove compact-limit extraction and uniform tails, not total-variation convergence.

### `Zeta23.OPICAFollowup.dilation_near_gap_family`

Defining file: `Zeta23/OPICAFollowup/NearGapLimits.lean`. Source: R1-CT1.

For 0<L<log2, nu_L=D_L+D_-L-2cosh(L/2)D0 is nonzero, even selfdual, origin0, gap e^-L and offlattice positive with the stated growth.

### `Zeta23.OPICAFollowup.dilation_normalized_limit_not_measure`

Defining file: `Zeta23/OPICAFollowup/NearGapLimits.lean`. Source: R1-CT1.

nu_L/L^2 converges on Schwartz tests to sum_n(n^2 delta_n_second -2n delta_n_first); limit nonzero and not order zero.

### `Zeta23.OPICAFollowup.renormalized_copoisson_tempered_family`

Defining file: `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`. Source: R1-CP1.

K_t=D_t+D_-t-exp(t/2)(delta0+dx), integral exp(-lambda t)K_t is an entire tempered-distribution-valued family, by actual cancellation on Schwartz tests.

### `Zeta23.OPICAFollowup.renormalized_copoisson_order_zero`

Defining file: `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`. Source: R1-CP1.

On 0<Re rho<1 prove cutoff local-TV convergence to rho^-1 delta0+[S_rho(|x|)+zeta(rho)|x|^(rho-1)+(1-rho)^-1]dx, including origin correction.

### `Zeta23.OPICAFollowup.zero_measure_exact_properties`

Defining file: `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`. Source: R1-CP1.

For actual nontrivial rho!=1/2, normalized complex measure has exact unit gap, origin0, even selfduality, linear variation and atom -1 at 1; its real part has the corresponding real properties.

### `Zeta23.OPICAFollowup.zero_measure_first_cell_sign`

Defining file: `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`. Source: R1-CP1.

Prove explicit first-cell negative value for |gamma|>3pi/(2log2), and both-sign conclusion for every nonzero real scalar projection at off-line zeros when |gamma|>2pi/log2; do not remove height/domain qualifiers.

### `Zeta23.OPICAFollowup.finite_sum_euler_maclaurin_uniform`

Defining file: `Zeta23/OPICAFollowup/ProfileEulerMaclaurin.lean`. Source: R2-S1a, R2-H1, F3.

Prove finite-sum expansion zeta(s)+x^(1-s)/(1-s)-B1({x})x^-s-s B2({x})x^(-s-1)/2+O_s(x^-Re(s)-2), locally uniformly in the required parameter domain; right integer endpoint retained.

### `Zeta23.OPICAFollowup.zero_profile_regular_selfdual`

Defining file: `Zeta23/OPICAFollowup/ZeroProfiles.lean`. Source: R2-S1a.

h is even continuous, L1 and L2, equals1 on [-1,1], Fourier-self-dual, with integral on positive halfline1/2; actual zeta zero and functional equation used.

### `Zeta23.OPICAFollowup.zero_profile_tail_and_jumps`

Defining file: `Zeta23/OPICAFollowup/ZeroProfiles.lean`. Source: R2-S1a.

h= kappa B2({x})/(2x^2)+O_rho(x^-3), exact differentiated finite sums imply h'=O(x^-2) between integers and h'(n+)-h'(n-)=-kappa/n^2; xh' belongs L2.

### `Zeta23.OPICAFollowup.log_unitary_form_identity`

Defining file: `Zeta23/OPICAFollowup/LogFourierSobolev.lean`. Source: R2-S1b, F1, F2, F3.

For the stated actual form domain, integral x^2|h'|^2 = integral |psi'|^2+(1/4)integral |h|^2 with psi=exp(t/2)h(exp t); prove unitary L2 conversion and weak derivative statement.

### `Zeta23.OPICAFollowup.log_fourier_plancherel`

Defining file: `Zeta23/OPICAFollowup/LogFourierSobolev.lean`. Source: F1, F2.

Establish exp(-i xi t) convention and Plancherel factor1/(2pi), differentiation and continuous H^-1,H^1 pairings used by the actual force.

### `Zeta23.OPICAFollowup.zero_profile_forced_euler`

Defining file: `Zeta23/OPICAFollowup/ForcedEuler.lean`. Source: R2-S1b.

On positive axis, -(x^2h')'=kappa(h-1+sum positive_integer_delta) in distributions; actual jumps produce atoms and no delta derivative.

### `Zeta23.OPICAFollowup.zero_profile_not_homogeneous_operator_vector`

Defining file: `Zeta23/OPICAFollowup/ForcedEuler.lean`. Source: R2-S1b.

Actual nonzero atoms prevent its distributional Euler image being an L2 function and hence prevent using the homogeneous self-adjoint eigenvalue inference; form identity retained.

### `Zeta23.OPICAFollowup.native_sampling_gram_identity`

Defining file: `Zeta23/OPICAFollowup/SamplingCompatibility.lean`. Source: R2-S2.

Qij=kappa_i(Nij+conj bj)=conj kappa_j(Nij+bi) after proving all sample sums, integrals and boundary limits; retain linear-first pairing convention explicitly translated to Lean.

### `Zeta23.OPICAFollowup.native_sampling_form_positive`

Defining file: `Zeta23/OPICAFollowup/SamplingCompatibility.lean`. Source: R2-S2.

N,Q and Q-N/4 are PSD for any finite actual profiles; divided-difference identity only when denominator nonzero; undivided version retained at conjugate coincidence.

### `Zeta23.OPICAFollowup.copoisson_zero_jets_measures`

Defining file: `Zeta23/OPICAFollowup/CoPoissonJets.lean`. Source: R2-H1.

For derivative index k<multiplicity(rho), normalized kappa jets retain genuine local measures, gap/origin, even selfduality and linear variation; prove parameter limits and differentiated forced chain.

### `Zeta23.OPICAFollowup.profile_jet_confluent_determinant`

Defining file: `Zeta23/OPICAFollowup/ConfluentProfiles.lean`. Source: R2-H2a.

For distinct nonzero kappa_j and multiplicities m_j, determinant=(-1)^(M(M-1)/2)*prod kappa_j^m_j*prod_{i<j}(kappa_j-kappa_i)^(m_i*m_j), with normalized jets.

### `Zeta23.OPICAFollowup.finite_zero_jet_independent`

Defining file: `Zeta23/OPICAFollowup/ConfluentProfiles.lean`. Source: R2-H2a.

Independence of the actual finite jet measures follows from their first-cell matrix; do not count reflected rho and1-rho as different kappa nodes.

### `Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero`

Defining file: `Zeta23/OPICAFollowup/FiniteSpanSeparation.lean`. Source: R2-H2b.

Any real finite combination nonnegative off Z is zero, and on an independent real basis all coefficients are zero; this does not classify arbitrary infinite/nonlinear families.

### `Zeta23.OPICAFollowup.fixed_basis_negative_mass_budget`

Defining file: `Zeta23/OPICAFollowup/FiniteSpanSeparation.lean`. Source: R2-H2b.

For each fixed independent real basis exists c_basis>0 such that global sinc-weighted negative mass >=c_basis*coefficient Euclidean norm; no uniform collision/growing-set constant.

### `Zeta23.OPICAFollowup.first_cell_negative_mass_cost`

Defining file: `Zeta23/OPICAFollowup/FirstCellCost.lean`. Source: R2-H3.

For |delta|<1/2,|gamma|>=16 on u in [4pi/(3|gamma|),5pi/(3|gamma|)], density<=-|gamma|exp(-u/2)/2; negative mass>=pi/6 and sinc-weighted mass>=8pi/(27gamma^2).

### `Zeta23.OPICAFollowup.square_fourier_defect`

Defining file: `Zeta23/OPICAFollowup/SquareDefect.lean`. Source: R2-S3.

For even continuous selfdual nonzero h in L1 intersect L2, h=A on[-1,1] and tending0, tau=|A-h|^2 dx-|A|^2 comb_nonzero has defect (h*conj h-|h|^2)dx and exact gap/sign/origin.

### `Zeta23.OPICAFollowup.square_defect_origin_positive`

Defining file: `Zeta23/OPICAFollowup/SquareDefect.lean`. Source: R2-S3.

The continuous C0 defect has value ||h||_2^2-|A|^2>0, including A=0 when h!=0; retain complex conjugation.

### `Zeta23.OPICAFollowup.square_no_lattice_repair`

Defining file: `Zeta23/OPICAFollowup/SquareDefect.lean`. Source: R2-S3.

No tempered lattice-supported order-zero correction can make tau selfdual; prove periodicity/atomic-versus-continuous argument, not an assumed absence of corrections.

### `Zeta23.OPICAFollowup.square_selfdual_projection_fills_gap`

Defining file: `Zeta23/OPICAFollowup/SquareDefect.lean`. Source: R2-S3.

(tau+F tau)/2 is selfdual but has strictly positive density on a nonempty interval about0 inside the old gap.

### `Zeta23.OPICAFollowup.sawtooth_integrable_force_identity`

Defining file: `Zeta23/OPICAFollowup/SawtoothForce.lean`. Source: F1.

w=exp(-t/2){exp t} is L1 intersect L2; g=-(D+1/2)w is tempered and equals N-exp(t/2)dt only as the initially compact-test difference; n=1 jump retained.

### `Zeta23.OPICAFollowup.sawtooth_actual_mellin_fourier`

Defining file: `Zeta23/OPICAFollowup/SawtoothForce.lean`. Source: F1.

For0<Re s<1 derive integral_0^infinity {x}x^(-s-1)=-zeta(s)/s; hence Flog(w)=-zeta(.5+i xi)/(.5+i xi), Flog(g)=zeta(.5+i xi).

### `Zeta23.OPICAFollowup.sawtooth_norm_weighted_zeta_moment`

Defining file: `Zeta23/OPICAFollowup/SawtoothForce.lean`. Source: F1.

Prove exact finite integer-cell norm identity and limit ||w||_2^2=log(2pi)-EulerGamma=(1/2pi)integral |zeta(.5+i xi)|^2/(xi^2+1/4); conclude g in H^-1.

### `Zeta23.OPICAFollowup.arithmetic_stieltjes_holomorphic`

Defining file: `Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean`. Source: F2.

For kappa outside[1/4,infinity), M=integral d omega/(a-kappa) is locally absolutely convergent and holomorphic, a=xi^2+1/4 and d omega=|zeta(.5+i xi)|^2 dxi/(2pi).

### `Zeta23.OPICAFollowup.arithmetic_stieltjes_sign_budget`

Defining file: `Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean`. Source: F2.

For Im kappa!=0, Im M/Im kappa=integral d omega/|a-kappa|^2>0 and explicit weighted-source bounds; no real-sample assertion.

### `Zeta23.OPICAFollowup.native_forced_resolvent_unique`

Defining file: `Zeta23/OPICAFollowup/NativeResolvent.lean`. Source: F2.

For actual off-line zero kappa nonreal, psi=exp(t/2)h(exp t) is the unique H1 solution (-(D^2)+1/4-kappa)psi=kappa g; actual Fourier quotient kappa zeta(.5+i xi)/(a-kappa).

### `Zeta23.OPICAFollowup.native_sample_stieltjes_identity`

Defining file: `Zeta23/OPICAFollowup/NativeResolvent.lean`. Source: F2.

Justify sample b_kappa=sum h(n)-1/2 as H^-1,H1 pairing, then prove b=kappa M(kappa), with all endpoint terms, normalization and conjugation.

### `Zeta23.OPICAFollowup.native_profile_spectral_norms`

Defining file: `Zeta23/OPICAFollowup/NativeResolvent.lean`. Source: F2.

Norm and Euler form equal |kappa|^2 integrals d omega/|a-kappa|^2 and a d omega/|a-kappa|^2. Include mixed compatibility and |b|<=|kappa|(1+|kappa|/|Im kappa|)(log(2pi)-EulerGamma).

### `Zeta23.OPICAFollowup.generic_forced_profile_unique`

Defining file: `Zeta23/OPICAFollowup/BoundaryAmplitude.lean`. Source: F3.

For 1/2<Re rho<1, Im rho!=0, htilde=1-Srho/brho-zeta(rho)x^(rho-1)/brho lies in the log form domain and uniquely solves the actual force equation; both ends controlled.

### `Zeta23.OPICAFollowup.generic_boundary_amplitude`

Defining file: `Zeta23/OPICAFollowup/BoundaryAmplitude.lean`. Source: F3.

On(0,1), htilde=1-zeta(rho)x^(rho-1)/brho; plateau iff zeta(rho)=0. At infinity the retained homogeneous term is -zeta(1-rho)x^-rho/brho plus the Bernoulli tail; no L1 assertion for generic rho.

### `Zeta23.OPICAFollowup.coupled_gram_collision_control`

Defining file: `Zeta23/OPICAFollowup/Counterexamples.lean`. Source: R1-MC1.

Exact two-exponential rational inner model has coupled cost (2-h^2)/(1-h^2) for0<h<1 and limit2 as h tends to0 from above although its Gram inverse becomes singular.

### `Zeta23.OPICAFollowup.norm_first_strictly_weaker_control`

Defining file: `Zeta23/OPICAFollowup/Counterexamples.lean`. Source: R1-AT1.

Constant B_n=exp(theta*T_n),S_n=1 has equal energy rate theta but positive-rate raw energy difference; theta>0.

### `Zeta23.OPICAFollowup.history_recovery_cost_control`

Defining file: `Zeta23/OPICAFollowup/Counterexamples.lean`. Source: R2-O2.

Rank-one target with history scale epsilon!=0 has minimum recovery norm1/|epsilon|; epsilon=exp(-aT) yields exponential cost.

### `Zeta23.OPICAFollowup.forced_positive_gram_nonreal_control`

Defining file: `Zeta23/OPICAFollowup/Counterexamples.lean`. Source: R2-S2.

Positive diagonal A and real forcing g with h_i=kappa_i(A-kappa_i I)^-1g yield the same coupled Gram identities at specified nonreal parameters; prove positivity as applicable, not actual-zero existence.

### `Zeta23.OPICAFollowup.fixed_two_factor_mask_rate_theta`

Defining file: `Zeta23/OPICAFollowup/Consumers.lean`. Source: R2-Q3, J5.2.

On the fixed actual r2,d1,C2,Q1,K8 construction, both high-mask realizations have positive-part rate exactly Theta by proved native J5.2 plus the two-mask norm-first interface.

### `Zeta23.OPICAFollowup.quiet_balanced_observation_implies_native_cut`

Defining file: `Zeta23/OPICAFollowup/Consumers.lean`. Source: R2-Q3, J5.2.

Explicitly conditional: a proved cofinal zero-rate upper for this complete actual observation implies Theta=0 and literal d0 all-positive-damping L2 (then consumes existing Step4 cut). Preserve the upper as an open antecedent, never an unconditional RH root.

### `Zeta23.OPICAFollowup.step123_word_jet_consumer`

Defining file: `Zeta23/OPICAFollowup/Consumers.lean`. Source: R1-NB1, R2-J1.

For the existing same Step123CompleteOutput, construct actual original field/pole and full native word observation, preserving source, zero, multiplicity, damping and correction identities; optional contour premise explicit.

### `Zeta23.OPICAFollowup.actual_zero_measure_span_consumer`

Defining file: `Zeta23/OPICAFollowup/Consumers.lean`. Source: R1-CP1, R2-H1, R2-H2b.

Instantiate true zero profile/jet objects and all P0 separator premises on each actual finite real combination; derive the finite-span exclusion without assuming measure status.

### `Zeta23.OPICAFollowup.actual_force_sampling_consumer`

Defining file: `Zeta23/OPICAFollowup/Consumers.lean`. Source: R2-S1b, F1, F2, F3.

Compose actual lattice force, log-unitary profile, spectral density, sample identity and generic boundary amplitude with the two Fourier conventions explicitly related. No homogeneous eigenproblem conclusion.


## Appendix C. Source links and reproducibility

Primary implementation source: https://github.com/HMarcusWH/zeta-23-lean/pull/293 . Every live file reference used for this spec is pinned to `553b4263b58d9fec178320de251ff299a0bd702a`, not moving main. The intake JSON identifies selected fetched blobs and review scope. The successful current PR formal job's source identity is retained separately from the uncompleted full parent harvest.

Final controlling paper: https://drive.google.com/file/d/1maOApH-lKrmHZgzh85Gq3RTc5Ot9WFwW/view . Final ledger: https://drive.google.com/file/d/1LincoDfkmwMWXrHlfYKyZXB6GtaKpoxh/view . Final paper contract: https://drive.google.com/file/d/1vViEEmJaLUYZAoL5OrEPQeOzkepZtUhS/view . Their mounted bytes and hashes are bound in the specification package. The destination used by earlier sessions is https://drive.google.com/drive/folders/1FwRkN6sbJ4_Fhrqe53wpsJtByD2RXILb . Earlier readback receipts certify earlier uploads only.

The included structural validation script checks this proposal's path/DAG/coverage/source consistency, not Lean proof correctness or a successful future PR. The package contains a specification generator, frozen selected mathematical inputs, preserved source navigation evidence, and a release digest manifest. It deliberately does not contain invented Lean proofs or counterfeit compiler outputs.

