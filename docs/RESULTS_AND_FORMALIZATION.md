# Results, manuscripts and formalization

This guide connects the mathematical outputs to their written statements and Lean sources. Start with the [project guide](PROJECT_GUIDE.md) for the argument, the [reuse catalogue](REUSABLE_COMPONENTS.md) for components, or the [paper reading routes](../papers/README.md#reading-guide) for prerequisites.

**Source baseline:** [7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9](https://github.com/HMarcusWH/zeta-23-lean/commit/7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9), the 21 November 2026 research archive. Relative Lean links below refer to those retained mathematical sources. Documentation descendants do not supply new theorem evidence. The [frozen current state](CURRENT_STATE.md) separates the source tree from historical compiler receipts.

The map covers **all 43 archived manuscripts**, with representative result-level mappings rather than a claim that every proposition in each PDF was formalized. A01–A43 refer to the row numbers in the original [archive inventory](../papers/README.md#all-pdfs-in-this-snapshot); they are not the author's Roman paper numbers. The groups below follow mathematical prerequisites, not upload order.

## How to read the evidence

A declaration link establishes where to inspect a statement and its proof term. It does not by itself establish a successful fresh compilation, independent mathematical review, or priority. This documentation pass checked the archived PDF identities, manuscript statement locations, representative identifiers and the cited consumer or axiom-audit source surfaces. It did not recompile the entire research development or individually rebind all historical receipts to the archive commit.

**PDF page numbers are one-based file pages.** Each manuscript checkpoint is the historical source revision cited by that paper; the relative consumer links navigate the retained archive source. The entry identifies whether that surface is an independently stated consumer, a downstream theorem, an anonymous example or an explicit type/axiom audit. A matching historical source-file blob does not rebind its transitive dependencies or establish a fresh compiler receipt.

| Dimension | What to record and inspect |
| --- | --- |
| Mathematical role | Abstract theorem, source-specific theorem, conditional implication, equivalence, paper composition, finite certificate, counterexample or open premise |
| Formalization relation | Exact named endpoint, multiple formal ingredients, paper-only integration, or portion not yet mapped in this guide |
| Source identity | The exact full declaration type, namespace, imports and immutable revision |
| Verification evidence | Compiler version, source-bound consumer and axiom checks, command outcome and the checkpoint to which they apply |
| Evidence availability | In-tree consumer/ledger, retained archive, externally referenced receipt, or not located |
| Reuse boundary | The domain, source, metric, normalization, quantifiers and additional premises a new application must provide |

A conditional implication may be fully proved while its antecedent is open. Conversely, a theorem proved in a paper may lack a matching Lean declaration. These are different questions. The scope notes below summarize the main assumptions; they never replace the complete source types.

### Formal-source and consumer entry points

| Family | Source/consumer navigation | Evidence boundary |
| --- | --- | --- |
| Early finite dictionary and detectors | [CCM facade](../Zeta23/CCM.lean), [ExceptionalZero facade](../Zeta23/ExceptionalZero.lean), [theorem/claim map](../research/RHRC/graph/generated/THEOREM_CLAIM_MAP.json) | Historical facades and registries have their own scope; no one facade is a receipt for every later result. |
| Native follow-up | [Source validation consumers](../Zeta23/OPICAFollowup/Validation.lean), [continuation ledger](../research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md) | The 100-root original contract and narrower continuation gates remain distinct. |
| Round 2 | [Validation modules](../Zeta23/OPICARound2/Validation), [package guide](../research/RHRC/integration/opica_round2/README.md) | Use the consumer for the selected result. The production facade and broader import surface differ. |
| Round 3 | [Validation modules](../Zeta23/OPICARound3/Validation), [package guide](../research/RHRC/integration/opica_round3/README.md) | A same-cutoff or first-birth consumer preserves hypotheses; it does not prove an independent sign bound. |
| Round 4 | [Validation modules](../Zeta23/OPICARound4/Validation), [root inventory](../research/RHRC/integration/opica_round4/ROOTS.json), [closure obligations](../research/RHRC/integration/opica_round4/CLOSURE_OBLIGATIONS.json) | Named support roots, local checks and full governed acceptance are separate evidence surfaces. |
| Arithmetic frontier and successors | [Current frontier guide](../research/RHRC/integration/opica_round4/arithmetic_frontier/README.md), [original build contract](../research/RHRC/integration/opica_round4/arithmetic_frontier/BUILD_SPEC.md), [Round 6 guide](../research/RHRC/integration/opica_round6/README.md), [Verify](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean) | The later finite Lean package does not automatically formalize every growing-horizon paper transfer. |

See [reproducibility](REPRODUCIBILITY.md) for actual commands and [citation](REPRODUCIBILITY.md#citation) for paper-versus-code citation examples. The metadata [manifest](../papers/MANIFEST_2026-11-21.json) identifies PDF bytes and provenance; it is not a proof-status registry.

## Find a result

| Mathematical task | Manuscripts and results | Reuse or tutorial |
| --- | --- | --- |
| Construct a finite negative witness and an exact dictionary | A43, A39, A42, A41, A40 | [Gram witness](EXAMPLES.md#gram-witness), [finite algebra](REUSABLE_COMPONENTS.md#finite-algebra-and-certificates) |
| Follow first-bad shells, true grounds and prime seams | A38, A37, A36, A35, A34, A33, A29, A32, A30, A31, A28, A27, A26, A25 | [Singular Schur example](EXAMPLES.md#singular-schur), [spectral tools](REUSABLE_COMPONENTS.md#spectral-and-local-analytic-tools) |
| Understand signed Fourier gaps and co-Poisson obstructions | A24, A22, A23, A20, A19, A16, A15 | [Harmonic tools](REUSABLE_COMPONENTS.md#harmonic-analysis-and-causal-approximation) |
| Work with the native causal source, Grams and approximation | A21, A18, A17, A14, A13, A12, A11, A10 | [Raw/filtered example](EXAMPLES.md#raw-filtered) |
| Follow the joint-source and late spectral synthesis | A09, A02, A03, A08, A07, A06, A05, A04, A01 | [Step 1–3 packet](EXAMPLES.md#step123-packet) |
| Read the final November arithmetic work | [Later source and research records](#later-source-and-research-records) | [Stopping tree](EXAMPLES.md#stopping-tree) |

## Finite detection and exact dictionaries

### A43

**[Explicit Gram witnesses](../papers/2026-11-21/Explicit_Gram_Witnesses_Off_Critical_Pair_Blocks_2026-08-25_v1_2_PROOFREAD.pdf).** For a positive signed pair block and two real vectors with nonzero Gram determinant, a denominator-free transverse vector has exactly negative energy.

**Representative source:** [`dotProduct_pairBlock_orthoWitness`](../Zeta23/ExceptionalZero/ProbeGramNegativity.lean) in namespace `Zeta23.ExceptionalZero`.

**Mapping:** Core exact identity and strict-negativity declaration; normalized margin, inertia and masking refinements remain paper-level consequences at the manuscript pin.

**Boundary:** This certifies one pair block. A positive background can mask that direction in the complete form.

**Manuscript location:** Theorem 2.5 and equation (2.1), PDF p. 3.

**Consumer / audit and checkpoint:** [`dotProduct_pairBlock_orthoWitness_neg`](../Zeta23/ExceptionalZero/ProbeGramNegativity.lean) (same-file downstream theorem; no separate independent consumer mapped here). Historical manuscript source: [`a47095149377`](https://github.com/HMarcusWH/zeta-23-lean/commit/a47095149377aeec01a0335945fcdcde311f0444); §9, PDF p. 9.

### A39

**[Complete two-translate detectors](../papers/2026-11-21/Complete_Two_Translate_Detectors_Theorem_Core_v0_3_PROOFREAD.pdf).** Every hypothetical off-critical zero eventually produces determinant failures along the explicit countable radius bank, with the aperture allowed to depend on its index.

**Representative source:** [`eventually_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero`](../Zeta23/ExceptionalZero/TwoTranslateCountableCriterion.lean) in namespace `Zeta23.ExceptionalZero`.

**Mapping:** Named tail-detection declaration; the same module records the countable-bank critical-line equivalence. Other statements require their individual source maps.

**Boundary:** Universal determinant nonnegativity remains a premise; countability does not prove it.

**Manuscript location:** Theorem 7.4 and its quantifier boundary in Remark 7.5, PDF p. 10; the countable-bank equivalence is Theorem 7.9 on that page.

**Consumer / audit and checkpoint:** [`eventually_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero`](../Zeta23/ExceptionalZero/TwoTranslateCountableCriterion.lean) (same-file #print axioms audit). Historical manuscript source: [`5e19483c905c`](https://github.com/HMarcusWH/zeta-23-lean/commit/5e19483c905c07cfe9fef0a97f834004e77b5fb9); §10 and the visible archival verification record, PDF pp. 11–12. Use the visible archival record, which supersedes the older PR #54 draft note retained in the text layer.

### A42

**[Scalar-defect reduction](../papers/2026-11-21/Scalar_Defect_Reduction_Finite_Weil_CCM_Dictionaries_2026-08-30_v0_1_PROOFREAD.pdf).** Agreement on the specified smooth core and diagonal rigidity reduce the finite dictionary discrepancy to the scalar tent defect times the all-ones matrix.

**Representative source:** [`zeroSideDiscrepancy_eq_tentDefect_smul_ones`](../Zeta23/CCM/DictionaryZeroSideTentDefect.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named source-specific reduction; tent mollification and final equality are separate declarations upstream of the dictionary bridge.

**Boundary:** The generic rank-at-most-two completion is a separate reusable theorem. A matrix identity supplies no positivity.

**Manuscript location:** Theorem 5.2 and equations (5.3)–(5.4), PDF p. 7.

**Consumer / audit and checkpoint:** [`zeroSideDiscrepancy_eq_tentDefect_smul_ones`](../Zeta23/CCM/DictionaryZeroSideTentDefect.lean) (same-file #print axioms audit). Historical manuscript source: [`317958bb495e`](https://github.com/HMarcusWH/zeta-23-lean/commit/317958bb495e2fe603c047480342d24fb0932519); §8, PDF pp. 9–10.

### A41

**[Exact normalization reconciliation](../papers/2026-11-21/Exact_Normalization_Reconciliation_Finite_Weil_CCM_2026-08-31_v0_1_PROOFREAD.pdf).** The direct-source canonical matrix differs from the literal later printed normalization by the specified scalar identity correction.

**Representative source:** [`canonicalSourceMatrix_eq_legacyPrintedMatrix_add_correction`](../Zeta23/CCM/SourceNormalizationRepair.lean) in namespace `Zeta23.CCM`.

**Mapping:** Exact source equality; the paper separately labels the closed calculus discrepancy as a manuscript calculation at its pin.

**Boundary:** The identity-matrix correction is not the rank-one all-ones defect in A42. Absolute eigenvalues depend on the normalization.

**Manuscript location:** Theorem 5.2 and equation (5.6), PDF p. 5.

**Consumer / audit and checkpoint:** [`canonicalSourceMatrix_eq_legacyPrintedMatrix_add_correction`](../Zeta23/CCM/SourceNormalizationRepair.lean) (same-file #print axioms audit). Historical manuscript source: [`54077e55f75b`](https://github.com/HMarcusWH/zeta-23-lean/commit/54077e55f75bf6bf556a1cfd3f92fc4259db50e6); §9, PDF p. 9.

### A40

**[Persistent finite detection](../papers/2026-11-21/Persistent_Finite_Detection_Off_Critical_Zeros_Weil_CCM_2026-09-03_v0_2.pdf).** A hypothetical off-critical zero forces a nonzero boundary-flat finite vector with negative canonical energy; centered extension preserves its value.

**Representative source:** [`exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero`](../Zeta23/ExceptionalZero/FiniteNegativeObstruction.lean) in namespace `Zeta23.ExceptionalZero`.

**Mapping:** Named finite-detection declaration; persistence uses NestedFinite and NestedEuclideanObstruction. The paper distinguishes the core from its composed RH-equivalent criterion.

**Boundary:** Three moment constraints and the common support/approximation topology are essential. This is conditional detection, not positivity.

**Manuscript location:** Theorem 6.3, PDF pp. 9–10; the composed persistence theorem is Theorem 9.1, PDF pp. 11–12.

**Consumer / audit and checkpoint:** [`exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero`](../Zeta23/ExceptionalZero/FiniteNegativeObstruction.lean) (same-file #print axioms audit). Historical manuscript source: [`c7129b1856ea`](https://github.com/HMarcusWH/zeta-23-lean/commit/c7129b1856ea03cdf8b831ae1424140f8a7d90a9); §11, PDF pp. 15–17.

## Spectral geometry and aperture calculus

### A38

**[First-bad cubic rigidity](../papers/2026-11-21/First_Bad_Cubic_Rigidity_Weil_CCM_2026-09-08_v0_2.pdf).** At the actual globally first bad cutoff, a one-dimensional intrinsic shell carries the obstruction and an exact cubic secular equation characterizes its negative eigenvalue.

**Representative source:** [`cubicSecularScalar_eq_zero_iff_exists_eigenmode`](../Zeta23/CCM/CubicSecularEquation.lean) in namespace `Zeta23.CCM`.

**Mapping:** Representative secular equivalence; the counterexample-to-first-bad producer is in GlobalFirstBadRigidity. The rest of the paper has its own module crosswalk.

**Boundary:** Predecessor nonnegativity and a safe negative shift are retained. The negative root is characterized, not excluded.

**Manuscript location:** Theorem 5.4, especially equivalence (47), PDF p. 10.

**Consumer / audit and checkpoint:** [`cubicSecularScalar_eq_zero_iff_exists_eigenmode`](../Zeta23/CCM/CubicSecularEquation.lean) (same-file #print axioms audit). Historical manuscript source: [`e1192857afed`](https://github.com/HMarcusWH/zeta-23-lean/commit/e1192857afed9f68fa4a13143ce690b62191b997); §12, PDF pp. 18–20.

### A37

**[Zero-shift source rigidity](../papers/2026-11-21/Zero_Shift_Source_Rigidity_Weil_CCM_2026-09-10_v0_3.pdf).** With the stated zero-shift preimages, the cross-parity coefficient times the production source vanishes on every even predecessor-kernel vector.

**Representative source:** [`crossParityZeroShiftGamma_mul_explicitSource_eq_zero_on_evenKernel`](../Zeta23/CCM/ZeroShiftCrossParityTransfer.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named denominator-free kernel/source identity.

**Boundary:** Solvability and a nonzero transfer coefficient are not automatic. Substituting zero into a singular resolvent is not licensed.

**Manuscript location:** Theorem 7.1 and equation (61), PDF p. 13.

**Consumer / audit and checkpoint:** [`crossParityZeroShiftGamma_mul_explicitSource_eq_zero_on_evenKernel`](../Zeta23/CCM/ZeroShiftCrossParityTransfer.lean) (same-file #print axioms audit). Historical manuscript source: [`753ee53a7fc0`](https://github.com/HMarcusWH/zeta-23-lean/commit/753ee53a7fc08bd3be9a5a0f37417629122395f9); §12, PDF pp. 17–19.

### A36

**[Log-cover determinant rigidity](../papers/2026-11-21/Log_Cover_Determinant_Rigidity_Weil_CCM_2026-09-12_v0_6.pdf).** Within a fixed prime-cutoff cell, dense predecessor regularity and retained first-bad ancestry produce a regular negative-energy certificate.

**Representative source:** [`exists_regular_cellMinimal_negativeCanonicalEnergyCertificate`](../Zeta23/CCM/RegularFirstBadCanonicalEnergy.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named certificate constructor; analytic deck-shift and discrepancy identities are separate ingredients.

**Boundary:** Selecting a new regular aperture needs witness persistence. No opposing canonical energy sign follows.

**Manuscript location:** Theorem 11.2, PDF p. 17; the additional off-critical-zero input is Theorem 12.2, PDF p. 18.

**Consumer / audit and checkpoint:** [`exists_regular_cellMinimal_negativeCanonicalEnergyCertificate`](../Zeta23/CCM/RegularFirstBadCanonicalEnergy.lean) (same-file #print axioms audit). Historical manuscript source: [`b6622dadab91`](https://github.com/HMarcusWH/zeta-23-lean/commit/b6622dadab911008c0a7238e9dc711c6f9946302); §15, PDF pp. 21–22. The archive refactors this endpoint through the stronger retained-first-bad constructor; do not transfer the old whole-file receipt to the changed blob.

### A35

**[Moment-jet rigidity](../papers/2026-11-21/Moment_Jet_Rigidity_Weil_CCM_2026-09-19_v0_2.pdf).** Vanishing lower centered moments determines the first surviving odd endpoint jet of the exact source energy.

**Representative source:** [`iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix`](../Zeta23/CCM/CanonicalSourceMomentJets.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named moment/jet identity; Riesz recurrences and the off-critical negative Riesz certificate are further mapped results.

**Boundary:** Endpoint terms must be retained. No independent sign for the arithmetic Riesz endpoint scalar is supplied.

**Manuscript location:** Theorem 4.1 and equation (40), PDF p. 9.

**Consumer / audit and checkpoint:** [`iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix`](../Zeta23/CCM/CanonicalSourceMomentJets.lean) (same-file #print axioms audit). Historical manuscript source: [`b418ff034428`](https://github.com/HMarcusWH/zeta-23-lean/commit/b418ff034428f92594bab0e5b8276181a086ee4b); §10, PDF pp. 18–19.

### A34

**[Cross-parity source-secular rigidity](../papers/2026-11-21/Cross_Parity_Source_Secular_Rigidity_Weil_CCM_2026-09-19_v0_2.pdf).** At a retained even negative root with the specified odd-good hypotheses, the completed odd secular response retains the full source and shifted resolvent cost.

**Representative source:** [`star_cubicSecularScalar_odd_mul_shellInner_eq_source_completion_of_even_root`](../Zeta23/CCM/CrossParitySecularCompletion.lean) in namespace `Zeta23.CCM`.

**Mapping:** Representative exact completion identity; inequalities consume the branch hypotheses separately.

**Boundary:** Two lower-cost inequalities combine by their maximum, not their sum. Resonant and other parity branches remain visible.

**Manuscript location:** Theorem 6.5 and equation (69), PDF p. 13; the odd-good budget is the additional Theorem 7.1 on that page.

**Consumer / audit and checkpoint:** [`star_cubicSecularScalar_odd_mul_shellInner_eq_source_completion_of_even_root`](../Zeta23/CCM/CrossParitySecularCompletion.lean) (same-file #print axioms audit). Historical manuscript source: [`b6c90fc29e6b`](https://github.com/HMarcusWH/zeta-23-lean/commit/b6c90fc29e6ba372efb02d12c7998d3b0c7dac5d); §13, PDF pp. 18–19.

### A33

**[One-coefficient cross-parity rigidity](../papers/2026-11-21/One_Coefficient_Cross_Parity_Rigidity_Weil_CCM_2026-09-23_FINAL.pdf).** The two cubic correction directions are collinear, forcing the exact affine relation between the transfer coefficients.

**Representative source:** [`six_mul_crossParitySecularGamma_add_index_mul_alpha`](../Zeta23/CCM/CrossParitySecularCorrectionCollapse.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named relation 6Γ+(2N−1)α=2N+5; source-coupling and zero-shift variants are separate declarations.

**Boundary:** One free coefficient does not give its sign or exclude the negative root.

**Manuscript location:** Theorem 5.2 and equations (44)–(45), PDF pp. 10–11.

**Consumer / audit and checkpoint:** [`six_mul_crossParitySecularGamma_add_index_mul_alpha`](../Zeta23/CCM/CrossParitySecularCorrectionCollapse.lean) (same-file #print axioms audit). Historical manuscript source: [`f9623be70595`](https://github.com/HMarcusWH/zeta-23-lean/commit/f9623be705955bd98ef563aa75d3244712009cac); §13, PDF pp. 18–20.

### A29

**[Retained real Gamma escape](../papers/2026-11-21/Retained_Real_Cross_Parity_Gamma_Escape_Weil_CCM_2026-09-24_v0_2_PROOFREAD.pdf).** On the selected-even/odd-good branch, a negative real transfer coefficient forces escape beyond the canonical shell-radius barrier.

**Representative source:** [`RegularCellMinimalNegativeEnergyCertificate.retainedGamma_neg_implies_shellCenter_sq_lt_sharpRadius`](../Zeta23/CCM/RegularFirstBadGammaObstruction.lean) in namespace `Zeta23.CCM`.

**Mapping:** Representative named retained-state implication; the complete deficit dichotomy uses the other statements in the same module.

**Boundary:** The positive-deficit and radius/sign hypotheses needed for exclusion are not proved by this implication.

**Manuscript location:** Theorem 12.2, PDF p. 11; the combined escape dichotomy is Theorem 12.4, PDF p. 12.

**Consumer / audit and checkpoint:** [`RegularCellMinimalNegativeEnergyCertificate.retainedGamma_neg_implies_shellCenter_sq_lt_sharpRadius`](../Zeta23/CCM/RegularFirstBadGammaObstruction.lean) (same-file #print axioms audit). Historical manuscript source: [`afc0f2d89fce`](https://github.com/HMarcusWH/zeta-23-lean/commit/afc0f2d89fce9f216053b75e45efb76bc61b00c2); §15, PDF pp. 13–15.

### A32

**[True-ground source arithmetic](../papers/2026-11-21/True_Ground_Source_Arithmetic_Rigidity_Weil_CCM_2026-09-26_v0_2_PROOFREAD.pdf).** The prime-remainder energy is the exact weighted integral for the same true-ground residual state, rather than a separately chosen vector.

**Representative source:** [`GlobalBottomResidualState.primeRemainderEnergy_eq_weight_integral`](../Zeta23/CCM/GlobalParityBottomPrimeWeight.lean) in namespace `Zeta23.CCM`.

**Mapping:** Representative same-state arithmetic identity; ground attainment, trichotomy and endpoint-jet results are separately mapped in the paper.

**Boundary:** A sign for a few endpoint derivatives is not a global sign for the selected arithmetic weight.

**Manuscript location:** Definition 9.1 and equation (31), PDF p. 11; the imported arithmetic decomposition is equations (29)–(30), PDF p. 10.

**Consumer / audit and checkpoint:** [`GlobalBottomResidualState.primeRemainderEnergy_eq_weight_integral`](../Zeta23/CCM/GlobalParityBottomPrimeWeight.lean) (same-file #print axioms audit). Historical manuscript source: [`d228f35ca333`](https://github.com/HMarcusWH/zeta-23-lean/commit/d228f35ca3338520131a883b9091fad16ef9c9b9); §18, PDF pp. 14–16.

### A30

**[Fixed-dimension ground contact](../papers/2026-11-21/Fixed_Dimension_Ground_Contact_Weil_CCM_2026-09-30_v0_2_PROOFREAD.pdf).** A hypothetical off-critical zero forces one finite dimension with a positive small-aperture ground and a negative later ground.

**Representative source:** [`exists_fixedN_ground_sign_opposition_of_offLine_zero`](../Zeta23/ExceptionalZero/GlobalParityBottomSignOpposition.lean) in namespace `Zeta23.ExceptionalZero`.

**Mapping:** Named sign-opposition producer; production continuity and the intermediate-value contact are separate ingredients.

**Boundary:** Keep the finite dimension fixed for the contact argument. A zero contact does not establish a first crossing or an outgoing barrier.

**Manuscript location:** Theorem 7.1, PDF p. 8; subsequent zero-contact extraction is Theorem 12.2, PDF p. 10.

**Consumer / audit and checkpoint:** [`exists_fixedN_ground_sign_opposition_of_offLine_zero`](../Zeta23/ExceptionalZero/GlobalParityBottomSignOpposition.lean) (same-file #print axioms audit). Historical manuscript source: [`53daac5a0690`](https://github.com/HMarcusWH/zeta-23-lean/commit/53daac5a0690e3ae52a0e758c2ac8ba7a26290e7); §15, PDF pp. 11–13.

### A31

**[Canonical first-crossing shell rigidity](../papers/2026-11-21/Canonical_First_Crossing_Shell_Rigidity_Weil_CCM_2026-10-01_v0_2_PROOFREAD.pdf).** The selected first-crossing shell has regular negative zero-shift endpoints arbitrarily close on the outgoing side.

**Representative source:** [`CanonicalParityFirstCrossingShell.exists_arbitrarilyClose_regularZeroShiftEndpoint_neg`](../Zeta23/CCM/FirstCrossingSourceDynamics.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named local selection result, supported by plateau, kernel-tower and contact-regime modules.

**Boundary:** Interior and logarithmic-seam closing barriers are additional obligations. Stationarity alone does not prohibit crossing.

**Manuscript location:** Theorem 9.1, PDF p. 10.

**Consumer / audit and checkpoint:** [`CanonicalParityFirstCrossingShell.exists_arbitrarilyClose_regularZeroShiftEndpoint_neg`](../Zeta23/CCM/FirstCrossingSourceDynamics.lean) (same-file #print axioms audit). Historical manuscript source: [`a716d62f386a`](https://github.com/HMarcusWH/zeta-23-lean/commit/a716d62f386ac6d43c70672c68ac316b62a613e2); §18, PDF pp. 14–16.

### A28

**[Second-order prime-seam regularity](../papers/2026-11-21/Second_Order_Prime_Seam_Regularity_Weil_CCM_2026-10-09_v0_2_PROOFREAD.pdf).** The actual compressed parity family and its first derivative possess the stated real-aperture derivatives across positive logarithmic seams.

**Representative source:** [`hasDerivAt_productionParityFirstJetCLM_pos`](../Zeta23/CCM/CanonicalFrozenApertureC2.lean) in namespace `Zeta23.CCM`.

**Mapping:** Representative second-derivative statement; seam gluing and continuity are explicit source ingredients.

**Boundary:** This paper leaves moving-aperture arithmetic authority F04 separate. A26 subsequently supplies that authority for the stated even family.

**Manuscript location:** Theorem 6.1, PDF pp. 8–9; the displayed derivative of the first-jet operator is the selected source endpoint.

**Consumer / audit and checkpoint:** [`hasDerivAt_productionParityFirstJetCLM_pos`](../Zeta23/CCM/CanonicalFrozenApertureC2.lean) (same-file #print axioms audit). Historical manuscript source: [`7225489a1d60`](https://github.com/HMarcusWH/zeta-23-lean/commit/7225489a1d60812743e419d5b9042c8dca7eef53); §12, PDF pp. 15–16. The pending historical Control-v2 check is resolved only in the later A27 record.

### A27

**[Inherited stationarity and Schur curvature](../papers/2026-11-21/Inherited_Stationarity_Optimized_Schur_Curvature_Weil_CCM_2026-10-10_v0_3_MERGE_VERIFIED.pdf).** The inherited contact kernel has zero compressed first variation; the stationary strict-even Schur contact has vanishing optimized curvature under its hypotheses.

**Representative source:** [`GeneratedGlobalFirstCrossing.inheritedContactFirstJetRestriction_eq_zero`](../Zeta23/CCM/FirstCrossingInheritedStationarity.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named inherited stationarity declaration; production_stationary_schur_curvature_eq_zero is the separate curvature endpoint.

**Boundary:** Simple-kernel, inherited/fresh-born and parity hypotheses matter. The paper's conditional F04 bridge is strengthened by A26.

**Manuscript location:** Theorem 5.3, PDF p. 7; the separate optimized-curvature endpoint is Theorem 11.2, PDF p. 15.

**Consumer / audit and checkpoint:** [`GeneratedGlobalFirstCrossing.inheritedContactFirstJetRestriction_eq_zero`](../Zeta23/CCM/FirstCrossingInheritedStationarity.lean) (same-file #print axioms audit). Historical manuscript source: [`7225489a1d60`](https://github.com/HMarcusWH/zeta-23-lean/commit/7225489a1d60812743e419d5b9042c8dca7eef53); §16, PDF pp. 22–24.

### A26

**[Global arithmetic derivative transport](../papers/2026-11-21/Global_Arithmetic_Derivative_Transport_Canonical_Weil_CCM_2026-10-24_v0_2_PROOFREAD.pdf).** For every positive aperture in the specified canonical even boundary-flat family, actual moving-aperture derivatives match the full physical arithmetic evaluations, including seams.

**Representative source:** [`productionContactF04DerivativeAuthority_of_pos`](../Zeta23/CCM/CanonicalGlobalF04.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named discharge of F04; canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos supplies its downstream identity.

**Boundary:** An exact necessary saturation equality is not an incompatible inequality. Other contact branches are not generally excluded.

**Manuscript location:** Theorem 5.3, PDF p. 10; downstream Euler-corrected identity is Theorem 6.2, PDF p. 11.

**Consumer / audit and checkpoint:** [`productionContactF04DerivativeAuthority_of_pos`](../Zeta23/CCM/CanonicalGlobalF04.lean) (same-file #print axioms audit). Historical manuscript source: [`40495f39b751`](https://github.com/HMarcusWH/zeta-23-lean/commit/40495f39b7510b49a7fe3493b42d9fe3880d6d22); §11, PDF pp. 16–18.

### A25

**[Exact parity inertia and moment filtration](../papers/2026-11-21/Exact_Parity_Inertia_Moment_Filtration_Finite_Sign_Rigidity_Weil_CCM_2026-10-24_v0_2_PROOFREAD.pdf).** The elementary source matrix has exact even/odd inertia on the legal carriers for source coordinate 0<ω≤1/2.

**Representative source:** [`evenBoundaryFlat_source_exactInertia`](../Zeta23/CCM/CanonicalAndreiefInertia.lean) in namespace `Zeta23.CCM`.

**Mapping:** Named even result; oddBoundaryFlat_source_exactInertia is its partner. Filtration and countermodels have separate declarations.

**Boundary:** An elementary source atom is not the full pole–Archimedean–prime operator. Its sign does not establish canonical positivity.

**Manuscript location:** Theorem 6.2, PDF p. 14 (both even and odd legal-carrier inertia).

**Consumer / audit and checkpoint:** [`evenBoundaryFlat_source_exactInertia`](../Zeta23/CCM/CanonicalAndreiefInertia.lean) (same-file #print axioms audit). Historical manuscript source: [`40495f39b751`](https://github.com/HMarcusWH/zeta-23-lean/commit/40495f39b7510b49a7fe3493b42d9fe3880d6d22); §12, PDF pp. 24–26. The full half-interval statement belongs to PR #287, beyond the selected PR #285 claims registered by PR #286.

## Fourier analysis and co-Poisson profiles

### A24

**[Signed Fourier gaps and weighted mixing](../papers/2026-11-21/Signed_Fourier_Gap_Rigidity_Weighted_Arithmetic_Mixing_Weil_CCM_2026-10-24_v0_2_PROOFREAD.pdf).** A real signed, locally finite Fourier-self-dual measure with the exact gap, linear variation growth and off-lattice sign conditions must vanish.

**Representative source:** [`signed_sharp_gap_separator`](../Zeta23/OPICA/SignedHeatSeparator.lean) in namespace `Zeta23.OPICA`.

**Mapping:** Named separator; negative-mass budgets and weighted noncompact mixing use additional declarations and domains.

**Boundary:** The actual contact-to-admissible-measure bridge is not supplied. Do not omit Jordan-part, growth or sign hypotheses.

**Manuscript location:** Theorem 1.1, PDF p. 2; signed pairing and separator proof in §§3–4, PDF pp. 6–8.

**Consumer / audit and checkpoint:** [`consume_signed_sharp_gap_separator`](../Zeta23/OPICA/Validation.lean) (restated expected-type consumer). Historical manuscript source: [`d53dd70d38b0`](https://github.com/HMarcusWH/zeta-23-lean/commit/d53dd70d38b0762af130b1d19b795af259f505f5); §13, PDF pp. 23–25.

### A22

**[Actual-zero co-Poisson measures](../papers/2026-11-21/Actual_Zero_CoPoisson_Measures_Self_Dual_Profiles_2026-10-24_v0_2_PROOFREAD.pdf).** A source-normalized measure at an actual nontrivial zero has the precise gap, Fourier, variation and lattice properties, including its signed off-lattice behavior.

**Representative source:** [`zero_measure_exact_properties`](../Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean) in namespace `Zeta23.OPICAFollowup`.

**Mapping:** Named measure package; zero_profile_regular_selfdual and tail/jump declarations cover the associated profile.

**Boundary:** The profile obeys a forced arithmetic equation. The paper's Euler consequence is a manuscript derivation at its pin.

**Manuscript location:** Theorem 1.1, PDF pp. 2–3; detailed measure construction and properties in §§4–5.

**Consumer / audit and checkpoint:** [`expected_zero_measure_exact_properties`](../Zeta23/OPICAFollowup/Validation.lean) (restated expected-type consumer and axiom audit). Historical manuscript source: [`b9627cc1e76c`](https://github.com/HMarcusWH/zeta-23-lean/commit/b9627cc1e76c7e4541cf86de8d79d31acda8f7d5); §13, PDF pp. 25–27. The manuscript explicitly records incomplete follow-up aggregate acceptance.

### A23

**[Near-sharp gaps and distributional escape](../papers/2026-11-21/Controlled_Near_Sharp_Fourier_Gaps_Distributional_Escape_Weil_CCM_2026-10-24_v0_2_PROOFREAD.pdf).** Near-unit-gapped measures converge to zero on Schwartz tests under a common variation bound; a rescaled example escapes the order-zero measure class.

**Representative source:** [`near_gap_controlled_limit_zero`](../Zeta23/OPICAFollowup/NearGapLimits.lean) in namespace `Zeta23.OPICAFollowup`.

**Mapping:** Named convergence theorem; dilation_normalized_limit_not_measure is the separate escape result.

**Boundary:** Uniform variation control is essential. A nonzero distributional limit need not be a locally finite measure.

**Manuscript location:** Theorem 1.1, PDF p. 2; quantitative estimate and controlled-limit proof in §§4–5, PDF pp. 8–9.

**Consumer / audit and checkpoint:** [`independent_expected_near_gap_controlled_limit_zero`](../Zeta23/OPICAFollowup/Validation.lean) (independent expected-type consumer and axiom audit). Historical manuscript source: [`7b156e062343`](https://github.com/HMarcusWH/zeta-23-lean/commit/7b156e062343e99211d65b893bed1b619d01c82d); §13, PDF pp. 20–21. The archive file adds later CT13Support and compact-continuous extraction results; do not transfer the old whole-file receipt to the changed blob.

### A20

**[Paper VII: arithmetic sawtooth and sampling](../papers/2026-11-21/Paper_VII_Arithmetic_Sawtooth_Stieltjes_Spectral_Sampling_2026-10-24_v0_2.pdf).** The actual arithmetic spectral measure gives a Stieltjes transform with the specified half-plane sign and exact native sampling identities.

**Representative source:** [`arithmetic_stieltjes_sign_budget`](../Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean) in namespace `Zeta23.OPICAFollowup`.

**Mapping:** Representative sign theorem; native_sample_stieltjes_identity supplies the zero-profile sampling bridge.

**Boundary:** Positive resolvent/Gram expressions do not make a parameter of a forced equation real.

**Manuscript location:** Theorem 6.5, holomorphic arithmetic Stieltjes calculus (PDF p. 11), and Corollary 6.6 (p. 12); exact source sampling is the separate Theorem 8.2 (p. 15).

**Consumer and historical evidence:** [ExpectedWeightedSpectralMeasure.lean](../research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedWeightedSpectralMeasure.lean) — `expected_arithmetic_stieltjes_sign_budget`; independent consumer of the nonreal Stieltjes sign and resolvent budget. The manuscript source crosswalk is §13 (PDF pp. 25–26), pinned to [cea7b2f](https://github.com/HMarcusWH/zeta-23-lean/commit/cea7b2f62ea847c18958cc7385151c8c2b09520d). The paper records the narrow weighted-measure checks and explicitly leaves the combined actual_force_sampling_consumer OPEN at this historical pin; the positive-Gram/forced-sampling composition is a separate obligation.

### A19

**[Paper VIII: nonlinear Fourier defects](../papers/2026-11-21/Paper_VIII_Nonlinear_Fourier_Duality_Defects_2026-10-24_v0_2_PROOFREAD.pdf).** For the specified self-dual plateau profile, the squared construction has an exact defect that no allowed lattice-supported order-zero correction can remove.

**Representative source:** [`square_no_lattice_repair`](../Zeta23/OPICAFollowup/SquareDefect.lean) in namespace `Zeta23.OPICAFollowup`.

**Mapping:** Named non-repair theorem; the defect formula and gap-filling self-dual projection are separate endpoints.

**Boundary:** The nonlinear operation is on a scalar profile. The permitted correction class and regularity assumptions cannot be discarded.

**Manuscript location:** Theorem 5.3, no tempered lattice repair (PDF p. 5); the actual-zeta-zero specialization is Theorem 7.1 (p. 7).

**Consumer and historical evidence:** [ExpectedSquareDefect.lean](../research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedSquareDefect.lean) — `expected_square_no_lattice_repair`; `expected_actual_square`; independent no-repair consumer and actual-zero specialization. The manuscript source crosswalk is §9 (PDF pp. 8–9), pinned to [cea7b2f](https://github.com/HMarcusWH/zeta-23-lean/commit/cea7b2f62ea847c18958cc7385151c8c2b09520d). The paper records four narrow square-defect checks while the full 100-root aggregate remained unaccepted at its pin.

### A16

**[Paper XI: finite quadratic non-repair](../papers/2026-11-21/Paper_XI_Finite_Quadratic_Rigidity_Lattice_NonRepair_2026-10-27_v0_2_PROOFREAD.pdf).** For an eligible finite realified block of actual profiles, self-duality of a symmetric quadratic combination forces its coefficient matrix to vanish.

**Representative source:** [`finite_quadratic_profile_selfdual_obstruction`](../Zeta23/OPICARound2/ProfileControls.lean) in namespace `Zeta23.OPICARound2`.

**Mapping:** Named finite theorem, with an independent ProfileControls consumer.

**Boundary:** Distinct spectral nodes, symmetry, finite dimension and the stated correction domain are essential; no infinite-family or quadratic-jet classification follows.

**Manuscript location:** Theorems 1.1 and 1.2, finite real quadratic rigidity and lattice non-repair (PDF p. 2); proofs are developed in §§3–6.

**Consumer and historical evidence:** [ProfileControls.lean](../Zeta23/OPICARound2/Validation/ProfileControls.lean) — `actual_finite_symmetric_quadratic_rigidity`; `actual_quadratic_arbitrary_tempered_lattice_measure_control`; native real symmetric-block consumer and its arbitrary tempered lattice-measure control. The manuscript source crosswalk is §9 (PDF pp. 10–11), pinned to [07278f0](https://github.com/HMarcusWH/zeta-23-lean/commit/07278f01fcd17fb14d465630766a02e940abb8a0). The paper binds the statement to the Round 2 source pin. The consumer file supplies types and axiom commands, not by its presence a new compiler result.

### A15

**[Paper XII: co-Poisson jets and sign rigidity](../papers/2026-11-21/Paper_XII_Multiplicity_Sensitive_CoPoisson_Zero_Jets_Finite_Span_Sign_Rigidity_2026-10-27_v0_2_PROOFREAD.pdf).** A fixed independent finite basis of admissible zero-jet combinations has a coefficient norm controlled by weighted off-lattice negative mass.

**Representative source:** [`fixed_basis_negative_mass_budget`](../Zeta23/OPICAFollowup/FiniteSpanSeparation.lean) in namespace `Zeta23.OPICAFollowup.FiniteSpan`.

**Mapping:** Named quantitative finite-span result; multiplicity-jet construction and confluent independence are upstream results.

**Boundary:** The coercivity constant depends on the chosen basis. No basis-uniform estimate or off-critical exclusion is asserted.

**Manuscript location:** Theorem 1.4, fixed-basis quantitative negative-mass rigidity (PDF p. 3), proved in §9 (pp. 12–14).

**Consumer and historical evidence:** [ExpectedActualFixedBudget.lean](../research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedActualFixedBudget.lean) — `expected_full_actual_euclidean_budget`; `no_positive_budget_without_independence`; independent actual-basis budget consumer and a negative control removing basis independence. The manuscript source crosswalk is §12 (PDF p. 16), pinned to [416aec2](https://github.com/HMarcusWH/zeta-23-lean/commit/416aec21d4d6634675639b5397cc300d1f826e34). The paper uses the merged PR #294 snapshot and its recorded narrow consumer checks; it does not claim a fresh aggregate replay.

## Native causal arithmetic and approximation

### A21

**[Corrected native source transforms](../papers/2026-11-21/Corrected_Native_Source_Transforms_Double_Exponential_Localization_Weil_OPICA_2026-10-24_v0_2_PROOFREAD.pdf).** Finite words of source transformations retain the exact meromorphic transform after the affine history correction is included.

**Representative source:** [`nativeWord_corrected_transform`](../Zeta23/OPICAFollowup/NativeTransformationWords.lean) in namespace `Zeta23.OPICAFollowup`.

**Mapping:** Representative corrected-transform identity; localization and observation statements have separate source roots.

**Boundary:** Local pole survival, physical norm growth and an incompatible arithmetic estimate are different claims. A17 later identifies the native window rate.

**Manuscript location:** Theorem 4.1, exact native corrected germ (PDF p. 7), using the correction recurrence in Proposition 3.2 (p. 6).

**Consumer and historical evidence:** [Validation.lean](../Zeta23/OPICAFollowup/Validation.lean) — `expected_nativeWord_corrected_transform`; explicit expected-type declaration in the relocated validation assembly; that assembly labels itself UNACCEPTED. The related [ExpectedWordJet.lean](../research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedWordJet.lean) exposes `expected_step123_word_jet_consumer`. The manuscript source crosswalk is §14 and Table 2 (PDF pp. 24–26), plus Appendix C.2 (p. 30), pinned to [ff7b7c7](https://github.com/HMarcusWH/zeta-23-lean/commit/ff7b7c70f072606afeaf9ea7d9ccacd2442b483c). The manuscript uses ff7b7c7 as its primary source pin and compares the later cea7b2f editorial checkpoint with identical theorem-module blobs. Its 41 historical/48 narrow/11 open split, and the later 41/49/10 split, both retain false aggregate acceptance.

### A18

**[Paper IX: multiplicity-sensitive residual memory](../papers/2026-11-21/Paper_IX_Multiplicity_Sensitive_Native_Residual_Terminal_Memory_2026-10-24_v0_2_PROOFREAD.pdf).** An actual right-of-line zero with its multiplicity forces exponential terminal memory for the unchanged native prime field, via a Laguerre residual pairing.

**Representative source:** [`native_terminal_memory_lower`](../Zeta23/OPICAFollowup/MultiplicityTail.lean) in namespace `Zeta23.OPICAFollowup`.

**Mapping:** Named conditional lower bound; exact norm and residual-pairing declarations identify its source and multiplicity.

**Boundary:** Keep the stable-input subtraction, positive part and completion parameters. This does not supply an opposing upper bound.

**Manuscript location:** Theorem 6.3, exact source-weighted terminal-memory lower bound (PDF p. 8).

**Consumer and historical evidence:** [ExpectedMultiplicity.lean](../research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedMultiplicity.lean) — `expected_native_terminal_memory_lower`; explicit native terminal-memory consumer retaining multiplicity and stable-input subtraction. The manuscript source crosswalk is §9 (PDF pp. 10–11), pinned to [cea7b2f](https://github.com/HMarcusWH/zeta-23-lean/commit/cea7b2f62ea847c18958cc7385151c8c2b09520d). The paper records four narrowly checked multiplicity roots and preserves the pending aggregate boundary; it does not claim complete original-contract acceptance.

### A17

**[Paper X: exact logarithmic-window rates](../papers/2026-11-21/Paper_X_Exact_Native_Logarithmic_Window_Rates_2026-10-27_v0_2_PROOFREAD.pdf).** For the fixed source order and logarithmic window with C>1, the positive logarithmic energy rate equals Θ, the supremum of horizontal zero displacements.

**Representative source:** [`native_fixed_source_window_rate`](../Zeta23/OPICAFollowup/NativeWindowRate.lean) in namespace `Zeta23.OPICAFollowup`.

**Mapping:** Named fixed-order theorem; moving-order and high-mask consequences have separate declarations, as does the Round 2 damping-abscissa equivalence.

**Boundary:** Identifying Θ does not prove Θ=0; no claim is made at the boundary damping value.

**Manuscript location:** Theorem 1.1, exact fixed-source logarithmic-window rate (PDF p. 2), with its continuous-horizon proof in §6 (pp. 9–10).

**Consumer and historical evidence:** [ExpectedPhysicalRates.lean](../research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedPhysicalRates.lean) — `expected_fixed_source`; `expected_order_zero`; independent fixed-source and original-source consumers of the physical-window limit. The manuscript source crosswalk is §10 (PDF pp. 13–14), pinned to [416aec2](https://github.com/HMarcusWH/zeta-23-lean/commit/416aec21d4d6634675639b5397cc300d1f826e34). The main rate theorem uses merged PR #294. The manuscript’s later positive-damping result refers separately to Round 2 pin 07278f0; those two source checkpoints must not be conflated.

### A14

**[Paper XIII: native causal probes and finite Grams](../papers/2026-11-21/Paper_XIII_Native_Causal_Probes_Finite_Gram_Certified_Regional_Exclusion_2026-10-27_v0_2_PROOFREAD.pdf).** The exact finite native Gram system gives Schur/determinant formulas for optimal projection error and a conditional regional-exclusion interface.

**Representative source:** [`probe_schur_error`](../Zeta23/OPICARound2/ProbeGram.lean) in namespace `Zeta23.OPICARound2`.

**Mapping:** Named finite error identity; source approximation budgets and regional certification require additional declarations.

**Boundary:** The recorded raw numerical trial returned NO_CERTIFICATE. Finite Gram positivity does not prove the limiting error vanishes.

**Manuscript location:** Theorem 6.1, native finite Schur/determinant identity (PDF p. 7).

**Consumer and historical evidence:** [ProbeGram.lean](../Zeta23/OPICARound2/Validation/ProbeGram.lean) — `expected_p09_schur`; `expected_p09_bordered_determinant`; `expected_p09_actual_minimizer`; separate Schur-error, bordered-determinant, and native minimizer consumers. The manuscript source crosswalk is §14 (PDF pp. 17–18) and Appendix E (p. 21), pinned to [07278f0](https://github.com/HMarcusWH/zeta-23-lean/commit/07278f01fcd17fb14d465630766a02e940abb8a0). The manuscript records NO_CERTIFICATE and false full-core/release status at this pin. Those historical limits remain separate from the validity claimed for individual source declarations.

### A13

**[Paper XIV: critical-boundary input cost](../papers/2026-11-21/Paper_XIV_Critical_Boundary_Multiplicity_Source_Visibility_Causal_Zeta_2026-10-27_v0_2_PROOFREAD.pdf).** At a critical-line zero with source order k smaller than zero multiplicity m, the exact operator has a quantitative residual-versus-input lower cost.

**Representative source:** [`native_probe_boundary_power_cost`](../Zeta23/OPICARound2/TruncationControls.lean) in namespace `Zeta23.OPICARound2`.

**Mapping:** Named power-cost declaration; infinitely many visible simple zeros and a coefficient corollary use external classical input/paper composition.

**Boundary:** Exact nonrange does not exclude approximation by unbounded inputs. No approximation limit is proved.

**Manuscript location:** Theorem 8.2, native critical-boundary power-law lower bound (PDF p. 8), summarized in Theorem 1.2 (p. 2). The paper’s further statements using external simple-zero results and its coefficient deductions are additional arguments; they do not follow from an existence claim for an approximating family.

**Consumer and historical evidence:** [TruncationControls.lean](../Zeta23/OPICARound2/Validation/TruncationControls.lean) — `truncation_consumer_026`; direct consumer retaining the source zero order k < zeroMult and the resulting norm-cost exponent. The manuscript source crosswalk is §14 (PDF pp. 13–14), pinned to [07278f0](https://github.com/HMarcusWH/zeta-23-lean/commit/07278f01fcd17fb14d465630766a02e940abb8a0). The manuscript cites the Round 2 declaration and its type/axiom audit surface at this historical pin.

### A12

**[Paper XV: fixed-filter four-column certificate](../papers/2026-11-21/Paper_XV_Fixed_Causal_Filter_Four_Column_Certificate_v0_2_PROOFREAD.pdf).** For the original source and four rational coefficients, a rigorous filtered residual upper bound contradicts the zero-evaluation lower bound on the stated small rectangle.

**Representative source:** [`filtered_four_column_region_certificate`](../Zeta23/OPICARound2/FiniteFilteredBaseline.lean) in namespace `Zeta23.OPICARound2`.

**Mapping:** Named finite filtered certificate, with FiniteFilteredBaseline validation consumers.

**Boundary:** The rectangle was already known by stronger classical verification. The filter is not surjective on the causal space; the raw norm is a different problem.

**Manuscript location:** Theorem 1.1, fixed-filter four-column certificate (PDF p. 2); its upper and hypothetical-zero lower bounds are Propositions 4.3 and 5.3 (pp. 7–8).

**Consumer and historical evidence:** [FiniteFilteredBaseline.lean](../Zeta23/OPICARound2/Validation/FiniteFilteredBaseline.lean) — `baseline_actual_native_four_column_upper`; `baseline_actual_zero_witness_lower`; `baseline_actual_closed_rectangle_nonvanishing`; `baseline_actual_reflected_rectangle_nonvanishing`; separate consumers for the upper bound, hypothetical-zero lower bound, and original/reflected region conclusions. The manuscript source crosswalk is §6.4 (PDF p. 9) and Appendix B (pp. 10–11), pinned to [07278f0](https://github.com/HMarcusWH/zeta-23-lean/commit/07278f01fcd17fb14d465630766a02e940abb8a0). The source pin and paper rational arithmetic checks are distinct evidence from a fresh analytic or Lean dependency replay.

### A11

**[Paper XVI: raw/filtered separation](../papers/2026-11-21/Paper_XVI_Finite_Prefix_Rigidity_Raw_Filtered_Separation_v0_2_PROOFREAD.pdf).** The same four coefficients have a large native raw residual from twelve exact pulse defects while the fixed-filter residual is small.

**Representative source:** [`native_isolated_pulse_lower_bound`](../Zeta23/OPICARound2/TruncationControls.lean) in namespace `Zeta23.OPICARound2`.

**Mapping:** Formal pulse lower-bound ingredient; the twelve-cell rational comparison and new integration are paper compositions, not asserted here as separately compiled endpoints.

**Boundary:** This same-vector contrast gives neither a global approximation limit nor a conclusion about every coefficient sequence.

**Manuscript location:** Theorem 6.1, Bessel divisor-defect inequality (PDF p. 7), supplies the source ingredient; the selected same-vector raw/filtered separation is Theorem 1.1 (p. 2), with the twelve-defect calculation in Lemma 7.1 and Proposition 7.2 (pp. 7–8). The exact raw/filtered Python example checks the finite rational arithmetic, not an independent proof of the analytic source inequality.

**Consumer and historical evidence:** [TruncationControls.lean](../Zeta23/OPICARound2/Validation/TruncationControls.lean) — `consumer_040`; consumer of the native pulse-separation constant and the finite Bessel lower bound for K contained in {1,…,2047}. The manuscript source crosswalk is Appendix B (PDF p. 11), pinned to [07278f0](https://github.com/HMarcusWH/zeta-23-lean/commit/07278f01fcd17fb14d465630766a02e940abb8a0). The paper identifies the existing native truncation source at this pin. Appendix B separates the new rational same-vector composition from a separately compiled Lean endpoint.

### A10

**[Paper XVII: confluent Laplace jets](../papers/2026-11-21/Paper_XVII_Confluent_Laplace_Jets_Conjugate_Pair_Bounds_v0_2_PROOFREAD.pdf).** Distinct right-half-plane nodes with multiplicity jets have an exact positive-definite confluent Laplace Gram and determinant, supporting simultaneous projection bounds.

**Representative source:** [`laplace_jet_gram`](../Zeta23/OPICARound2/DualCertificates.lean) in namespace `Zeta23.OPICARound2`.

**Mapping:** Named general Gram package; the conjugate-pair improvement and displayed derivative-jet increment are paper integrations at the manuscript pin.

**Boundary:** Node distinctness and the positive real part matter. The displayed improvement is a lower-bound improvement, not an upper bound on the exact projection ratio.

**Manuscript location:** Theorem 3.1, confluent Gram matrix and determinant (PDF pp. 3–4); simultaneous distance is Theorem 4.1 (p. 4). The conjugate-pair factor and derivative refinements in Theorem 1.1, Proposition 5.1, and Theorem 6.2 are manuscript consequences, not additional endpoints certified merely by laplace_jet_gram.

**Consumer and historical evidence:** [DualCertificates.lean](../Zeta23/OPICARound2/Validation/DualCertificates.lean) — `expected_p17_complete`; explicit full Gram/determinant consumer, accompanied by repeated-node and factorial negative controls. The manuscript source crosswalk is §7.2 (PDF p. 8) and Appendix B (p. 9), pinned to [775692f](https://github.com/HMarcusWH/zeta-23-lean/commit/775692f2e72d76b6a97cf66926a86cc96342c109). The manuscript distinguishes source-established Gram statements from its symbolic checks and paper deductions; this documentation pass does not rerun those compiler checks.

## Joint-source and late spectral synthesis

### A09

**[Paper XVIII: cofinal two-parity instability](../papers/2026-11-21/Paper_XVIII_Cofinal_Two_Parity_Instability_2026-10-29_v0_2_PROOFREAD.pdf).** A hypothetical off-critical zero forces simultaneous strict negativity in both physical neutral parities at a common aperture and cutoff, arbitrarily far out.

**Representative source:** [`cofinally_both_neutral_negative_of_off_line_zero`](../Zeta23/OPICARound3/CofinalSimultaneousNegative.lean) in namespace `Zeta23.OPICARound3`.

**Mapping:** Named cofinal producer; uniform intervals and own-first-birth witnesses are separate endpoints.

**Boundary:** The two parity births need not coincide. An eventual joint negative-index upper bound of one is an independent closing premise.

**Manuscript location:** Theorem 5.2, cofinal simultaneous physical parity negativity, and Corollary 5.3 (PDF p. 9).

**Consumer and historical evidence:** [CofinalSimultaneousNegative.lean](../Zeta23/OPICARound3/Validation/CofinalSimultaneousNegative.lean) — `cofinally_both_neutral_negative_of_off_line_zero_consumer`; `simultaneous_physical_witnesses_consumer`; direct cofinal consumer and extraction of same-cutoff physical witnesses. The manuscript source crosswalk is §10.2 (PDF pp. 17–18), pinned to [8109728](https://github.com/HMarcusWH/zeta-23-lean/commit/8109728135135a58eb98920180e03f77439c1da4). The authoritative theorem is in the merged PR #297 snapshot. The paper separately mentions the later Round 4 index at 3cf99b4; that later index does not supply a new replay of this theorem.

### A02

**[Paper XIX: grouped residues and visibility](../papers/2026-11-21/Paper_XIX_Grouped_Signed_Spectral_Residues_Source_Visibility_2026-10-29_v0_2_PROOFREAD.pdf).** In the stated Hermitian rank-one interface, a grouped zero residue is equivalent to whole-eigenspace input or transported-output invisibility.

**Representative source:** [`grouped_residue_zero_iff_input_or_output_invisible`](../Zeta23/OPICARound4/VisibilityRigidity.lean) in namespace `Zeta23.OPICARound4`.

**Mapping:** Named visibility equivalence; signed resolvent/Pick expansions and actual-ground closure consumers are separate results.

**Boundary:** A zero residue does not remove an eigenvalue. Strict-ground comparisons plus tie exclusion restate eventual positivity rather than proving a weaker independent estimate.

**Manuscript location:** Theorem 5.3, grouped zero-residue rigidity (PDF p. 10).

**Consumer and historical evidence:** [IntegrationVisibilityRigidity.lean](../Zeta23/OPICARound4/Validation/IntegrationVisibilityRigidity.lean) — `native_even_zero_residue_classification`; `native_odd_zero_residue_classification`; native parity specializations of the grouped-residue equivalence, with type/axiom audit commands. The manuscript source crosswalk is §10.3 (PDF p. 18) and Appendix C (PDF pp. 22–23), pinned to [3cf99b4](https://github.com/HMarcusWH/zeta-23-lean/commit/3cf99b4ea74209bba372beca7c66e5150ee6fa4c). The paper inspected the open PR #298 source on 29 October 2026; its source inspection was not a fresh compiler or full axiom replay.

### A03

**[Paper XX: corrected Chebyshev discrepancy](../papers/2026-11-21/Paper_XX_Exact_Chebyshev_Discrepancy_Concentration_Source_Tests_2026-10-30_v0_2_PROOFREAD.pdf).** The actual corrected source-selected mixed test has exact endpoint cancellation and an exact Chebyshev discrepancy representation.

**Representative source:** [`native_prime_discrepancy_integral`](../Zeta23/OPICARound4/PrimeDiscrepancyIntegral.lean) in namespace `Zeta23.OPICARound4`.

**Mapping:** Named native arithmetic identity; nativeSourceAtom_norm_le_two is the separate sharp dimension-free atom estimate.

**Boundary:** The adaptive prime-discrepancy and continuum–Archimedean smallness estimates remain premises. Mixed rows and diagonal energies are not interchangeable.

**Manuscript location:** Theorem 7.2, exact native corrected-source Chebyshev discrepancy, with endpoint cancellation in Lemma 7.1 (PDF p. 13).

**Consumer and historical evidence:** [IntegrationSource.lean](../Zeta23/OPICARound4/Validation/IntegrationSource.lean) — `native_prime_discrepancy_integral`; explicit #check and #print axioms commands for this declaration; no separately named proof consumer for this exact identity is identified here. The manuscript source crosswalk is Appendix C (PDF pp. 24–25), pinned to [3cf99b4](https://github.com/HMarcusWH/zeta-23-lean/commit/3cf99b4ea74209bba372beca7c66e5150ee6fa4c). The paper records source inspection on 30 October 2026 at the open PR #298 pin; it does not report a new full-tree replay.

### A08

**[Paper XXI: finite-to-smooth Schur transport](../papers/2026-11-21/Paper_XXI_Complete_Finite_to_Smooth_Schur_Transport_FINAL.pdf).** The complete three-channel comparison error has a source-only envelope vanishing after every fixed exponential rescaling at the prescribed quartic cutoff.

**Representative source:** [`sourceSchurUniformEnvelope_mul_exp_tendsto_zero`](../Zeta23/OPICARound4/QuarticErrorReduction.lean) in namespace `Zeta23.OPICARound4`.

**Mapping:** Named envelope limit; finite forcing, Schur transport and packet-uniform threshold declarations provide the full comparison.

**Boundary:** This preserves a lower obstruction. It does not bound the genuine smooth-source expression from above.

**Manuscript location:** Theorem 7.1, vanishing after every fixed exponential rescaling (PDF p. 10).

**Consumer and historical evidence:** [ErrorReduction.lean](../Zeta23/OPICARound4/Validation/ErrorReduction.lean) — `all_exponential_rates_consumer`; `threshold_before_packet_consumer`; direct consumers of the all-exponential-rates limit and the threshold-before-packet quantifier order. The manuscript source crosswalk is §10 and Appendix A (PDF pp. 13–14), pinned to [ff323fe](https://github.com/HMarcusWH/zeta-23-lean/commit/ff323fef60cf297cd12ce7f0d54768fa8545891f). The manuscript records local type/axiom checks at its Round 4 pin; this is not a fresh full Linux acceptance receipt.

### A07

**[Paper XXII: branch-complete ground arithmetic](../papers/2026-11-21/Paper_XXII_Exact_Ground_Arithmetic_Branch_Complete_Source_Rigidity_v0_1.pdf).** The same finite physical state with two negative parity grounds satisfies a strict-even, strict-odd or kernel-safe tied arithmetic constraint packet.

**Representative source:** [`joint_ground_constraints_of_both_negative`](../Zeta23/OPICARound4/JointGroundConstraints.lean) in namespace `Zeta23.OPICARound4`.

**Mapping:** Named branch-complete same-state theorem and a cofinal producer.

**Boundary:** An exhaustive disjunction does not exclude its branches. The odd source and reciprocal even input carry different signs.

**Manuscript location:** Theorem 8.2, branch-complete same-cutoff ground certificate (PDF p. 13); its conditional cofinal form is Theorem 9.2 (p. 14).

**Consumer and historical evidence:** [GroundConstraints.lean](../Zeta23/OPICARound4/Validation/GroundConstraints.lean) — `joint_ground_constraints_of_both_negative`; `cofinally_joint_ground_constraints_of_off_line_zero`; independently stated anonymous example declarations applying the fixed-state and cofinal theorems. The manuscript source crosswalk is Appendix C (PDF pp. 19–20), pinned to [ff323fe](https://github.com/HMarcusWH/zeta-23-lean/commit/ff323fef60cf297cd12ce7f0d54768fa8545891f). The paper reports local compiler/type/axiom checks with existing dependencies and keeps the complete Linux production lanes separate.

### A06

**[Paper XXIII: joint quartic ground synchronization](../papers/2026-11-21/Paper_XXIII_Joint_Quartic_Ground_Source_Rigidity_FINAL_v1_0.pdf).** A hypothetical off-critical zero forces both physical parity sectors negative at the original prescribed quartic cutoff for every sufficiently large aperture.

**Representative source:** [`eventually_both_negative_at_original_quartic`](../Zeta23/OPICARound4/CommonQuarticGround.lean) in namespace `Zeta23.OPICARound4`.

**Mapping:** Named synchronization theorem; own-birth complement bounds and tie visibility are separate mapped declarations. The paper's full final grouping is a composition.

**Boundary:** Detector, selected predecessor, own-newborn and true-ground vectors/cutoffs remain distinct. No uniform global index upper bound is supplied.

**Manuscript location:** Theorem 23.2, eventual common-quartic two-parity negativity (PDF p. 9); the later packet synchronization is Theorem 23.3 (p. 11). The expanded joint synthesis in Theorem 23.8 (PDF pp. 17–18) combines additional source declarations; it is broader than this one representative endpoint.

**Consumer and historical evidence:** [JointGround.lean](../Zeta23/OPICARound4/Validation/JointGround.lean) — `common_quartic_uniform_threshold_consumer`; direct consumer extracting a uniform eventual-aperture threshold from the representative theorem. The manuscript source crosswalk is §11 (PDF pp. 22–24) and Appendix A (pp. 25–27), pinned to [fb45853](https://github.com/HMarcusWH/zeta-23-lean/commit/fb45853c49ec7099e4f3d3617373fe3bbd6a06ee). The manuscript records selected local support compilation, while new visibility replay and full current-head acceptance remained separate obligations.

### A05

**[Paper XXV: signed Möbius/Mellin compression](../papers/2026-11-21/Paper_XXV_Signed_Mobius_Mellin_Moment_Compression_FINAL_v1_0.pdf).** The original finite arithmetic quadratic is compressed into signed Möbius moments and a Mellin–Fourier representation, retaining the critical O(N) error scale.

**Representative source:** [`actualCorrelationLongTerm_eq_sampling_quadratic`](../Zeta23/OPICARound4/ActualSourceHyperbola.lean) in namespace `Zeta23.OPICARound4`.

**Mapping:** Mapped formal ingredient only. The new all-order regularity, alias, spectral and compression theorems are manuscript proofs at the pin; their full formal endpoints are not mapped here.

**Boundary:** An equivalent representation does not prove the missing arithmetic lower bound. Source-blind Hankel positivity is ruled out, not established.

**Manuscript location:** Theorem 25.5, moment compression with O(N) error (PDF p. 14); Theorem 25.7, signed Mellin–Fourier representation (p. 18); Theorem 25.8, equivalence of the three critical lower-bound formulations (p. 20). Section 13 expressly asserts no matching new Lean declarations for any of the eight main Paper XXV theorems. The listed new module names in §13.2 are proposals, not existing formalizations.

**Consumer and historical evidence:** [Hyperbola.lean](../Zeta23/OPICARound4/Validation/Hyperbola.lean) — `validation_madness_exact_sampling_bridge`; consumer of the earlier exact sampling identity used as an ingredient by this paper. The manuscript source crosswalk is §13.1 (PDF pp. 23–24), pinned to [451ad69](https://github.com/HMarcusWH/zeta-23-lean/commit/451ad696437d6f8fc5badd827ce252dfcfd801e3). The pin fixes the literal native definitions and existing arithmetic interfaces. Section 13 distinguishes those inspected definitions from a fresh compiler replay.

### A04

**[Paper XXVI: regular quartic spectral flow](../papers/2026-11-21/Paper_XXVI_Regular_Quartic_Spectral_Flow_Schur_Inertia_FINAL_v1_0.pdf).** At a regular selected aperture, negative inertia equals the count of negative one-shell Schur pivots, yielding a local chamber and first-birth ledger.

**Representative source:** [`cofinally_both_negative_and_native_regular`](../Zeta23/OPICARound4/RegularCells/NativeRegularBirthSelection.lean) in namespace `Zeta23.OPICARound4.RegularCells`.

**Mapping:** Mapped formal regularity/negativity ingredient. The full inertia ledger, chamber theorem and joint synthesis are manuscript deductions, not exact new declarations at the paper pin.

**Boundary:** Nonunitary congruence preserves inertia, not eigenvalues. Local chambers do not automatically cross prime seams or quartic jumps.

**Manuscript location:** Theorem 26.2, cofinal quartic negativity with all-predecessor regularity (PDF p. 9). The one-shell inertia formula (Theorem 26.4, PDF p. 11), finite ledger (26.5, p. 13), local chamber (26.6, p. 15), and full synthesis (26.8, pp. 19–20) are explicitly paper-proved algebra or compositions, without separately compiled endpoints at this pin.

**Consumer and historical evidence:** [NativeGroundRegularity.lean](../Zeta23/OPICARound4/Validation/NativeGroundRegularity.lean) — `cofinal_native_regular_births_consumer`; related downstream consumer of cofinally_regular_first_common_births, rather than a separate direct consumer of the representative theorem. The manuscript source crosswalk is Appendix C (PDF pp. 29–30), pinned to [451ad69](https://github.com/HMarcusWH/zeta-23-lean/commit/451ad696437d6f8fc5badd827ce252dfcfd801e3). The paper records selected local Windows native compilation with historical parent dependencies at draft PR #299; fresh independent current-head acceptance remained required.

### A01

**[Paper XXVII: prime-phase noncollision](../papers/2026-11-21/Paper_XXVII_Prime_Phase_Noncollision_Source_Packet_FINAL_v1_0.pdf).** A hypothetical off-critical zero yields cofinally selected same-source deep packets with simultaneous invertibility and disjoint parity spectra for 3≤K≤Kd at the original quartic detector.

**Representative source:** [`cofinally_actual_packet_joint_regular_disjoint_spectra`](../Zeta23/OPICARound4/RegularCells/PacketSpectralSelection.lean) in namespace `Zeta23.OPICARound4.NativeParityPencils`.

**Mapping:** Named central conjunction; visibility and simplicity are additional exact compositions with SeparatedSourceVisibility, not one blanket whole-paper certificate.

**Boundary:** The packet retains any requested parity and 0<β<|Re ρ−1/2|. No uniform spectral gap, overlap lower bound, every-aperture noncollision or opposing source sign follows.

**Manuscript location:** Theorem 27.8 (PDF pp. 20–21), especially the explicit joint certificate through equations (51)–(54). The source-visibility and simplicity conclusions at the end of Theorem 27.8 additionally compose the separate SeparatedSourceVisibility declarations; the expanded final sentence is not one separately compiled endpoint.

**Consumer and historical evidence:** [NativeNoncollision.lean](../Zeta23/OPICARound4/Validation/NativeNoncollision.lean) — `genuine_packet_same_detector_spectral_check`; direct independently stated consumer of the representative joint certificate. The manuscript source crosswalk is Appendix D, §§D.1–D.4 (PDF pp. 31–32), pinned to [8bf89fd](https://github.com/HMarcusWH/zeta-23-lean/commit/8bf89fd668f48c28a1629cf791e717eb00ec6242). The manuscript reports local type/axiom checks at the open PR #299 pin and explicitly does not claim a fresh independent full production replay.

## Later source and research records

The 43 PDFs are not the complete November source history. Important later mathematics and investigations are recorded in Lean and Markdown. The following rows connect them to the final tree without attributing later work to an earlier paper.

| Result ID | Mathematical output | Exact source and research record | Scope and missing premise |
| --- | --- | --- | --- |
| N01 | Zero-strip / native moment-slice rate ladder | [ZeroFreeFloor.lean](../Zeta23/OPICARound4/ArithmeticFrontier/ZeroFreeFloor.lean): `zeroStrip_iff_even_fixed_rates`, `zeroStrip_iff_odd_fixed_rates`; [frontier specification](../research/RHRC/integration/opica_round4/arithmetic_frontier/BUILD_SPEC.md) | Fixed-rate lower bounds retain their all-late quantifiers and original quartic moment slices. A rate equivalence does not establish a smaller rate. |
| N02 | Logical strength of C1, SB, PG and SE | [ZeroFreeFloor.lean](../Zeta23/OPICARound4/ArithmeticFrontier/ZeroFreeFloor.lean): `riemannHypothesis_iff_cofinal_moment_slice_bounds`, `riemannHypothesis_iff_cofinal_moment_slice_semibounded`, `riemannHypothesis_iff_fixed_parity_polynomial`, `riemannHypothesis_iff_fixed_parity_subexponential` | These are explicit RH equivalences. Delay and scale variants retain the admissible-cost hypotheses in their own types. |
| N03 | Exact-data finite positivity certificates | [FiniteCertificateSoundness.lean](../Zeta23/OPICARound4/ArithmeticFrontier/FiniteCertificateSoundness.lean): `posDef_of_shifted_factor`, `shifted_factor_requires_positive_shift`; [example](EXAMPLES.md#positivity-certificate) | The positive shift and exact real residual bound prove sound finite algebra. The native Arb/transcendental enclosure bridge is explicitly open in this source. |
| N04 | Source-core compression with full leakage | [SourceColumnCore.lean](../Zeta23/OPICARound4/ArithmeticFrontier/SourceColumnCore.lean): `core_shift_certificate`, `core_shift_certificate_of_columns` | The core sign and whole-complement leakage are premises. Nonorthogonal columns retain their physical Gram matrix. |
| N05 | Round 5 parity-moment exact sequence | [ParityMomentBridge.lean](../Zeta23/OPICARound5/ParityMomentBridge.lean): `fixedMomentParityShortExact`, `finrank_fixedEvenMomentSeed`, `finrank_fixedOddMomentSeed` | The file is in Round 5; its namespace remains `Zeta23.OPICARound4.ArithmeticFrontier`. The centered-index map is not an isometry and does not automatically transfer positivity. |
| N06 | Finite signed Gram and selector-energy identities | [FiniteWeightedGram.lean](../Zeta23/OPICARound6/PrimeFactorPaths/FiniteWeightedGram.lean): `signed_energy`, `ordered_minors`; [FiniteSelectorEnergy.lean](../Zeta23/OPICARound6/PrimeFactorPaths/FiniteSelectorEnergy.lean): `signed_weight_energy_comparison` | Exact signed identities are separate from inequalities requiring nonnegative weights or explicit height bounds. |
| N07 | Opposed parity excess/deficit with forced coefficient four | [ParityDeficitProduct.lean](../Zeta23/OPICARound6/PrimeFactorPaths/ParityDeficitProduct.lean): `quadrant_remainder`, `weighted_absolute_remainder`, `forced_coefficient`; [arithmetic derivation](../research/RHRC/integration/opica_round6/evidence/step4-parity-deficit-2026-11-20/SURVIVOR_HAAR_FINGERPRINTS.md) | Finite algebra is formal source. The independent cofinal opposed-product estimate remains `P303_OPPOSED_PRODUCT_UPPER`; the growing-horizon transfer also retains `PAPER_ROUTE_VALIDATION`. |
| N08 | Finite stopping-cover/high-path duality | [StoppingAlgebra.lean](../Zeta23/OPICARound6/PrimeFactorPaths/StoppingAlgebra.lean): `Observations.value_le_iff_cover`, `Observations.lt_value_iff_highPath`, `Observations.no_cover_iff_highPath`; [example](EXAMPLES.md#stopping-tree) | Exact finite trees, delays and complete cuts. This duality does not prove the arithmetic bound on the native stopping cost. |
| N09 | Native cells, whole shells, survivor/partner costs and finite transfer | [Round 6 package](../research/RHRC/integration/opica_round6/README.md), [finite audit surface](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean), [native transfer](../Zeta23/OPICARound6/PrimeFactorPaths/NativeFullTransfer.lean) | This guide maps the package/import surface; individual theorem correspondences beyond N06–N08 are not exhaustively transcribed. Preserve fixed origin, complete shells and spent partners. |
| N10 | Nested-cut arithmetic route | [LOCAL_PRIME_GRAPH_CUTS.md](../research/RHRC/integration/opica_round6/evidence/step4-nested-cuts-2026-11-20/LOCAL_PRIME_GRAPH_CUTS.md), [constraint register](../research/RHRC/integration/opica_round6/CONSTRAINTS.json) | A growing-horizon paper route with independent `N20_JOINT_ARITHMETIC_UPPER` and formal-transfer `PAPER_ROUTE_VALIDATION` obligations. The finite stopping lemmas are ingredients, not a formal proof of the whole route. |

The original survivor-charge route separately retains `ACTUAL_UPPER` and `PAPER_ROUTE_VALIDATION`. These identifiers are exact obligation names, not established arithmetic estimates. The [Round 6 route account](../research/RHRC/integration/opica_round6/README.md) explains their quantifiers and alternatives.

## Scoped supersessions

A later result changes a particular boundary under particular hypotheses. The old paper and its evidence remain historical records.

| Earlier state | Later result | What remains distinct or open |
| --- | --- | --- |
| A28/A27 leave F04 moving-aperture arithmetic transport separate | A26 supplies `productionContactF04DerivativeAuthority_of_pos` for the canonical even boundary-flat family at all positive apertures, including seams | It does not exclude all first crossings, parity ties or fresh-born branches. |
| A21 distinguishes physical growth from local pole survival and leaves exact native window-rate identification open | A17 identifies the native terminal-window rate with Θ | An identity for Θ does not prove Θ=0. Boundary damping behavior has a separate scope. |
| A09 supplies cofinal common physical parity negativity | A06 gives eventual simultaneous negativity at the prescribed original quartic cutoff | Cofinal and eventual quantifiers differ; own first-birth cutoffs still need not be equal. |
| A07/A04 organize singular/shared grounds and regular selection | A01 selects cofinal genuine deep packets with disjoint spectra for every `3 ≤ K ≤ Kd` | It is not every-aperture noncollision. It retains `0 < β < |Re ρ − 1/2|` and supplies no uniform gap or source-overlap magnitude. |
| The initial arithmetic-frontier specification describes reverse implications as expected work | N01/N02 link the later rate ladder and RH equivalences actually present in `ZeroFreeFloor.lean` | Equivalence is a logical-strength audit, not the missing arithmetic inequality. |

### Two normalization corrections that must stay separate

The rank-one dictionary discrepancy in A42 is `δL • (1 1ᵀ)`. The scalar correction in A41 is a multiple of the identity `I`. The first concerns extending an explicit-formula identity from a smooth core. The second changes the absolute normalization of the finite operator. They have different ranks, spectral effects and proof roles; neither can be substituted for the other.

## Missing and partially mapped material

- **Paper XXIV:** no separately named PDF was present in the archived source folder. Later A05 cites it. The actual hyperbola and sampling ingredients are available in [MobiusHyperbola.lean](../Zeta23/OPICARound4/MobiusHyperbola.lean), [ActualSourceHyperbola.lean](../Zeta23/OPICARound4/ActualSourceHyperbola.lean) and [HyperbolaDiagonal.lean](../Zeta23/OPICARound4/HyperbolaDiagonal.lean). This identifies available code, not a recovered manuscript.
- **Two earlier retained PDFs:** [OPICA Followup Final Audited Paper, 21 October](../research/RHRC/integration/opica_followup/continuation/2026-10-22/inputs/OPICA_Followup_Final_Audited_Paper_2026-10-21.pdf) and [OPICA Beyond PR Paper Round 2, 21 October](../research/RHRC/integration/opica_followup/continuation/2026-10-22/inputs/OPICA_Beyond_PR_Paper_Round2_2026-10-21.pdf) are preserved separately from the 43-file archive. Their full internal theorem crosswalks are not newly remapped here; use their [continuation entry point](../research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md).
- **Unlisted results inside a mapped paper:** the representative declaration does not validate every assertion in that PDF. Read its formal-source section, complete theorem types and recorded commit before using an additional result. An unmapped portion is an explicit navigation gap, not evidence that it is false or already formalized.
- **Historical receipts:** manuscript claims of successful compilation apply to the named historical source, toolchain and scope. A consumer file present in the current tree is not a replacement for its actual execution receipt. If that receipt is externally referenced or unavailable, retain that limitation.

## Using or extending this map

For a new result-level entry, record the exact statement, assumptions, manuscript location, declaration and namespace, relationship between the two, consumer, source pin, evidence location, reuse example and remaining limit. Resolve long names against the source rather than copying PDF line-wrap fragments. A proof term, a type consumer and a numerical agreement have different roles.

The original [paper manifest](../papers/MANIFEST_2026-11-21.json), package `ROOTS`/constraint registries and source-bound receipts remain their own authoritative records. This guide is human navigation over them, not a replacement claim registry. Cite the manuscript for its written argument and the pinned declaration for the formal statement using the [citation guide](REPRODUCIBILITY.md#citation).
