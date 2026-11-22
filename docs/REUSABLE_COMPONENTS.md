# Reusable mathematics and research tools

This repository contains useful finite algebra, spectral calculus, approximation arguments and audit tooling in addition to its unfinished RH attempt. This catalogue starts from a problem someone might want to solve elsewhere and points to the exact implementation. The [results map](RESULTS_AND_FORMALIZATION.md) supplies the manuscript context; the [examples](EXAMPLES.md) supply small entry points.

**Baseline:** the mathematical source at [7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9](https://github.com/HMarcusWH/zeta-23-lean/commit/7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9), archived 21 November 2026. This catalogue verifies source locations and describes their types. It is not a new whole-repository compilation receipt or an assertion of mathematical priority. Follow [reproducibility](REPRODUCIBILITY.md) before reporting a fresh check.

## Choose a component

| Your task | Start here | Packaging at this snapshot |
| --- | --- | --- |
| Exhibit a negative direction in a signed rank-two block | [Explicit Gram witness](#explicit-gram-witness) | Generic statement; project imports |
| Reconstruct a symmetric matrix from its zero-sum restriction | [Codimension-one completion](#codimension-one-matrix-completion) | Generic statement; project imports |
| Certify strict positivity with an approximate factorization | [Shifted-factor certificate](#shifted-factor-positivity-certificate) | Generic; Mathlib-only imports |
| Lift a bound from selected columns to the full space | [Source-column core](#source-column-core-and-leakage) | Generic; Mathlib-only imports |
| Manipulate finite weighted quadratic energies | [Weighted Gram algebra](#finite-weighted-gram-algebra) | Generic; Mathlib-only imports |
| Control errors in positive-part energies | [Selector energy](#positive-part-selector-stability) | Generic; Mathlib-only imports |
| Relate opposed signs to a scalar discrepancy | [Parity-deficit product](#opposed-sign-products) | Generic; Mathlib-only imports |
| Compare a complete stopping cover with a persistent path | [Stopping-tree duality](#finite-stopping-tree-duality) | Generic; Mathlib-only imports |
| Use Hermitian inertia and positive/negative parts | [Inherited linear algebra](#inherited-hermitian-linear-algebra) | Generic; upstream attribution required |
| Take a Schur complement at a singular block | [Kernel-safe Schur response](#kernel-safe-schur-response) | Generic statement; project imports |
| Differentiate a scalar Schur expression three times | [Abstract Schur calculus](#abstract-third-order-schur-calculus) | Generic; Mathlib-only imports |
| Prove independence of exponential frequencies with meromorphic coefficients | [Frequency separation](#meromorphic-frequency-separation) | Generic; Mathlib-only imports |
| Retain signs in a finite spectral response | [Signed residues](#signed-spectral-response-and-abel-summation) | Generic; Mathlib-only core |
| Work with analytic germs modulo a prescribed zero | [Local analytic quotients](#analytic-germs-and-finite-jets) | Generic analytic core; project imports |
| Build finite approximants with exact endpoint moments | [Boundary-flat approximation](#boundary-flat-approximation-and-centered-extension) | Source-adapted framework; project imports |
| Separate signed Fourier measures with a spectral gap | [Signed gap separator](#signed-fourier-gap-separation) | Precise measure class; project imports |
| Turn Laplace jets into finite Gram bounds | [Confluent Laplace certificates](#confluent-laplace-jet-certificates) | Generic analytic core; source applications bundled |
| Bound the actual finite source atom independently of dimension | [Native atom budget](#dimension-free-native-source-atom-bound) | Source-specific |
| Compare raw and filtered causal approximation | [Native causal certificates](#native-causal-approximation-and-filtered-certificates) | Source-specific |
| Audit research claims, runs and bounded searches | [Research infrastructure](#research-infrastructure) | Project contracts; adaptation required |

## What “reusable” means here

**Generic statement** means the theorem can be instantiated without a zeta-zero assumption. It does not mean its current file has a small dependency closure. **Source-specific result** retains the actual CCM or native causal source and its normalization. **Research infrastructure** operates on declared contracts, source identities and evidence records; it does not establish the mathematics described in those records.

“Mathlib-only imports” means the listed source file imports no project module. It is a good extraction candidate, but has not been packaged or compatibility-tested as a separate library. “Project imports” means the named module is the smallest practical import identified here; it may bring a large transitive development. Import the file indicated by each entry using its dotted path without `.lean`, for example:

```lean
import Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra

#check Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra.Observations.value_le_iff_cover
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra.Observations.value_le_iff_cover
```

An import and `#check` locate an existing constant. For an independent consumer, reconstruct the full intended type, check the theorem against that type, inspect axioms, and record the exact source and compiler. The [formalization guide](RESULTS_AND_FORMALIZATION.md#formal-source-and-consumer-entry-points) links existing consumers. The scope summaries below retain the important hypotheses; the linked Lean type remains authoritative.

## Finite algebra and certificates

### Explicit Gram witness

**Problem and result.** For real finite vectors $x,y$, define

$$
\Delta=\|x\|^2\|y\|^2-\langle x,y\rangle^2,
\qquad w=\|x\|^2y-\langle x,y\rangle x.
$$

For $B=c(xx^T-yy^T)$, the identity $w^TBw=-c\Delta^2$ supplies a denominator-free negative witness when $c>0$ and $\Delta\ne0$. It works without diagonalizing $B$.

**Source and inputs.** Import [ProbeGramNegativity](../Zeta23/ExceptionalZero/ProbeGramNegativity.lean), namespace `Zeta23.ExceptionalZero`. Inspect `pairBlock`, `gramDet`, `orthoWitness`, `dotProduct_pairBlock_orthoWitness` and `dotProduct_pairBlock_orthoWitness_neg`. The Lean statement uses a finite index type and complex-coordinate vectors fixed by conjugation, encoding real vectors. The coefficient sign and nonzero Gram determinant are explicit premises.

**Reuse and limits.** Generic finite algebra with project imports (`ZeroSide` and exceptional-zero definitions). A new application supplies the actual signed block and its transverse vectors. This witness certifies that block; adding other terms can change its energy. For the normalized witness, the energy is $-c\Delta/\|x\|^2$, which is a different formula from the unnormalized identity above. See [A43](RESULTS_AND_FORMALIZATION.md#a43) and the [worked Gram example](EXAMPLES.md#gram-witness). This guide did not locate a separate small standalone consumer for the generic identity; its proof is in the source module.

### Codimension-one matrix completion

**Problem and result.** A finite complex symmetric matrix whose bilinear form vanishes on the specified zero-sum test space has the form $A=\mathbf1 a^T+a\mathbf1^T$, hence rank at most two. The basis-difference version reduces the input to an explicit finite family of tests about a chosen pivot.

**Source and inputs.** Import [CodimOneMatrixCompletion](../Zeta23/CCM/CodimOneMatrixCompletion.lean), namespace `Zeta23.CCM`. The endpoints are `codimOneMatrixCompletion_of_basisDiff` and `rank_codimOneMatrixCompletion_of_basisDiff_le_two`. Supply the finite index type, pivot, transpose symmetry and vanishing pairings on the declared real basis-difference probes. This is a symmetric bilinear statement, so a Hermitian application needs the appropriate conversion.

**Reuse and limits.** Generic statement with the heavier `DictionaryAnalysis` import. [DictionaryZeroSideCompletion](../Zeta23/CCM/DictionaryZeroSideCompletion.lean) is a source-specific consumer. The rank-one scalar-defect conclusion in [A42](RESULTS_AND_FORMALIZATION.md#a42) uses additional dictionary and diagonal information; it is stronger than this abstract rank-two theorem. A possible new use is reconstructing a matrix known only on a conserved-sum subspace, after proving the same vanishing hypotheses.

### Shifted-factor positivity certificate

**Problem and result.** An approximate factor $R$ can certify a strict quadratic-form lower bound for an exact real matrix $A$:

$$
0<\tau,\qquad \|A-\tau I-RR^T\|_F^2<\tau^2
\quad\Longrightarrow\quad x^TAx>0\quad(x\ne0).
$$

**Source and inputs.** Import [FiniteCertificateSoundness](../Zeta23/OPICARound4/ArithmeticFrontier/FiniteCertificateSoundness.lean), namespace `Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness`. Use `posDef_of_shifted_factor`; `quad`, `froSq` and `normSq` define the exact finite quantities. No matrix-symmetry premise is needed for this quadratic-form conclusion. `not_nonneg_of_negative_witness` gives the opposite certificate, and `pencil_checkpoint_of_posDef` consumes a positive pencil checkpoint.

**Reuse and limits.** Generic, with Mathlib-only imports. The strict positive shift is essential: `shifted_factor_requires_positive_shift` records a counterexample to omitting it. A numerical implementation must independently prove that its interval or rational data enclose the intended matrix and bound the Frobenius residual. The arithmetic-frontier native enclosure bridge remains a separate obligation; a floating-point factorization is not this theorem's premise. The [positivity example](EXAMPLES.md#positivity-certificate) shows a small exact instance. See [N03 in the later-source map](RESULTS_AND_FORMALIZATION.md#later-source-and-research-records) for evidence scope.

### Source-column core and leakage

**Problem and result.** A lower bound on a selected subspace can be lifted to the full space if coupling to its entire orthogonal complement is controlled. For a self-adjoint $H$, an orthogonally complemented subspace $S$, and $0\le\eta\le\varepsilon/4$, `core_shift_certificate` combines

$$
|\langle Hx,q\rangle|\le\eta\|x\|\|q\|
\quad(x\in E,\ q\in S^\perp)
$$

with the core bound $\operatorname{Re}\langle Hp,p\rangle\ge-11\varepsilon\|p\|^2/12$ to obtain $\operatorname{Re}\langle Hv,v\rangle\ge-\varepsilon\|v\|^2$ for every $v$.

**Source and inputs.** Import [SourceColumnCore](../Zeta23/OPICARound4/ArithmeticFrontier/SourceColumnCore.lean), namespace `Zeta23.OPICARound4.ArithmeticFrontier`. `CoreLeakageBound` quantifies over every ambient $x$, not only $x\in S$. `core_shift_certificate_of_columns` uses a finite-dimensional complex inner-product space and any linear column map $C$; the bound is in the physical norm $\|Cc\|^2$. Thus the coordinate Gram $C^*C$ must be retained if the columns are nonorthogonal.

**Reuse and limits.** Generic, with a Mathlib projection import. `core_witness_transport` also projects an actual negative trial with loss $3\eta$, assuming $3\eta<d$; it does not identify the projection with a ground eigenvector. [Carriers validation](../Zeta23/OPICARound4/ArithmeticFrontier/Validation/Carriers.lean) and [SourceColumnTrace](../Zeta23/OPICARound4/ArithmeticFrontier/SourceColumnTrace.lean) provide consumers. A new application must prove both leakage and the core inequality. The theorem does not manufacture either premise.

### Finite weighted Gram algebra

**Problem and result.** Expand a weighted energy under a linear combination, or express a two-column Gram determinant as a sum of squared minors. These identities retain the weights exactly:

$$
2\big(E(l)E(h)-C(l,h)^2\big)
=\sum_{i,j\in s}w_iw_j(l_ih_j-l_jh_i)^2.
$$

**Source and inputs.** Import [FiniteWeightedGram](../Zeta23/OPICARound6/PrimeFactorPaths/FiniteWeightedGram.lean), namespace `Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram`. Use `energy`, `cross`, `signed_energy`, `ordered_minors` and `determinant_nonneg`. The algebraic identities allow arbitrary real weights on a finite set. The determinant inequality separately requires $w_i\ge0$ on that set.

**Reuse and limits.** Generic, Mathlib-only, with independently stated type and axiom consumers in [Verify](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean). This is suitable finite algebra for weighted least squares or energy comparisons after matching definitions. It supplies no positive-definiteness claim for signed weights and no asymptotic estimate for a growing arithmetic family.

### Positive-part selector stability

**Problem and result.** Bound the change in a squared positive-part energy when the underlying observations change. If $|u|,|v|\le H$, then

$$
|[u]_+^2-[v]_+^2|\le2H|u-v|.
$$

**Source and inputs.** Import [FiniteSelectorEnergy](../Zeta23/OPICARound6/PrimeFactorPaths/FiniteSelectorEnergy.lean), namespace `Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy`. `posSq_sub_le` is the scalar estimate. `signed_weight_energy_comparison` retains arbitrary real weights, their absolute values in the error budget, a polarity with absolute value one, and an individual height bound at each finite index. `weighted_energy_comparison` and `weighted_sq_distance_le` specialize the nonnegative-weight case.

**Reuse and limits.** Generic, Mathlib-only, consumed in [Verify](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean). This can transport a finite approximation into a selector-energy estimate once the heights and errors have been supplied. Dropping height factors or replacing a signed selector with an absolute-value observation changes the statement. No uniform native height or growing-horizon error bound is supplied by this lemma.

### Opposed-sign products

**Problem and result.** Two signed observations admit the exact algebraic reduction

$$
4[e]_+[-o]_+=\max\{[e-o]_+^2-(e+o)^2,0\},
$$

and the remaining discrepancy lies between zero and $(e+o)^2$. This exposes precisely which scalar term must be controlled to replace a sign-selective energy by an opposed-sign product.

**Source and inputs.** Import [ParityDeficitProduct](../Zeta23/OPICARound6/PrimeFactorPaths/ParityDeficitProduct.lean), namespace `Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct`, for `quadrant_remainder`, `weighted_absolute_remainder` and `forced_coefficient`. Import [StoppingAlgebra](../Zeta23/OPICARound6/PrimeFactorPaths/StoppingAlgebra.lean), namespace `Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra`, for `opposed_eq_charge_minus_discrepancy`. Scalar identities hold for all real $e,o$; the weighted remainder estimate requires nonnegative weights.

**Reuse and limits.** Both files have Mathlib-only imports and consumers in [Verify](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean). The coefficient four is forced by the scalar identity. In another application, prove the discrepancy bound and preserve the sign pairing. In the repository, the required arithmetic upper bound remains open; the algebraic reduction is not that upper bound.

### Finite stopping-tree duality

**Problem and result.** In a finite binary observation tree, compute the best achievable minimum along a path and compare it with a complete cover by low-cost stopping nodes. The definitions account for an eligibility delay $k$. At each eligible fork the value is `min cost (max left right)`; during the delay it is the maximum of the child values.

**Source and inputs.** Import [StoppingAlgebra](../Zeta23/OPICARound6/PrimeFactorPaths/StoppingAlgebra.lean), namespace `Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra`. `Observations` stores real costs. `Observations.value_le_iff_cover`, `Observations.lt_value_iff_highPath` and `Observations.no_cover_iff_highPath` prove the cover/path alternatives for every finite tree, real threshold and natural delay. The separate integer-valued `Charges.branch_of_total` produces a branch meeting the depth-scaled charge threshold.

**Reuse and limits.** Generic, Mathlib-only, consumed in [Verify](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean). The [stopping-tree example](EXAMPLES.md#stopping-tree) computes a small case. Leaf and delay behavior are part of the recursive definition and must match any application. The theorem is finite; infinite survival, complete arithmetic covers and a uniform bound across horizons require further arguments.

### Inherited Hermitian linear algebra

**Problem and result.** The inherited seven-file linear-algebra development supplies positive and negative parts of Hermitian matrices, positive index, inertia comparisons, trace inequalities and perturbation bounds. For example, `finrank_le_posIndex_of_posDefOn` bounds the dimension of any subspace on which a Hermitian quadratic form is positive definite.

**Source and inputs.** Start at [Sylvester](../Zeta23/LinAlg/Sylvester.lean), namespace `RHLinalg`, and its [LinAlg directory](../Zeta23/LinAlg). The Sylvester result uses a finite matrix over an `RCLike` field, Hermitian symmetry and the explicit `PosDefOn` condition on the subspace. `posDefOn_range_hermPosPart` gives the corresponding positive-part construction.

**Reuse and attribution.** Generic and already organized as a separate source family. The file headers attribute this development to the upstream paper's authors and Anthropic; it is not an original contribution of this fork. Retain those headers, [LICENSE](../LICENSE), [NOTICE](../NOTICE) and the account in [UPSTREAM_README](../UPSTREAM_README.md). Check the original theorem consumers and pinned build before extracting it into another development.

## Spectral and local analytic tools

### Kernel-safe Schur response

**Problem and result.** A singular self-adjoint block can still have a canonical response to a vector in its range. Restricting the response to the orthogonal complement of the kernel selects the unique permitted preimage and gives an exact one-shell energy identity.

**Source and inputs.** Import [KernelSafeSchur](../Zeta23/OPICARound3/KernelSafeSchur.lean), namespace `Zeta23.OPICARound3`. `kernelSafeResponse_spec` requires $b\in\operatorname{range}A$; `kernel_projection_zero_iff_range` identifies this range condition for a symmetric finite-dimensional operator. `oneShellSchurScalar_energy` uses an isometric embedding, the compressed block and the explicit source. Retain the full finite-dimensional complex inner-product-space and symmetry assumptions from the type.

**Reuse and limits.** The operator statement is generic, but it imports `CCM.IsometricDetectorSchur`. A new application must establish range membership; evaluating a totalized inverse at a singular point does not do that. The [singular Schur example](EXAMPLES.md#singular-schur) contrasts a permitted response with a source outside the range. See [A07](RESULTS_AND_FORMALIZATION.md#a07) for the later branch-complete ground analysis, which treats the remaining cases separately.

### Abstract third-order Schur calculus

**Problem and result.** Differentiate $a(t)-\langle b(t),H(t)^{-1}b(t)\rangle$ three times at a point where $b(t_0)=0$. The response formulation packages the derivatives through the solved first response and retains all operator-variation terms. A separate one-sided theorem obtains the necessary third-derivative sign when the value and first two derivatives vanish and the expression is negative arbitrarily close to the base point from the right.

**Source and inputs.** Import [AbstractCubicSchur](../Zeta23/CCM/AbstractCubicSchur.lean), namespace `Zeta23.CCM`. Use `cubic_schur_third_deriv`, `cubic_schur_third_deriv_response` and `cubic_schur_third_nonpos_of_right_negative`. The theorem is over a complete real inner-product space with the stated derivative chains, an invertible operator at the base point, vanishing $b(t_0)$, and the symmetry assumptions required by the response identity.

**Reuse and limits.** Generic, Mathlib-only. [CanonicalOneStepDomination](../Zeta23/CCM/CanonicalOneStepDomination.lean) is a project application. A new perturbation problem must prove its derivative hypotheses and inverse-domain conditions. The necessary sign is not an a priori barrier to crossing, and a singular-base-point problem belongs to the preceding component or a different calculus.

### Meromorphic frequency separation

**Problem and result.** The finite sum $\sum_i a_i(z)\exp(i c_i/z)$, with distinct real frequencies $c_i$ and coefficient germs meromorphic at zero, cannot vanish on a punctured neighborhood of zero if at least one coefficient germ is nonzero there. The proof compares exponential growth on an imaginary reciprocal ray with the polynomial growth allowed by a meromorphic germ. The reciprocal variable in the exponent is essential to this statement.

**Source and inputs.** Import [MeromorphicFrequencyIndependence](../Zeta23/OPICARound4/RegularCells/MeromorphicFrequencyIndependence.lean), namespace `Zeta23.OPICARound4.RegularCells`. Use `meromorphic_imaginaryReciprocal_isBigO_pow`, `meromorphic_imaginaryReciprocal_div_exp_tendsto_zero`, `meromorphic_frequency_ray_max_nonzero` and `meromorphic_frequency_germ_nonzero`. Supply the finite frequency set, injective real frequencies on it, coefficient meromorphicity at zero and a nonzero coefficient germ.

**Reuse and limits.** Generic, Mathlib-only; [PrimeLaurentNonidentity](../Zeta23/OPICARound4/RegularCells/PrimeLaurentNonidentity.lean) and [FinitePrimeLaurentAlgebra](../Zeta23/OPICARound4/RegularCells/FinitePrimeLaurentAlgebra.lean) are source applications. The coefficient class matters: arbitrary essential singularities could absorb the exponential frequencies. This result supplies nonidentity, not a quantitative lower bound or a uniform spectral gap. See [A01](RESULTS_AND_FORMALIZATION.md#a01).

### Signed spectral response and Abel summation

**Problem and result.** Keep the signs of residues in $F(\lambda)=\sum_i r_i/(\mu_i-\lambda)$. Differentiation retains the signed numerator; below a common lower spectral bound $b$,

$$
(b-\lambda)F(\lambda)\le
\frac{\sum_i|r_i|+\sum_i r_i}{2}.
$$

**Source and inputs.** Import [SignedSpectral](../Zeta23/OPICARound4/SignedSpectral.lean), namespace `Zeta23.OPICARound4`. `signed_response_hasDerivAt` requires avoidance of every eigenvalue. `signed_resolvent_upper` requires $\lambda<b\le\mu_i$. `signed_response_lt_one_of_budget` adds the strict positive-mass budget below $b-\lambda$. `signed_prefix_abel` is the finite summation-by-parts identity; `signed_prefix_nonnegative` requires nonnegative prefixes, a decreasing kernel and the nonnegative endpoint term.

**Reuse and limits.** The core is generic and Mathlib-only. [IntegrationSource validation](../Zeta23/OPICARound4/Validation/IntegrationSource.lean) includes source consumers. Repeated eigenspaces should be grouped through their actual projector residues; [VisibilityRigidity](../Zeta23/OPICARound4/VisibilityRigidity.lean) supplies `grouped_residue_zero_iff_input_or_output_invisible` for the project's visibility setup. Signed residues do not imply monotonicity. The strict budget is a premise to prove in a new application, and is the missing arithmetic input on this route. See [A02](RESULTS_AND_FORMALIZATION.md#a02).

### Analytic germs and finite jets

**Problem and result.** Quotient actual analytic germs by a multiplier with a known zero order, and identify the quotient with finite Taylor data. Membership in the coordinate-power ideal is equivalent to vanishing lower jets.

**Source and inputs.** Import [LocalQuotients](../Zeta23/OPICA/LocalQuotients.lean), namespace `Zeta23.OPICA`. Inspect `zero_ideal_eq_coordinate_power`, `coordinate_ideal_iff_lower_jets_zero` and `truncated_taylor_quotient_equiv`, together with `MultiplierOrderData` in [LocalData](../Zeta23/OPICA/LocalData.lean). The objects are analytic germs at a specified complex center, with an explicitly controlled multiplier zero and its order.

**Reuse and limits.** The local analytic construction is generic but remains in the OPICA source family. [OPICA validation](../Zeta23/OPICA/Validation.lean) and [follow-up validation](../Zeta23/OPICAFollowup/Validation.lean) provide consumers. A new application must supply actual analyticity and the order data. Passing to a meromorphic field would make a nonzero multiplier invertible and destroy the intended quotient. See the jet-related [A15](RESULTS_AND_FORMALIZATION.md#a15) for the source application, whose global Fourier identities require additional hypotheses.

## Harmonic analysis and causal approximation

### Boundary-flat approximation and centered extension

**Problem and result.** Approximate an admissible compactly supported test by a finite Fourier construction while imposing three exact moment constraints. Extend the centered coefficient vector to a larger cutoff without changing its frequencies, moments, localized test or canonical quadratic value.

**Source and inputs.** The practical imports are [BoundaryFlatProjection](../Zeta23/CCM/BoundaryFlatProjection.lean), [BoundaryFlatApproximation](../Zeta23/CCM/BoundaryFlatApproximation.lean), [LocalizedFourierApproximation](../Zeta23/CCM/LocalizedFourierApproximation.lean) and [NestedFinite](../Zeta23/CCM/NestedFinite.lean), namespace `Zeta23.CCM`. Start with `exists_boundaryFlatFinite_WCONT_approx`, then `centeredEmbedding`, `centeredMoment_centeredZeroExtend`, `localizedFiniteVector_centeredZeroExtend` and `quadraticForm_canonicalSourceMatrix_centeredZeroExtend`.

**Reuse and limits.** This is a source-adapted approximation framework with substantial project imports. Preserve positive fixed aperture, strict interior support, the required $C^2$ regularity and the stated continuity topology. A three-mode algebraic correction alone does not establish a legal globally $C^2$ test. Constants proved for fixed aperture are not automatically uniform in aperture. Extension follows centered indices, not a prefix insertion. [FiniteNegativeObstruction](../Zeta23/ExceptionalZero/FiniteNegativeObstruction.lean) is a consumer; [A40](RESULTS_AND_FORMALIZATION.md#a40) explains the conditional finite detector. A different kernel or moment family needs its own approximation and continuity proofs.

### Signed Fourier gap separation

**Problem and result.** The sharp-gap separator proves that a Fourier-self-dual signed measure with the specified gap and off-lattice nonnegativity must vanish. Dropping the off-lattice nonnegativity premise, the companion budget instead makes positive mass in a separated region pay a quantitative amount of negative mass off the lattice. Both conclusions retain the positive and negative Jordan parts and their growth conditions.

**Source and inputs.** Import [SignedHeatSeparator](../Zeta23/OPICA/SignedHeatSeparator.lean), namespace `Zeta23.OPICA`. Inspect `signed_sharp_gap_separator`, `signed_gap_negative_weighted_mass_budget` and `signed_gap_negative_mass_budget`. Their common input is the defined locally finite real signed-measure class with linear total-variation growth, Fourier self-duality and the unit gap for both Jordan parts. The separator adds `OffLatticeNonnegative`. The quantitative budget instead uses a region with parameters $1\le R$ and $0<d\le1/2$; it also handles infinite total negative mass.

**Reuse and limits.** Harmonic-analysis theorem for a precise measure class, with project imports. The consumers are in [OPICA validation](../Zeta23/OPICA/Validation.lean). A possible new application is separating signed Fourier measures under comparable gap constraints. It must establish every measure and transform hypothesis; the result cannot be applied to an arbitrary formal distribution or a profile obtained by deleting a source term. [A24](RESULTS_AND_FORMALIZATION.md#a24) and [A23](RESULTS_AND_FORMALIZATION.md#a23) distinguish the exact-gap theorem from near-gap compactness and variation-escape consequences.

### Confluent Laplace-jet certificates

**Problem and result.** Represent finitely many Laplace derivative observations by Hilbert-space vectors, compute their Gram matrix and determinant, and turn the orthogonal projection onto their span into a lower bound on an approximation error.

**Source and inputs.** Import [DualCertificates](../Zeta23/OPICARound2/DualCertificates.lean), namespace `Zeta23.OPICARound2`. The core endpoints are `laplaceJetGram_posDef`, `laplaceJetGram_confluent_determinant`, `laplace_jet_gram`, `dualJetProjection_norm_sq` and `dualJetProjection_le_infDist`. Nodes lie in the open right half-plane; distinct nodes and their prescribed finite multiplicities determine the jet family. Positive definiteness requires the node-injectivity hypothesis.

**Reuse and limits.** Generic analytic and linear-algebra content is bundled with the causal source and actual-zero applications. [DualCertificates validation](../Zeta23/OPICARound2/Validation/DualCertificates.lean) reconstructs consumer types. `laplaceJetGram_not_posDef_of_repeated_nodes` records the repeated-node boundary; repeated observations cannot be treated as independent constraints. A new approximation problem must supply the actual annihilation/orthogonality conditions before using the projection as a dual bound. [A10](RESULTS_AND_FORMALIZATION.md#a10) distinguishes the formal Gram core from Paper XVII's further conjugate-pair compositions.

### Dimension-free native source-atom bound

**Problem and result.** Bound the norm of the actual finite source atom by two, uniformly in cutoff dimension, and retain a mixed inner-product bound for source pairings.

**Source and inputs.** Import [NativeSourceBudget](../Zeta23/OPICARound4/NativeSourceBudget.lean), namespace `Zeta23.OPICARound4`. `nativeSourceAtom_norm_le_two`, `nativeSourceAtom_apply_norm` and `native_source_mixed_norm` apply for the specified frequency parameter $0\le\omega\le1$, with the half-window convention encoded in the source. [IntegrationSource validation](../Zeta23/OPICARound4/Validation/IntegrationSource.lean) contains consumers.

**Reuse and limits.** This is a source-specific estimate with project imports. A new application can copy the proof pattern only after identifying an operator with the same structure. Uniformity in cutoff $K$ does not give uniform control of a resolvent, an arbitrary source row or aperture dependence. Source-exchange concentration adds separate discrepancy assumptions. See [A03](RESULTS_AND_FORMALIZATION.md#a03).

### Native causal approximation and filtered certificates

**Problem and result.** Build Gram and Schur observations from one fixed compact causal source, retain the error introduced by truncation, and certify a small filtered approximation through exact bounds. This family is also a useful record of why a good filtered trial can be a very poor raw trial.

**Source and inputs.** Start with [ProbeGram](../Zeta23/OPICARound2/ProbeGram.lean), [FixedFilter](../Zeta23/OPICARound2/FixedFilter.lean), [TruncationControls](../Zeta23/OPICARound2/TruncationControls.lean) and [FiniteFilteredBaseline](../Zeta23/OPICARound2/FiniteFilteredBaseline.lean), namespace `Zeta23.OPICARound2`. Inspect `probe_schur_error` and `filtered_four_column_region_certificate`. The certificate retains the original compact source at scale $1/4096$, its prescribed causal filter, the coefficient vector $(1,-1,-1,-2/3)$, and the exact filtered $L^2$ error convention.

**Reuse and limits.** Source-specific and substantially coupled to the native analytic construction. [FiniteFilteredBaseline validation](../Zeta23/OPICARound2/Validation/FiniteFilteredBaseline.lean) is the formal consumer. The [raw/filtered walkthrough](EXAMPLES.md#raw-filtered) gives the actual finite constants and distinguishes Lean endpoints from Paper XVI's manuscript integration. The filtered certificate excludes only its stated small rectangle, already within the known zero-free verification region discussed in the manuscript. It proves no raw residual convergence or universal bound. A new source/filter pair needs a new transform, causal identity, truncation proof, metric and certificate.

## Research infrastructure

### Evidence-bound research execution

**Problem and output.** Record what a run actually used, keep the declared claim and proof obligations separate from the run outcome, and expose the difference between a bounded search result, a checked theorem and full release acceptance. These patterns can help another proof or scientific-computing project maintain an inspectable research history.

**Source and inputs.** Begin with [FRAMEWORKS](FRAMEWORKS.md) and the [composition package](../research/RHRC/integration/opica_composition/README.md). Relevant implementation entry points include [journal.py](../research/RHRC/integration/opica_composition/journal.py), [evidence.py](../research/RHRC/integration/opica_composition/evidence.py), [contracts.py](../research/RHRC/integration/opica_composition/contracts.py), [countermodels.py](../research/RHRC/integration/opica_composition/countermodels.py) and [composition_search.py](../research/RHRC/integration/opica_composition/composition_search.py). The [graph guide](../research/RHRC/graph/README.md) describes graph extraction and claim navigation.

| Mechanism | Required input | Inspectable output | Adaptation needed |
| --- | --- | --- | --- |
| Journal and evidence binding | Exact source identity, event schema, tool outcome and declared scope | Run/event history tied to its inputs | Replace project contracts, storage/provider assumptions and acceptance policy |
| Independent theorem consumers | Intended full theorem type, import path and pinned compiler | Type check and axiom report for that source | Reconstruct the new claim's actual type; checking only its name is insufficient |
| Source-scope validation | Reviewed path/blob policy and exact comparison base | Accepted exact tree or explicit mismatches | Establish a new policy; do not broadly exempt inconvenient files |
| Bounded composition search | Finite candidate menu, rule semantics and explicit obligations | Candidates, rejected steps and remaining premises | Define sound application rules; finite exhaustion does not cover unenumerated ideas |
| Negative controls and countermodels | Precisely stated proposed inference and test domain | A counterexample or bounded diagnostic | Prove or check the countermodel's connection to the intended statement |
| Claim/dependency graph | Source nodes and typed edge relations | Navigation and dependency views | Preserve the distinction between import, logical implication, provenance and proposed route |

**Reuse and limits.** These are research infrastructure components, not an installable generic service. Some runtime paths depend on particular host/provider versions and historical JSON schemas. The [infrastructure example](EXAMPLES.md#infrastructure-replay) exercises a bounded local operation; the [reproduction guide](REPRODUCIBILITY.md) distinguishes that from governed acceptance. A green wrapper, successful proposal generation or generated graph never discharges an open mathematical premise.

## Adapting a component responsibly

For a new application, first choose an exact declaration and read its full type. Record the new object's source, domain, normalization, norm, quantifiers and sign convention beside the old ones. Then provide a small consumer using the narrow module import and independently stated target type. For generic extraction, preserve source provenance and check the extracted import closure under the chosen pinned toolchain. For a source-specific result, prove the new source bridge before using the old downstream estimate.

The existing [examples](EXAMPLES.md) demonstrate the intended scale of a first consumer. Suggested uses in this catalogue are possible applications, not completed transfers. The final arithmetic-frontier and Round 6 source restrictions remain open even where the finite transfer lemma is proved.

Retain [LICENSE](../LICENSE), [NOTICE](../NOTICE), applicable file headers and upstream attribution. Cite the exact code revision and the particular manuscript result separately; [citation instructions](REPRODUCIBILITY.md#citation) explain the distinction. None of the reusable results is a blanket claim that the accompanying PDF, the whole repository or the RH attempt has been fully verified.
