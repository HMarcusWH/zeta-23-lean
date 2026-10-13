# Post-285 research report (Steps 18–120: M31, M38, M55, M65–M77)

Terminal claim: **RH_OPEN**. This report is the M77 integration note for the
post-285 branch. It sorts every result into one of five classes:

- **PROVED**: a Lean root in `PROOF_ROOTS.json` that compiles with only
  `propext`, `Classical.choice` and `Quot.sound`. It stays `PROVED_PENDING_CI`
  until a PR head that carries it passes CI; the ledgers then record that
  head's receipt.
- **DERIVED**: a correct argument on paper that Lean has not checked.
- **EXPERIMENTAL SIGNAL**: floating-point or interval evidence. It never counts
  as a proof.
- **LEAD**: a concrete next step that looks viable.
- **OPEN**: no proof, and no claim of one.

The machine-readable versions are:
- `STEP_STATUS_MATRIX.json` (Steps 18–120);
- `OPEN_OBLIGATIONS.json` (M31, M32, M38, M55, M65, M66, M70–M77 plus
  cross-references into the post-284 ledger);
- `PROOF_ROOTS.json`;
- `EXPERIMENT_DISPOSITIONS.json`;
- `WORKFLOW_HARVEST.json`.

`build_post285_ledgers.py --write` regenerates all five, and
`check_post285_ledgers.py` is the CI firewall that keeps them current.

**Endpoint correction (2026-10-13, PR #290).** The historical M51 statement
below says `[1/400, log 16]`, but the actual legacy producer clips at
`U = 2772588722239781/10^15 < log 16`. Its 1,310-interval evidence establishes
only the finite rational range `[1/400, U]`. The remaining interval
`(U, log 16]` stays OPEN for this receipt and is now recorded as
`M51_K2_EXACT_LOG16_ENDPOINT` in the live ledgers. The original observations
remain below for provenance; this correction governs their scope. This legacy
evidence does not validate the invalidated unguarded post287 transcript. See
[the migration record](../post287/LEGACY_M51_ENDPOINT_MIGRATION.md).

## 1. PROVED in this PR

| Package | Module | Main roots | Steps |
|---|---|---|---|
| M74 | `CanonicalSecularResolvent` | `canonical_rankOneIntertwining`, `canonical_apply_resolventRay`, `canonical_det_eq`, `canonical_resolventRay_contact_iff`, `canonical_ker_eq_span_of_contact`, `canonical_ward_identity`, `canonicalResolventGamma_pos`, `canonical_momentFour_resolventRay`, `canonical_contact_phase`, `canonical_re_conj_mul_momentFour_pos_of_approx` | 49–52, 97, 111, 112, 116–118 |
| M70 | `CanonicalSourceExcursion` | `sourceEnergyRe_excursions_of_zeroSum` | 108 |
| M73 | `CanonicalCenteredIndexPoincare` | `centeredHalfShiftMass_eq`, `sum_normSq_le_four_mul`, `parityGap_mul_norm_sq_le_four_mul_source_mul_momentFour` | 89, 90, 115 |
| M75 | `CanonicalSourcePrimeSampling` | `norm_sourceEntry_sub_le`, `exists_sourceNegativeWindow`, `exists_prime_physicalSecondPrimeTerm_pos_and_two_neg` | 119, 120 |
| M72 | `CanonicalSourceSpectralFlow` | `exists_sourceDegenerate_of_half_neg`, `parityBoundaryFlat_sourceDegenerate` | 45, 110 (first passage) |
| M26–M28, M14 | `CanonicalShiftedSecular` | `canonical_shifted_det_eq`, `canonical_shifted_eigen_iff`, `canonical_finrank_eigenspace_le_one`, `canonical_contact_overlap`, `canonical_contact_overlap_norm_le`, `canonical_odd_ker_le_span`, `canonical_odd_contact_iff`, `canonical_odd_det_eq`, `canonical_tied_contact_orthogonality` | 58, 59 (simplicity), 60 (identity), 64; branch analysis |
| M28 | `CanonicalContactOverlapSign` | `exists_det_eq_ofReal_pos_of_coercive`, `secular_resolvent_slope_pos`, `secular_overlap_pos`, `canonical_contact_overlap_pos` | 60 (sign) |
| M65 | `CanonicalPrimeFreeF04` | `hasDerivAt_integral_moving_upper`, `matrixRealEnergy_canonical_eq_regularized`, `hasDerivAt_wCorrection`, `hasDerivAt_primeFreeFirstChannel`, `productionContactF04DerivativeAuthority_of_lt_log_two` | 21, 24, 27, 93, 101, 105 on `(0, log 2)` |
| M06/M53 (global F04) | `CanonicalGlobalF04` | `hasDerivAt_ite_le`, `productionArithmeticRealValue_eq_channels_sum`, `hasDerivAt_primeFirstChannel`, `productionContactF04DerivativeAuthority_of_pos`, `canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos` | 21, 24, 27, 93, 101, 105 at every `L > 0` |
| M66, Step 103, F07 | `CanonicalLocalBirdfishie` | `productionSecondDerivativePhysicalValue_eq_neg_primeFreeSecondTest`, `productionContactEulerCurvature_le`, `productionContactEulerCurvature_neg`, `GeneratedStrictEvenContact.secondPhysicalValue_eq_two_mul_responseCost`, `GeneratedStrictEvenContact.fresh_of_lt_primeFreeRadius`, `GeneratedStrictEvenContact.completed_production_frontier_unconditional` | 19, 27, 74, 102–104 |
| M31 (conditional barrier) | `CanonicalSecularGronwall` | `gronwall_lower_bound`, `gronwall_pos`, `evenCompressedCanonical_det_eq_zero_of_bottom_eq_zero`, `canonical_evenBottom_pos_of_gronwall` | 66 |
| M55, M38 | `CanonicalWeightedChebyshevAbel` | `psi_sub_self_eq_weightedRemainder`, `abs_psi_sub_self_sub_one_le`, `isGreatest_weightedRemainder`, `isGLB_weightedRemainder` | 75, 96 |
| M71 | `CanonicalAndreiefInertia` | `det_integral_eq_integral_det_mul_prod`, `integral_det_mul_prod_eq`, `andreiefSign_mul_det_gram_pos`, `jacobi_alternating_split`, `sourceSesq_eq_convolution`, `sourceSesq_evenCarrier_cosPow`, `sourceSesq_oddCarrier_cosPow`, `evenBoundaryFlat_source_exactInertia`, `oddBoundaryFlat_source_exactInertia`, `parityBoundaryFlat_source_indefinite` | 44, 109 |
| M27 | `CanonicalAlternatingRootSlopes` | `det_sub_smul_eq_prod_eigenvalues`, `one_sub_canonicalSecularFunction_eq`, `canonical_secular_hasDerivAt_root`, `canonical_secular_root_slope_sign` | 59 (root slopes) |
| M08 (abstract) | `AbstractCubicSchur` | `cubic_schur_third_deriv`, `cubic_schur_third_deriv_response`, `cubic_schur_third_nonpos_of_right_negative` | 34 (abstract part) |
| M09, M03 (staircase) | `WeightedRemainderIdentity` | `canonicalPolePrimeDiscrepancy_eq_fixedStaircase`, `matrixRealEnergy_pole_sub_prime_eq_fixedStaircase`, `regularizedCompletePhysicalRHS_eq_weightedRemainder`, `productionArithmeticRealValue_eq_weightedRemainder`, `productionArithmeticRealValue_sq_mul_indexEnergy_eq_weightedRemainder`, `GeneratedStrictEvenContact.indexEnergyValue_eq_neg_responseCost`, `GeneratedStrictEvenContact.weightedRemainder_balance` | 32; M03 staircase |
| M45 | `CanonicalSourceOddEndpointQuantitative` | `re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat`, `re_quadraticForm_sourceMatrix_neg_of_mem_oddBoundaryFlat`, `re_quadraticForm_sourceMatrix_aperture_le_of_mem_oddBoundaryFlat`, `sourceAtomRealEnergy_le_of_le_oddEndpointAngle`, `abs_sin_sub_sub_cube_le`, `sourceOddTaylorConstant_sq` | 82 |
| M49 | `CanonicalRecentPrimeSecondVariation` | `sourceAtomRealEnergy_index_le_of_contactAngle`, `sourceAtomRealEnergy_index_le_of_contactAngle_coercivity`, `sourceAtomRealEnergy_index_le_of_contactAngle_four`, `primeTerm_ge_of_contactAngle_four` | 84, 90 |
| M50 | `CanonicalContactOlderPrimeBudget` | `GeneratedStrictEvenContact.poleArch_sub_primeSamples_eq`, `GeneratedStrictEvenContact.olderPrimeBudget`, `GeneratedStrictEvenContact.olderPrimeBudget_finite`, `productionContactIndexEnergy_le_of_norm_eq_one`, `primeSourceCoordinate_mem_of_mem_Icc` | 91 |
| M59, M61 | `CanonicalContactSourceOlderPrimeBalance` | `contactSourcePairing_balance`, `contactSourcePairing_nearOld_balance`, `canonicalResolventGamma_le`, `contactSourceMargin_ge`, `contactSourcePairing_older_le`, `contactSourcePairing_zero` | 98 (real pairing), 99 |
| M33, M34 | `CanonicalContactRemainderOscillation` | `sourceAtomRealEnergy_index_signReversal`, `explicitCanonicalSourceMoment_ne_zero_of_parityGap`, `intervalIntegrable_weightedRemainder_exp_mul`, `abs_integral_mul_le_half_oscillation`, `GeneratedStrictEvenContact.remainderOscillation_budget` | 68, 70, 71 |
| M44 | `CanonicalEnteringPrimePhysicalJet` | `productionContactValue_eq_withoutAtom_add_jump`, `enteringPrimePhysicalJump_log_add`, `sourceAtomRealEnergy_seventh_taylor`, `enteringPrimePhysicalJump_seventh_order`, `enteringPrimeLeadingCoefficient_pos`, `enteringPrimePhysicalJump_ge_of_angle`, `enteringPrimePhysicalJump_pos_near_seam` | 81 |
| M29 | `CanonicalSourceResolventDerivatives` | `hasDerivAt_secularRayFamily`, `hasDerivAt_secularScalarFamily`, `hasDerivAt_secularScalarFirst`, `secularScalar_stationary`, `isUnit_canonicalOddFamily`, `canonicalSecularScalar_eq`, `canonicalSecularScalar_hasDerivAt`, `cubicDefectFunctional_contDiffOn`, `cubicDefectFunctional_hasDerivAt`, `canonicalSecularScalar_stationary` | 61, 62 |
| M03 (Laplace) | `SourceRankTwoLaplace` | `integral_exp_neg_half_mul_sourceEntryReal`, `integral_exp_neg_half_mul_sourceEnergy`, `integral_exp_neg_half_mul_sourceEnergy_of_even`, `integral_exp_neg_half_mul_sourceEnergy_of_odd` | M03 (no step row) |

### What these results do not say

- **M74** works for every aperture `L > 0` and `K ≥ 2` where the odd Rayleigh
  bottom is positive. It does not say that a contact exists or that none exists.
  The condition `S_L(x_L) = 1` is equivalent to contact, so it is never used as
  an independent opposite side. `A_L` is the even compressed operator and is
  kept separate from the scalar `𝓐_L`. `D` is not assumed unitary anywhere.
- **M70** is a statement about the source energy `e_{Dz}(ω)` as a function of
  `ω`. It is not a statement about the arithmetic functional.
- **M73** improves the centered-index coercivity constant from `C_K < 5` to
  `4`. Only the upper bound is proved. That `1/4` is sharp is an experimental
  signal.
- **M75** proves that individual prime summands have opposite signs. It does
  not bound their sum. The aperture threshold is `L ≥ π² M_K log 2`, about
  `3.7·10³` at `K = 2`, so the theorem only applies at very large apertures.
- **`CanonicalShiftedSecular`** proves that every even eigenvalue below the odd
  floor is simple, and the exact Step 60 overlap identity
  `⟪x_L, D⁻¹g⟫ · S_L(w_L) = ‖x_L‖²` at an even contact. The alternating root
  slopes are a separate module (M27). The odd-first and tied statements are identities.
  They exclude no branch.
- **`CanonicalContactOverlapSign`** proves that both `S_L(w_L)` and
  `⟪x_L, D⁻¹g⟫` are real and strictly positive at an even contact, given an
  even bottom `≥ 0` and an odd bottom `> 0`. The even-bottom hypothesis is the
  first-crossing geometry. It is assumed, never inferred from `T ≤ 1`. The
  theorem does not say that a contact exists.
- **M65 and global F04** are derivative transport only. They say that the three
  fields of `ProductionContactF04DerivativeAuthority L K` hold for the actual
  canonical even compressed family, at every `L > 0` and every `K`. They give no
  sign and exclude no contact. The single `cCorrection` repair is the one inside
  `canonicalSourceMatrix`; nothing adds it a second time.
- **M66** proves that the Euler-corrected curvature `E'' + (2/L)E'` is strictly
  negative on nonzero even boundary-flat vectors for
  `0 < L < ε_K = 1/(2π²(2K+1)K²)`. So a generated strict-even contact with
  `L* < ε_K` is not stationary, hence fresh-born. This is **possibly vacuous**:
  numerically the even ground is positive on all of `(0, log 2)` for
  `K = 2..16`, so no generated contact is known to lie below `ε_K`. It says
  nothing above `ε_K` and nothing about odd-first, tied or interior branches.
- **Step 103 and the F07 frontier.** At a stationary generated strict-even
  contact, the complete second physical value (pole, archimedean and every
  prime up to `e^{L*}`) equals `2⟨A w, w⟩ ≥ 0` for the stationary response `w`.
  The post-284 frontier theorems that needed an F04 hypothesis now hold without
  it (`*_unconditional`). They show the stationary production remainder is
  strictly positive at every stationary generated strict-even contact.
  Excluding that saturation is OBS-060O, which stays OPEN.
- **M55** is classical, unconditional arithmetic: the exact partial summation
  `ψ(x) − x = 1 + √x R(x) − ½∫₁ˣ R(t)/√t dt` for real `x ≥ 1`, and the transfer
  bound `|ψ(x) − x − 1| ≤ 2M√x` when `|R| ≤ M` on `[1, x]`. It proves no size of
  `R`. A bound `R(x) = O_ε(x^ε)` for every `ε > 0` would be RH-strength, so no
  theorem in this project may take it as a premise.
- **M38** makes the oscillation of `R` on `[1, e^L]` a finite computation: the
  supremum is a maximum over integers, and the infimum is a finite minimum that
  may be only a left limit. It bounds nothing.
- **M31** is a **conditional** barrier. The abstract part is the Grönwall lower
  bound `y(t) ≥ y(a) exp(−∫ₐᵗ C)` for `y' ≥ −C y` with `C` continuous. The
  canonical part says: if the odd bottom is positive on `[L₀, L₁]`, the even
  bottom is positive at `L₀`, and the secular margin `y = 1 − T`
  (`det A_L = det B_L · y`) obeys `y' ≥ −C y`, then the even bottom stays
  positive on `[L₀, L₁]`. The inequality `y' ≥ −C y` is the plan's (67.1), and
  no admissible `C_K` is known (M32, OPEN). The theorem excludes nothing by
  itself, and the start `A_{L₀} ≻ 0` is a separate hypothesis.
- **M72** proves a first degenerate passage on `(1/2, 1)` whenever the
  half-aperture form has a negative vector. The multiplicity count, which needs
  continuous eigenvalue branches, is still OPEN.
- **M71** is about the elementary `sourceMatrix ω` on the even and odd
  boundary-flat carriers. For every `0 < ω ≤ 1/2` and `K ≥ 2` it gives exact
  inertia `(K/2, (K−1)/2, 0)` (even) and `((K−1)/2, K/2, 0)` (odd), with
  nondegeneracy and maximality of the definite dimensions. The bound `ω ≤ 1/2`
  (aperture `a ≤ π`) is used and cannot be dropped: on `(1/2, 1)` the inertia
  changes (M72). The moment-filtered carriers of post-284 M18 are not covered,
  and nothing here concerns the canonical operator or its contacts.
- **M27** is about the secular function `T_L(λ)` at a fixed aperture `L`, for
  real `λ` below the odd Rayleigh bottom. There
  `1 − T_L(λ) = ∏(a_i − λ)/∏(b_k − λ)` over the eigenvalues of `A_L` and `B_L`,
  and at each even eigenvalue `a_j` below the odd floor the slope
  `T_L'(a_j) = ∏_{i≠j}(a_i − a_j)/∏_k(b_k − a_j)` is nonzero with sign
  `(−1)^{#{i : a_i < a_j}}`, so `+, −, +, …` with the roots numbered
  increasingly. It says nothing about `∂_L T_L`, about `T_L` between roots, or
  about whether a contact occurs. With the M28 overlap positivity it is
  consistent: a contact at the bottom of a positive semidefinite `A_L` is the
  first root, where the slope is positive. On the sampled float grid at most one
  even eigenvalue lies below the odd floor, so the alternation beyond the first
  root is proved but not exercised numerically.
- **M08** is abstract calculus for a block family `a(t)`, `b(t)`, `H(t)` with
  `b(t₀) = 0` and `H(t₀)` invertible: `s''' = a''' − 3⟪b', R b''⟫ − 3⟪b'', R b'⟫
  + 6⟪b', R H' R b'⟫`, the symmetric and response forms
  `a''' + 6⟪b'', w⟫ + 6⟪H' w, w⟫` with `w = −R b'`, and `s''' ≤ 0` at a zero of
  order three that turns negative to the right. That sign is necessary, not
  contradictory. The arithmetic third identity for `⟨F''' z, z⟩` needs
  moving-aperture `C³` transport of the full source and stays OPEN.
- **M09** rewrites the zero-endpoint production value as
  `A_L[h] = ∫₀ᴸ R(e^t) h' + ∫₀ᴸ (e^{−t/2} − ρ) h` for `C¹` tests with
  `h(0) = h(L) = 0`. It is an identity: nothing is said about the sign or size
  of `R`. At a stationary generated strict-even contact it gives
  `A_{L*}[t² e_{Dz}(1 − t/L*)] = −2 L*⁴ C/(2π)² ≤ 0` with `C = ⟪A w, w⟫`, and
  the equivalent balance against `R(e^t)`. That is a necessary condition every
  such contact satisfies, not a contradiction. Excluding a stationary contact
  would need a positive lower bound for the same weighted `R` functional on the
  same contact, which is OBS-060O and stays OPEN.
- **M50** splits that balance at the prime samples:
  `P − ∑_q β_q e_{Dz}(ω_q) = −2L*⁴C/(2π)²` with `β_q = Λ(q)(log q)²/√q`.
  For any `θ` inside the M49 contact angle, the older samples `ω_q > θ` must
  carry at least `P + 2L*⁴C/(2π)² + b∑_{ω_q ≤ θ} β_q ω_q⁷` (91.1), and that
  quantity is at most `2(2K+1)K² ∑_{ω_q > θ} β_q ω_q` (91.2). Both are
  necessary conditions at every stationary generated contact. No lower bound
  for `P` and no upper bound for the older terms is proved, so nothing is
  excluded (M51 OPEN).
- **M59 and M61** work with the mixed atom `h_z`, not the energy `e_{Dz}`. At an
  even contact with `λ_odd > 0`, `p_z = Re(conj(M₄)h_z)` satisfies
  `I − Σ_q (Λ(q)/√q) p_z(ω_q) = |M₄|²/γ`, and for every split `θ`,
  `I − O + N = |M₄|²/γ`. With `γ ≤ ‖g‖²/λ_odd` this gives
  `O ≤ I + N − λ_odd|M₄|²/‖g‖² < I + N`. No F04 is used. The sign of `N` (a
  near-edge sign of `p_z`) is not proved. The opposite side `O ≥ I + N` (99C)
  is OPEN, is never assumed, and would be needed to exclude anything.
- **M33** (Step 68) is about the source energy of the contact-generated vector
  only. At a normalized even ground eigenvector with positive parity gap,
  `H(v) ≠ 0`, `e_{Dz}` is negative on an explicit `(0, θ]`, equals `2‖Dz‖²` at
  `ω = 1`, and so vanishes in `(θ, 1)`. The turning points of the physical test
  (Step 69) stay interval evidence.
- **M34** (Steps 70, 71). The representation (70.1) is M09. For any bounds
  `m ≤ R(eᵗ) ≤ M` on `[0, L*]`, a stationary generated contact satisfies
  `|∫ (e^{−t/2} − ρ) h + 2L*⁴C/(2π)²| ≤ (M − m)/2 · ∫ |h'|` (71.2). This is
  necessary, not a contradiction, and no size of `R` is assumed: a bound
  `R = O(x^ε)` would be RH-strength.
- **M44** (Step 81) is about one fixed legal even vector and one newly entering
  atom. With the other atoms and the background held fixed, the `q`-atom adds
  `a h⁷ + O(h⁸)` with `a > 0` at `L = log q + h`. This is not positivity of the
  total `Q`, not an eigenvalue jump, and nothing at a contact. It also does not
  conflict with the negative ninth-order even-energy seam term (Step 56), which
  is a different observable.
- **M29** (Steps 61, 62) gives the first two derivatives of `T = H_L(x_L)` and,
  where `T' = T'' = 0`, the identities they force. It gives no sign. The third
  derivative (Step 63) needs `C³`, which is proved only inside fixed cells, so
  the third-order obstruction at a contact stays OPEN.

### Proof outline for M71

1. **Andréief.** Expanding `det[∫ f_i g_j dμ]` by Leibniz and
   `integral_fintype_prod_eq_prod` gives `∫ det[f_m(x_i)] ∏ g_i(x_i) dμ^r`.
   Averaging over the coordinate permutations (`measurePreserving_piCongrLeft`)
   gives `(1/r!) ∫ det[f_m(x_i)] det[g_m(x_i)] dμ^r`.
2. **Signed minors.** With `f_k = w cos^k` and `g_k(t) = f_k(a − t)`, both
   determinants factor as weights times Vandermonde determinants in `cos x_i`
   and `cos(a − x_i)`. For `0 < a ≤ π`, `cos` is strictly decreasing on
   `[0, a]`, so every pair factor `(cos x_j − cos x_i)(cos(a − x_j) − cos(a − x_i))`
   is `≤ 0`, and `< 0` when `x_i ≠ x_j`. Clamping the variables to `[0, a]`
   makes the integrand sign-definite on all of `ℝ^r`, and a box of `r` disjoint
   subintervals of `(0, a)` has positive measure. Hence
   `(−1)^{r(r−1)/2} D_r > 0` for the Gram matrix
   `G_kl = ∫_0^a w(t) cos^k t · w(a−t) cos^l(a−t) dt`.
3. **Jacobi by Cramer vectors.** `w_k = ∑_{l ≤ k} adj(G_{k+1})_{l,k} e_l`
   satisfies `B(e_i, w_k) = 0` for `i < k` and `B(e_k, w_k) = D_{k+1}`, so the
   `w_k` are mutually orthogonal with `B(w_k, w_k) = D_k D_{k+1}`. Pivot signs
   `(−1)^k` put the even-index `w_k` in a positive definite subspace and the
   odd-index ones in a negative definite subspace, and
   `exactInertia_of_orthogonal_split` gives exact inertia.
4. **Carrier Gram.** The sesquilinear form of the Fourier convolution
   representation and the lattice character identities
   (`latticeCos(cos(n·t)) = cos t · cos(n·t)`, and so on) give
   `B(e_k, e_l) = π⁻¹ G_kl` with `w = (1 − cos)²` on the even carrier basis
   `evenCarrierMap m (cos^k)`, and `−π⁻¹ G_kl` with `w = sin · (1 − cos)` on the
   odd basis `oddCarrierMap m (cos^k)`, `k ≤ m = K − 2`. Their span is the whole
   carrier by dimension count.

### Proof outline for F04 and M66

M65 starts from the real M05 regularized energy identity with the exact
weights `Λ(q)(log q)²/√q`. On `0 < L < log 2` no prime power lies below `e^L`,
so the energy is an integral against `W − ρ` plus the `w(L)` correction. Lean
differentiates it under a moving upper limit (`hasDerivAt_integral_moving_upper`)
with `t ρ(t)` replaced by the continuous `regularizedArchScale`, which removes
the `1/(2t)` singularity. The endpoint terms cancel because
`wCorrection'(L) = e^{−L/2} ρ(L)` and `e_z(0) = e'_z(0) = 0` on even
boundary-flat vectors. The mixed field follows by real polarization of both
sides.

Global F04 writes the prime staircase as a finite sum of terms switched on by
`log q ≤ L`. Each entering term has zero value and zero slope at its seam,
because `e_z(0) = e'_z(0) = 0` (energy channel) and `e'_z(0) = e''_z(0) = 0`
(first channel) on boundary-flat vectors. `hasDerivAt_ite_le` then glues the
one-sided derivatives at the seam.

M66 uses `e''_z = −(2π)² e_{Dz}` for zero-sum vectors to rewrite the
Euler-corrected second test as `−(2π)²/L⁴ · Q_K(L, z)`. It then applies the
existing M42 lower bound `primeFreeSecondTest_ge`,
`Q_K ≥ L² M (1/(4π²) − L(2K+1)K²/2)`.

### F04 strength audit

- **Statement.** `productionContactF04DerivativeAuthority_of_pos :
  ∀ (K : ℕ) {L : ℝ}, 0 < L → ProductionContactF04DerivativeAuthority L K`. The
  only premise is `0 < L`. There is no contact, sign, F04-equivalent or
  RH-equivalent hypothesis, and no section variable adds one.
- **Target.** `ProductionContactF04DerivativeAuthority` is the post-284
  structure itself, not a renamed copy. Its three fields are the first
  variation, the Euler-corrected fixed second variation, and the mixed aperture
  derivative of the actual canonical even compressed family, each equal to the
  complete physical functional (pole, archimedean and every prime up to `e^L`)
  of the clamped production test. This is the plan's F04 at every aperture.
- **Consumers.** Ten `Zeta23/CCM` theorems took this structure as a hypothesis.
  Each has an instance here with no F04 hypothesis:
  - `canonicalFirstVariation_eq_physical_of_pos`,
    `canonicalFixedSecondEuler_eq_physical_of_pos`,
    `canonicalMixedFirstVariation_eq_physical_of_pos`;
  - `canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos`,
    `canonicalStationaryCurvature_eq_productionSaturationGap_of_pos`;
  - `GeneratedStrictEvenContact.production_stationary_saturation_unconditional`,
    `…production_stationary_remainder_pos_unconditional`,
    `…inherited_production_saturation_unconditional`,
    `…completed_production_frontier_unconditional`,
    `…inherited_completed_production_frontier_unconditional`.
- **Not changed.** The eight claim-contract wrappers in
  `Zeta23/RHRC/ContactCalculusContract.lean` still take `hF04` as a parameter.
  They can be instantiated with the constructor. #286 has merged and kept the
  two F04-bound registered claims OPEN; they are promoted one at a time only
  after CI is green on this head. The structure's docstring in
  `FirstCrossingProductionCurvatureBridge.lean` still calls F04 "presently
  OPEN". It is left as written to avoid editing #284 sources, and this ledger
  is the authority.

## 2. DERIVED (not formalized)

### M72 multiplicity

Continuous eigenvalue branches of the Hermitian family `ω ↦ S(ω)|_V` give at
least as many passages, counted with multiplicity, as there are negative
half-aperture eigenvalues. **Status: OPEN in Lean.**

## 3. EXPERIMENTAL SIGNAL

The details are in `FALSIFICATION_REPORT.md`.

- **M76.** Rank-one holds to 2e-15 on the executable canonical matrices. On the
  46 float-resolved points (`K = 2..5`, `L ≤ 6`), the margin `1 − T(L)` is
  positive, with a minimum of 4.4e-4.
  - Pole and prime channels cancel at up to 7e9 times the net value.
- **M76 in Arb: all 96 grid points certified (interval evidence).** Arb at 256
  bits certifies `A > 0`, `B > 0` and `1 − T(L) > 0` at every grid point,
  including the 50 that float64 cannot resolve (it had shown negative bottoms
  at 13 of them).
  - The margin falls to `2.2·10⁻⁹` at `K = 5, L = 6`, and `λ_min(A)` to
    `9.7·10⁻²⁵`. The pole channel cancels at up to `2·10¹⁶` times `T`.
  - Scaling every prime weight by `1 ± 10⁻⁶` destroys positivity at the
    deepest point of each `K`, in both directions.
  - The `K = 2` grid minima are the grid points nearest `2πk/γ₁`, and `K = 3`, `4`
    dip deepest at `L = 4 ≈ 2π·9/γ₁`. This is pointwise; nothing between grid
    points is claimed.
- **M73.** The optimal Poincaré constant decreases toward `1/4`; it is 0.2513 at
  `K = 80`.
- **M75.** The window `η_K` is very conservative. The true negative run is
  about 198 times `2η_K`.
- **F04 regression.** At matrix level against the executable canonical matrix,
  the first identity holds to 5e-8 and the Euler identity to 1.2e-6 for
  `K = 2..5`. This covers the prime-free window, prime cells and the seams
  `log 3, log 4, log 5` exactly. Both negative controls (a nonzero coefficient
  sum, and `cCorrection` added twice) miss by exactly the predicted amount.
- **M66 radius.** The Euler form stays negative definite up to about
  `L = 0.55` (`K = 2`), falling to 0.30 (`K = 16`). The proved radius `ε_K` is
  smaller by two to four orders of magnitude.
- **Step 28, certified.** At `K = 2`, `L = 1.2`, `z = (1,−4,6,−4,1)` the
  historical floats are now Arb enclosures: `E(Dz) ≈ +0.2154944559 > 0` and
  `A_L[t² e_{Dz}] ≈ −0.5224196282 < 0`. `z` is not a contact; the pair only
  shows that ordinary odd positivity does not give weighted positivity.
- **M49 near-edge angle.** On the float canonical matrices the contact angle
  `θ_*` contains prime samples for `K = 2` (most `L`) and sometimes for `K = 3`,
  but none for `K = 4..6` with `L ≤ 6`. The near-edge benefit proved in M49 is
  therefore vacuous for larger `K` on this grid; it cannot by itself drive an
  exclusion.
- **M50 cancellation.** At the even ground states of the same grid, `P` and
  the prime sum cancel to `6.6·10⁻⁴|P|` or better for `L ≥ 2`, while the
  finite form's right side is at least `114|P|` wherever older samples exist.
  The size bound behind (91.2) loses all of that cancellation, so an older-prime
  estimate for M51 has to work with `P` and the primes together.
- **M44 next order.** At 216 seam rows the remainder `|ΔQ − a h⁷|/h⁸` tends to
  `7a/log q`, as predicted by expanding `ω_h⁷`. The entering atom is of order
  `h⁷` near the seam. At an even ground state the same atom is covered by the
  M49 lower bound once `ω_h` is inside the contact angle; M44 adds the exact
  leading coefficient.
- **M51: no `K = 2` even contact on `[1/400, log 16]` (interval evidence).** For
  `K = 2` the legal even carrier is one-dimensional, so the even compression is
  the scalar `λ(L) = ⟨z, S_L z⟩/⟨z, z⟩` with `z = (1, −4, 6, −4, 1)`. Arb
  certifies `λ > 0` on the whole range, so for `K = 2` there is no contact there
  for M51 to obstruct. By the F04 identity a `K = 2` stationary contact would
  need `λ = λ' = λ'' = 0`.
  **Scope correction:** this historical certificate stops at
  `U = 2772588722239781/10^15`; the remaining exact-log16 gap is OPEN.
- **The `K = 2` near-contacts sit at `L = 2πk/γ₁`.** `λ` comes within
  `3.2·10⁻¹⁰` of zero. Its local minima are at `L γ₁/(2π) = 3.0008, 4.0008,
  5.0008, 6.0025`. Numerically `λ` is the sum of nonnegative single-zero terms
  over the first 100 zeros, to `3·10⁻⁹`. At each minimum the `γ₁` term nearly
  vanishes and what is left is the contribution of `γ₂, γ₃, …`. Scaling all
  prime weights by `1 + 10⁻⁶` already makes `λ` negative there. So an
  arithmetic opposite side has to resolve margins of the size of the
  higher-zero contributions; this is the explicit formula at work, and it is not
  independent of the zeros.
- **M63: both contact identities nearly hold at the near-contacts.** At the
  four `K = 2` minima the source-moment identity (98B) misses `|M₄|²/γ` by a
  relative `λ/λ_odd` (`0.027` down to `0.0054`), and the F04 curvature identity
  misses `V = 0` by `|V|/|P|` from `1.7·10⁻²` down to `1.4·10⁻⁵`. Each route's
  opposite side ((98C)/(99C) for the source moment, `V > 0` at a stationary
  contact for F04) therefore has to separate an exact contact from
  near-contacts at which its own identity already holds to those margins. The
  curvature route is the tighter of the two here. Neither route excludes
  anything.
- **No even contact below `log 2`.** For `K = 2..16`, the even compressed
  ground stays positive on `(0, log 2)`. Its minimum sits at the right end and
  falls from 0.096 (`K = 2`) to 0.003 (`K = 16`).

## 4. LEADS

1. **A larger Euler radius.** The proved `ε_K` is smaller than the observed
   negativity radius (0.3–0.55) by a factor of about `200` to `10⁴`. All of
   that loss sits in the M42 lower bound `primeFreeSecondTest_ge`. A sharper
   lower bound for `Q_K` on the even boundary-flat carrier would extend M66
   directly, possibly to a window that is not vacuous.
2. **The even ground below `log 2`.** The observed positivity of the even
   ground on `(0, log 2)` is the statement "no strict-even first contact in the
   prime-free window". With F04 and the Euler identity now proved there, a
   lower bound on `Q_K` along the whole window is a concrete target.
3. **Close `(0, 1/400)` for `K = 2`.** `λ ≈ −log L − 0.90` there, and M66
   gives `E'' + (2/L)E' < 0` on `(0, ε_2)`. A proved limit `L²λ'(L) → 0` would
   make `λ` decreasing there and finish `(0, log 16]`.
4. **The `K = 3` near-contacts.** Repeat the M51 certificate on the
   two-dimensional `K = 3` even carrier (an Arb eigenvalue enclosure instead of
   a scalar) and test whether its minima also sit at `L = 2πk/γ₁`. The M76 Arb
   grid already puts the deepest `K = 3` dip at `L = 4`, where
   `L γ₁/(2π) = 8.998`. A first try with a fixed eigenframe on each interval
   (Taylor bounds for the 2×2 entries, then the Schur complement) did not
   finish the cell `[log 14, log 15]` in 30 minutes. The binding term is the
   ball enclosure of the second derivative: evaluated over `[c − r, c + r]`,
   the compressed `A''` has radius about `1.4·10⁵ r` at 128 and 256 bits alike,
   because the pole, archimedean and prime channels are enclosed separately and
   their cancellation is lost. With the bottom near `10⁻¹¹` this forces
   `r ≲ 10⁻⁵`, about three hours for this one cell, and the bottom falls to
   `10⁻¹⁵`–`10⁻¹⁷` beyond `L ≈ 4`. The eigenvalue itself would allow
   `r ≈ 10⁻³`–`10⁻²` (float scout of `λ'`, `λ''`). Enclosures that keep the
   cancellation (Taylor models in `L − c`, or the compressed forms evaluated
   as one kernel sum) are the likely way through.
5. **A sharper M75 window.** The 198× slack in `η_K` suggests that a
   second-derivative window could lower the `π² M_K log 2` threshold by orders
   of magnitude.

## 5. Global branch analysis (M14, M77)

At a first-contact aperture `L*`, both bottoms are positive for `L < L*`.
Three branch types can occur at `L*`:

| Branch | At `L*` | What is available |
|---|---|---|
| Even-first (strict-even) | even bottom = 0, odd bottom > 0 | **PROVED (M74):** `ker A = ℂ ∙ x_L`; contact iff `S_L(x_L) = 1`; phase lock `Re(conj(S z) M4 z) = γ|S z|² > 0`. **PROVED (M28 sign):** `⟪x_L, D⁻¹g⟫ > 0`. **PROVED (M66):** not stationary when `L* < ε_K`. **PROVED (Step 103):** if stationary, the second physical value is `2⟨A w, w⟩ ≥ 0`. The opposite-side sign is OPEN (M76). |
| Even-first, eigenvalue structure | odd bottom > 0 | **PROVED (`CanonicalShiftedSecular`):** every even eigenvalue below the odd floor is simple; `det(A − λ) = det(B − λ)(1 − T_L(λ))`. |
| Odd-first | odd bottom = 0, even bottom > 0 | **PROVED (`CanonicalShiftedSecular`):** see the swapped instance below. |
| Tied | both bottoms = 0 | **PROVED (`canonical_tied_contact_orthogonality`):** see the tied identity below. Nothing beyond that. |

**Odd-first, swapped instance.** The relation
`A D⁻¹ − D⁻¹ B = (−D⁻¹ g) ⊗ (H ∘ D⁻¹)` is again a rank-one intertwining, so the
abstract M74 algebra applies with the roles of the two sectors swapped. This
gives:
- `ker B ⊆ ℂ ∙ D A⁻¹ D⁻¹ g`;
- contact iff `H(A⁻¹ D⁻¹ g) = −1`;
- `det B = det A · (1 + H(A⁻¹ D⁻¹ g))`.

**Tied identity.** For `A z = 0` and `B y = 0`, pairing the rank-one relation
with `y` and using the symmetry of `B` gives `H(z)⟨y, g⟩ = 0`. So either
`D z ∈ ker B`, or `g ⊥ ker B`.

**On the M76 grid the approach is even-first (signal).** At all 96 Arb-certified
grid points (`K = 2..5`, `L = k/4 ≤ 6`) both bottoms are positive and the even
bottom is below the odd bottom, by a factor from `0.49` down to `1.1·10⁻³`. The
odd-first and tied branches are not approached there. This is pointwise
evidence, not a statement about any contact.

Branches outside first contact (fresh-born, interior, later crossings) stay
OPEN, as in post-284 M14. No branch is excluded.

## 6. Audit of the post-284 OPEN rows

The post-284 ledger has 37 OPEN rows. This PR leaves those rows untouched and
records how this PR affects each one in `post284_cross_references`. Each row
falls into one of these classes:

| Class | Rows | Comment |
|---|---|---|
| F04-bound | F04_PRODUCTION_DERIVATIVE_AUTHORITY, M09_WEIGHTED_REMAINDER_IDENTITY, F_M33_M34, F_M37, F_M48, F_M49_M51, F_M53_M65, F_M66 | The F04 premise is discharged at every `L > 0`. F_M33_M34, F_M53_M65, F_M66, M09 and the F04 authority itself are proved here, and F_M49_M51 is proved except for M51. The others keep their non-F04 parts open |
| Operator seam germs | M07, M10, M11, F_M23_M24, F_M44 | Need operator-norm Taylor majorants at frozen prime seams. The fixed-vector physical jet of F_M44 is proved here (M44); its operator upgrade stays OPEN |
| Classical arithmetic | F_M38, F_M55 | Proved here (M38, M55) |
| Abstract analysis | F_M31 | Proved here as a conditional barrier (M31); the coefficient bound M32 stays OPEN |
| Abstract algebra | M03_RANK_TWO_LAPLACE, M03_WEIGHTED_STAIRCASE_REEXPRESSION | Proved here (M03_RANK_TWO_LAPLACE_TRANSFORM, M03_FIXED_STAIRCASE_REEXPRESSION) |
| Proved here | M17 (as M71, on the boundary-flat carriers for every `0 < ω ≤ 1/2`), F_M27 (simplicity, and the alternating root slopes as M27), M08_ABSTRACT_CUBIC_SCHUR (as M08; the arithmetic third identity stays OPEN), M16 (subsumed by M71 at every `0 < ω ≤ 1/2`), F_M45 (as M45, with the plan's angle and constant) | The post-284 rows are historical and stay as they were; filtered carriers stay OPEN |
| Partly addressed here | M18 (first passage), F_M21 (phase identity), F_M46 (constant 4), F_M58_M63 (phase lock, M59 real pairing, M61 exact balance), F_M28 (overlap identity and sign), M14 (odd-first and tied algebra), F_M29 (first and second derivatives; the third-order obstruction stays OPEN) | See the cross-references |
| Research or contact-conditioned | M03_TWO_SCALAR, M13, F_M22, F_M25, F_M32, F_M39, F_M56_M57, F_M68, OBS060O | No viable proof route identified in this PR |
| Provenance | OAI_SEVEN_EIGHTHS_LOCAL_IMPORT | Audit only |
| Terminal | RH | RH_OPEN |

## 7. OPEN, kept open on purpose

`check_post285_ledgers.py` refuses to let any of these leave OPEN:
- `M14_BRANCH_EXCLUSION`;
- `M32_CANONICAL_GRONWALL_COEFFICIENT`, the coefficient bound (67.1) that the
  M31 barrier needs;
- `M76_ARITHMETIC_COMPOSITION`, the opposite-side sign of the canonical complete
  arithmetic target;
- `OBS060O_STATIONARY_SATURATION_EXCLUSION`;
- `RH`.

Nothing in this PR excludes a strict-even first contact above `ε_K`, and
nothing excludes a stationary one (OBS-060O). Nothing in it proves a
sign of `𝓐_L`. No unconditional theorem in it assumes the desired inequality as a hypothesis;
the conditional M31 barrier states (67.1) as an explicit hypothesis and is not
an exclusion.
