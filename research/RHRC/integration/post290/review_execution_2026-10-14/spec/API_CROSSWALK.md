# Exact 99-public-API crosswalk

This is not a progress percentage. Existing source names, printed compiler roots, semantic coverage and final acceptance are different. Current types below are literal receipt types; new contracts are specifications, not printed compiler output.

## M01.01 — `Zeta23.CCM.universalSincSource`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T03**.

Origin: `Zeta23.CCM.UniversalSincSourceFacade`.

Required contract: Construct the exact infinite-convolution source; density, support, positivity, symmetry, smoothness, transform and scaling.

## M01.02 — `Zeta23.CCM.universalSincSource_nonneg`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T03**.

Origin: `Zeta23.CCM.UniversalSincSourceFacade`.

Required contract: ∀ {s : ℝ}, 0 < s → ∀ (x : ℝ), 0 ≤ Zeta23.CCM.universalSincSource s x

## M01.03 — `Zeta23.CCM.universalSincSource_integral_one`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T03**.

Origin: `Zeta23.CCM.UniversalSincSourceFacade`.

Required contract: ∀ {s : ℝ}, 0 < s → ∫ (x : ℝ), Zeta23.CCM.universalSincSource s x = 1

## M01.04 — `Zeta23.CCM.universalSincSource_support`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T03**.

Origin: `Zeta23.CCM.UniversalSincSourceFacade`.

Required contract: ∀ {s : ℝ}, 0 < s → tsupport (Zeta23.CCM.universalSincSource s) ⊆ Set.Icc (-s) s

## M01.05 — `Zeta23.CCM.universalSincSource_contDiff`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T03**.

Origin: `Zeta23.CCM.UniversalSincSourceFacade`.

Required contract: ∀ {s : ℝ}, 0 < s → ContDiff ℝ (↑⊤) (Zeta23.CCM.universalSincSource s)

## M01.06 — `Zeta23.CCM.paperFT_universalSincSource`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T03**.

Origin: `Zeta23.CCM.UniversalSincSourceFacade`.

Required contract: ∀ {s : ℝ}, 0 < s → (Zeta23.paperFT fun x => ↑(Zeta23.CCM.universalSincSource s x)) = Zeta23.CCM.UniversalSinc.product s

## M02.01 — `Zeta23.CCM.universalSincSource_gevrey_bound`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T03**.

Origin: `None`.

Required contract: s>0 implies constructed source-only C,H>0 and for every n,x, |q_s^(n)(x)| <= C H^n (n!)^2. Preserve exact q_s identification.

Checked reuse: `Zeta23.CCM.UniversalSinc.norm_iteratedDeriv_inverseCandidate_le_gevrey`.

## M02.02 — `Zeta23.CCM.poleKilled_universalSincSource_norm_sq`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T03**.

Origin: `None`.

Required contract: s>0 implies ||Pq_s||_2^2 = s^-5||q_1 second derivative||_2^2 +(1/2)s^-3||q_1 first derivative||_2^2 +(1/16)s^-1||q_1||_2^2. R2.

## M02.03 — `Zeta23.CCM.universalSincProduct_decay`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T03**.

Origin: `None`.

Required contract: Reexport exact all-real-frequency product Gevrey decay, with original constants and domain; no new simplicity assertion.

Checked reuse: `Zeta23.CCM.UniversalSinc.product_norm_ofReal_le_gevrey`.

## M03.01 — `Zeta23.ExceptionalZero.universalSincPoleKilled_visible_at_offLine_zero`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T03**.

Origin: `None`.

Required contract: Actual rho with Re rho !=1/2 gives nonzero physical pole-killed transform at the exact paperFT spectral coordinate. Reuse physical identification, not multiplier name only.

Checked reuse: `Zeta23.ExceptionalZero.fixed_originalSincMultiplier_square_ne_zero_at_off_line_zero`.

## M04.01 — `Zeta23.ExceptionalZero.originalDetectorCorrelation_pos_excursions`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.ExceptionalZero.OriginalDetectorPhaseDepth`.

Required contract: ∀ (ρ : ↑Zeta23.zetaZeroConfig.carrier),   (↑ρ).re ≠ 1 / 2 →     ∀ {β : ℝ},       β < |(↑ρ).re - 1 / 2| →         ∀ (A M : ℝ), ∃ a, A < a ∧ M * Real.exp (2 * β * a) < Zeta23.ExceptionalZero.fixedOriginalSincCorrelationReal a

## M04.02 — `Zeta23.ExceptionalZero.originalDetectorCorrelation_neg_excursions`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.ExceptionalZero.OriginalDetectorPhaseDepth`.

Required contract: ∀ (ρ : ↑Zeta23.zetaZeroConfig.carrier),   (↑ρ).re ≠ 1 / 2 →     ∀ {β : ℝ},       β < |(↑ρ).re - 1 / 2| →         ∀ (A M : ℝ),           ∃ a, A < a ∧ Zeta23.ExceptionalZero.fixedOriginalSincCorrelationReal a < -(M * Real.exp (2 * β * a))

## M04.03 — `Zeta23.ExceptionalZero.originalDetector_eachPhase_cofinal_depth`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.ExceptionalZero.OriginalDetectorPhaseDepth`.

Required contract: ∀ (ρ : ↑Zeta23.zetaZeroConfig.carrier) {β σ : ℝ},   0 < β →     β < |(↑ρ).re - 1 / 2| →       σ = 1 ∨ σ = -1 →         ∀ (R : ℝ),           ∃ L,             max R 4 < L ∧               ∃ a,                 L = Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a ∧                   tsupport (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) ⊆ Set.Icc 1 (L - 1) ∧                     ∫ (x : ℝ), ‖Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a x‖ ^ 2 = 1 ∧                       (Zeta23.CCM.localizedWeilAdditiveRHS (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a)                             (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a)).re ≤                         -Real.exp (β * L)

## M05.01 — `Zeta23.CCM.originalDetectorFiniteImage`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFiniteTransport`.

Required contract: Fixed endpoint order m=4 in core; degree M=4, N=ceil(L^4)-4. Construct positive padding and exact phase; prove physical/coefficient norm bridge and quantitative error.

## M05.02 — `Zeta23.CCM.originalDetectorFiniteImage_legal`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFiniteTransport`.

Required contract: ∀ (c : ℝ) {L : ℝ} (hL : 2 ≤ L),   Zeta23.CCM.originalDetectorFiniteImage L c ⋯ ∈     Zeta23.CCM.euclideanBoundaryFlatSubspace (Zeta23.CCM.originalDetectorQuarticCutoff L)

## M05.03 — `Zeta23.CCM.originalDetectorFiniteImage_poleNeutral`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFiniteTransport`.

Required contract: ∀ (c : ℝ) {L : ℝ} (hL : 2 ≤ L),   (Zeta23.CCM.canonicalPoleEvenFunctional L (Zeta23.CCM.originalDetectorQuarticCutoff L))         (Zeta23.CCM.originalDetectorFiniteImage L c ⋯) =       0 ∧     (Zeta23.CCM.canonicalPoleOddFunctional L (Zeta23.CCM.originalDetectorQuarticCutoff L))         (Zeta23.CCM.originalDetectorFiniteImage L c ⋯) =       0

## M05.04 — `Zeta23.CCM.originalDetectorFiniteImage_endpointJets`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFiniteTransport`.

Required contract: ∀ (c : ℝ) {L : ℝ} (hL : 2 ≤ L) {r : ℕ},   r ≤ 4 →     Zeta23.CCM.centeredMoment (Zeta23.CCM.originalDetectorQuarticCutoff L) r         ((EuclideanSpace.equiv (Fin (2 * Zeta23.CCM.originalDetectorQuarticCutoff L + 1)) ℂ)           (Zeta23.CCM.originalDetectorFiniteImage L c ⋯)) =       0

## M05.05 — `Zeta23.CCM.originalDetectorFiniteImage_error_bound`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFiniteTransport`.

Required contract: ∀ {L c : ℝ} (hL : 2 ≤ L),   1 + Zeta23.CCM.UniversalSinc.fixedScale ≤ c →     c + Zeta23.CCM.UniversalSinc.fixedScale ≤ L - 1 →       ∀ (r : ℕ) {x : ℝ},         x ∈ Set.Icc 0 L →           ‖iteratedDeriv r                   (fun y => Zeta23.ExceptionalZero.originalSincTest Zeta23.CCM.UniversalSinc.fixedScale (y - c)) x -                 iteratedDeriv r                   (Zeta23.CCM.localizedFiniteFunction L (Zeta23.CCM.originalDetectorQuarticCutoff L)                     ((EuclideanSpace.equiv (Fin (2 * Zeta23.CCM.originalDetectorQuarticCutoff L + 1)) ℂ)                       (Zeta23.CCM.originalDetectorFiniteImage L c ⋯)))                   x‖ ≤             Zeta23.CCM.originalDetectorPaddedFinitePoleImageJetBudget Zeta23.CCM.UniversalSinc.fixedScale L r

## M05.06 — `Zeta23.CCM.originalDetectorFiniteImage_quartic_error_tendsto_zero`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFiniteTransport`.

Required contract: ∀ (r : ℕ) (β : ℝ),   Filter.Tendsto     (fun L =>       Zeta23.CCM.originalDetectorPaddedFinitePoleImageJetBudget Zeta23.CCM.UniversalSinc.fixedScale L r *         Real.exp (β * L))     Filter.atTop (nhds 0)

## M06.01 — `Zeta23.CCM.originalDetectorPhaseGram_eq`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFinitePhasePlane`.

Required contract: ∀ (L c : ℝ) (hL : 0 < L),   Zeta23.CCM.originalDetectorPaddedFinitePhaseGram L c hL =     !![Zeta23.CCM.originalDetectorPaddedFinitePhaseGram L c hL 0 0,         Zeta23.CCM.originalDetectorPaddedFinitePhaseGram L c hL 0 1;       Zeta23.CCM.originalDetectorPaddedFinitePhaseGram L c hL 0 1,         Zeta23.CCM.originalDetectorPaddedFinitePhaseGram L c hL 0 0]

## M06.02 — `Zeta23.CCM.originalDetectorPhaseEnergy_eq`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFinitePhasePlane`.

Required contract: ∀ (L c : ℝ) (hL : 0 < L),   Zeta23.CCM.originalDetectorPaddedFinitePhaseNativeEnergy L c hL =     !![Zeta23.CCM.originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 0,         Zeta23.CCM.originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 1;       Zeta23.CCM.originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 1,         Zeta23.CCM.originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 0]

## M06.03 — `Zeta23.CCM.originalDetectorPhaseRayleigh_eq`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T04**.

Origin: `Zeta23.CCM.OriginalDetectorFinitePhasePlane`.

Required contract: ∀ (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ),   (inner ℂ           ((Matrix.toEuclideanLin (Zeta23.CCM.canonicalSourceMatrix L (Zeta23.CCM.originalDetectorQuarticCutoff L)))             (Zeta23.CCM.originalDetectorPaddedFinitePhasePlaneVector L c hL z))           (Zeta23.CCM.originalDetectorPaddedFinitePhasePlaneVector L c hL z)).re /       ‖Zeta23.CCM.originalDetectorPaddedFinitePhasePlaneVector L c hL z‖ ^ 2 =     (Zeta23.CCM.originalDetectorPaddedFinitePhaseMatrixValue           (Zeta23.CCM.originalDetectorPaddedFinitePhaseNativeEnergy L c hL) z).re /       (Zeta23.CCM.originalDetectorPaddedFinitePhaseMatrixValue (Zeta23.CCM.originalDetectorPaddedFinitePhaseGram L c hL)           z).re

## M07.01 — `Zeta23.CCM.canonicalPoleNeutralEven`

Current: **EXACT_API_ABSENT**. Kind: DEFINITION. Task: **T05**.

Origin: `None`.

Required contract: Transparent alias of actual poleNeutralEvenSubspace L K; keep native legal carrier and inherited metric.

## M07.02 — `Zeta23.CCM.canonicalPoleNeutralOdd`

Current: **EXACT_API_ABSENT**. Kind: DEFINITION. Task: **T05**.

Origin: `None`.

Required contract: Transparent alias of actual poleNeutralOddSubspace L K; keep native legal carrier and inherited metric.

## M07.03 — `Zeta23.CCM.poleNeutral_iff_exponentialMoments`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: Bundle the actual even and odd physical two-pole iff theorems on their own legal carriers.

Checked reuse: `Zeta23.CCM.poleNeutralEven_iff_exponentialMoments`, `Zeta23.CCM.poleNeutralOdd_iff_exponentialMoments`.

## M07.04 — `Zeta23.CCM.poleNeutral_parity_finrank`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: L>0,K>=3: both native neutral parity spaces have finrank K-2; separately record zero spaces for K<3.

Checked reuse: `Zeta23.CCM.finrank_poleNeutralEvenSubspace`, `Zeta23.CCM.finrank_poleNeutralOddSubspace`.

## M07.05 — `Zeta23.CCM.poleNeutralIndexEquiv`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T05**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralCarrier`.

Required contract: Define physical pole-neutral carriers, dimensions, nonzero normals and algebraic nonunitary D0 equivalence. Handle K<3 separately.

## M07.06 — `Zeta23.CCM.poleNeutralIndex_norm_lower`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T05**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralCarrier`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (K : ℕ) (u : ↥(Zeta23.CCM.poleNeutralEvenSubspace L K)),   ‖u‖ ^ 2 ≤ 4 * ‖(Zeta23.CCM.poleNeutralIndexLinearMap hL K) u‖ ^ 2

## M08.01 — `Zeta23.CCM.poleNormalCoefficient`

Current: **EXACT_API_ABSENT**. Kind: DEFINITION. Task: **T05**.

Origin: `None`.

Required contract: Alias actual even output normal multiplier poleNeutralEvenOutputCoefficient; not the quadratic-normal scalar b.

## M08.02 — `Zeta23.CCM.correctedCanonicalSource`

Current: **EXACT_API_ABSENT**. Kind: DEFINITION. Task: **T05**.

Origin: `None`.

Required contract: Alias actual corrected scalar S0=S-b*alpha and retain the corresponding linear functional when used in RankOneIntertwining.

## M08.03 — `Zeta23.CCM.poleNormal_index_projection_eq`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: Actual Q_odd D v_even = -b g0, with all actual projections and normalization.

Checked reuse: `Zeta23.CCM.poleNeutralOddProjection_index_evenNormal_eq_cubic`.

## M08.04 — `Zeta23.CCM.canonicalPoleNeutral_rankOneIntertwining`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: Actual B0 D0-D0 A0=g0 S0, instantiated from native source, not a hypothesis.

Checked reuse: `Zeta23.CCM.canonicalPoleNeutralRankOneIntertwining`.

## M08.05 — `Zeta23.CCM.poleNeutral_cubic_pairing_eq_momentFour`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T05**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralNormals`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (K : ℕ) (u : ↥(Zeta23.CCM.poleNeutralEvenSubspace L K)),   inner ℂ (Zeta23.CCM.poleNeutralCubicCompressionVector L K) ((Zeta23.CCM.poleNeutralIndexLinearMap hL K) u) =     Zeta23.CCM.centeredMoment K 4 (Zeta23.CCM.evenBoundaryFlatRawCoefficients K ↑u)

## M09.01 — `Zeta23.CCM.poleNeutral_source_moment_energy_eq`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T06**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralSourceMoment`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (K : ℕ),   2 ≤ K →     ∀ (lam : ℝ) (u : ↥(Zeta23.CCM.poleNeutralEvenSubspace L K)),       (Zeta23.CCM.poleNeutralEvenCompressedCanonical L K) u = ↑lam • u →         (star (Zeta23.CCM.poleNeutralCorrectedCubicSource L K u) *               Zeta23.CCM.centeredMoment K 4 (Zeta23.CCM.evenBoundaryFlatRawCoefficients K ↑u)).re =           (inner ℂ               ((Zeta23.CCM.poleNeutralOddCompressedCanonical L K) ((Zeta23.CCM.poleNeutralIndexLinearMap hL K) u) -                 ↑lam • (Zeta23.CCM.poleNeutralIndexLinearMap hL K) u)               ((Zeta23.CCM.poleNeutralIndexLinearMap hL K) u)).re

## M09.02 — `Zeta23.CCM.poleNeutral_strictEven_source_moment_pos`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T06**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralSourceMoment`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (u : ↥(Zeta23.CCM.poleNeutralEvenSubspace L K)),   u ≠ 0 →     (Zeta23.CCM.poleNeutralEvenCompressedCanonical L K) u = ↑(Zeta23.CCM.poleNeutralEvenRayleighBottom L K hL hK) • u →       Zeta23.CCM.poleNeutralEvenRayleighBottom L K hL hK < Zeta23.CCM.poleNeutralOddRayleighBottom L K hL hK →         0 <           (star (Zeta23.CCM.poleNeutralCorrectedCubicSource L K u) *               Zeta23.CCM.centeredMoment K 4 (Zeta23.CCM.evenBoundaryFlatRawCoefficients K ↑u)).re

## M09.03 — `Zeta23.CCM.poleNeutral_trial_residual_bound`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T06**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralTrialResidualBounds`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : ↥(Zeta23.CCM.poleNeutralEvenSubspace L K)),   (Zeta23.CCM.poleNeutralOddRayleighBottom L K hL hK - lam) * ‖(Zeta23.CCM.poleNeutralIndexLinearMap hL K) u‖ ^ 2 ≤     ‖Zeta23.CCM.poleNeutralCorrectedCubicSource L K u‖ *         ‖Zeta23.CCM.centeredMoment K 4 (Zeta23.CCM.evenBoundaryFlatRawCoefficients K ↑u)‖ +       ‖(Zeta23.CCM.poleNeutralIndexLinearMap hL K) (Zeta23.CCM.poleNeutralTrialResidual L K lam u)‖ *         ‖(Zeta23.CCM.poleNeutralIndexLinearMap hL K) u‖

## M09.04 — `Zeta23.CCM.poleNeutral_momentFour_zero_residual_lower`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T06**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralTrialResidualBounds`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : ↥(Zeta23.CCM.poleNeutralEvenSubspace L K)),   lam < Zeta23.CCM.poleNeutralOddRayleighBottom L K hL hK →     Zeta23.CCM.centeredMoment K 4 (Zeta23.CCM.evenBoundaryFlatRawCoefficients K ↑u) = 0 →       (Zeta23.CCM.poleNeutralOddRayleighBottom L K hL hK - lam) * ‖u‖ / (2 * ↑K) ≤         ‖Zeta23.CCM.poleNeutralTrialResidual L K lam u‖

## M09.05 — `Zeta23.CCM.poleNeutral_simpleEven_momentFour_ne_zero`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T06**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralGroundConstraints`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : ↥(Zeta23.CCM.poleNeutralEvenSubspace L K)),   u ≠ 0 →     (Zeta23.CCM.poleNeutralEvenCompressedCanonical L K) u = ↑lam • u →       lam ≤ Zeta23.CCM.poleNeutralOddRayleighBottom L K hL hK →         Module.finrank ℂ ↥(Module.End.eigenspace (Zeta23.CCM.poleNeutralEvenCompressedCanonical L K) ↑lam) = 1 →           Zeta23.CCM.centeredMoment K 4 (Zeta23.CCM.evenBoundaryFlatRawCoefficients K ↑u) ≠ 0

## M10.01 — `Zeta23.CCM.poleNeutralEvenShiftedRay`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T05**.

Origin: `Zeta23.CCM.CanonicalPoleNeutralShiftedSecular`.

Required contract: Instantiate generic shifted secular algebra for both strict branches; derive strict odd via adjoint and the specified minus sign.

## M10.02 — `Zeta23.CCM.poleNeutral_evenShifted_eigen_iff`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: Below actual odd bottom: lambda is an even eigenvalue iff S0(x_lambda)=1; x_lambda uses actual invertible odd shift.

Checked reuse: `Zeta23.CCM.poleNeutral_even_eigenvector_eq_source_smul_shiftedRay`, `Zeta23.CCM.poleNeutral_even_eigen_shiftedRay_source_eq_one`.

## M10.03 — `Zeta23.CCM.poleNeutral_evenShifted_det_eq`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: Below odd bottom: det(A0-lambda)=det(B0-lambda)*(1-S0(x_lambda)).

Checked reuse: `Zeta23.CCM.poleNeutral_even_shifted_det_quotient`.

## M10.04 — `Zeta23.CCM.poleNeutralOddShiftedRay`

Current: **EXACT_API_ABSENT**. Kind: DEFINITION. Task: **T05**.

Origin: `None`.

Required contract: Alias actual negative adjoint ray -(D0*)^-1(A0-lambda)^-1 S0*, not the even ray.

## M10.05 — `Zeta23.CCM.poleNeutral_oddShifted_eigen_iff`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: Below actual even bottom: lambda is an odd eigenvalue iff <g0,y_lambda>=1 in the existing inner-product convention.

Checked reuse: `Zeta23.CCM.poleNeutral_odd_eigenvector_eq_pairing_smul_adjointRay`, `Zeta23.CCM.poleNeutral_odd_eigen_adjointRay_pairing_eq_one`.

## M10.06 — `Zeta23.CCM.poleNeutral_oddShifted_det_eq`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: Below even bottom: det(B0-lambda)=det(A0-lambda)*(1-<g0,y_lambda>).

Checked reuse: `Zeta23.CCM.poleNeutral_odd_adjoint_shifted_det_quotient`.

## M11.01 — `Zeta23.CCM.PoleNeutralGroundBranch`

Current: **EXACT_API_ABSENT**. Kind: INDUCTIVE. Task: **T05**.

Origin: `None`.

Required contract: Inductive strictEven/strictOdd/tie tag indexed by actual neutral bottoms and their proof conditions; selected parity remains a separate field.

## M11.02 — `Zeta23.CCM.poleNeutralGround_branch_exhaustive`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: Trichotomy of actual neutral bottoms at one L,K; no branch skipped.

## M11.03 — `Zeta23.CCM.poleNeutral_tied_kernel_compatibility`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: For every actual tied even or odd eigenvector, its own-side intertwining forcing annihilates the opposite shifted kernel; retain source scalar possibly zero.

Checked reuse: `Zeta23.CCM.poleNeutral_tied_ground_singular_safe_package`.

## M11.04 — `Zeta23.CCM.poleNeutral_tied_complementary_response`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T05**.

Origin: `None`.

Required contract: For those actual tied vectors: inverse on positive complement plus actual kernel component; prove range membership before inverse.

Checked reuse: `Zeta23.CCM.poleNeutral_tied_ground_singular_safe_package`.

## M12.01 — `Zeta23.CCM.exists_bottomAvoidingThreshold`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.CCM.CanonicalDeepThresholdSelection`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (Kd : ℕ),   3 ≤ Kd →     ∀ (D : ℝ),       0 < D →         ∃ eta,           D / 3 < eta ∧             eta < D / 2 ∧               ∀ (K : ℕ) (hK : 3 ≤ K),                 K ≤ Kd →                   Zeta23.CCM.nativeDeepThresholdGap D Kd ≤ |Zeta23.CCM.poleNeutralGlobalRayleighBottom L K hL hK + eta|

## M12.02 — `Zeta23.CCM.exists_least_deepPoleNeutralCutoff`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.CCM.CanonicalDeepThresholdSelection`.

Required contract: ∀ {L : ℝ} (hL : 0 < L) (Kd : ℕ),   3 ≤ Kd →     ∀ (D : ℝ),       0 < D →         ∀ p ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace Kd,           (Zeta23.CCM.canonicalPoleEvenFunctional L Kd) p = 0 →             (Zeta23.CCM.canonicalPoleOddFunctional L Kd) p = 0 →               ‖p‖ = 1 →                 (inner ℂ ((Matrix.toEuclideanLin (Zeta23.CCM.canonicalSourceMatrix L Kd)) p) p).re ≤ -D →                   Nonempty (Zeta23.CCM.NativeDeepThresholdGroundData L Kd D hL)

## M12.03 — `Zeta23.CCM.deepThreshold_predecessor_inverse_bound`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.CCM.CanonicalDeepThresholdSelection`.

Required contract: ∀ {L D : ℝ} {Kd : ℕ} {hL : 0 < L},   0 < D →     ∀ (s : Zeta23.CCM.NativeDeepThresholdGroundData L Kd D hL),       ∃ r,         ‖LinearMap.toContinuousLinearMap ↑r.evenGround.symm‖ ≤ 6 * ↑(Kd - 1) / D ∧           ‖LinearMap.toContinuousLinearMap ↑r.oddGround.symm‖ ≤ 6 * ↑(Kd - 1) / D ∧             ‖LinearMap.toContinuousLinearMap ↑r.evenDetector.symm‖ ≤ 12 * ↑(Kd - 1) / D ∧               ‖LinearMap.toContinuousLinearMap ↑r.oddDetector.symm‖ ≤ 12 * ↑(Kd - 1) / D

## M12.04 — `Zeta23.CCM.deepThreshold_selectedParity_simple`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.CCM.CanonicalDeepThresholdSelection`.

Required contract: ∀ {L D : ℝ} {Kd : ℕ} {hL : 0 < L},   0 < D →     ∀ (s : Zeta23.CCM.NativeDeepThresholdGroundData L Kd D hL),       (Module.finrank ℂ ↥(Module.End.eigenspace (Zeta23.CCM.poleNeutralEvenCompressedCanonical L s.cutoff) ↑s.lam) = 1 ∧           ∃ u, ‖u‖ = 1 ∧ (Zeta23.CCM.poleNeutralEvenCompressedCanonical L s.cutoff) u = ↑s.lam • u) ∨         Module.finrank ℂ ↥(Module.End.eigenspace (Zeta23.CCM.poleNeutralOddCompressedCanonical L s.cutoff) ↑s.lam) = 1 ∧           ∃ w, ‖w‖ = 1 ∧ (Zeta23.CCM.poleNeutralOddCompressedCanonical L s.cutoff) w = ↑s.lam • w

## M13.01 — `Zeta23.CCM.DetectorRetainedSchurState`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: STRUCTURE. Task: **T14**.

Origin: `Zeta23.CCM.DetectorRetainedSchurState`.

Required contract: Keep the one-step selected-ground scalar and the full detector-complement Schur form distinct; prove DS/DL.

## M13.02 — `Zeta23.CCM.selectedGround_shiftedSchur_eq`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.CCM.DetectorRetainedSchurState`.

Required contract: ∀ {sigma : Zeta23.CCM.ReversalParity} {L D : ℝ} {Kd : ℕ} {hL : 0 < L}   (state : Zeta23.CCM.DetectorRetainedSchurState sigma L Kd D hL),   let gamma := state.selectedParity;   have J := Zeta23.CCM.nativeSelectedGroundPredecessorEmbedding gamma state.selection;   have T := Zeta23.CCM.nativePoleNeutralParityShifted gamma L state.selection.cutoff state.selection.lam;   have P := Zeta23.CCM.nativeSelectedGroundPredecessorEquiv gamma state.inverses;   have y := (Zeta23.CCM.isometricDetectorComplementCoordinate J) state.selectedGround;   have response := (Zeta23.CCM.isometricDetectorResponse J T P) y;   inner ℂ ((Zeta23.CCM.nativePoleNeutralParityCanonical gamma L state.selection.cutoff) ↑y) ↑y -       ↑state.selection.lam * inner ℂ ↑y ↑y =     inner ℂ (P response) response

## M13.03 — `Zeta23.CCM.originalDetector_schur_completion`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.CCM.DetectorRetainedSchurState`.

Required contract: ∀ {sigma : Zeta23.CCM.ReversalParity} {L D : ℝ} {Kd : ℕ} {hL : 0 < L}   (state : Zeta23.CCM.DetectorRetainedSchurState sigma L Kd D hL),   let J := Zeta23.CCM.nativeDetectorPredecessorEmbedding sigma state.selection;   have T := Zeta23.CCM.nativePoleNeutralParityShifted sigma L Kd (-state.selection.eta);   have P := Zeta23.CCM.nativeDetectorPredecessorEquiv sigma state.inverses;   have x := (LinearMap.adjoint J.toLinearMap) state.detector;   have y := (Zeta23.CCM.isometricDetectorComplementCoordinate J) state.detector;   have z := x + (Zeta23.CCM.isometricDetectorResponse J T P) y;   inner ℂ (T state.detector) state.detector =     inner ℂ (P z) z + inner ℂ ((Zeta23.CCM.nativeDetectorSchurOperator sigma state.inverses) y) y

## M13.04 — `Zeta23.CCM.originalDetector_schur_loss_lower`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T14**.

Origin: `Zeta23.CCM.DetectorRetainedSchurState`.

Required contract: ∀ {sigma : Zeta23.CCM.ReversalParity} {L D : ℝ} {Kd : ℕ} {hL : 0 < L}   (state : Zeta23.CCM.DetectorRetainedSchurState sigma L Kd D hL),   have y :=     (Zeta23.CCM.isometricDetectorComplementCoordinate         (Zeta23.CCM.nativeDetectorPredecessorEmbedding sigma state.selection))       state.detector;   y ≠ 0 ∧     (inner ℂ ((Zeta23.CCM.nativeDetectorSchurOperator sigma state.inverses) y) y).re ≤ -(D - state.selection.eta) ∧       (inner ℂ ((Zeta23.CCM.nativeDetectorSchurOperator sigma state.inverses) y) y).re < -D / 2

## M14.01 — `Zeta23.CCM.canonicalTrialResidual`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T06**.

Origin: `Zeta23.CCM.CanonicalTrialResidualChannels`.

Required contract: Independent spectral and native-channel definitions of the same trial residual in its own parity T_sigma,0 (A0 even; B0 odd), not the selected-ground parity; complete complex Gram terms; even M4 bounds apply only to eligible even inputs.

**Scope:** Legacy named residual is on LEGAL carrier; mandatory native packet must use new neutral companion with explicit parity/metric.

## M14.02 — `Zeta23.CCM.canonicalTrialResidual_variance_eq`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T06**.

Origin: `None`.

Required contract: Alias existing LEGAL residual variance; native packet uses separately named neutral variance with actual own parity.

Checked reuse: `Zeta23.CCM.canonicalTrialResidual_variance`.

**Scope:** Legacy named residual is on LEGAL carrier; mandatory native packet must use new neutral companion with explicit parity/metric.

## M14.03 — `Zeta23.CCM.canonicalTrialResidual_channels_sum`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T06**.

Origin: `None`.

Required contract: Alias existing LEGAL residual channel sum, alongside mandatory neutral companion. Never infer neutral from legal.

Checked reuse: `Zeta23.CCM.nativeTrialResidual_sum`, `Zeta23.CCM.parityCanonicalTrialChannel_sum`.

**Scope:** Legacy named residual is on LEGAL carrier; mandatory native packet must use new neutral companion with explicit parity/metric.

## M14.04 — `Zeta23.CCM.canonicalTrialResidual_gram_sum`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T06**.

Origin: `None`.

Required contract: Alias existing LEGAL Gram equality, alongside mandatory neutral companion with all complex cross terms.

Checked reuse: `Zeta23.CCM.canonicalTrialResidual_channelGram`.

**Scope:** Legacy named residual is on LEGAL carrier; mandatory native packet must use new neutral companion with explicit parity/metric.

## M15.01 — `Zeta23.CCM.nativeOriginalPrimeField`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T08**.

Origin: `Zeta23.CCM.OriginalSincNativeSource`.

Required contract: Actual integer/von-Mangoldt fields X,U and N*X=U; full finite divisor identity; prove required rapid integer-drive bound on exact j.

## M15.02 — `Zeta23.CCM.nativeOriginalIntegerDrive`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T08**.

Origin: `Zeta23.CCM.OriginalSincNativeSource`.

Required contract: Actual integer/von-Mangoldt fields X,U and N*X=U; full finite divisor identity; prove required rapid integer-drive bound on exact j.

## M15.03 — `Zeta23.CCM.native_divisor_convolution_identity`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T08**.

Origin: `None`.

Required contract: Literal nativeIntegerTranslateAction applied to actual X_j equals actual U_j, pointwise local finite before any L2 assumption.

Checked reuse: `Zeta23.CCM.nativeIntegerTranslateAction_primeField_eq_integerDriveField`.

## M15.04 — `Zeta23.CCM.native_primeCoefficients_unique`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T08**.

Origin: `Zeta23.CCM.NativeIntegerPrimeSource`.

Required contract: ∀ (f : ArithmeticFunction ℝ), (∀ (n : ℕ), ∑ d ∈ n.divisors, f d = Real.log ↑n) → f = ArithmeticFunction.vonMangoldt

## M15.05 — `Zeta23.CCM.nativeOriginalIntegerDrive_rapid_bound`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T08**.

Origin: `None`.

Required contract: For every A>0 construct C>0,T>=0 from A and the fixed source with |U(t)|<=C exp(-A*t) for t>=T. Prove via R2.2 finite-order lattice summation. Existing first-order bound supports current Y but does not by itself meet this stronger named rapid bound. A03 optimized double-exponential estimate stays optional.

Checked reuse: `Zeta23.CCM.nativeOriginalIntegerDrive_decay`.

## M16.01 — `Zeta23.CCM.poleNeutral_compactInverse_exists_unique`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T07**.

Origin: `Zeta23.CCM.PoleNeutralCompactInverse`.

Required contract: ∀ {s : ℝ},   0 ≤ s →     ∀ {f : ℝ → ℂ},       MeasureTheory.MemLp f 2 MeasureTheory.volume →         (∀ x ∉ Set.Icc (-s) s, f x = 0) →           ∫ (x : ℝ), Zeta23.CCM.nativePoleExponential (1 / 2) x * f x = 0 →             ∫ (x : ℝ), Zeta23.CCM.nativePoleExponential (-1 / 2) x * f x = 0 → ∃! u, True

**Scope:** Default pretty type hides the binder type in existsUnique u, True. Actual source binder is NativeCompactPoleH2 s f; print full typed witness and structure fields in final semantic receipt.

## M16.02 — `Zeta23.CCM.poleNeutral_compactInverse_support`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T07**.

Origin: `Zeta23.CCM.PoleNeutralCompactInverse`.

Required contract: ∀ {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume)   (hsupport : ∀ x ∉ Set.Icc (-s) s, f x = 0) (hplus : ∫ (x : ℝ), Zeta23.CCM.nativePoleExponential (1 / 2) x * f x = 0)   (hminus : ∫ (x : ℝ), Zeta23.CCM.nativePoleExponential (-1 / 2) x * f x = 0),   tsupport (Zeta23.CCM.nativePoleCompactH2 hs hf hsupport hplus hminus).value ⊆ Set.Icc (-s) s

## M16.03 — `Zeta23.CCM.poleNeutral_compactInverse_norm_bound`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T07**.

Origin: `Zeta23.CCM.PoleNeutralCompactInverse`.

Required contract: ∀ {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume)   (hsupport : ∀ x ∉ Set.Icc (-s) s, f x = 0) (hplus : ∫ (x : ℝ), Zeta23.CCM.nativePoleExponential (1 / 2) x * f x = 0)   (hminus : ∫ (x : ℝ), Zeta23.CCM.nativePoleExponential (-1 / 2) x * f x = 0),   (MeasureTheory.eLpNorm (Zeta23.CCM.nativePoleCompactH2 hs hf hsupport hplus hminus).value 2         MeasureTheory.volume).toReal ≤     4 * (MeasureTheory.eLpNorm f 2 MeasureTheory.volume).toReal

## M17.01 — `Zeta23.CCM.originalDetector_correlationField_eq_sourceConvolution`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T11**.

Origin: `None`.

Required contract: Literal Pi*(k*k)=q*X_j, pointwise with local cutoff/convolution exchanges proved. R5.5.

## M17.02 — `Zeta23.CCM.originalDetector_projectedForcing_eq`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T11**.

Origin: `None`.

Required contract: Actual b_eta = (P+eta I)x+B y for original finite p, and full original-response channel decomposition with explicit difference p_phys-f. R5.

## M17.03 — `Zeta23.CCM.originalDetector_forcing_error_bound`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T11**.

Origin: `None`.

Required contract: The exact H1 projection bound of R5.6, with finite-mode and eta factors retained and source-only asymptotic after proved eta control.

## M18.01 — `Zeta23.CCM.nativePositiveCompletion`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T08**.

Origin: `Zeta23.CCM.NativePositiveCompletion`.

Required contract: Actual a-triangle and c completion; exact multiplier; sound mass bound below 605/621; independently stable actual Y.

## M18.02 — `Zeta23.CCM.nativePositiveCompletion_nonneg`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T08**.

Origin: `Zeta23.CCM.NativePositiveCompletion`.

Required contract: ∀ (t : ℝ), 0 ≤ Zeta23.CCM.nativePositiveCompletion t

## M18.03 — `Zeta23.CCM.nativePositiveCompletion_laplace`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T08**.

Origin: `None`.

Required contract: For Re w>0,w!=1/2 actual Laplace(a)=R(w)zeta(w+1/2); separate exceptional value Laplace(a)(1/2)=1/2.

## M18.04 — `Zeta23.CCM.nativePositiveCompletion_mass_lt`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T08**.

Origin: `None`.

Required contract: Actual L1 norm strictly below605/621, from completed native mass proof, not Python fixture.

Checked reuse: `Zeta23.CCM.nativePositiveCompletion_integral_norm_lt_605_div_621`.

## M18.05 — `Zeta23.CCM.nativeCompletedInput`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T08**.

Origin: `Zeta23.CCM.NativeCompletedInput`.

Required contract: Actual a-triangle and c completion; exact multiplier; sound mass bound below 605/621; independently stable actual Y.

## M18.06 — `Zeta23.CCM.nativeCompletedInput_equation`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T08**.

Origin: `Zeta23.CCM.NativeCompletionEquation`.

Required contract: ∀ (t : ℝ),   ∫ (s : ℝ), Zeta23.CCM.nativePositiveCompletion s * Zeta23.CCM.nativeOriginalPrimeField (t - s) =     Zeta23.CCM.nativeCompletedInput t

## M18.07 — `Zeta23.CCM.nativeCompletedInput_memLp`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T08**.

Origin: `Zeta23.CCM.NativeCompletedInput`.

Required contract: ∀ {epsilon : ℝ},   0 ≤ epsilon → MeasureTheory.MemLp (Zeta23.CCM.nativeDampedCompletedInput epsilon) 2 MeasureTheory.volume

## M19.01 — `Zeta23.CCM.nativeAdjointResidualIterate`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T01**.

Origin: `Zeta23.CCM.NativeDampedCompletionResidual`.

Required contract: Core: actual finite-step identity, norm monotonicity and invariant adjoint-kernel projection. Strong convergence is an explicitly optional promotion, not needed for B-Y.

## M19.02 — `Zeta23.CCM.nativeAdjointResidual_norm_loss`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T01**.

Origin: `Zeta23.CCM.NativeDampedCompletionResidual`.

Required contract: ∀ (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (e : ↥Zeta23.CCM.nativeCompletionCausalL2),   ‖Zeta23.CCM.nativeAdjointResidualStep epsilon hepsilon e‖ ^ 2 ≤     ‖e‖ ^ 2 - (2 - (605 / 621) ^ 2) * ‖(Zeta23.CCM.nativeDampedCompletionCausalL2Adjoint epsilon hepsilon) e‖ ^ 2

## M19.03 — `Zeta23.CCM.nativeAdjointResidual_norm_antitone`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T01**.

Origin: `Zeta23.CCM.NativeDampedCompletionResidual`.

Required contract: ∀ (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (e : ↥Zeta23.CCM.nativeCompletionCausalL2),   Antitone fun n => ‖Zeta23.CCM.nativeAdjointResidualIterate epsilon hepsilon e n‖

## M19.04 — `Zeta23.CCM.nativeAdjointResidual_kernelProjection_preserved`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T01**.

Origin: `Zeta23.CCM.NativeDampedCompletionResidual`.

Required contract: ∀ (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (e : ↥Zeta23.CCM.nativeCompletionCausalL2) (n : ℕ),   (Zeta23.CCM.nativeCompletionAdjointKernelProjection epsilon hepsilon)       (Zeta23.CCM.nativeAdjointResidualIterate epsilon hepsilon e n) =     (Zeta23.CCM.nativeCompletionAdjointKernelProjection epsilon hepsilon) e

## M20.01 — `Zeta23.ExceptionalZero.nativeZeroJetAdjointWitness`

Current: **SOURCE_DEFINED_KIND_NOT_PRINTED_IN_SELECTED_RECEIPT**. Kind: DEFINITION. Task: **T01**.

Origin: `Zeta23.ExceptionalZero.NativeRangeZeroJetObstruction`.

Required contract: Direct multiplicity-aware exponential-polynomial L2 witness against actual Yepsilon; no need to port full Hardy factorization.

## M20.02 — `Zeta23.ExceptionalZero.nativeZeroJet_annihilates_range`

Current: **COMPILER_CHECKED_COMPONENT**. Kind: THEOREM. Task: **T01**.

Origin: `Zeta23.ExceptionalZero.NativeActualKernelZeroJets`.

Required contract: ∀ (rho : ↑Zeta23.zetaZeroConfig.carrier) (hoff : (↑rho).re ≠ 1 / 2) (f : ↥Zeta23.CCM.nativeCompletionCausalL2),   inner ℂ (Zeta23.ExceptionalZero.nativeZeroJetAdjointWitness rho hoff)       ((Zeta23.CCM.nativeDampedCompletionCausalL2Operator (Zeta23.ExceptionalZero.nativeZeroJetDamping rho) ⋯) f) =     0

## M20.03 — `Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_ne_zero`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T01**.

Origin: `None`.

Required contract: Actual <psi_rho,Y_epsilon_rho> !=0 with degree m-1 and value (-1)^m R(p)J(p)zeta^(m)(rhoR). R1.

Checked reuse: `Zeta23.CCM.nativeCausalExponentialWitness_inner_completedInput`, `Zeta23.CCM.nativeCompletedInput_complexLaplace`, `Zeta23.ExceptionalZero.nativeZeroJetInputMultiplier_order`, `Zeta23.ExceptionalZero.nativeZeroJetSourceFactor_ne_zero`.

## M20.04 — `Zeta23.ExceptionalZero.nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T01**.

Origin: `None`.

Required contract: Actual off-line rho implies actual stable Y_epsilon outside closure(range A_epsilon), with constructed damping and witness; no order premises supplied.

Checked reuse: `Zeta23.CCM.nativeCompletedInput_not_mem_rangeClosure_of_analyticOrders`, `Zeta23.ExceptionalZero.nativeActualKernelLaplace_order_of_zero`.

## M21.01 — `Zeta23.CCM.OriginalNativeExteriorRecord`

Current: **EXACT_API_ABSENT**. Kind: STRUCTURE. Task: **T12**.

Origin: `None`.

Required contract: Constructed original source response, interior, two causal exterior restrictions, histories, exact reconstruction and finite-source/normal/Galerkin distinctions. Not full-contact data.

## M21.02 — `Zeta23.CCM.originalNativeExterior_history_eq`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T12**.

Origin: `None`.

Required contract: Exact convolution/causal split including actual nonzero interior history; no generic free history substituted.

## M21.03 — `Zeta23.CCM.originalNativeExterior_residual_eq`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T12**.

Origin: `None`.

Required contract: Actual response equals defined native channels and projected/outer/normal decomposition on supported finite tests.

## M22.01 — `Zeta23.CCM.Step123NativeOutput`

Current: **EXACT_API_ABSENT**. Kind: STRUCTURE. Task: **T13**.

Origin: `None`.

Required contract: Rho-free dependent mathematical record indexed beta,sigma,a with one actual padded retained state and all fields in OUTPUT_FIELD_CONTRACT.json.

## M22.02 — `Zeta23.CCM.Step123NativeOutput.arithmeticView`

Current: **EXACT_API_ABSENT**. Kind: DEFINITION. Task: **T13**.

Origin: `None`.

Required contract: Projection of literal native X,U, divisor identity and original source bridge from the same packet.

## M22.03 — `Zeta23.CCM.Step123NativeOutput.rangeView`

Current: **EXACT_API_ABSENT**. Kind: DEFINITION. Task: **T13**.

Origin: `None`.

Required contract: Projection of literal a,Y,A_epsilon, domain/transform and adjoint iteration data, no range-membership assertion.

## M22.04 — `Zeta23.CCM.Step123NativeOutput.structuralView`

Current: **EXACT_API_ABSENT**. Kind: DEFINITION. Task: **T13**.

Origin: `None`.

Required contract: Projection of same detector/selected ground, both Schur records, source correction, residual and exterior; branches explicit.

## M23.01 — `Zeta23.ExceptionalZero.GeneratedStep123Output`

Current: **EXACT_API_ABSENT**. Kind: STRUCTURE. Task: **T14**.

Origin: `None`.

Required contract: Zero-indexed extension storing chosen separation, late aperture, the filled native packet and constructed actual zero-jet obstruction.

## M23.02 — `Zeta23.ExceptionalZero.exists_step123Output_of_offLine_zero`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T14**.

Origin: `None`.

Required contract: Actual rho,0<beta<displacement,phase,R -> nonempty generated packet at L>max(R,4), Kd=ceil L^4, unit native energy<=-exp(beta L), no extra Step1-3 hypotheses.

Checked reuse: `Zeta23.CCM.exists_originalDetectorPaddedPhase_admissible_retained_state`.

## M23.03 — `Zeta23.ExceptionalZero.exists_eachPhase_cofinal_step123Output`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T14**.

Origin: `None`.

Required contract: Both original phases separately have the flagship cofinal output quantifiers; no simultaneous deep-aperture conclusion.

Checked reuse: `Zeta23.CCM.exists_originalDetectorPaddedPhase_admissible_retained_state`.

## M24.01 — `Zeta23.ExceptionalZero.riemannHypothesis_of_originalPrimeField_allDampedL2`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T15**.

Origin: `None`.

Required contract: Original A-X predicate -> Mathlib RiemannHypothesis; use A-X->B-Y and actual obstruction.

Checked reuse: `Zeta23.CCM.nativeCompletedInput_mem_rangeClosure_of_prime_memLp`.

**Scope:** Conditional sufficiency only; its A-X/B-Y/C-Schur premise remains OPEN.

## M24.02 — `Zeta23.ExceptionalZero.riemannHypothesis_of_nativeInput_allRangeClosure`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T15**.

Origin: `None`.

Required contract: Original B-Y predicate -> Mathlib RiemannHypothesis; actual Y/kernel/witness only.

**Scope:** Conditional sufficiency only; its A-X/B-Y/C-Schur premise remains OPEN.

## M24.03 — `Zeta23.ExceptionalZero.riemannHypothesis_of_detectorSchurLoss_subexponential`

Current: **EXACT_API_ABSENT**. Kind: THEOREM. Task: **T15**.

Origin: `None`.

Required contract: Original C-Schur universal complete signed bound -> Mathlib RiemannHypothesis; use same-state cofinal depth, no A-X/B-Y premise.

Checked reuse: `Zeta23.CCM.originalDetector_schur_loss_lower`.

**Scope:** Conditional sufficiency only; its A-X/B-Y/C-Schur premise remains OPEN.
