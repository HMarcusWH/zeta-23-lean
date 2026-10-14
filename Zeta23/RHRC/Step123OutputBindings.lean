import Zeta23.CCM.UniversalSincDetector
import Zeta23.CCM.IsometricDetectorSchur
import Zeta23.CCM.IsometricGroundSchur
import Zeta23.CCM.NativeDetectorSchur
import Zeta23.CCM.NativeSelectedGroundSchur
import Zeta23.CCM.DetectorRetainedSchurState
import Zeta23.CCM.OriginalDetectorFourierPrerequisites
import Zeta23.CCM.OriginalSincWeightedPoleMoments
import Zeta23.CCM.NativeAbelDiscrepancy
import Zeta23.CCM.OriginalSincLogDrive
import Zeta23.ExceptionalZero.PositiveLaplaceBoundary
import Zeta23.ExceptionalZero.PositiveLaplaceAnalytic
import Zeta23.ExceptionalZero.UniversalSincSignedLaplace
import Zeta23.CCM.UniversalSincProductMoments
import Zeta23.CCM.UniversalSincInverseGevreyBounds
import Zeta23.ExceptionalZero.PositiveLaplaceTilt
import Zeta23.CCM.NativeDeepThresholdInverseBudgets
import Zeta23.CCM.NativeDeepThresholdSimplicity
import Zeta23.CCM.NativeDeepThresholdEvenMoment
import Zeta23.CCM.UniversalSincDetectorBounds
import Zeta23.CCM.UniversalSincDetectorInverse
import Zeta23.CCM.UniversalSincSourceLaw
import Zeta23.CCM.UniversalSincSourceCharacteristic
import Zeta23.CCM.UniversalSincBoxDensity
import Zeta23.CCM.UniversalSincSourceTail
import Zeta23.CCM.UniversalSincSourceDensity
import Zeta23.CCM.UniversalSincSourceDensityTransform
import Zeta23.CCM.UniversalSincSourceDensityIdentification
import Zeta23.CCM.UniversalSincSourceComplexTransform
import Zeta23.CCM.UniversalSincSourceSymmetry
import Zeta23.CCM.UniversalSincSourceFacade
import Zeta23.CCM.OriginalSincNativeSource
import Zeta23.CCM.OriginalSincNativeMass
import Zeta23.ExceptionalZero.UniversalSincNativeSourceIdentification
import Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie
import Zeta23.ExceptionalZero.UniversalSincPhysicalDetector
import Zeta23.ExceptionalZero.UniversalSincDetectorVisibility
import Zeta23.CCM.CanonicalPoleNeutralGeometry
import Zeta23.CCM.CanonicalPoleNeutralCarrier
import Zeta23.CCM.CanonicalPoleExponentialMoments
import Zeta23.CCM.CanonicalPoleNeutralIntertwining
import Zeta23.CCM.CanonicalPoleNeutralNormals
import Zeta23.CCM.CanonicalPoleNeutralCubicWitness
import Zeta23.CCM.CanonicalPoleNeutralSourceMoment
import Zeta23.CCM.CanonicalPoleNeutralIndexRigidity
import Zeta23.CCM.CanonicalTrialResidualChannels
import Zeta23.CCM.NativeIntegerPrimeSource
import Zeta23.CCM.NativeIntegerPrimeField
import Zeta23.CCM.NativeIntegerPrimeConvolution
import Zeta23.CCM.NativePositiveCompletion
import Zeta23.CCM.NativePositiveCompletionCells
import Zeta23.CCM.NativePositiveCompletionMass
import Zeta23.CCM.NativePositiveCompletionHead
import Zeta23.CCM.NativePositiveCompletionTail
import Zeta23.CCM.NativePositiveCompletionCertificate
import Zeta23.CCM.CanonicalPoleNeutralShiftedSecular
import Zeta23.CCM.CanonicalPoleNeutralTiePackage
import Zeta23.ExceptionalZero.ZetaRealStripNonvanishing
import Zeta23.CCM.CanonicalPoleNeutralNesting
import Zeta23.CCM.CanonicalPoleNeutralBottomNFlow
import Zeta23.CCM.FiniteBottomGapSelector
import Zeta23.CCM.CanonicalDeepThresholdSelection
import Zeta23.CCM.NativePoleNeutralTrialDepth
import Zeta23.CCM.PoleNeutralCompactInverse
import Zeta23.CCM.NativeDeepThresholdGround
import Zeta23.CCM.PoleNeutralUniqueness
import Zeta23.CCM.OriginalSincCompactPotential
import Zeta23.ExceptionalZero.PositiveMomentSeries
import Zeta23.ExceptionalZero.PositiveMGFContinuation
import Zeta23.ExceptionalZero.UniversalSincCorrelationReal
import Zeta23.CCM.NativeFloorCompletionSource
import Zeta23.CCM.NativeRationalCompletionLaplace
import Zeta23.CCM.Step123PrimeSeam
import Zeta23.RHRC.SourceCandidateResolution
import Lean.Util.CollectAxioms

open Lean Lean.Elab Command

/-!
Audit of the implemented components only. None of the missing output-producer
roots is replaced by a generic interface here. The complete M25 acceptance
remains open until the original mandatory producer declarations exist.
Uses the repository's existing compiler-backed source-candidate resolver.
-/

run_cmd do
  let some checkedHead ← liftIO <| IO.getEnv "POST290_CHECKED_HEAD"
    | throwError "Missing POST290_CHECKED_HEAD compiler context"
  let some checkedTree ← liftIO <| IO.getEnv "POST290_CHECKED_TREE"
    | throwError "Missing POST290_CHECKED_TREE compiler context"
  liftIO <| IO.println s!"POST290_COMPILER_CONTEXT\t{checkedHead}\t{checkedTree}"
  let roots : Array (Name × String) := #[
    (``Zeta23.CCM.UniversalSinc.hasSum_width, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.summable_norm_sinc_sub_one, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.multipliable_sinc, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.hasProdUniformlyOn_compact, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.analyticAt_product, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.fixed_coincident_factor_zeros, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.product_norm_ofReal_le_one, "Zeta23.CCM.UniversalSincDetectorBounds"),
    (``Zeta23.CCM.UniversalSinc.product_norm_ofReal_le_gevrey, "Zeta23.CCM.UniversalSincDetectorBounds"),
    (``Zeta23.CCM.UniversalSinc.integrable_product_ofReal_norm_moment, "Zeta23.CCM.UniversalSincDetectorInverse"),
    (``Zeta23.CCM.UniversalSinc.integrable_product_ofReal, "Zeta23.CCM.UniversalSincDetectorInverse"),
    (``Zeta23.CCM.UniversalSinc.inverseCandidate_eq_fourier, "Zeta23.CCM.UniversalSincDetectorInverse"),
    (``Zeta23.CCM.UniversalSinc.contDiff_inverseCandidate, "Zeta23.CCM.UniversalSincDetectorInverse"),
    (``Zeta23.CCM.UniversalSinc.sourceSampleSum_sub_partial_abs_le, "Zeta23.CCM.UniversalSincSourceLaw"),
    (``Zeta23.CCM.UniversalSinc.sourceSampleSum_ae_eq_unclamped, "Zeta23.CCM.UniversalSincSourceLaw"),
    (``Zeta23.CCM.UniversalSinc.originalSourceLaw_isProbabilityMeasure, "Zeta23.CCM.UniversalSincSourceLaw"),
    (``Zeta23.CCM.UniversalSinc.originalSourceLaw_interval_mass, "Zeta23.CCM.UniversalSincSourceLaw"),
    (``Zeta23.CCM.UniversalSinc.originalSourceLaw_eq_map_scale, "Zeta23.CCM.UniversalSincSourceLaw"),
    (``Zeta23.CCM.UniversalSinc.fixed_originalSourceLaw_isProbabilityMeasure, "Zeta23.CCM.UniversalSincSourceLaw"),
    (``Zeta23.CCM.UniversalSinc.charFun_centeredUnitBoxLaw, "Zeta23.CCM.UniversalSincSourceCharacteristic"),
    (``Zeta23.CCM.UniversalSinc.charFun_sourceSamplePartialSum, "Zeta23.CCM.UniversalSincSourceCharacteristic"),
    (``Zeta23.CCM.UniversalSinc.charFun_originalSourceLaw, "Zeta23.CCM.UniversalSincSourceCharacteristic"),
    (``Zeta23.CCM.UniversalSinc.originalSourceLaw_map_neg, "Zeta23.CCM.UniversalSincSourceCharacteristic"),
    (``Zeta23.CCM.UniversalSinc.uniformBoxPairDensity_eq_convolution, "Zeta23.CCM.UniversalSincBoxDensity"),
    (``Zeta23.CCM.UniversalSinc.originalBoxPairDensity_positive_normalized, "Zeta23.CCM.UniversalSincBoxDensity"),
    (``Zeta23.CCM.UniversalSinc.sourceSampleTail_abs_le, "Zeta23.CCM.UniversalSincSourceTail"),
    (``Zeta23.CCM.UniversalSinc.multipliable_sinc_tail, "Zeta23.CCM.UniversalSincSourceTail"),
    (``Zeta23.CCM.UniversalSinc.charFun_originalSourceTailLaw, "Zeta23.CCM.UniversalSincSourceTail"),
    (``Zeta23.CCM.UniversalSinc.originalSourceLaw_eq_prefix_conv_tail, "Zeta23.CCM.UniversalSincSourceTail"),
    (``Zeta23.CCM.UniversalSinc.originalDensityCandidate_nonneg, "Zeta23.CCM.UniversalSincSourceDensity"),
    (``Zeta23.CCM.UniversalSinc.continuous_originalDensityCandidate, "Zeta23.CCM.UniversalSincSourceDensity"),
    (``Zeta23.CCM.UniversalSinc.originalDensityCandidate_hasCompactSupport, "Zeta23.CCM.UniversalSincSourceDensity"),
    (``Zeta23.CCM.UniversalSinc.integral_originalDensityCandidate, "Zeta23.CCM.UniversalSincSourceDensity"),
    (``Zeta23.CCM.UniversalSinc.paperFT_originalDensityCandidate_ofReal, "Zeta23.CCM.UniversalSincSourceDensityTransform"),
    (``Zeta23.CCM.UniversalSinc.originalSourceLaw_eq_withDensity, "Zeta23.CCM.UniversalSincSourceDensityIdentification"),
    (``Zeta23.CCM.UniversalSinc.inverseCandidate_eq_originalDensityComplex, "Zeta23.CCM.UniversalSincSourceDensityIdentification"),
    (``Zeta23.CCM.UniversalSinc.contDiff_originalDensityCandidate, "Zeta23.CCM.UniversalSincSourceDensityIdentification"),
    (``Zeta23.CCM.UniversalSinc.paperFT_originalDensityComplex, "Zeta23.CCM.UniversalSincSourceComplexTransform"),
    (``Zeta23.CCM.UniversalSinc.fixed_paperFT_originalDensityComplex, "Zeta23.CCM.UniversalSincSourceComplexTransform"),
    (``Zeta23.CCM.UniversalSinc.originalDensityCandidate_even, "Zeta23.CCM.UniversalSincSourceSymmetry"),
    (``Zeta23.CCM.universalSincSource_nonneg, "Zeta23.CCM.UniversalSincSourceFacade"),
    (``Zeta23.CCM.universalSincSource_integral_one, "Zeta23.CCM.UniversalSincSourceFacade"),
    (``Zeta23.CCM.universalSincSource_support, "Zeta23.CCM.UniversalSincSourceFacade"),
    (``Zeta23.CCM.universalSincSource_contDiff, "Zeta23.CCM.UniversalSincSourceFacade"),
    (``Zeta23.CCM.paperFT_universalSincSource, "Zeta23.CCM.UniversalSincSourceFacade"),
    (``Zeta23.CCM.universalSincKernel_support, "Zeta23.CCM.UniversalSincSourceFacade"),
    (``Zeta23.CCM.universalSincSecondKernel_support, "Zeta23.CCM.UniversalSincSourceFacade"),
    (``Zeta23.CCM.universalSincSecondSource_integral, "Zeta23.CCM.UniversalSincSourceFacade"),
    (``Zeta23.CCM.nativeOriginalSource_supported, "Zeta23.CCM.OriginalSincNativeSource"),
    (``Zeta23.CCM.nativeOriginalSource_integral, "Zeta23.CCM.OriginalSincNativeSource"),
    (``Zeta23.CCM.nativeOriginalPrimeField_firstPrime_atom, "Zeta23.CCM.OriginalSincNativeSource"),
    (``Zeta23.CCM.nativeOriginalPrimeField_firstPrimeWindow_integral, "Zeta23.CCM.OriginalSincNativeMass"),
    (``Zeta23.CCM.nativeOriginalPrimeField_not_identically_zero, "Zeta23.CCM.OriginalSincNativeMass"),
    (``Zeta23.ExceptionalZero.originalSincSecondTest_eq_native_kernel, "Zeta23.ExceptionalZero.UniversalSincNativeSourceIdentification"),
    (``Zeta23.ExceptionalZero.nativeOriginalSource_cast_eq_physical, "Zeta23.ExceptionalZero.UniversalSincNativeSourceIdentification"),
    (``Zeta23.CCM.poleNeutralIndex_adjoint_index_eq_square_of_momentFour_eq_zero, "Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie"),
    (``Zeta23.CCM.poleNeutralOddShifted_isPositive_of_le_bottom, "Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie"),
    (``Zeta23.CCM.poleNeutral_simpleEven_tie_momentFour_ne_zero, "Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie"),
    (``Zeta23.ExceptionalZero.paperFT_originalSincTest, "Zeta23.ExceptionalZero.UniversalSincPhysicalDetector"),
    (``Zeta23.ExceptionalZero.paperFT_originalSincSecondTest, "Zeta23.ExceptionalZero.UniversalSincPhysicalDetector"),
    (``Zeta23.ExceptionalZero.fixed_originalSincTest_square_ne_zero_at_off_line_zero, "Zeta23.ExceptionalZero.UniversalSincPhysicalDetector"),
    (``Zeta23.ExceptionalZero.absolutelySummable_originalSincSquaredFilter, "Zeta23.ExceptionalZero.UniversalSincPhysicalDetector"),
    (``Zeta23.ExceptionalZero.originalSincCorrelation_eq_filteredSquaredFamily, "Zeta23.ExceptionalZero.UniversalSincPhysicalDetector"),
    (``Zeta23.ExceptionalZero.fixed_originalSincCorrelation_not_subexponential_of_right_zero, "Zeta23.ExceptionalZero.UniversalSincPhysicalDetector"),
    (``Zeta23.CCM.UniversalSinc.product_ne_zero_of_im_ne_zero, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.fixed_product_ne_zero_of_im_ne_zero, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.ExceptionalZero.originalSincMultiplier_ne_zero_at_off_line_zero,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.ExceptionalZero.fixed_originalSincMultiplier_square_ne_zero_at_off_line_zero,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.ExceptionalZero.originalSincMultiplier_eq_zero_iff_of_im_ne_zero,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.ExceptionalZero.originalSincMultiplier_deriv_ne_zero_at_elementary_pair,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.CCM.canonicalPoleOddFunctional_evenIndex, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.poleNeutralIndexLinearMap_injective, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.poleNeutralIndexLinearMap_surjective, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.canonicalPoleEvenFunctional_nonzeroWitness, "Zeta23.CCM.CanonicalPoleNeutralCarrier"),
    (``Zeta23.CCM.finrank_poleNeutralEvenSubspace, "Zeta23.CCM.CanonicalPoleNeutralCarrier"),
    (``Zeta23.CCM.finrank_poleNeutralOddSubspace, "Zeta23.CCM.CanonicalPoleNeutralCarrier"),
    (``Zeta23.CCM.poleNeutralIndex_norm_lower, "Zeta23.CCM.CanonicalPoleNeutralCarrier"),
    (``Zeta23.CCM.canonicalPoleExponentialMoment_eq_profiles, "Zeta23.CCM.CanonicalPoleExponentialMoments"),
    (``Zeta23.CCM.canonicalPoleExponentialMoments_iff_profiles, "Zeta23.CCM.CanonicalPoleExponentialMoments"),
    (``Zeta23.CCM.poleNeutralEven_iff_exponentialMoments, "Zeta23.CCM.CanonicalPoleExponentialMoments"),
    (``Zeta23.CCM.poleNeutralOdd_iff_exponentialMoments, "Zeta23.CCM.CanonicalPoleExponentialMoments"),
    (``Zeta23.CCM.poleNeutralCompressedIndexDefect_eq_projected_legal_add_residual,
      "Zeta23.CCM.CanonicalPoleNeutralIntertwining"),
    (``Zeta23.CCM.poleOddProfile_dot_centeredZeroExtend, "Zeta23.CCM.CanonicalPoleNeutralNesting"),
    (``Zeta23.CCM.canonicalPoleEvenFunctional_centeredZeroExtend, "Zeta23.CCM.CanonicalPoleNeutralNesting"),
    (``Zeta23.CCM.canonicalPoleOddFunctional_centeredZeroExtend, "Zeta23.CCM.CanonicalPoleNeutralNesting"),
    (``Zeta23.CCM.inner_canonicalSourceMatrix_euclideanCenteredZeroExtend, "Zeta23.CCM.CanonicalPoleNeutralNesting"),
    (``Zeta23.CCM.inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend, "Zeta23.CCM.CanonicalPoleNeutralNesting"),
    (``Zeta23.CCM.inner_poleNeutralOddCompressedCanonical_centeredZeroExtend, "Zeta23.CCM.CanonicalPoleNeutralNesting"),
    (``Zeta23.CCM.poleNeutralEvenRayleighBottom_antitone_of_le, "Zeta23.CCM.CanonicalPoleNeutralBottomNFlow"),
    (``Zeta23.CCM.poleNeutralOddRayleighBottom_antitone_of_le, "Zeta23.CCM.CanonicalPoleNeutralBottomNFlow"),
    (``Zeta23.CCM.poleNeutralGlobalRayleighBottom_antitone_of_le, "Zeta23.CCM.CanonicalPoleNeutralBottomNFlow"),
    (``Zeta23.CCM.poleNeutralEven_predecessor_compression_eq, "Zeta23.CCM.CanonicalPoleNeutralBottomNFlow"),
    (``Zeta23.CCM.poleNeutralOdd_predecessor_compression_eq, "Zeta23.CCM.CanonicalPoleNeutralBottomNFlow"),
    (``Zeta23.CCM.finrank_poleNeutralEven_successor_shell_eq_one, "Zeta23.CCM.CanonicalPoleNeutralBottomNFlow"),
    (``Zeta23.CCM.finrank_poleNeutralOdd_successor_shell_eq_one, "Zeta23.CCM.CanonicalPoleNeutralBottomNFlow"),
    (``Zeta23.CCM.exists_finite_real_gap_selector, "Zeta23.CCM.FiniteBottomGapSelector"),
    (``Zeta23.CCM.exists_nativeDeepThreshold_bottom_separator, "Zeta23.CCM.CanonicalDeepThresholdSelection"),
    (``Zeta23.CCM.nativeDeepThreshold_crossing_retains_gap, "Zeta23.CCM.CanonicalDeepThresholdSelection"),
    (``Zeta23.CCM.nativeDeepThreshold_noncrossing_has_lower_gap, "Zeta23.CCM.CanonicalDeepThresholdSelection"),
    (``Zeta23.CCM.nativeTrial_evenOdd_norm_sq_split, "Zeta23.CCM.NativePoleNeutralTrialDepth"),
    (``Zeta23.CCM.nativeGlobalBottom_mul_norm_sq_le_given_trial_energy, "Zeta23.CCM.NativePoleNeutralTrialDepth"),
    (``Zeta23.CCM.nativeGlobalBottom_le_neg_depth_of_given_unit_trial, "Zeta23.CCM.NativePoleNeutralTrialDepth"),
    (``Zeta23.CCM.exists_nativeDeepThresholdGround_of_given_trial, "Zeta23.CCM.NativeDeepThresholdGround"),
    (``Zeta23.CCM.poleNeutral_homogeneous_eq_zero, "Zeta23.CCM.PoleNeutralUniqueness"),
    (``Zeta23.CCM.poleNeutral_eq_of_clamped_jets, "Zeta23.CCM.PoleNeutralUniqueness"),
    (``Zeta23.CCM.originalSincCompactPotential_eq_universalSincKernel, "Zeta23.CCM.PoleNeutralUniqueness"),
    (``Zeta23.CCM.nativePoleCompactInverse_contDiff_two, "Zeta23.CCM.PoleNeutralCompactInverse"),
    (``Zeta23.CCM.nativePoleCompactInverse_pole_equation, "Zeta23.CCM.PoleNeutralCompactInverse"),
    (``Zeta23.CCM.nativePoleCompactInverse_hasCompactSupport, "Zeta23.CCM.PoleNeutralCompactInverse"),
    (``Zeta23.CCM.nativePoleCompactInverse_clamped_traces, "Zeta23.CCM.PoleNeutralCompactInverse"),
    (``Zeta23.CCM.universalSincSecondKernel_elementary_moments, "Zeta23.CCM.OriginalSincCompactPotential"),
    (``Zeta23.CCM.originalSincCompactPotential_pole_equation, "Zeta23.CCM.OriginalSincCompactPotential"),
    (``Zeta23.CCM.originalSincCompactPotential_hasCompactSupport, "Zeta23.CCM.OriginalSincCompactPotential"),
    (``Zeta23.CCM.originalSincCompactPotential_clamped_traces, "Zeta23.CCM.OriginalSincCompactPotential"),
    (``Zeta23.CCM.originalSincCompactPotential_memLp_two, "Zeta23.CCM.OriginalSincCompactPotential"),
    (``Zeta23.CCM.originalSincCompactPotentialDerivative_memLp_two, "Zeta23.CCM.OriginalSincCompactPotential"),
    (``Zeta23.CCM.originalSincCompactPotentialSecondDerivative_memLp_two, "Zeta23.CCM.OriginalSincCompactPotential"),
    (``Zeta23.ExceptionalZero.lintegral_exp_mul_eq_tsum_positive_moments, "Zeta23.ExceptionalZero.PositiveMomentSeries"),
    (``Zeta23.ExceptionalZero.integrable_exp_mul_of_summable_positive_moments, "Zeta23.ExceptionalZero.PositiveMomentSeries"),
    (``Zeta23.ExceptionalZero.integral_exp_mul_eq_tsum_positive_moments, "Zeta23.ExceptionalZero.PositiveMomentSeries"),
    (``Zeta23.ExceptionalZero.iteratedDeriv_eq_moment_of_complexMGF_continuation, "Zeta23.ExceptionalZero.PositiveMGFContinuation"),
    (``Zeta23.ExceptionalZero.summable_moments_of_complexMGF_continuation, "Zeta23.ExceptionalZero.PositiveMGFContinuation"),
    (``Zeta23.ExceptionalZero.integrable_exp_mul_of_complexMGF_continuation, "Zeta23.ExceptionalZero.PositiveMGFContinuation"),
    (``Zeta23.ExceptionalZero.exists_integrable_exp_mul_gt_of_complexMGF_continuation, "Zeta23.ExceptionalZero.PositiveMGFContinuation"),
    (``Zeta23.ExceptionalZero.squaredWeilFilteredFamily_even, "Zeta23.ExceptionalZero.UniversalSincCorrelationReal"),
    (``Zeta23.ExceptionalZero.fixed_originalSincCorrelation_im_eq_zero, "Zeta23.ExceptionalZero.UniversalSincCorrelationReal"),
    (``Zeta23.CCM.coe_poleNeutralIndexLinearMap_legal, "Zeta23.CCM.CanonicalPoleNeutralIntertwining"),
    (``Zeta23.CCM.poleNeutralCompressedIndexDefect_eq_cubicSource_add_residual,
      "Zeta23.CCM.CanonicalPoleNeutralIntertwining"),
    (``Zeta23.CCM.canonicalPoleEvenLegalNormal_ne_zero, "Zeta23.CCM.CanonicalPoleNeutralNormals"),
    (``Zeta23.CCM.canonicalPoleOddLegalNormal_ne_zero, "Zeta23.CCM.CanonicalPoleNeutralNormals"),
    (``Zeta23.CCM.poleNeutralEvenOutputResidual_eq_normal, "Zeta23.CCM.CanonicalPoleNeutralNormals"),
    (``Zeta23.CCM.poleNeutralOddProjection_index_evenNormal_eq_cubic, "Zeta23.CCM.CanonicalPoleNeutralNormals"),
    (``Zeta23.CCM.poleNeutralCompressedIndexDefect_eq_correctedCubicSource, "Zeta23.CCM.CanonicalPoleNeutralNormals"),
    (``Zeta23.CCM.canonicalPoleNeutralRankOneIntertwining, "Zeta23.CCM.CanonicalPoleNeutralNormals"),
    (``Zeta23.CCM.poleNeutral_cubic_pairing_eq_momentFour, "Zeta23.CCM.CanonicalPoleNeutralNormals"),
    (``Zeta23.CCM.poleNeutralMomentFourWitness_momentFour_ne_zero, "Zeta23.CCM.CanonicalPoleNeutralCubicWitness"),
    (``Zeta23.CCM.poleNeutralCubicCompressionVector_ne_zero, "Zeta23.CCM.CanonicalPoleNeutralCubicWitness"),
    (``Zeta23.CCM.poleNeutralIndexInverse_norm_le_two, "Zeta23.CCM.CanonicalPoleNeutralSourceMoment"),
    (``Zeta23.CCM.exists_eigenmode_at_poleNeutralEvenRayleighBottom, "Zeta23.CCM.CanonicalPoleNeutralSourceMoment"),
    (``Zeta23.CCM.exists_eigenmode_at_poleNeutralOddRayleighBottom, "Zeta23.CCM.CanonicalPoleNeutralSourceMoment"),
    (``Zeta23.CCM.poleNeutral_source_moment_energy_eq, "Zeta23.CCM.CanonicalPoleNeutralSourceMoment"),
    (``Zeta23.CCM.poleNeutral_strictEven_source_moment_pos, "Zeta23.CCM.CanonicalPoleNeutralSourceMoment"),
    (``Zeta23.CCM.poleNeutral_strictEven_source_ne_zero, "Zeta23.CCM.CanonicalPoleNeutralSourceMoment"),
    (``Zeta23.CCM.poleNeutral_strictEven_momentFour_ne_zero, "Zeta23.CCM.CanonicalPoleNeutralSourceMoment"),
    (``Zeta23.CCM.eq_zero_of_indexMatrix_sq_eigen_of_moments_zero_one, "Zeta23.CCM.CanonicalPoleNeutralIndexRigidity"),
    (``Zeta23.CCM.indexMatrix_sq_mem_evenBoundaryFlat_of_momentFour_eq_zero, "Zeta23.CCM.CanonicalPoleNeutralIndexRigidity"),
    (``Zeta23.CCM.poleEvenProfile_dot_indexMatrix_sq_eq_zero, "Zeta23.CCM.CanonicalPoleNeutralIndexRigidity"),
    (``Zeta23.CCM.canonicalSourceMatrix_mulVec_eq_negative_arch_prime_of_profiles,
      "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.inner_poleNeutralEvenCompressedCanonical_self, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.inner_poleNeutralOddCompressedCanonical_self, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.canonicalSourceMatrix_mulVec_poleNeutralEven_eq_negative_arch_prime,
      "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.native_primeCoefficients_unique, "Zeta23.CCM.NativeIntegerPrimeSource"),
    (``Zeta23.CCM.canonicalTrialResidual_variance, "Zeta23.CCM.CanonicalTrialResidualChannels"),
    (``Zeta23.CCM.canonicalTrialResidual_channelGram, "Zeta23.CCM.CanonicalTrialResidualChannels"),
    (``Zeta23.CCM.poleNeutralEvenTrialResidual_variance, "Zeta23.CCM.CanonicalTrialResidualChannels"),
    (``Zeta23.CCM.poleNeutralOddTrialResidual_variance, "Zeta23.CCM.CanonicalTrialResidualChannels"),
    (``Zeta23.CCM.poleNeutralEvenTrialResidual_channelGram, "Zeta23.CCM.CanonicalTrialResidualChannels"),
    (``Zeta23.CCM.poleNeutralOddTrialResidual_channelGram, "Zeta23.CCM.CanonicalTrialResidualChannels"),
    (``Zeta23.CCM.native_weighted_dirichlet_identity, "Zeta23.CCM.NativeIntegerPrimeSource"),
    (``Zeta23.CCM.nativePrimeField_eq_history_sum, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativeIntegerDriveField_eq_history_sum, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativePrimeField_zero_before_firstPrime, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativePrimeField_frozen_firstPrime_atom, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativePrimeField_continuous, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativePositiveCompletion_nonneg, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.nativePositiveCompletion_pos_of_nonneg, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.nativePositiveCompletionLogDensity_cell, "Zeta23.CCM.NativePositiveCompletionCells"),
    (``Zeta23.CCM.nativePositiveCompletionLogDensity_cell_le, "Zeta23.CCM.NativePositiveCompletionCells"),
    (``Zeta23.CCM.nativePositiveCompletionLogDensity_integrableOn, "Zeta23.CCM.NativePositiveCompletionMass"),
    (``Zeta23.CCM.nativePositiveCompletion_mass_eq_logIntegral, "Zeta23.CCM.NativePositiveCompletionMass"),
    (``Zeta23.CCM.nativePositiveCompletionLogDensity_cell_integral_le, "Zeta23.CCM.NativePositiveCompletionMass"),
    (``Zeta23.CCM.nativePositiveCompletionLogDensity_cell_integral, "Zeta23.CCM.NativePositiveCompletionHead"),
    (``Zeta23.CCM.nativePositiveCompletionLogDensity_head_integral, "Zeta23.CCM.NativePositiveCompletionHead"),
    (``Zeta23.CCM.nativePositiveCompletionLogDensity_hasSum_tail_cells, "Zeta23.CCM.NativePositiveCompletionTail"),
    (``Zeta23.CCM.nativePositiveCompletionLogDensity_tail_integral_le, "Zeta23.CCM.NativePositiveCompletionTail"),
    (``Zeta23.CCM.nativePositiveCompletion_mass_lt_605_div_621, "Zeta23.CCM.NativePositiveCompletionCertificate"),
    (``Zeta23.CCM.nativePositiveCompletion_integrable, "Zeta23.CCM.NativePositiveCompletionCertificate"),
    (``Zeta23.CCM.nativePositiveCompletion_integral_norm_lt_605_div_621, "Zeta23.CCM.NativePositiveCompletionCertificate"),
    (``Zeta23.CCM.poleNeutralEvenShiftedCanonical_coercive, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.poleNeutralOddShiftedCanonical_coercive, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.poleNeutral_even_eigen_shiftedRay_source_eq_one, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.poleNeutral_even_shifted_det_quotient, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.poleNeutral_adjoint_rankOne_identity, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.poleNeutral_odd_eigen_adjoint_competitor_source_dichotomy, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.poleNeutral_odd_eigen_adjointRay_pairing_eq_one, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.poleNeutral_odd_adjoint_shifted_det_quotient, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.exists_poleNeutral_strictEven_ground_shifted_normalization, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.exists_poleNeutral_strictOdd_ground_adjoint_normalization, "Zeta23.CCM.CanonicalPoleNeutralShiftedSecular"),
    (``Zeta23.CCM.poleNeutral_even_eigen_shifted_kernel_compatibility, "Zeta23.CCM.CanonicalPoleNeutralTiePackage"),
    (``Zeta23.CCM.poleNeutralEvenEigen_index_eq_kernel_add_complement, "Zeta23.CCM.CanonicalPoleNeutralTiePackage"),
    (``Zeta23.CCM.poleNeutral_even_eigen_complement_source_eq, "Zeta23.CCM.CanonicalPoleNeutralTiePackage"),
    (``Zeta23.CCM.poleNeutral_tied_ground_singular_safe_package, "Zeta23.CCM.CanonicalPoleNeutralTiePackage"),
    (``Zeta23.ExceptionalZero.riemannZeta_re_le_neg_div_one_sub, "Zeta23.ExceptionalZero.ZetaRealStripNonvanishing"),
    (``Zeta23.ExceptionalZero.riemannZeta_ne_zero_of_real_critical_strip, "Zeta23.ExceptionalZero.ZetaRealStripNonvanishing"),
    (``Zeta23.ExceptionalZero.zetaZeroCarrier_im_ne_zero, "Zeta23.ExceptionalZero.ZetaRealStripNonvanishing"),
    (``Zeta23.ExceptionalZero.analyticAt_filteredResolvent_ofReal, "Zeta23.ExceptionalZero.ZetaRealStripNonvanishing"),
    (``Zeta23.CCM.nativeIntegerTranslateAction_primeField_eq_integerDriveField,
      "Zeta23.CCM.NativeIntegerPrimeConvolution"),
    (``Zeta23.CCM.nativePositiveCompletion_le_exp, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.nativePositiveCompletion_integrableOn, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.nativeIntegerTranslateAction_rationalKernel_eq_positiveCompletion,
      "Zeta23.CCM.NativeFloorCompletionSource"),
    (``Zeta23.CCM.nativeRationalCausalKernel_damped_integrableOn, "Zeta23.CCM.NativeRationalCompletionLaplace"),
    (``Zeta23.CCM.nativeRationalCausalKernel_realLaplace, "Zeta23.CCM.NativeRationalCompletionLaplace"),
    (``Zeta23.CCM.nativeRationalCausalKernel_signed_integral, "Zeta23.CCM.NativeRationalCompletionLaplace"),
    (``Zeta23.CCM.step123_enteringPrimeSourceMatrix_zero, "Zeta23.CCM.Step123PrimeSeam"),
    (``Zeta23.CCM.step123_qBasis_logSeam_zero, "Zeta23.CCM.Step123PrimeSeam"),
    (``Zeta23.CCM.UniversalSinc.polynomial_sqrt_decay_Ioi_integral, "Zeta23.CCM.UniversalSincProductMoments"),
    (``Zeta23.CCM.UniversalSinc.polynomial_sqrt_decay_integral, "Zeta23.CCM.UniversalSincProductMoments"),
    (``Zeta23.CCM.UniversalSinc.product_norm_moment_integral_le_factorial, "Zeta23.CCM.UniversalSincProductMoments"),
    (``Zeta23.CCM.UniversalSinc.factorial_two_mul_add_one_le, "Zeta23.CCM.UniversalSincProductMoments"),
    (``Zeta23.CCM.UniversalSinc.product_norm_moment_integral_le_gevrey, "Zeta23.CCM.UniversalSincProductMoments"),
    (``Zeta23.CCM.UniversalSinc.integrable_product_ofReal_smul_moment, "Zeta23.CCM.UniversalSincInverseGevreyBounds"),
    (``Zeta23.CCM.UniversalSinc.iteratedDeriv_fourier_product, "Zeta23.CCM.UniversalSincInverseGevreyBounds"),
    (``Zeta23.CCM.UniversalSinc.norm_iteratedDeriv_fourier_product_le_moment, "Zeta23.CCM.UniversalSincInverseGevreyBounds"),
    (``Zeta23.CCM.UniversalSinc.norm_iteratedDeriv_inverseCandidate_le_moment, "Zeta23.CCM.UniversalSincInverseGevreyBounds"),
    (``Zeta23.CCM.UniversalSinc.norm_iteratedDeriv_inverseCandidate_le_gevrey, "Zeta23.CCM.UniversalSincInverseGevreyBounds"),
    (``Zeta23.ExceptionalZero.positiveLaplaceTilt_isFiniteMeasure, "Zeta23.ExceptionalZero.PositiveLaplaceTilt"),
    (``Zeta23.ExceptionalZero.positiveLaplaceTilt_apply_univ, "Zeta23.ExceptionalZero.PositiveLaplaceTilt"),
    (``Zeta23.ExceptionalZero.positiveLaplaceTilt_ae_nonneg, "Zeta23.ExceptionalZero.PositiveLaplaceTilt"),
    (``Zeta23.ExceptionalZero.integrable_exp_positiveLaplaceTilt_iff, "Zeta23.ExceptionalZero.PositiveLaplaceTilt"),
    (``Zeta23.ExceptionalZero.integrable_cexp_positiveLaplaceTilt_iff, "Zeta23.ExceptionalZero.PositiveLaplaceTilt"),
    (``Zeta23.ExceptionalZero.complexMGF_positiveLaplaceTilt, "Zeta23.ExceptionalZero.PositiveLaplaceTilt"),
    (``Zeta23.ExceptionalZero.zero_mem_interior_integrableExpSet_positiveLaplaceTilt, "Zeta23.ExceptionalZero.PositiveLaplaceTilt"),
    (``Zeta23.CCM.nativeDeepThreshold_even_ground_coercive, "Zeta23.CCM.NativeDeepThresholdInverseBudgets"),
    (``Zeta23.CCM.nativeDeepThreshold_odd_ground_coercive, "Zeta23.CCM.NativeDeepThresholdInverseBudgets"),
    (``Zeta23.CCM.nativeDeepThreshold_even_detector_coercive, "Zeta23.CCM.NativeDeepThresholdInverseBudgets"),
    (``Zeta23.CCM.nativeDeepThreshold_odd_detector_coercive, "Zeta23.CCM.NativeDeepThresholdInverseBudgets"),
    (``Zeta23.CCM.nativeDeepThreshold_inverse_norms_zero_at_first, "Zeta23.CCM.NativeDeepThresholdInverseBudgets"),
    (``Zeta23.CCM.exists_nativeDeepThresholdGround_with_inverseBudgets_of_given_trial, "Zeta23.CCM.NativeDeepThresholdInverseBudgets"),
    (``Zeta23.CCM.nativeDeepThreshold_even_eigenspace_finrank_le_one, "Zeta23.CCM.NativeDeepThresholdSimplicity"),
    (``Zeta23.CCM.nativeDeepThreshold_odd_eigenspace_finrank_le_one, "Zeta23.CCM.NativeDeepThresholdSimplicity"),
    (``Zeta23.CCM.nativeDeepThreshold_even_ground_simple, "Zeta23.CCM.NativeDeepThresholdSimplicity"),
    (``Zeta23.CCM.nativeDeepThreshold_odd_ground_simple, "Zeta23.CCM.NativeDeepThresholdSimplicity"),
    (``Zeta23.CCM.nativeDeepThreshold_selectedParity_simple, "Zeta23.CCM.NativeDeepThresholdSimplicity"),
    (``Zeta23.CCM.nativeDeepThreshold_even_ground_momentFour_ne_zero, "Zeta23.CCM.NativeDeepThresholdEvenMoment"),
    (``Zeta23.CCM.nativeDeepThreshold_strictEven_ground_source_ne_zero, "Zeta23.CCM.NativeDeepThresholdEvenMoment"),
    (``Zeta23.CCM.isometricDetector_coordinate_decomposition, "Zeta23.CCM.IsometricDetectorSchur"),
    (``Zeta23.CCM.isometricDetectorComplement_adjoint_eq_zero, "Zeta23.CCM.IsometricDetectorSchur"),
    (``Zeta23.CCM.inner_isometricDetectorSchurOperator, "Zeta23.CCM.IsometricDetectorSchur"),
    (``Zeta23.CCM.isometricDetectorSchur_completedSquare, "Zeta23.CCM.IsometricDetectorSchur"),
    (``Zeta23.CCM.isometricDetectorSchur_negative_depth, "Zeta23.CCM.IsometricDetectorSchur"),
    (``Zeta23.CCM.isometricGroundSchur_kernel_package, "Zeta23.CCM.IsometricGroundSchur"),
    (``Zeta23.CCM.isometricGroundSchur_scalar_identity, "Zeta23.CCM.IsometricGroundSchur"),
    (``Zeta23.CCM.nativePoleNeutralParity_predecessor_compression_eq, "Zeta23.CCM.NativeDetectorSchur"),
    (``Zeta23.CCM.nativeDetectorPredecessorEquiv_inverse_bound, "Zeta23.CCM.NativeDetectorSchur"),
    (``Zeta23.CCM.nativeDetectorComplement_finrank, "Zeta23.CCM.NativeDetectorSchur"),
    (``Zeta23.CCM.nativeDetectorCoupling_shift_eq_unshifted, "Zeta23.CCM.NativeDetectorSchur"),
    (``Zeta23.CCM.nativeDetectorPredecessorEquiv_eq_compression, "Zeta23.CCM.NativeDetectorSchur"),
    (``Zeta23.CCM.nativeDetectorSchur_completedSquare, "Zeta23.CCM.NativeDetectorSchur"),
    (``Zeta23.CCM.nativeDetectorSchur_original_depth, "Zeta23.CCM.NativeDetectorSchur"),
    (``Zeta23.CCM.nativeSelectedGroundPredecessorEquiv_inverse_bound, "Zeta23.CCM.NativeSelectedGroundSchur"),
    (``Zeta23.CCM.nativeSelectedGroundShell_finrank_eq_one, "Zeta23.CCM.NativeSelectedGroundSchur"),
    (``Zeta23.CCM.nativeSelectedGroundPredecessorEquiv_eq_compression, "Zeta23.CCM.NativeSelectedGroundSchur"),
    (``Zeta23.CCM.nativeSelectedGroundSchur_kernel_package, "Zeta23.CCM.NativeSelectedGroundSchur"),
    (``Zeta23.CCM.nativeSelectedGround_shiftedSchur_eq, "Zeta23.CCM.NativeSelectedGroundSchur"),
    (``Zeta23.CCM.originalDetectorRawCutoff_add_four, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.originalDetectorRawCutoff_lower, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.originalDetectorRawCutoff_upper, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.originalDetectorRawCutoff_div_lower, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.originalDetectorLobe_iteratedDeriv_le_gevrey, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.originalDetectorLobe_endpoint_jets, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.originalDetectorLobe_fourierCoeff_jet_step, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.originalDetectorLobe_fourierCoeff_eq_jet, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.norm_originalDetectorLobe_jet_fourierCoeff_le, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.norm_originalDetectorLobe_fourierCoeff_le_gevrey_order, "Zeta23.CCM.OriginalDetectorFourierPrerequisites"),
    (``Zeta23.CCM.nativePoleMoment_deriv, "Zeta23.CCM.OriginalSincWeightedPoleMoments"),
    (``Zeta23.CCM.nativePoleFirstMoment_deriv, "Zeta23.CCM.OriginalSincWeightedPoleMoments"),
    (``Zeta23.CCM.nativePoleMoment_differential, "Zeta23.CCM.OriginalSincWeightedPoleMoments"),
    (``Zeta23.CCM.nativePoleFirstMoment_differential, "Zeta23.CCM.OriginalSincWeightedPoleMoments"),
    (``Zeta23.CCM.universalSincSecondKernel_first_elementary_moments, "Zeta23.CCM.OriginalSincWeightedPoleMoments"),
    (``Zeta23.CCM.nativeOriginalSource_weighted_elementary_moments, "Zeta23.CCM.OriginalSincWeightedPoleMoments"),
    (``Zeta23.CCM.nativeIntegerAbel_discrepancy_eq, "Zeta23.CCM.NativeAbelDiscrepancy"),
    (``Zeta23.CCM.nativeIntegerAbel_discrepancy_bound, "Zeta23.CCM.NativeAbelDiscrepancy"),
    (``Zeta23.CCM.nativeOriginalLogDriveSummand_zero_below, "Zeta23.CCM.OriginalSincLogDrive"),
    (``Zeta23.CCM.nativeOriginalLogDriveSummand_zero_above, "Zeta23.CCM.OriginalSincLogDrive"),
    (``Zeta23.CCM.nativeOriginalLogDriveSummand_contDiff, "Zeta23.CCM.OriginalSincLogDrive"),
    (``Zeta23.CCM.nativeOriginalLogDriveSummand_hasCompactSupport, "Zeta23.CCM.OriginalSincLogDrive"),
    (``Zeta23.CCM.nativeOriginalLogDriveSummand_at_nat, "Zeta23.CCM.OriginalSincLogDrive"),
    (``Zeta23.CCM.nativeOriginalIntegerDrive_eq_abel_sum, "Zeta23.CCM.OriginalSincLogDrive"),
    (``Zeta23.CCM.nativeOriginalIntegerDrive_abel_discrepancy_bound, "Zeta23.CCM.OriginalSincLogDrive"),
    (``Zeta23.ExceptionalZero.integrable_positiveLaplaceWeight_mono, "Zeta23.ExceptionalZero.PositiveLaplaceBoundary"),
    (``Zeta23.ExceptionalZero.positiveLaplaceAbscissa_le_of_integrable, "Zeta23.ExceptionalZero.PositiveLaplaceBoundary"),
    (``Zeta23.ExceptionalZero.integrable_positiveLaplaceWeight_of_abscissa_lt, "Zeta23.ExceptionalZero.PositiveLaplaceBoundary"),
    (``Zeta23.ExceptionalZero.not_differentiable_positiveLaplace_continuation_at_abscissa, "Zeta23.ExceptionalZero.PositiveLaplaceBoundary"),
    (``Zeta23.ExceptionalZero.not_analyticAt_positiveLaplace_continuation_at_abscissa, "Zeta23.ExceptionalZero.PositiveLaplaceBoundary"),
    (``Zeta23.ExceptionalZero.positiveLaplaceTransform_not_analyticAt_abscissa, "Zeta23.ExceptionalZero.PositiveLaplaceBoundary"),
    (``Zeta23.ExceptionalZero.fixedOriginalSincCorrelationReal_ofReal, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.measurable_fixedOriginalSincCorrelation, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.abs_fixedOriginalSincCorrelationReal_le, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.integrable_fixedOriginalSincCorrelation_weight, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.positiveLaplaceTransform_fixedOriginalSincCorrelation_safe, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.analyticAt_fixedOriginalSincResolvent_ofReal, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.fixedOriginalSincSquaredCoeff_ne_zero, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.measurable_fixedOriginalSincSignedTail, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.fixedOriginalSincSignedTail_nonneg, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.integrable_fixedOriginalSincSignedTail_weight, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.positiveLaplaceDomain_fixedOriginalSincSignedTail_nonempty, "Zeta23.ExceptionalZero.UniversalSincSignedLaplace"),
    (``Zeta23.ExceptionalZero.analyticAt_positiveLaplaceTransform_of_integrable_nhds, "Zeta23.ExceptionalZero.PositiveLaplaceAnalytic"),
    (``Zeta23.ExceptionalZero.analyticAt_positiveLaplaceTransform_of_abscissa_lt, "Zeta23.ExceptionalZero.PositiveLaplaceAnalytic"),
    (``Zeta23.ExceptionalZero.meromorphicOn_positiveLaplaceTransform_abscissa_halfPlane, "Zeta23.ExceptionalZero.PositiveLaplaceAnalytic"),
    (``Zeta23.CCM.nativePoleNeutralParityAmbient_poles, "Zeta23.CCM.DetectorRetainedSchurState"),
    (``Zeta23.CCM.nativePoleNeutralParityAmbient_energy, "Zeta23.CCM.DetectorRetainedSchurState"),
    (``Zeta23.CCM.exists_detectorRetainedSchurState_of_original_native_trial, "Zeta23.CCM.DetectorRetainedSchurState"),
    (``Zeta23.CCM.originalDetector_schur_loss_lower, "Zeta23.CCM.DetectorRetainedSchurState"),
    (``Zeta23.CCM.originalDetector_schur_completion, "Zeta23.CCM.DetectorRetainedSchurState"),
    (``Zeta23.CCM.selectedGround_shiftedSchur_eq, "Zeta23.CCM.DetectorRetainedSchurState")]
  let queries := roots.map fun (name, mod) =>
    ({ sourceId := name.toString, moduleName := mod, shortName := name.toString,
       sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery)
  Zeta23.RHRC.resolveSourceCandidates queries
  for (name, _) in roots do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unadmitted proof dependency in {name}: {ax}"
    let names := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"POST290_AXIOMS\t{name}\t{names}"
