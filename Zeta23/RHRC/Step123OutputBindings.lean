import Zeta23.CCM.UniversalSincDetector
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
    (``Zeta23.CCM.step123_qBasis_logSeam_zero, "Zeta23.CCM.Step123PrimeSeam")]
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
