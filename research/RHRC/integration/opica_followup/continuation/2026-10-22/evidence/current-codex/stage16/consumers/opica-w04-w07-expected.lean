import Zeta23.OPICAFollowup.NativeWindowRate
import Zeta23.OPICAFollowup.NearGapLimits
open Set MeasureTheory
open scoped FourierTransform
namespace Zeta23.OPICAFollowup.W04W07Independent
theorem expected_window_integrable (d : ℕ) (C T : ℝ) :
    IntegrableOn (fun t : ℝ => |Zeta23.OPICAFollowup.primeFieldFamily d t| ^ 2)
      (Icc (T - C * Real.log T) T) :=
  Zeta23.OPICAFollowup.nativeWindowEnergy_integrable d C T
theorem expected_window_nonneg (d : ℕ) (C T : ℝ) :
    0 ≤ Zeta23.OPICAFollowup.nativeWindowEnergy d C T :=
  Zeta23.OPICAFollowup.nativeWindowEnergy_nonneg d C T
theorem expected_window_causal_zero (d : ℕ) (C T : ℝ)
    (hT : T < Zeta23.OPICAFollowup.nativeCausalGap) :
    Zeta23.OPICAFollowup.nativeWindowEnergy d C T = 0 :=
  Zeta23.OPICAFollowup.nativeWindowEnergy_zero_before_causal_gap d C T hT
theorem expected_window_rate_nonneg (d : ℕ) (C T : ℝ) (hT : 0 < T) :
    0 ≤ Zeta23.OPICAFollowup.nativeWindowLogRate d C T :=
  Zeta23.OPICAFollowup.nativeWindowLogRate_nonneg d C T hT
theorem expected_ct1_origin_coefficient (L : ℝ) :
    Real.exp (L / 2) + Real.exp (-L / 2) - 2 * Real.cosh (L / 2) = 0 :=
  Zeta23.OPICAFollowup.nearGapComb_origin_coefficient_zero L
theorem expected_ct1_radius {L : ℝ} (hL : 0 < L)
    (hu : L < Real.log 2) :
    (1 / 2 : ℝ) < Real.exp (-L) ∧ Real.exp (-L) < 1 :=
  Zeta23.OPICAFollowup.nearGapComb_radius_bounds hL hu
theorem expected_completion_interval {C Theta delta b : ℝ}
    (hC : 1 < C) (hdelta : Theta + (C - 1) * b < C * delta) :
    ∃ xi : ℝ, (Theta - delta) / (C - 1) < xi ∧ xi < delta - b :=
  Zeta23.OPICAFollowup.nativeWindow_rate_parameter_interval hC hdelta
theorem expected_exponent_margin {C Theta delta b xi : ℝ}
    (hC : 1 < C)
    (hlow : (Theta - delta) / (C - 1) < xi)
    (hhigh : xi < delta - b) :
    Theta - C * xi < delta - xi ∧ b < delta - xi :=
  Zeta23.OPICAFollowup.nativeWindow_rate_exponent_margin hC hlow hhigh
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_completion_interval
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_exponent_margin
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_window_integrable
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_window_nonneg
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_window_causal_zero
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_window_rate_nonneg
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_origin_coefficient
theorem expected_ct1_signed_growth (L : ℝ) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).HasLinearGrowth :=
  Zeta23.OPICAFollowup.nearGapCombFamily_growth L
theorem expected_ct1_distribution (L : ℝ) :
    ∃ D : TemperedDistribution ℝ ℂ,
      D = Zeta23.OPICAFollowup.nearGapCombDistribution L :=
  ⟨Zeta23.OPICAFollowup.nearGapCombDistribution L, rfl⟩
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_signed_growth
theorem expected_jordan_add_pairing
    (mu nu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (hmu : mu.HasLinearGrowth) (hnu : nu.HasLinearGrowth)
    (f : SchwartzMap ℝ ℂ) :
    (Zeta23.OPICAFollowup.localJordanAdd mu nu).distributionOfLinearGrowth
      (Zeta23.OPICAFollowup.nearGap_localJordanAdd_growth mu nu hmu hnu) f =
    mu.distributionOfLinearGrowth hmu f +
    nu.distributionOfLinearGrowth hnu f :=
  Zeta23.OPICAFollowup.nearGap_localJordanAdd_pairing mu nu hmu hnu f
theorem expected_ct1_exp_sum_uniform {L : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2) :
    Real.exp (L / 2) + Real.exp (-L / 2) ≤ 3 :=
  Zeta23.OPICAFollowup.nearGap_dilation_exp_sum_le_three hL hu
theorem expected_ct1_uniform_scalar_budget {L R : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2) (hR : 0 ≤ R) :
    (6 + 4 * R) * (Real.exp (L / 2) + Real.exp (-L / 2)) ≤
      18 * (1 + R) :=
  Zeta23.OPICAFollowup.nearGap_dilation_uniform_scalar_budget hL hu hR
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_exp_sum_uniform
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_uniform_scalar_budget
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_jordan_add_pairing
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_distribution
theorem expected_ct1_variation_domination (L : ℝ) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).totalVariation ≤
      ((Zeta23.OPICAFollowup.dilatedCombJordan L).totalVariation +
       (Zeta23.OPICAFollowup.dilatedCombJordan (-L)).totalVariation) +
      ENNReal.ofReal |-(2 * Real.cosh (L / 2))| •
        (Zeta23.OPICAFollowup.dilatedCombJordan 0).totalVariation :=
  Zeta23.OPICAFollowup.nearGapCombFamily_variation_le L
theorem expected_ct1_positive_variation (t : ℝ) :
    (Zeta23.OPICAFollowup.dilatedCombJordan t).totalVariation =
    Zeta23.OPICAFollowup.dilatedCombMeasure t :=
  Zeta23.OPICAFollowup.nearGap_dilatedComb_variation t
theorem expected_ct1_actual_uniform_variation {L R : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2) (hR : 0 ≤ R) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).totalVariation.real
      (Icc (-R) R) ≤ 18 * (1 + R) :=
  Zeta23.OPICAFollowup.nearGapCombFamily_uniform_variation hL hu hR
theorem expected_ct1_common_schwartz_growth {L : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2) :
    Zeta23.OPICAFollowup.CommonLinearMassBound 18
      (Zeta23.OPICAFollowup.nearGapCombFamily L).totalVariation :=
  Zeta23.OPICAFollowup.nearGapCombFamily_common_growth hL hu
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_variation_domination
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_positive_variation
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_actual_uniform_variation
theorem expected_ct1_uniform_schwartz_tails {L R M : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2)
    (hM : 0 ≤ M) (hR : 1 ≤ R)
    (f : ℝ → ℂ) (hf : Continuous f)
    (hdecay : ∀ x : ℝ, |x| ^ 3 * ‖f x‖ ≤ M) :
    IntegrableOn f {x : ℝ | R ≤ |x|}
      (Zeta23.OPICAFollowup.nearGapCombFamily L).totalVariation ∧
    (∫ x in {x : ℝ | R ≤ |x|}, ‖f x‖
      ∂(Zeta23.OPICAFollowup.nearGapCombFamily L).totalVariation) ≤
      72 * M / R ^ 2 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_uniform_schwartz_tail
    hL hu hM hR f hf hdecay
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_uniform_schwartz_tails
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_common_schwartz_growth
theorem expected_ct1_compact_measure_identity (L : ℝ)
    (K : Set ℝ) (hK : IsCompact K) :
    Zeta23.OPICAFollowup.localSignedCompactRestriction
      (Zeta23.OPICAFollowup.nearGapCombFamily L) K hK =
    Zeta23.OPICAFollowup.localSignedCompactRestriction
      (Zeta23.OPICAFollowup.dilatedCombJordan L) K hK +
    Zeta23.OPICAFollowup.localSignedCompactRestriction
      (Zeta23.OPICAFollowup.dilatedCombJordan (-L)) K hK -
    (2 * Real.cosh (L / 2)) •
      Zeta23.OPICAFollowup.localSignedCompactRestriction
        (Zeta23.OPICAFollowup.dilatedCombJordan 0) K hK :=
  Zeta23.OPICAFollowup.nearGapCombFamily_compactRestriction L K hK
theorem expected_dilated_comb_physical_origin (t : ℝ) :
    Zeta23.OPICAFollowup.localSignedCompactRestriction
      (Zeta23.OPICAFollowup.dilatedCombJordan t)
      ({0} : Set ℝ) isCompact_singleton ({0} : Set ℝ) =
        Real.exp (t / 2) :=
  Zeta23.OPICAFollowup.nearGap_dilatedComb_origin_signed t
theorem expected_ct1_physical_origin_cancelled (L : ℝ) :
    Zeta23.OPICAFollowup.localSignedCompactRestriction
      (Zeta23.OPICAFollowup.nearGapCombFamily L)
      ({0} : Set ℝ) isCompact_singleton ({0} : Set ℝ) = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_origin_signed_zero L
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_dilated_comb_physical_origin
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_physical_origin_cancelled
theorem expected_actual_integer_first_gap (t : ℝ) (n : ℤ)
    (hn : Zeta23.OPICAFollowup.scaledLatticePoint t n ∈
      Ioo (-Real.exp t) (Real.exp t)) : n = 0 :=
  Zeta23.OPICAFollowup.scaledLatticePoint_in_first_gap t n hn
theorem expected_actual_positive_comb_punctured_gap (t : ℝ) :
    Zeta23.OPICAFollowup.dilatedCombMeasure t
      (Ioo (-Real.exp t) (Real.exp t) \ ({0} : Set ℝ)) = 0 :=
  Zeta23.OPICAFollowup.dilatedCombMeasure_punctured_gap t
theorem expected_actual_three_carriers_gap {L : ℝ} (hL : 0 ≤ L) :
    Zeta23.OPICAFollowup.dilatedCombMeasure L
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 ∧
    Zeta23.OPICAFollowup.dilatedCombMeasure (-L)
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 ∧
    Zeta23.OPICAFollowup.dilatedCombMeasure 0
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 :=
  Zeta23.OPICAFollowup.nearGapComb_three_carriers_punctured_gap hL
theorem expected_actual_ct1_signed_compact_gap {L : ℝ}
    (hL : 0 ≤ L) (K : Set ℝ) (hK : IsCompact K) :
    Zeta23.OPICAFollowup.localSignedCompactRestriction
      (Zeta23.OPICAFollowup.nearGapCombFamily L) K hK
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_punctured_gap_signed hL K hK
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_actual_integer_first_gap
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_actual_positive_comb_punctured_gap
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_actual_three_carriers_gap
theorem expected_signed_origin_collar
    (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) (h0 : (0 : ℝ) ∈ K) :
    Zeta23.OPICAFollowup.localSignedCompactRestriction mu K hK
      ({0} : Set ℝ) =
    Zeta23.OPICAFollowup.localSignedCompactRestriction mu
      ({0} : Set ℝ) isCompact_singleton ({0} : Set ℝ) :=
  Zeta23.OPICAFollowup.nearGap_signed_origin_restriction_of_mem
    mu K hK h0
theorem expected_ct1_origin_every_compact (L : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (h0 : (0 : ℝ) ∈ K) :
    Zeta23.OPICAFollowup.localSignedCompactRestriction
      (Zeta23.OPICAFollowup.nearGapCombFamily L) K hK
      ({0} : Set ℝ) = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_origin_signed_zero_on_compact
    L K hK h0
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_signed_origin_collar
theorem expected_jordan_singleton_no_cancellation
    (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure) (x : ℝ)
    (hzero : Zeta23.OPICAFollowup.localSignedCompactRestriction
      mu ({x} : Set ℝ) isCompact_singleton ({x} : Set ℝ) = 0) :
    mu.positive ({x} : Set ℝ) = 0 ∧
      mu.negative ({x} : Set ℝ) = 0 :=
  Zeta23.OPICAFollowup.nearGap_jordan_singleton_of_signed_zero
    mu x hzero
theorem expected_ct1_origin_jordan_pair_zero (L : ℝ) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).positive
      ({0} : Set ℝ) = 0 ∧
    (Zeta23.OPICAFollowup.nearGapCombFamily L).negative
      ({0} : Set ℝ) = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_origin_jordan_zero L
theorem expected_ct1_punctured_jordan_zero {L : ℝ}
    (hL : 0 ≤ L) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).positive
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 ∧
    (Zeta23.OPICAFollowup.nearGapCombFamily L).negative
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_punctured_gap_jordan_zero hL
theorem expected_ct1_punctured_total_variation_zero {L : ℝ}
    (hL : 0 ≤ L) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).totalVariation
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_punctured_gap_variation_zero hL
theorem expected_ct1_genuine_jordan_gap {L : ℝ}
    (hL : 0 ≤ L) :
    Zeta23.OPICAFollowup.hasNearGap
      (Zeta23.OPICAFollowup.nearGapCombFamily L)
      (Real.exp (-L)) :=
  Zeta23.OPICAFollowup.nearGapCombFamily_actual_gap hL
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_jordan_singleton_no_cancellation
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_origin_jordan_pair_zero
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_punctured_jordan_zero
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_punctured_total_variation_zero
theorem expected_integer_comb_offlattice_zero :
    Zeta23.OPICAFollowup.dilatedCombMeasure 0
      Zeta23.OPICA.integerLatticeᶜ = 0 :=
  Zeta23.OPICAFollowup.nearGap_undilatedComb_integer_support
theorem expected_negative_jordan_source_bound
    (mu nu : Zeta23.OPICA.LocallyFiniteSignedMeasure) :
    (Zeta23.OPICAFollowup.localJordanAdd mu nu).negative ≤
      mu.negative + nu.negative :=
  Zeta23.OPICAFollowup.nearGap_localJordanAdd_negative_le mu nu
theorem expected_ct1_negative_integer_support (L : ℝ) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).negative
      Zeta23.OPICA.integerLatticeᶜ = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_negative_integer_support L
theorem expected_ct1_offlattice_nonnegative (L : ℝ) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).OffLatticeNonnegative :=
  Zeta23.OPICAFollowup.nearGapCombFamily_offlattice_nonnegative L
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_integer_comb_offlattice_zero
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_negative_jordan_source_bound
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_negative_integer_support
theorem expected_explicit_CT1_source_fourier_selfdual (L : ℝ) :
    𝓕 (Zeta23.OPICAFollowup.nearGapExplicitDilationDistribution L) =
      Zeta23.OPICAFollowup.nearGapExplicitDilationDistribution L :=
  Zeta23.OPICAFollowup.nearGapExplicitDilationDistribution_selfdual L
theorem expected_scaled_counting_atom (t : ℝ) (n : ℤ) :
    Zeta23.OPICAFollowup.scaledLatticeMeasure t
      ({Zeta23.OPICAFollowup.scaledLatticePoint t n} : Set ℝ) = 1 :=
  Zeta23.OPICAFollowup.scaledLatticeMeasure_atom t n
theorem expected_actual_dilation_atom (t : ℝ) (n : ℤ) :
    Zeta23.OPICAFollowup.dilatedCombMeasure t
      ({Zeta23.OPICAFollowup.scaledLatticePoint t n} : Set ℝ) =
        ENNReal.ofReal (Real.exp (t / 2)) :=
  Zeta23.OPICAFollowup.dilatedCombMeasure_atom t n
theorem expected_first_ct1_point_not_integer {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    Real.exp L ∉ Zeta23.OPICA.integerLattice :=
  Zeta23.OPICAFollowup.nearGap_first_dilated_point_off_integer hL hu
theorem expected_CT1_physical_nonzero_signed_atom {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    0 < Zeta23.OPICAFollowup.localSignedCompactRestriction
      (Zeta23.OPICAFollowup.nearGapCombFamily L)
      ({Real.exp L} : Set ℝ) isCompact_singleton
      ({Real.exp L} : Set ℝ) :=
  Zeta23.OPICAFollowup.nearGapCombFamily_first_atom_signed_pos hL hu
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_scaled_counting_atom
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_actual_dilation_atom
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_first_ct1_point_not_integer
theorem expected_CT1_positive_jordan_atom {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    0 < (Zeta23.OPICAFollowup.nearGapCombFamily L).positive.real
      ({Real.exp L} : Set ℝ) :=
  Zeta23.OPICAFollowup.nearGapCombFamily_first_atom_positive_real_pos hL hu
theorem expected_CT1_positive_measure_nonzero {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).positive ≠ 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_positive_nonzero hL hu
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_positive_jordan_atom
theorem expected_dilation_near_gap_family
    (L : ℝ) (hL : 0 < L) (hu : L < Real.log 2) :
    (∀ K : Set ℝ, ∀ hK : IsCompact K,
      Zeta23.OPICAFollowup.localSignedCompactRestriction
        (Zeta23.OPICAFollowup.nearGapCombFamily L) K hK =
      Zeta23.OPICAFollowup.localSignedCompactRestriction
        (Zeta23.OPICAFollowup.dilatedCombJordan L) K hK +
      Zeta23.OPICAFollowup.localSignedCompactRestriction
        (Zeta23.OPICAFollowup.dilatedCombJordan (-L)) K hK -
      (2 * Real.cosh (L / 2)) •
        Zeta23.OPICAFollowup.localSignedCompactRestriction
          (Zeta23.OPICAFollowup.dilatedCombJordan 0) K hK) ∧
    (Zeta23.OPICAFollowup.nearGapCombFamily L).HasLinearGrowth ∧
    Zeta23.OPICAFollowup.CommonLinearMassBound 18
      (Zeta23.OPICAFollowup.nearGapCombFamily L).totalVariation ∧
    (Zeta23.OPICAFollowup.nearGapCombFamily L).FourierSelfdual
      (Zeta23.OPICAFollowup.nearGapCombFamily_growth L) ∧
    (∀ f : SchwartzMap ℝ ℂ,
      Zeta23.OPICAFollowup.nearGapCombDistribution L
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (LinearIsometryEquiv.neg ℝ (E := ℝ)) f) =
      Zeta23.OPICAFollowup.nearGapCombDistribution L f) ∧
    Zeta23.OPICAFollowup.hasNearGap
      (Zeta23.OPICAFollowup.nearGapCombFamily L) (Real.exp (-L)) ∧
    ((1 / 2 : ℝ) < Real.exp (-L) ∧ Real.exp (-L) < 1) ∧
    (Zeta23.OPICAFollowup.nearGapCombFamily L).OffLatticeNonnegative ∧
    ((Zeta23.OPICAFollowup.nearGapCombFamily L).positive
        ({0} : Set ℝ) = 0 ∧
      (Zeta23.OPICAFollowup.nearGapCombFamily L).negative
        ({0} : Set ℝ) = 0) ∧
    (Zeta23.OPICAFollowup.nearGapCombFamily L).positive ≠ 0 ∧
    (MeasureTheory.Measure.map (fun x : ℝ => -x)
        (Zeta23.OPICAFollowup.nearGapCombFamily L).positive =
        (Zeta23.OPICAFollowup.nearGapCombFamily L).positive ∧
      MeasureTheory.Measure.map (fun x : ℝ => -x)
        (Zeta23.OPICAFollowup.nearGapCombFamily L).negative =
        (Zeta23.OPICAFollowup.nearGapCombFamily L).negative) ∧
    ((Zeta23.OPICAFollowup.nearGapCombFamily L).positive.real
        ({Real.exp (-L)} : Set ℝ) = Real.exp (-L / 2) ∧
      (Zeta23.OPICAFollowup.nearGapCombFamily L).negative
        ({Real.exp (-L)} : Set ℝ) = 0) :=
  Zeta23.OPICAFollowup.dilation_near_gap_family L hL hu
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_dilation_near_gap_family
theorem expected_selfdual_jordan_even
    (nu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu) :
    MeasureTheory.Measure.map (fun x : ℝ => -x) nu.positive = nu.positive ∧
      MeasureTheory.Measure.map (fun x : ℝ => -x) nu.negative = nu.negative :=
  Zeta23.OPICAFollowup.jordan_even_of_selfdual nu hnu hself
theorem expected_CT1_gap_edge_atom {L : ℝ} (hL : 0 < L) (hu : L < Real.log 2) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).positive.real
        ({Real.exp (-L)} : Set ℝ) = Real.exp (-L / 2) ∧
      (Zeta23.OPICAFollowup.nearGapCombFamily L).negative
        ({Real.exp (-L)} : Set ℝ) = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_gap_edge_atom hL hu
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_selfdual_jordan_even
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_gap_edge_atom
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_positive_measure_nonzero
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_physical_nonzero_signed_atom
theorem expected_CT1_canonical_equals_explicit_if_scalar_bridge
    (L : ℝ)
    (hscale :
      (Zeta23.OPICAFollowup.localJordanScale (-(2 * Real.cosh (L / 2)))
        (Zeta23.OPICAFollowup.dilatedCombJordan 0)).distributionOfLinearGrowth
        (Zeta23.OPICAFollowup.nearGap_localJordanScale_growth _ _
          (Zeta23.OPICAFollowup.dilatedCombJordan_growth 0)) =
        (-(((2 * Real.cosh (L / 2) : ℝ) : ℂ))) •
          Zeta23.OPICAFollowup.dilatedCombDistribution 0) :
    Zeta23.OPICAFollowup.nearGapCombDistribution L =
      Zeta23.OPICAFollowup.nearGapExplicitDilationDistribution L :=
  Zeta23.OPICAFollowup.nearGapCombDistribution_eq_explicit_of_scale_pairing
    L hscale
theorem expected_CT1_canonical_selfdual_if_scalar_bridge
    (L : ℝ)
    (hscale :
      (Zeta23.OPICAFollowup.localJordanScale (-(2 * Real.cosh (L / 2)))
        (Zeta23.OPICAFollowup.dilatedCombJordan 0)).distributionOfLinearGrowth
        (Zeta23.OPICAFollowup.nearGap_localJordanScale_growth _ _
          (Zeta23.OPICAFollowup.dilatedCombJordan_growth 0)) =
        (-(((2 * Real.cosh (L / 2) : ℝ) : ℂ))) •
          Zeta23.OPICAFollowup.dilatedCombDistribution 0) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).FourierSelfdual
      (Zeta23.OPICAFollowup.nearGapCombFamily_growth L) :=
  Zeta23.OPICAFollowup.nearGapCombDistribution_selfdual_of_scale_pairing
    L hscale
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_canonical_equals_explicit_if_scalar_bridge
theorem expected_CT1_physical_negative_scale_pairing (t c : ℝ)
    (hc : 0 ≤ c) :
    (Zeta23.OPICAFollowup.localJordanScale (-c)
      (Zeta23.OPICAFollowup.dilatedCombJordan t)).distributionOfLinearGrowth
      (Zeta23.OPICAFollowup.nearGap_localJordanScale_growth
        (-c) (Zeta23.OPICAFollowup.dilatedCombJordan t)
        (Zeta23.OPICAFollowup.dilatedCombJordan_growth t)) =
      (-(c : ℂ)) • Zeta23.OPICAFollowup.dilatedCombDistribution t :=
  Zeta23.OPICAFollowup.nearGap_dilatedComb_negative_scale_pairing t c hc
theorem expected_CT1_physical_equals_explicit (L : ℝ) :
    Zeta23.OPICAFollowup.nearGapCombDistribution L =
      Zeta23.OPICAFollowup.nearGapExplicitDilationDistribution L :=
  Zeta23.OPICAFollowup.nearGapCombDistribution_eq_explicit L
theorem expected_CT1_physical_fourier_selfdual (L : ℝ) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).FourierSelfdual
      (Zeta23.OPICAFollowup.nearGapCombFamily_growth L) :=
  Zeta23.OPICAFollowup.nearGapCombFamily_fourier_selfdual L
theorem expected_CT1_actual_offinteger_mass_budget
    {L R d : ℝ} (hL : 0 < L) (hu : L < Real.log 2)
    (hR : 1 ≤ R) (hd : 0 < d) (hdhalf : d ≤ 1 / 2) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).negative
      (Zeta23.OPICA.signedBudgetRegion R d) = 0 ∧
    (Zeta23.OPICAFollowup.nearGapCombFamily L).positive.real
      (Zeta23.OPICA.signedBudgetRegion R d) ≤
      (Real.pi ^ 2 * R ^ 2 / (4 * d ^ 2)) *
        (1 - Real.exp (-L)) * 36 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_offinteger_mass_budget
    hL hu hR hd hdhalf
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_physical_negative_scale_pairing
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_physical_equals_explicit
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_physical_fourier_selfdual
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_actual_offinteger_mass_budget
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_CT1_canonical_selfdual_if_scalar_bridge
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_explicit_CT1_source_fourier_selfdual
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_offlattice_nonnegative
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_genuine_jordan_gap
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_origin_every_compact
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_actual_ct1_signed_compact_gap
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_compact_measure_identity
#print axioms Zeta23.OPICAFollowup.W04W07Independent.expected_ct1_radius
end Zeta23.OPICAFollowup.W04W07Independent
