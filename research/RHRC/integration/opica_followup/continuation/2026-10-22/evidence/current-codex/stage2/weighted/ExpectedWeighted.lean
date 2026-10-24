import Zeta23.OPICAFollowup.WeightedMixing

noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal FourierTransform SchwartzMap
open Zeta23.OPICA Zeta23.OPICAFollowup

namespace OPICAWeightedIndependent

/-- Independent full frozen statement, with arbitrary complex locally finite
input and the true-variation exponential moment. No support assumption. -/
theorem expected_weighted_mixture_exists_fourier
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2<a) (hm : mixingExponentialMoment a sigma<∞) :
    ∃ (nu : LocallyFiniteComplexMeasure) (hg : nu.HasLinearGrowth),
      nu=weightedDilationMixture sigma a ha.le hm ∧
      (∀ f : SchwartzMap ℝ ℂ, nu.integral f=
        sigma.integral (fun t => dilatedCombDistribution t f)) ∧
      𝓕 (nu.distributionOfLinearGrowth hg)=
        (weightedDilationMixture (reflectedMixingMeasure sigma) a ha.le
          (mixingExponentialMoment_reflect_lt_top sigma a hm)).distributionOfLinearGrowth
            (weightedDilationMixture_growth _ _ _ _) ∧
      nu.compactRestriction ({0} : Set ℝ) isCompact_singleton ({0} : Set ℝ)=
        sigma.integral (fun t => (Real.exp (t/2) : ℂ)) ∧
      (∀ (f : SchwartzMap ℝ ℂ) (i : Fin 4),
        Integrable (fun z : ℝ × ℤ => (Real.exp (z.1/2) : ℂ)*f (mixtureLatticePoint z))
          ((mixingCoordinate sigma i).prod (Measure.count : Measure ℤ))) :=
  weighted_mixture_exists_fourier sigma a ha hm

/-- The actual positive constructor acts on the entire lattice, and evaluation
on arbitrary measurable sets is the literal mixture integral. -/
theorem expected_positive_actual_measure (mu : Measure ℝ) [SFinite mu]
    (s : Set ℝ) (hs : MeasurableSet s) :
    positiveDilationMixture mu s=∫⁻ t, dilatedCombMeasure t s ∂mu :=
  positiveDilationMixture_apply mu s hs

theorem expected_positive_parameter_atom (t : ℝ) :
    positiveDilationMixture (Measure.dirac t)=dilatedCombMeasure t := by
  apply Measure.ext
  intro s hs
  rw [positiveDilationMixture_apply _ s hs,lintegral_dirac]

/-- Even a finite input atom gives infinite whole-line output mass, so the
construction has not accidentally been confined to finite complex measures. -/
theorem expected_infinite_output_mass :
    positiveDilationMixture (Measure.dirac (0 : ℝ)) univ=∞ := by
  rw [expected_positive_parameter_atom]
  simp only [dilatedCombMeasure,zero_div,Real.exp_zero,ENNReal.ofReal_one,one_smul,
    scaledLatticeMeasure,Measure.map_apply (scaledLatticePoint_measurable 0) MeasurableSet.univ,
    preimage_univ]
  exact Measure.count_apply_infinite infinite_univ

theorem expected_positive_origin (mu : Measure ℝ) [SFinite mu] :
    positiveDilationMixture mu ({0} : Set ℝ)=∫⁻ t, ENNReal.ofReal (Real.exp (t/2)) ∂mu :=
  positiveDilationMixture_origin mu

def imaginaryParameterAtom : LocallyFiniteComplexMeasure :=
  ⟨localJordanDifference 0 0,localJordanDifference (Measure.dirac (0 : ℝ)) 0⟩

lemma imaginaryParameterAtom_moment : mixingExponentialMoment 1 imaginaryParameterAtom<∞ := by
  apply (lintegral_mono' imaginaryParameterAtom.totalVariation_le_control le_rfl).trans_lt
  simp [imaginaryParameterAtom,LocallyFiniteComplexMeasure.variationControl,
    LocallyFiniteSignedMeasure.totalVariation,localJordanDifference]

/-- Purely imaginary coefficients are retained, including their sign. -/
theorem expected_imaginary_origin :
    (weightedDilationMixture imaginaryParameterAtom 1 (by norm_num)
      imaginaryParameterAtom_moment).compactRestriction ({0} : Set ℝ)
        isCompact_singleton ({0} : Set ℝ)=I := by
  rw [weightedDilationMixture_origin]
  simp [imaginaryParameterAtom,LocallyFiniteComplexMeasure.integral,localJordanDifference]

/-- The absolute Fubini gate holds without a compact-support or positivity
premise on the complex parameter measure. -/
theorem expected_full_product_integrability (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2<a) (hm : mixingExponentialMoment a sigma<∞)
    (f : SchwartzMap ℝ ℂ) (i : Fin 4) :
    Integrable (fun z : ℝ × ℤ => (Real.exp (z.1/2) : ℂ)*f (mixtureLatticePoint z))
      ((mixingCoordinate sigma i).prod (Measure.count : Measure ℤ)) :=
  positiveDilationMixture_product_integrable _ a ha.le (mixingCoordinate_moment sigma a hm i) f

def realParameterMeasure (mu : LocallyFiniteSignedMeasure) : LocallyFiniteComplexMeasure :=
  ⟨mu,localJordanDifference 0 0⟩

/-- Every actual locally finite real signed parameter measure embeds in the
full theorem, and the constructed output has zero imaginary Jordan component. -/
theorem expected_real_parameter_output (mu : LocallyFiniteSignedMeasure) (a : ℝ)
    (ha : 1/2<a) (hm : mixingExponentialMoment a (realParameterMeasure mu)<∞) :
    (weightedDilationMixture (realParameterMeasure mu) a ha.le hm).imPart=
      localJordanDifference 0 0 := by
  simp [weightedDilationMixture,mixingCoordinate,realParameterMeasure,
    positiveDilationMixture,localJordanDifference]

end OPICAWeightedIndependent

#print axioms Zeta23.OPICAFollowup.weighted_mixture_exists_fourier
#print axioms OPICAWeightedIndependent.expected_weighted_mixture_exists_fourier
#print axioms OPICAWeightedIndependent.expected_positive_actual_measure
#print axioms OPICAWeightedIndependent.expected_positive_parameter_atom
#print axioms OPICAWeightedIndependent.expected_infinite_output_mass
#print axioms OPICAWeightedIndependent.expected_positive_origin
#print axioms OPICAWeightedIndependent.expected_imaginary_origin
#print axioms OPICAWeightedIndependent.expected_full_product_integrability
#print axioms OPICAWeightedIndependent.expected_real_parameter_output
