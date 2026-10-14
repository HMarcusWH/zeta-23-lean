import Zeta23.ExceptionalZero.UniversalSincSignedLaplace
import Zeta23.ExceptionalZero.PositiveLaplaceAnalytic
import Mathlib.Tactic.LinearCombination

/-!
# Exact Laplace transform of the actual signed cutoff tail

The initial interval is retained as a literal compact correction. On the
safe half-plane the signed tail has transform
  epsilon*(R(z)-H_T(z)) + M*exp(-(z-theta)*T)/(z-theta).
This specializes to the rational M/(z-theta) term when T=0. The complete
actual squared-Weil resolvent R still has poles at 2(rho-1/2), and the
underlying physical correlation remains C(2a).

No positivity assumption is needed for this algebraic transport. Genuine
integrability of every split term is supplied by the actual source's
coefficient bound and elementary exponential decay.
-/

noncomputable section

open Set MeasureTheory Complex Filter
open scoped Topology

namespace Zeta23.ExceptionalZero

private theorem integral_const_mul_tail_C (μ : Measure ℝ) (c : ℂ) (f : ℝ → ℂ) :
    (∫ a : ℝ, c * f a ∂μ) = c * ∫ a : ℝ, f a ∂μ := integral_const_mul c f

/-- Equality of the real and complex kernel norms gives genuine Laplace
integrability transport, including signed measurable real sources. -/
theorem integrable_complexLaplaceKernel_iff_real_weight {u : ℝ → ℝ}
    (hu : Measurable u) (z : ℂ) :
    Integrable (fun a : ℝ => (u a : ℂ) * Complex.exp (-z * (a : ℂ))) positiveLaplaceHalfLine ↔
      Integrable (positiveLaplaceWeight u z.re) positiveLaplaceHalfLine := by
  have hCmeas : AEStronglyMeasurable
      (fun a : ℝ => (u a : ℂ) * Complex.exp (-z * (a : ℂ))) positiveLaplaceHalfLine :=
    ((Complex.continuous_ofReal.measurable.comp hu).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable)
      .aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable (positiveLaplaceWeight u z.re) positiveLaplaceHalfLine :=
    (hu.mul ((measurable_const.mul measurable_id).exp)).aestronglyMeasurable
  apply integrable_congr' hCmeas hRmeas
  filter_upwards with a
  unfold positiveLaplaceWeight
  rw [Complex.norm_mul, Complex.norm_real, Complex.norm_exp, norm_mul]
  have hre : (-z * (a : ℂ)).re = -z.re * a := by simp only
    [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre, Real.norm_of_nonneg (Real.exp_pos _).le]

def fixedOriginalSincInitialLaplace (T : ℝ) (z : ℂ) : ℂ :=
  ∫ a : ℝ in Ico 0 T,
    (fixedOriginalSincCorrelationReal a : ℂ) * Complex.exp (-z * (a : ℂ))

private theorem integrableOn_fixedOriginalSincCorrelation_complex_kernel
    {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun a : ℝ =>
      (fixedOriginalSincCorrelationReal a : ℂ) * Complex.exp (-z * (a : ℂ))) (Ici 0) :=
  (integrable_complexLaplaceKernel_iff_real_weight
    measurable_fixedOriginalSincCorrelationReal z).mpr
      (integrable_fixedOriginalSincCorrelation_weight hz)

/-- Subtracting the actual compact initial correction leaves the actual
correlation's tail transform. -/
theorem integral_fixedOriginalSincCorrelation_tail {T : ℝ} (hT : 0 ≤ T)
    {z : ℂ} (hz : 1 < z.re) :
    (∫ a : ℝ in Ici T,
      (fixedOriginalSincCorrelationReal a : ℂ) * Complex.exp (-z * (a : ℂ))) =
      filteredResolvent fixedOriginalSincSquaredFilter (1 / 2 : ℂ) z -
        fixedOriginalSincInitialLaplace T z := by
  have hfull := integrableOn_fixedOriginalSincCorrelation_complex_kernel hz
  have hhead := hfull.mono_set (show Ico (0 : ℝ) T ⊆ Ici 0 from fun _ h => h.1)
  have htail := hfull.mono_set (show Ici T ⊆ Ici (0 : ℝ) from fun _ h => hT.trans h)
  have hdisjoint : Disjoint (Ico (0 : ℝ) T) (Ici T) := by
    apply Set.disjoint_left.mpr
    intro a ha htail
    exact (not_le_of_gt ha.2) htail
  have hsplit := setIntegral_union hdisjoint measurableSet_Ici hhead htail
  rw [Ico_union_Ici_eq_Ici hT] at hsplit
  have hsafe :
      (∫ a : ℝ in Ici 0,
        (fixedOriginalSincCorrelationReal a : ℂ) * Complex.exp (-z * (a : ℂ))) =
        filteredResolvent fixedOriginalSincSquaredFilter (1 / 2 : ℂ) z :=
    positiveLaplaceTransform_fixedOriginalSincCorrelation_safe hz
  rw [hsafe] at hsplit
  unfold fixedOriginalSincInitialLaplace
  linear_combination -hsplit

private theorem signedTail_complex_kernel_indicator (T θ M ε : ℝ) (z : ℂ) :
    (fun a : ℝ => (fixedOriginalSincSignedTail T θ M ε a : ℂ) *
      Complex.exp (-z * (a : ℂ))) =
      (Ici T).indicator (fun a : ℝ =>
        (ε : ℂ) * ((fixedOriginalSincCorrelationReal a : ℂ) * Complex.exp (-z * (a : ℂ))) +
        (M : ℂ) * Complex.exp (-(z - (θ : ℂ)) * (a : ℂ))) := by
  funext a
  by_cases ha : a ∈ Ici T
  · simp only [fixedOriginalSincSignedTail, Set.indicator_of_mem ha]
    rw [Complex.ofReal_add, add_mul]
    have herror : ((M * Real.exp (θ * a) : ℝ) : ℂ) * Complex.exp (-z * (a : ℂ)) =
        (M : ℂ) * Complex.exp (-(z - (θ : ℂ)) * (a : ℂ)) := by
      rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
      rw [show ((θ * a : ℝ) : ℂ) + -z * (a : ℂ) =
        -(z - (θ : ℂ)) * (a : ℂ) by push_cast; ring]
    rw [herror, Complex.ofReal_mul]
    ring
  · simp only [fixedOriginalSincSignedTail, Set.indicator_of_notMem ha,
      Complex.ofReal_zero, zero_mul]

private theorem integral_error_tail {T θ : ℝ} {z : ℂ} (hθ : θ < z.re) :
    (∫ a : ℝ in Ici T, Complex.exp (-(z - (θ : ℂ)) * (a : ℂ))) =
      Complex.exp (-(z - (θ : ℂ)) * (T : ℂ)) / (z - (θ : ℂ)) := by
  have hdecay : (-(z - (θ : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
    linarith
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi hdecay T]
  simp only [neg_div, div_neg, neg_neg]

/-- Exact safe transform of the literal cutoff signed tail. -/
theorem positiveLaplaceTransform_fixedOriginalSincSignedTail_safe
    {T θ M ε : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : 1 < z.re) (hθ : θ < z.re) :
    positiveLaplaceTransform (fixedOriginalSincSignedTail T θ M ε) z =
      (ε : ℂ) *
        (filteredResolvent fixedOriginalSincSquaredFilter (1 / 2 : ℂ) z -
          fixedOriginalSincInitialLaplace T z) +
      (M : ℂ) * Complex.exp (-(z - (θ : ℂ)) * (T : ℂ)) / (z - (θ : ℂ)) := by
  unfold positiveLaplaceTransform
  rw [signedTail_complex_kernel_indicator, integral_indicator measurableSet_Ici]
  unfold positiveLaplaceHalfLine
  rw [Measure.restrict_restrict_of_subset
    (show Ici T ⊆ Ici (0 : ℝ) from fun _ h => hT.trans h)]
  have hfull := integrableOn_fixedOriginalSincCorrelation_complex_kernel hz
  have htail := hfull.mono_set (show Ici T ⊆ Ici (0 : ℝ) from fun _ h => hT.trans h)
  have hdecay : (-(z - (θ : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
    linarith
  have herror : IntegrableOn (fun a : ℝ =>
      Complex.exp (-(z - (θ : ℂ)) * (a : ℂ))) (Ici T) :=
    integrableOn_Ici_iff_integrableOn_Ioi.mpr (integrableOn_exp_mul_complex_Ioi hdecay T)
  rw [integral_add (htail.const_mul (ε : ℂ)) (herror.const_mul (M : ℂ)),
    integral_const_mul_tail_C, integral_const_mul_tail_C,
    integral_fixedOriginalSincCorrelation_tail hT hz, integral_error_tail hθ]
  ring

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.integrable_complexLaplaceKernel_iff_real_weight
#print axioms Zeta23.ExceptionalZero.integral_fixedOriginalSincCorrelation_tail
#print axioms Zeta23.ExceptionalZero.positiveLaplaceTransform_fixedOriginalSincSignedTail_safe
