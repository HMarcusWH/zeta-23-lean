import Zeta23.ExceptionalZero.UniversalSincSignedTailTransform
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The actual compact initial correction is entire

The hard cutoff is retained. Its actual weighted integrability for every
real parameter comes from continuity of the absolutely summable fixed
family on the compact initial interval. Splitting a signed source into
its positive and negative parts then lets the literal tilt/MGF theorem
prove analyticity; no smoothing of the cutoff or analyticity premise is
used.
-/

noncomputable section

open Set MeasureTheory Complex Filter
open scoped Topology

namespace Zeta23.ExceptionalZero

private def signedLaplacePositivePart (u : ℝ → ℝ) (a : ℝ) : ℝ := max (u a) 0
private def signedLaplaceNegativePart (u : ℝ → ℝ) (a : ℝ) : ℝ := max (-u a) 0

private theorem integrable_positivePart_weight {u : ℝ → ℝ} (hu : Measurable u) {p : ℝ}
    (hInt : Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine) :
    Integrable (positiveLaplaceWeight (signedLaplacePositivePart u) p) positiveLaplaceHalfLine := by
  have hmeas : AEStronglyMeasurable
      (positiveLaplaceWeight (signedLaplacePositivePart u) p) positiveLaplaceHalfLine :=
    ((hu.max measurable_const).mul ((measurable_const.mul measurable_id).exp)).aestronglyMeasurable
  refine hInt.norm.mono' hmeas ?_
  filter_upwards with a
  unfold positiveLaplaceWeight signedLaplacePositivePart
  rw [Real.norm_of_nonneg
      (mul_nonneg (le_max_right (u a) 0) (Real.exp_pos _).le), norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (max_le (le_abs_self (u a)) (abs_nonneg (u a))) (Real.exp_pos _).le

private theorem integrable_negativePart_weight {u : ℝ → ℝ} (hu : Measurable u) {p : ℝ}
    (hInt : Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine) :
    Integrable (positiveLaplaceWeight (signedLaplaceNegativePart u) p) positiveLaplaceHalfLine := by
  have hneg : Integrable (positiveLaplaceWeight (fun a => -u a) p) positiveLaplaceHalfLine := by
    have heq : positiveLaplaceWeight (fun a => -u a) p = -positiveLaplaceWeight u p := by
      funext a
      simp [positiveLaplaceWeight]
    rw [heq]
    exact hInt.neg
  exact integrable_positivePart_weight hu.neg hneg

/-- Signed measurable sources with genuine weighted integrability at every
real parameter have an entire Laplace transform. -/
theorem analyticAt_signedLaplaceTransform_of_all_integrable {u : ℝ → ℝ}
    (hu : Measurable u)
    (hInt : ∀ p : ℝ, Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine) (z : ℂ) :
    AnalyticAt ℂ (positiveLaplaceTransform u) z := by
  have hPmeas : Measurable (signedLaplacePositivePart u) := hu.max measurable_const
  have hNmeas : Measurable (signedLaplaceNegativePart u) := hu.neg.max measurable_const
  have hPint (p : ℝ) := integrable_positivePart_weight hu (hInt p)
  have hNint (p : ℝ) := integrable_negativePart_weight hu (hInt p)
  have hPA : AnalyticAt ℂ (positiveLaplaceTransform (signedLaplacePositivePart u)) z :=
    analyticAt_positiveLaplaceTransform_of_integrable_nhds hPmeas
      (fun a _ => le_max_right (u a) 0) (Eventually.of_forall hPint)
  have hNA : AnalyticAt ℂ (positiveLaplaceTransform (signedLaplaceNegativePart u)) z :=
    analyticAt_positiveLaplaceTransform_of_integrable_nhds hNmeas
      (fun a _ => le_max_right (-u a) 0) (Eventually.of_forall hNint)
  have hvalue (a : ℝ) : u a = signedLaplacePositivePart u a - signedLaplaceNegativePart u a := by
    by_cases ha : 0 ≤ u a
    · simp only [signedLaplacePositivePart, signedLaplaceNegativePart,
        max_eq_left ha, max_eq_right (neg_nonpos.mpr ha), sub_zero]
    · have hle : u a ≤ 0 := le_of_not_ge ha
      simp only [signedLaplacePositivePart, signedLaplaceNegativePart,
        max_eq_right hle, max_eq_left (neg_nonneg.mpr hle), zero_sub, neg_neg]
  have heq : positiveLaplaceTransform u =
      positiveLaplaceTransform (signedLaplacePositivePart u) -
        positiveLaplaceTransform (signedLaplaceNegativePart u) := by
    funext w
    have hPC := (integrable_complexLaplaceKernel_iff_real_weight hPmeas w).mpr (hPint w.re)
    have hNC := (integrable_complexLaplaceKernel_iff_real_weight hNmeas w).mpr (hNint w.re)
    have hfun : (fun a : ℝ => (u a : ℂ) * Complex.exp (-w * (a : ℂ))) =
        fun a : ℝ => (signedLaplacePositivePart u a : ℂ) * Complex.exp (-w * (a : ℂ)) -
          (signedLaplaceNegativePart u a : ℂ) * Complex.exp (-w * (a : ℂ)) := by
      funext a
      calc
        _ = ((signedLaplacePositivePart u a - signedLaplaceNegativePart u a : ℝ) : ℂ) *
            Complex.exp (-w * (a : ℂ)) := congrArg
              (fun v : ℝ => (v : ℂ) * Complex.exp (-w * (a : ℂ))) (hvalue a)
        _ = _ := by rw [Complex.ofReal_sub, sub_mul]
    simp only [positiveLaplaceTransform, Pi.sub_apply]
    rw [hfun, integral_sub hPC hNC]
  rw [heq]
  exact hPA.sub hNA

def fixedOriginalSincInitialSource (T : ℝ) : ℝ → ℝ :=
  (Ico 0 T).indicator fixedOriginalSincCorrelationReal

theorem measurable_fixedOriginalSincInitialSource (T : ℝ) :
    Measurable (fixedOriginalSincInitialSource T) :=
  measurable_fixedOriginalSincCorrelationReal.indicator measurableSet_Ico

/-- All weighted initial-source integrals are genuine compact integrals. -/
theorem integrable_fixedOriginalSincInitialSource_weight {T : ℝ} (hT : 0 ≤ T) (p : ℝ) :
    Integrable (positiveLaplaceWeight (fixedOriginalSincInitialSource T) p)
      positiveLaplaceHalfLine := by
  have hC : ContinuousOn fixedOriginalSincCorrelation (Icc 0 T) := by
    have heq : fixedOriginalSincCorrelation =
        filteredZeroFamily fixedOriginalSincSquaredFilter (1 / 2 : ℂ) :=
      funext fixedOriginalSincCorrelation_eq_filteredFamily
    rw [heq]
    exact continuousOn_filteredZeroFamily_Icc
      (absolutelySummable_originalSincSquaredFilter CCM.UniversalSinc.fixedScale_pos)
      (by norm_num) hT
  have hR : ContinuousOn fixedOriginalSincCorrelationReal (Icc 0 T) :=
    Complex.continuous_re.comp_continuousOn hC
  have hExp : Continuous (fun a : ℝ => Real.exp (-p * a)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hcont : ContinuousOn (positiveLaplaceWeight fixedOriginalSincCorrelationReal p) (Icc 0 T) :=
    hR.mul hExp.continuousOn
  have hIcc : IntegrableOn (positiveLaplaceWeight fixedOriginalSincCorrelationReal p)
      (Icc 0 T) volume := hcont.integrableOn_Icc
  have hIco := hIcc.mono_set Ico_subset_Icc_self
  have hcut := hIco.integrable_indicator (show MeasurableSet (Ico (0 : ℝ) T) from measurableSet_Ico)
  have hhalf : Integrable ((Ico 0 T).indicator (positiveLaplaceWeight fixedOriginalSincCorrelationReal p))
      positiveLaplaceHalfLine := hcut.mono_measure Measure.restrict_le_self
  have heq : positiveLaplaceWeight (fixedOriginalSincInitialSource T) p =
      (Ico 0 T).indicator (positiveLaplaceWeight fixedOriginalSincCorrelationReal p) := by
    funext a
    by_cases ha : a ∈ Ico 0 T
    · simp only [positiveLaplaceWeight, fixedOriginalSincInitialSource, Set.indicator_of_mem ha]
    · simp only [positiveLaplaceWeight, fixedOriginalSincInitialSource,
        Set.indicator_of_notMem ha, zero_mul]
  rw [heq]
  exact hhalf

theorem positiveLaplaceTransform_fixedOriginalSincInitialSource (T : ℝ) (z : ℂ) :
    positiveLaplaceTransform (fixedOriginalSincInitialSource T) z = fixedOriginalSincInitialLaplace T z := by
  have hfun : (fun a : ℝ => (fixedOriginalSincInitialSource T a : ℂ) * Complex.exp (-z * (a : ℂ))) =
      (Ico 0 T).indicator (fun a : ℝ =>
        (fixedOriginalSincCorrelationReal a : ℂ) * Complex.exp (-z * (a : ℂ))) := by
    funext a
    by_cases ha : a ∈ Ico 0 T
    · simp only [fixedOriginalSincInitialSource, Set.indicator_of_mem ha]
    · simp only [fixedOriginalSincInitialSource, Set.indicator_of_notMem ha,
        Complex.ofReal_zero, zero_mul]
  unfold positiveLaplaceTransform
  rw [hfun, integral_indicator measurableSet_Ico]
  unfold positiveLaplaceHalfLine
  rw [Measure.restrict_restrict_of_subset
    (show Ico (0 : ℝ) T ⊆ Ici 0 from fun _ h => h.1)]
  rfl

/-- The actual unsmoothed compact correction is entire. -/
theorem analyticAt_fixedOriginalSincInitialLaplace {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    AnalyticAt ℂ (fixedOriginalSincInitialLaplace T) z := by
  have heq : fixedOriginalSincInitialLaplace T =
      positiveLaplaceTransform (fixedOriginalSincInitialSource T) :=
    funext fun w => (positiveLaplaceTransform_fixedOriginalSincInitialSource T w).symm
  rw [heq]
  exact analyticAt_signedLaplaceTransform_of_all_integrable
    (measurable_fixedOriginalSincInitialSource T) (integrable_fixedOriginalSincInitialSource_weight hT) z

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.analyticAt_signedLaplaceTransform_of_all_integrable
#print axioms Zeta23.ExceptionalZero.integrable_fixedOriginalSincInitialSource_weight
#print axioms Zeta23.ExceptionalZero.positiveLaplaceTransform_fixedOriginalSincInitialSource
#print axioms Zeta23.ExceptionalZero.analyticAt_fixedOriginalSincInitialLaplace
