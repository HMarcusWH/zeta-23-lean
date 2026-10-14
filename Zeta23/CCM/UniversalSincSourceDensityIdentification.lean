import Zeta23.CCM.UniversalSincSourceDensityTransform
import Zeta23.CCM.UniversalSincDetectorInverse
import Mathlib.Analysis.Fourier.Inversion

/-!
# Exact density and inverse identification for the original probability law

Both sides are the actual constructed objects. Probability and the
characteristic identity prove the source law's density measure. Function
Fourier inversion, with the explicit negative scaling and its absolute
Jacobian, identifies that positive compact density with the smooth inverse
candidate in the paper convention. No density/inverse bridge is a premise.
-/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology FourierTransform

namespace Zeta23.CCM.UniversalSinc

def originalDensityComplex (s x : ℝ) : ℂ := (originalDensityCandidate s x : ℂ)

def originalDensityMeasure (s : ℝ) : Measure ℝ :=
  volume.withDensity (fun x : ℝ => ENNReal.ofReal (originalDensityCandidate s x))

theorem originalDensityMeasure_isProbabilityMeasure {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (originalDensityMeasure s) := by
  constructor
  unfold originalDensityMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_originalDensityCandidate hs)
      (ae_of_all _ (originalDensityCandidate_nonneg hs)), integral_originalDensityCandidate hs]
  norm_num

theorem charFun_originalDensityMeasure {s : ℝ} (hs : 0 < s) (r : ℝ) :
    charFun (originalDensityMeasure s) r = product s (r : ℂ) := by
  rw [charFun_apply_real]
  unfold originalDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_originalDensityCandidate hs).measurable.ennreal_ofReal
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (originalDensityCandidate_nonneg hs _),
    RCLike.real_smul_eq_coe_mul]
  have hFT := paperFT_originalDensityCandidate_ofReal hs r
  rw [Zeta23.paperFT_def] at hFT
  apply Eq.trans _ hFT
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  congr 1
  ring

/-- The original infinite-convolution law is exactly the measure of the
actual positive compact density, proved through its transform. -/
theorem originalSourceLaw_eq_withDensity {s : ℝ} (hs : 0 < s) :
    originalSourceLaw s =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (originalDensityCandidate s x)) := by
  letI : IsProbabilityMeasure (originalSourceLaw s) := originalSourceLaw_isProbabilityMeasure hs.le
  letI : IsProbabilityMeasure (originalDensityMeasure s) := originalDensityMeasure_isProbabilityMeasure hs
  change originalSourceLaw s = originalDensityMeasure s
  apply Measure.ext_of_charFun
  funext r
  rw [charFun_originalSourceLaw hs.le, charFun_originalDensityMeasure hs]

theorem integrable_originalDensityComplex {s : ℝ} (hs : 0 < s) :
    Integrable (originalDensityComplex s) := (integrable_originalDensityCandidate hs).ofReal

theorem continuous_originalDensityComplex {s : ℝ} (hs : 0 < s) :
    Continuous (originalDensityComplex s) :=
  Complex.continuous_ofReal.comp (continuous_originalDensityCandidate hs)

/-- The forward sign conversion is explicit, including its factor `2π`. -/
theorem fourier_originalDensityComplex {s : ℝ} (hs : 0 < s) :
    𝓕 (originalDensityComplex s) =
      fun w : ℝ => product s (((-(2 * Real.pi)) * w : ℝ) : ℂ) := by
  funext w
  calc
    _ = Zeta23.paperFT (originalDensityComplex s) (-(2 * Real.pi * w)) :=
      Zeta23.fourier_eq_paperFT _ w
    _ = Zeta23.paperFT (originalDensityComplex s) (((-(2 * Real.pi)) * w : ℝ) : ℂ) := by
      congr 1
      push_cast
      ring
    _ = _ := paperFT_originalDensityCandidate_ofReal hs _

theorem integrable_fourier_originalDensityComplex {s : ℝ} (hs : 0 < s) :
    Integrable (𝓕 (originalDensityComplex s)) := by
  rw [fourier_originalDensityComplex hs]
  exact (integrable_product_ofReal hs).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))

private theorem inverse_of_fourier_density_eq_candidate {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (𝓕⁻ (𝓕 (originalDensityComplex s))) x = inverseCandidate s x := by
  let g : ℝ → ℂ := fun ξ => product s (ξ : ℂ) *
    Complex.exp (I * ((-x : ℝ) : ℂ) * (ξ : ℂ))
  calc
    _ = ∫ w : ℝ, g ((-(2 * Real.pi)) * w) := by
      rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul,
        fourier_originalDensityComplex hs]
      apply integral_congr_ae
      filter_upwards with w
      simp only [smul_eq_mul, g]
      rw [mul_comm]
      congr 1
      congr 1
      push_cast
      ring
    _ = |(-(2 * Real.pi) : ℝ)⁻¹| • ∫ ξ : ℝ, g ξ :=
      Measure.integral_comp_mul_left g (-(2 * Real.pi))
    _ = inverseCandidate s x := by
      have hnorm : |(-(2 * Real.pi) : ℝ)⁻¹| = 1 / (2 * Real.pi) := by
        rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
        simp only [one_div]
      rw [hnorm, RCLike.real_smul_eq_coe_mul]
      rfl

/-- Exact normalized inverse identity, derived from actual source/density
construction and function Fourier inversion. -/
theorem inverseCandidate_eq_originalDensityComplex {s : ℝ} (hs : 0 < s) :
    inverseCandidate s = originalDensityComplex s := by
  funext x
  calc
    _ = (𝓕⁻ (𝓕 (originalDensityComplex s))) x :=
      (inverse_of_fourier_density_eq_candidate hs x).symm
    _ = _ := (integrable_originalDensityComplex hs).fourierInv_fourier_eq
      (integrable_fourier_originalDensityComplex hs) (continuous_originalDensityComplex hs).continuousAt

/-- Smoothness transfers to the actual real density through the exact
normalized inverse identity, rather than through a caller certificate. -/
theorem contDiff_originalDensityCandidate {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (originalDensityCandidate s) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (originalDensityComplex s) := by
    rw [← inverseCandidate_eq_originalDensityComplex hs]
    exact contDiff_inverseCandidate hs
  have hre := Complex.reCLM.contDiff.comp hc
  simpa only [originalDensityComplex, Function.comp_def, Complex.reCLM_apply,
    Complex.ofReal_re] using hre

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.originalSourceLaw_eq_withDensity
#print axioms Zeta23.CCM.UniversalSinc.fourier_originalDensityComplex
#print axioms Zeta23.CCM.UniversalSinc.inverseCandidate_eq_originalDensityComplex
#print axioms Zeta23.CCM.UniversalSinc.contDiff_originalDensityCandidate
