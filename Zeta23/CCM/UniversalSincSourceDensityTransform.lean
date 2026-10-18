import Zeta23.CCM.UniversalSincSourceDensity
import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.Fourier.Convolution

/-!
# Real physical Fourier identity for the actual prefix/tail density

The proof retains the paper's positive forward phase and the prescribed
unequal boxes. Mixed prefix/tail Fubini is justified by an actual integrable
joint function. This is a real-axis identity; the complex extension and
the inverse/measure identification require their separate consuming proofs.
-/

noncomputable section

open Set MeasureTheory Complex ContinuousLinearMap
open scoped Topology Convolution FourierTransform

namespace Zeta23.CCM.UniversalSinc

private theorem integral_const_mul_measure_C (μ : Measure ℝ) (c : ℂ) (f : ℝ → ℂ) :
    (∫ x : ℝ, c * f x ∂μ) = c * ∫ x : ℝ, f x ∂μ := integral_const_mul c f

private theorem integral_mul_const_measure_C (μ : Measure ℝ) (c : ℂ) (f : ℝ → ℂ) :
    (∫ x : ℝ, f x * c ∂μ) = (∫ x : ℝ, f x ∂μ) * c := integral_mul_const c f

def uniformBoxDensityComplex (a : ℝ) (x : ℝ) : ℂ := (uniformBoxDensity a x : ℂ)

theorem integrable_uniformBoxDensityComplex (a : ℝ) : Integrable (uniformBoxDensityComplex a) := by
  exact (integrable_uniformBoxDensity a).ofReal

/-- Exact real physical transform of a literal normalized box. -/
theorem paperFT_uniformBoxDensity_ofReal {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Zeta23.paperFT (uniformBoxDensityComplex a) (r : ℂ) = sinc ((a * r : ℝ) : ℂ) := by
  by_cases hr : r = 0
  · subst r
    rw [Zeta23.paperFT_def]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one,
      uniformBoxDensityComplex]
    rw [integral_complex_ofReal, integral_uniformBoxDensity ha]
    simp
  have hfun : (fun x : ℝ => uniformBoxDensityComplex a x * Complex.exp (I * (r : ℂ) * x)) =
      (Icc (-a) a).indicator
        (fun x : ℝ => ((1 / (2 * a) : ℝ) : ℂ) * Complex.exp ((r : ℂ) * x * I)) := by
    funext x
    by_cases hx : x ∈ Icc (-a) a
    · simp only [uniformBoxDensityComplex, uniformBoxDensity, Set.indicator_of_mem hx]
      congr 2
      ring
    · simp [uniformBoxDensityComplex, uniformBoxDensity, hx]
  rw [Zeta23.paperFT_def, hfun, integral_indicator measurableSet_Icc,
    integral_const_mul_measure_C, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  have hi : (∫ x in -a..a, Complex.exp ((r : ℂ) * x * I)) =
      ((2 * a : ℝ) : ℂ) * (Real.sinc (a * r) : ℂ) := by
    have hc := intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => Complex.exp ((x : ℂ) * I)) (a := -a) (b := a) hr
    simp only [Complex.ofReal_mul, mul_neg] at hc
    rw [hc, integral_exp_mul_I_eq_sinc, Complex.real_smul]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero, add_zero,
        zero_add] <;>
      rw [mul_comm r a] <;>
      field_simp [hr] <;> ring
  rw [hi, sinc_ofReal]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero, add_zero,
      zero_add] <;>
    field_simp [ha.ne'] <;> ring

private theorem boxPair_complex_eq_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fun x : ℝ => (uniformBoxPairDensity a b x : ℂ)) =
      uniformBoxDensityComplex a ⋆[mul ℂ ℂ, volume] uniformBoxDensityComplex b := by
  funext x
  rw [uniformBoxPairDensity_eq_convolution ha hb]
  change ((∫ y : ℝ, uniformBoxDensity a y * uniformBoxDensity b (x - y) : ℝ) : ℂ) =
    ∫ y : ℝ, uniformBoxDensityComplex a y * uniformBoxDensityComplex b (x - y)
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with y
  simp only [uniformBoxDensityComplex, Complex.ofReal_mul]

theorem paperFT_originalBoxPairDensity_ofReal {s : ℝ} (hs : 0 < s) (r : ℝ) :
    Zeta23.paperFT (fun x : ℝ => (originalBoxPairDensity s x : ℂ)) (r : ℂ) =
      partialProduct s r 2 := by
  unfold originalBoxPairDensity
  rw [boxPair_complex_eq_convolution (width_pos hs 0) (width_pos hs 1),
    Zeta23.paperFT_ofReal_eq_fourier,
    Real.fourier_mul_convolution_eq (integrable_uniformBoxDensityComplex _)
      (integrable_uniformBoxDensityComplex _),
    ← Zeta23.paperFT_ofReal_eq_fourier, ← Zeta23.paperFT_ofReal_eq_fourier,
    paperFT_uniformBoxDensity_ofReal (width_pos hs 0),
    paperFT_uniformBoxDensity_ofReal (width_pos hs 1)]
  simp only [partialProduct, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    Complex.ofReal_mul]

private theorem density_joint_character_integrable {s : ℝ} (hs : 0 < s) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ => (originalBoxPairDensity s (p.2 - p.1) : ℂ) *
      Complex.exp (I * (r : ℂ) * (p.2 : ℂ))) ((originalSourceTailLaw s 2).prod volume) := by
  apply (originalDensityCandidate_joint_integrable hs).mono'
  · have hc : Continuous (fun p : ℝ × ℝ => (originalBoxPairDensity s (p.2 - p.1) : ℂ) *
        Complex.exp (I * (r : ℂ) * (p.2 : ℂ))) := by
      exact (Complex.continuous_ofReal.comp ((continuous_originalBoxPairDensity s).comp
        (continuous_snd.sub continuous_fst))).mul
        (Complex.continuous_exp.comp ((continuous_const.mul continuous_const).mul
          (Complex.continuous_ofReal.comp continuous_snd)))
    exact hc.aestronglyMeasurable
  · filter_upwards with p
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : ‖Complex.exp (I * (r : ℂ) * (p.2 : ℂ))‖ = 1 := by
      rw [show I * (r : ℂ) * (p.2 : ℂ) = I * ((r * p.2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_exp_I_mul_ofReal]
    rw [he, mul_one, abs_of_nonneg (originalBoxPairDensity_nonneg hs _)]

private theorem prefix_shift_transform (s r y : ℝ) :
    (∫ x : ℝ, (originalBoxPairDensity s (x - y) : ℂ) * Complex.exp (I * (r : ℂ) * (x : ℂ))) =
      Zeta23.paperFT (fun x : ℝ => (originalBoxPairDensity s x : ℂ)) (r : ℂ) *
        Complex.exp (I * (r : ℂ) * (y : ℂ)) := by
  have hfun : (fun x : ℝ => (originalBoxPairDensity s (x - y) : ℂ) *
      Complex.exp (I * (r : ℂ) * (x : ℂ))) =
      (fun x : ℝ => (originalBoxPairDensity s ((x - y)) : ℂ) *
        Complex.exp (I * (r : ℂ) * (((x - y) + y : ℝ) : ℂ))) := by
    funext x
    rw [sub_add_cancel]
  rw [hfun, integral_sub_right_eq_self
    (fun x : ℝ => (originalBoxPairDensity s x : ℂ) *
      Complex.exp (I * (r : ℂ) * ((x + y : ℝ) : ℂ))) y]
  have hsplit : (fun x : ℝ => (originalBoxPairDensity s x : ℂ) *
      Complex.exp (I * (r : ℂ) * ((x + y : ℝ) : ℂ))) =
      (fun x : ℝ => ((originalBoxPairDensity s x : ℂ) * Complex.exp (I * (r : ℂ) * (x : ℂ))) *
        Complex.exp (I * (r : ℂ) * (y : ℂ))) := by
    funext x
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [hsplit, integral_mul_const_measure_C]
  rfl

/-- The literal positive compact density has the literal original real
Fourier product; neither visibility nor a transform bridge is supplied. -/
theorem paperFT_originalDensityCandidate_ofReal {s : ℝ} (hs : 0 < s) (r : ℝ) :
    Zeta23.paperFT (fun x : ℝ => (originalDensityCandidate s x : ℂ)) (r : ℂ) =
      product s (r : ℂ) := by
  letI : IsProbabilityMeasure (originalSourceTailLaw s 2) :=
    originalSourceTailLaw_isProbabilityMeasure hs.le 2
  rw [Zeta23.paperFT_def]
  have hinner : ∀ x : ℝ, (originalDensityCandidate s x : ℂ) * Complex.exp (I * (r : ℂ) * x) =
      ∫ y : ℝ, (originalBoxPairDensity s (x - y) : ℂ) * Complex.exp (I * (r : ℂ) * x)
        ∂originalSourceTailLaw s 2 := by
    intro x
    unfold originalDensityCandidate
    rw [← integral_complex_ofReal, integral_mul_const_measure_C]
  simp_rw [hinner]
  rw [← integral_integral_swap (density_joint_character_integrable hs r)]
  simp_rw [prefix_shift_transform]
  rw [integral_const_mul_measure_C]
  have hphase : (∫ y : ℝ, Complex.exp (I * (r : ℂ) * y) ∂originalSourceTailLaw s 2) =
      charFun (originalSourceTailLaw s 2) r := by
    rw [charFun_apply_real]
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    ring
  rw [hphase, paperFT_originalBoxPairDensity_ofReal hs,
    charFun_originalSourceTailLaw hs.le]
  simpa only [partialProduct, product] using
    (Multipliable.prod_mul_tprod_nat_mul'
      (f := fun n : ℕ => sinc ((width s n : ℂ) * (r : ℂ))) (k := 2)
      (multipliable_sinc_tail hs.le 2 (r : ℂ)))

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.paperFT_uniformBoxDensity_ofReal
#print axioms Zeta23.CCM.UniversalSinc.paperFT_originalBoxPairDensity_ofReal
#print axioms Zeta23.CCM.UniversalSinc.paperFT_originalDensityCandidate_ofReal
